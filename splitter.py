import bisect, calendar, colorsys, gc, hashlib, json, logging, os, re, shutil, struct, sys, xml.etree.ElementTree as ET, zipfile
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import date, timedelta
from pathlib import Path

import requests
from tqdm import tqdm

SNAP_DEFAULTS = {"Content": None, "IsSaved": False, "Media IDs": "", "Type": "snap"}
SNAP_KEYS = ["From", "Media Type", "Created", "Conversation Title", "IsSender", "Created(microseconds)"]
TARGET_JSON = {"chat_history.json", "snap_history.json", "friends.json"}
PHASE_NAMES = ["Extracting zips", "Matching media", "Writing output", "Fetching avatars"]
TIMESTAMP_MATCH_THRESHOLD = 30_000  # max ms proximity for timestamp matching
MEDIA_PENALTY = 5_000               # penalty per existing match to spread media
AVATAR_SIZE = 54
_GHOST_SVG = Path(__file__).parent / "ghost.svg"
GHOST_PATH = ET.parse(_GHOST_SVG).find(".//{http://www.w3.org/2000/svg}path").get("d")
SVG_NS = {"svg": "http://www.w3.org/2000/svg", "xlink": "http://www.w3.org/1999/xlink"}
LOGGER = logging.getLogger(__name__)


class Progress:
    """Single cumulative progress bar across all phases."""
    def __init__(self):
        self._phase = 0
        self._bar = tqdm(
            total=0, unit="it", leave=False, ascii=".:#", colour="#00d4aa",
            bar_format="{desc}  {bar}  {n_fmt}/{total_fmt} [{elapsed}]",
        )

    def phase(self, total):
        self._phase += 1
        desc = PHASE_NAMES[self._phase - 1] if self._phase <= len(PHASE_NAMES) else f"Phase {self._phase}"
        self._bar.total += total
        self._bar.set_description(f"[{self._phase}/{len(PHASE_NAMES)}] {desc}")
        self._bar.refresh()

    def update(self, n=1):
        self._bar.update(n)

    def close(self):
        self._bar.close()


def get_mtime(info):
    """Extract UTC mtime from ZipInfo central directory 0x5455 extra field."""
    extra = info.extra
    i = 0
    while i + 4 <= len(extra):
        tag, size = struct.unpack_from("<HH", extra, i)
        i += 4
        if tag == 0x5455 and size >= 5 and extra[i] & 1:
            return struct.unpack_from("<I", extra, i + 1)[0]
        i += size
    return calendar.timegm(info.date_time + (0, 0, -1))


def extract_zips(input_dir, tmp_dir, progress):
    """Extract json/ and chat_media/ from zips, preserving real timestamps."""
    zips = sorted(input_dir.glob("*.zip"))
    if not zips:
        sys.exit("No zip files found in 'input'.")

    primary = [z for z in zips if not re.search(r"-\d+\.zip$", z.name)]
    secondary = sorted(
        [z for z in zips if re.search(r"-\d+\.zip$", z.name)],
        key=lambda z: int(re.search(r"-(\d+)\.zip$", z.name).group(1)),
    )

    all_zips = primary + secondary
    progress.phase(len(all_zips))
    for zf_path in all_zips:
        with zipfile.ZipFile(zf_path) as zf:
            for info in zf.infolist():
                if info.is_dir():
                    continue
                parts = Path(info.filename).parts
                is_json = len(parts) > 1 and parts[-2] == "json" and parts[-1] in TARGET_JSON
                is_media = "chat_media" in parts

                if not (is_json or is_media):
                    continue

                if is_json:
                    dest = tmp_dir / "json" / parts[-1]
                else:
                    idx = parts.index("chat_media")
                    dest = tmp_dir / Path(*parts[idx:])

                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes(zf.read(info.filename))
                mtime = get_mtime(info)
                os.utime(dest, (mtime, mtime))
        progress.update(1)


def load_display_names(json_dir):
    """Parse friends.json to map Username -> Display Name."""
    path = json_dir / "friends.json"
    if not path.exists():
        return {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        return {
            e["Username"]: e.get("Display Name", "")
            for cat in data.values() if isinstance(cat, list)
            for e in cat if isinstance(e, dict) and "Username" in e
        }
    except (OSError, json.JSONDecodeError, TypeError) as exc:
        LOGGER.warning("Unable to load display names from %s: %s", path, exc)
        return {}


def load_history_json(json_dir, filename):
    """Load an optional Snapchat history file, returning an empty history if absent."""
    path = json_dir / filename
    if not path.exists():
        LOGGER.warning("%s was not found; continuing with an empty history.", path)
        return {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        LOGGER.warning("Unable to load %s; continuing with an empty history: %s", path, exc)
        return {}
    if not isinstance(data, dict):
        LOGGER.warning("%s did not contain a conversation object; continuing with an empty history.", path)
        return {}
    return data


def find_owner(chat_data, snap_data):
    """Identify account owner from first outgoing message."""
    for conv in [*chat_data.values(), *snap_data.values()]:
        for m in conv:
            if m.get("IsSender"):
                return m.get("From", "unknown_user")
    return "unknown_user"


def build_days(chat_data, snap_data):
    """Organize all messages into a days[date][conv_id] structure."""
    days = defaultdict(lambda: defaultdict(list))
    usernames = set()
    group_info = []
    group_titles = {}

    for c_id, msgs in chat_data.items():
        participants, title = set(), None
        for m in msgs:
            m["Type"] = "message"
            days[m["Created"][:10]][c_id].append(m)
            if f := m.get("From"):
                usernames.add(f)
                participants.add(f)
            title = title or m.get("Conversation Title")
        if "-" in c_id:
            group_titles[c_id] = title or c_id
            group_info.append({"group_id": c_id, "name": title or c_id, "members": sorted(participants)})
        else:
            usernames.add(c_id)

    for c_id, msgs in snap_data.items():
        for m in msgs:
            days[m["Created"][:10]][c_id].append({k: m.get(k) for k in SNAP_KEYS} | SNAP_DEFAULTS)
            if f := m.get("From"):
                usernames.add(f)
            if "-" in c_id and c_id not in group_titles:
                t = m.get("Conversation Title")
                if t:
                    group_titles[c_id] = t
        if "-" not in c_id:
            usernames.add(c_id)

    return days, usernames, group_info, group_titles


def _build_message_index(days):
    """Build sorted timestamp indexes per day for fast media matching."""
    indexes = {}
    for day, day_convs in days.items():
        entries = []
        for msgs in day_convs.values():
            msgs.sort(key=lambda x: x.get("Created(microseconds)", 0))
            entries.extend((m.get("Created(microseconds)", 0), m) for m in msgs)
        entries.sort(key=lambda x: x[0])
        indexes[day] = {
            "timestamps": [timestamp for timestamp, _ in entries],
            "messages": [message for _, message in entries],
        }
    return indexes


def _closest_message(index, mtime_ms):
    """Return the closest indexed message to mtime_ms using binary search."""
    timestamps = index["timestamps"]
    if not timestamps:
        return None, float("inf"), float("inf")

    window_start = bisect.bisect_left(timestamps, mtime_ms - TIMESTAMP_MATCH_THRESHOLD)
    window_end = bisect.bisect_right(timestamps, mtime_ms + TIMESTAMP_MATCH_THRESHOLD)
    candidates = range(window_start, window_end)
    if window_start == window_end:
        pos = bisect.bisect_left(timestamps, mtime_ms)
        candidates = (pos - 1, pos)

    best, best_diff, best_real = None, float("inf"), float("inf")
    for candidate in candidates:
        if not 0 <= candidate < len(timestamps):
            continue
        message = index["messages"][candidate]
        real_diff = abs(timestamps[candidate] - mtime_ms)
        ranked_diff = real_diff + len(message.get("media_filenames", [])) * MEDIA_PENALTY
        if ranked_diff < best_diff:
            best, best_diff, best_real = message, ranked_diff, real_diff
    return best, best_diff, best_real


def match_media(days, media_dir, progress):
    """Scan media, pair overlays by mtime bucket, match all files to messages by timestamp."""
    media_files, overlay_files = [], []
    for f in (media_dir.iterdir() if media_dir.exists() else []):
        if not f.is_file() or "thumbnail" in f.name.lower():
            continue
        if "_overlay~" in f.name:
            overlay_files.append(f)
        elif "_media~" in f.name or re.search(r"_b~.+\.\w+$", f.name):
            media_files.append(f)

    # Pair overlays by mtime bucket (same second = same snap event, overlays are duplicates)
    overlay_pairs = {}
    mtime_buckets = defaultdict(lambda: [[], []])
    for f in media_files:
        if "_media~" in f.name:
            mtime_buckets[int(f.stat().st_mtime)][0].append(f)
    for f in overlay_files:
        mtime_buckets[int(f.stat().st_mtime)][1].append(f)
    for ms, ovs in mtime_buckets.values():
        for i, m in enumerate(ms):
            if ovs:
                overlay_pairs[m.name] = ovs[i % len(ovs)]

    # Sort and flatten messages once so each media file can match via binary search.
    indexes = _build_message_index(days)

    matched = 0
    progress.phase(len(media_files))
    for f in media_files:
        try:
            media_day = date.fromisoformat(f.name[:10])
        except ValueError:
            LOGGER.warning("Skipping media file with an invalid date prefix: %s", f.name)
            progress.update(1)
            continue

        mtime_ms = int(f.stat().st_mtime * 1000)
        best, best_diff, best_real = None, float("inf"), float("inf")
        for offset in (0, -1, 1):
            target = str(media_day + timedelta(offset))
            candidate, ranked_diff, real_diff = _closest_message(
                indexes.get(target, {"timestamps": [], "messages": []}),
                mtime_ms,
            )
            if ranked_diff < best_diff:
                best, best_diff, best_real = candidate, ranked_diff, real_diff
        if best and best_real <= TIMESTAMP_MATCH_THRESHOLD:
            best.setdefault("media_filenames", []).append(f.name)
            matched += 1
        progress.update(1)

    return media_files, overlay_pairs, matched


def _media_type(ext):
    """Map file extension to a media type string."""
    ext = ext.lower().lstrip(".")
    if ext in ("jpg", "jpeg", "png", "gif", "webp"):
        return "IMAGE"
    if ext in ("mp4", "mov", "avi", "webm"):
        return "VIDEO"
    if ext in ("mp3", "aac", "m4a", "wav", "ogg"):
        return "AUDIO"
    return "IMAGE"


def _copy_message_media(m, media_dir, folder, overlay_pairs):
    """Copy media files for a single message, return set of copied filenames."""
    fnames = m.get("media_filenames", [])
    if not fnames:
        return set()

    rel_paths, copied = [], set()
    for fname in fnames:
        src = media_dir / fname
        if not src.exists():
            continue
        copied.add(fname)

        if fname in overlay_pairs:
            dest = folder / "media" / src.stem
            dest.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, dest / fname)
            shutil.copy2(overlay_pairs[fname], dest / overlay_pairs[fname].name)
            rel_paths.append(f"media/{src.stem}")
        else:
            (folder / "media").mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, folder / "media" / fname)
            rel_paths.append(f"media/{fname}")

    if rel_paths:
        m["media_locations"] = rel_paths

    return copied


def _collect_orphans(day, media_by_day, day_mapped, folder):
    """Detect and copy orphaned media for a day, returning the orphan list."""
    orphaned = []
    for fname, f in sorted(media_by_day.get(day, {}).items()):
        if fname not in day_mapped:
            ext = f.suffix.lstrip(".")
            orphan_dir = folder / "orphaned"
            orphan_dir.mkdir(parents=True, exist_ok=True)
            shutil.copy2(f, orphan_dir / fname)
            orphaned.append({
                "path": f"orphaned/{fname}",
                "filename": fname,
                "type": _media_type(ext),
                "extension": ext,
            })
    return orphaned


def write_output(days, overlay_pairs, media_dir, out, group_titles, all_media_files, progress):
    """Write a single conversations.json per day with stats and orphaned media."""
    days_out = out / "days"
    if days_out.exists():
        shutil.rmtree(days_out)

    media_by_day = defaultdict(dict)
    for f in all_media_files:
        media_by_day[f.name[:10]][f.name] = f

    sorted_days = sorted(days.items())
    progress.phase(len(sorted_days))
    for day, convs in sorted_days:
        folder = days_out / day
        folder.mkdir(parents=True, exist_ok=True)

        conversations = []
        day_media_count = 0
        day_mapped = set()

        for c_id, msgs in convs.items():
            for m in msgs:
                copied = _copy_message_media(m, media_dir, folder, overlay_pairs)
                day_mapped.update(copied)
                day_media_count += len(copied)

            is_group = "-" in c_id
            conv_entry = {"id": c_id, "conversation_id": c_id,
                          "conversation_type": "group" if is_group else "individual", "messages": msgs}
            if is_group:
                conv_entry["group_name"] = group_titles.get(c_id, c_id)
            conversations.append(conv_entry)

        orphaned = _collect_orphans(day, media_by_day, day_mapped, folder)

        (folder / "conversations.json").write_text(json.dumps({
            "date": day,
            "stats": {
                "conversationCount": len(conversations),
                "messageCount": sum(len(msgs) for msgs in convs.values()),
                "mediaCount": day_media_count,
            },
            "conversations": conversations,
            "orphanedMedia": {"orphaned_media_count": len(orphaned), "orphaned_media": orphaned},
        }, indent=2, ensure_ascii=False), encoding="utf-8")
        progress.update(1)

    return len(sorted_days)


def _fallback_svg(username):
    """Ghost SVG with a deterministic color derived from the username."""
    hue = int.from_bytes(hashlib.sha256(username.encode()).digest()[:2], "little") % 360
    r, g, b = colorsys.hls_to_rgb(hue / 360, 0.6, 0.3)
    fill = f"#{int(r*255):02x}{int(g*255):02x}{int(b*255):02x}"
    return (
        f'<svg viewBox="0 0 {AVATAR_SIZE} {AVATAR_SIZE}" xmlns="http://www.w3.org/2000/svg">'
        f'<path d="{GHOST_PATH}" fill="{fill}" stroke="black" stroke-opacity="0.2" stroke-width="0.9"/>'
        f'</svg>'
    )


def _fetch_avatar(username):
    """Fetch a single Bitmoji SVG, returning fallback on any failure."""
    try:
        resp = requests.get(
            "https://app.snapchat.com/web/deeplink/snapcode",
            params={"username": username, "type": "SVG", "bitmoji": "enable"},
            timeout=10,
        )
        resp.raise_for_status()
        root = ET.fromstring(resp.text)
        img = root.find(".//svg:image", SVG_NS)
        if img is None:
            raise ValueError("No <image> in SVG")
        href = img.get(f"{{{SVG_NS['xlink']}}}href") or img.get("href")
        if not href:
            raise ValueError("No href on <image>")
        return username, (
            f'<svg viewBox="0 0 {AVATAR_SIZE} {AVATAR_SIZE}" xmlns="http://www.w3.org/2000/svg" '
            f'xmlns:xlink="http://www.w3.org/1999/xlink">'
            f'<image href="{href}" x="0" y="0" width="{AVATAR_SIZE}" height="{AVATAR_SIZE}"/>'
            f'</svg>'
        )
    except (requests.RequestException, ET.ParseError, ValueError) as exc:
        LOGGER.warning("Unable to fetch Bitmoji for %s: %s", username, exc)
        return username, _fallback_svg(username)


def generate_bitmoji_assets(usernames, output_root, progress=None):
    """Fetch and save Bitmoji avatars, returning {username: relative_path}."""
    if not usernames:
        return {}
    bitmoji_dir = output_root / "bitmoji"
    bitmoji_dir.mkdir(parents=True, exist_ok=True)
    paths = {}
    with ThreadPoolExecutor(max_workers=min(8, len(usernames))) as pool:
        futures = [pool.submit(_fetch_avatar, u) for u in usernames]
        for f in as_completed(futures):
            username, svg = f.result()
            filename = f"{username}.svg"
            (bitmoji_dir / filename).write_text(svg, encoding="utf-8")
            paths[username] = f"bitmoji/{filename}"
            if progress is not None:
                progress.update(1)
    return paths


def main():
    logging.basicConfig(level=logging.WARNING, format="%(levelname)s: %(message)s")
    input_dir, tmp_dir = Path("input"), Path("_tmp_extract")
    if tmp_dir.exists():
        shutil.rmtree(tmp_dir)

    progress = Progress()
    extract_zips(input_dir, tmp_dir, progress)

    json_dir = tmp_dir / "json"
    media_dir = tmp_dir / "chat_media"
    chat_data = load_history_json(json_dir, "chat_history.json")
    snap_data = load_history_json(json_dir, "snap_history.json")

    owner = find_owner(chat_data, snap_data)
    days, usernames, group_info, group_titles = build_days(chat_data, snap_data)
    del chat_data, snap_data
    gc.collect()
    usernames.add(owner)

    media_files, overlay_pairs, matched = match_media(days, media_dir, progress)

    out = Path("output")
    total_files = write_output(days, overlay_pairs, media_dir, out, group_titles, media_files, progress)

    # Index & Bitmoji
    display_map = load_display_names(json_dir)
    valid_usernames = {u for u in usernames if u}
    progress.phase(len(valid_usernames))
    bitmoji_paths = generate_bitmoji_assets(valid_usernames, out, progress)
    users = [
        {"username": u, "display_name": display_map.get(u, u), "bitmoji": bitmoji_paths.get(u, f"bitmoji/{u}.svg")}
        for u in sorted(usernames) if u
    ]
    (out / "index.json").write_text(
        json.dumps({"account_owner": owner, "users": users, "groups": group_info}, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )
    progress.close()

    shutil.rmtree(tmp_dir)
    min_date, max_date = min(days.keys()), max(days.keys())
    len_days, total_media = len(days), len(media_files)
    orphaned = total_media - matched
    matched_pct = matched / max(total_media, 1) * 100
    orphaned_pct = orphaned / max(total_media, 1) * 100

    print(f"{'=' * 80}\n{'SNAPCHAT EXPORT PROCESSING COMPLETE':^80}\n{'=' * 80}\n")
    print(f"OVERVIEW\n{'-' * 80}")
    print(f"{'Account Owner':<19}: {owner}")
    print(f"{'Date Range':<19}: {min_date} to {max_date}")
    print(f"{'Total Parsed':<19}: {total_files} day files across {len_days} active days\n")
    print(f"MEDIA MATCHING\n{'-' * 80}")
    print(f"{'Matched Media':<19}: {matched} / {total_media} ({matched_pct:.1f}%)")
    print(f"{'Orphaned Media':<19}: {orphaned} files ({orphaned_pct:.1f}%) - safely copied to 'orphaned' folders\n")
    print(f"{'=' * 80}")
    print("Done! All files successfully written to the 'output' directory.")


if __name__ == "__main__":
    main()
