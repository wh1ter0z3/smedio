#!/usr/bin/env python3
"""Smedio: YouTube and live TV in one lightweight app for low-end Linux laptops and ARM tablets.

Everything plays inside the window through an embedded libmpv with hardware decoding (VA-API on
PCs, V4L2 on ARM tablets and phones such as Qualcomm's Venus), and only in formats the hardware
decodes, asked once at start (hw_decoders): older Intel GPUs (e.g. HD 520 / Skylake) handle H.264
and 8-bit HEVC, newer ones and many ARM decoders VP9 and AV1 too, which YouTube then uses (up to
4K); anything else would stutter on the CPU.

  * YouTube, ad-free and limited to formats the hardware decodes. Two ways to use it:
    - Local library: subscriptions, likes, playlists and history live in a SQLite file on this
      device, and "For you" recommendations are computed here.
    - Google account: reads your real YouTube feeds using the login cookies of a browser you
      choose. Read-only: nothing is ever written to your account.
  * Live TV: any IPTV playlist (M3U), and every country and region from iptv-org.
"""
import csv
import ctypes
import ctypes.util
import glob
import gzip
import hashlib
import itertools
import json
import locale
import multiprocessing
import math
import os
import random
import re
import shutil
import socket
import sqlite3
import struct
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from collections import Counter
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor, as_completed
from concurrent.futures import TimeoutError as FutureTimeout
from datetime import datetime

APP_ID = 'dev.smedio.Smedio'
VERSION = '3.5.1'
APP_DIR = os.path.dirname(os.path.realpath(__file__))
VENV_BIN = os.path.join(APP_DIR, 'venv', 'bin')
BUNDLED_LIBMPV = os.path.join(APP_DIR, 'lib', 'libmpv.so.2')

# Use the app's private, up-to-date yt-dlp (and its Deno JS runtime) when install.sh made one,
# else the system's (a distribution package).
HAVE_VENV = os.path.isdir(VENV_BIN)
for _sp in glob.glob(os.path.join(APP_DIR, 'venv', 'lib', 'python3*', 'site-packages')):
    sys.path.insert(0, _sp)
if HAVE_VENV:
    os.environ['PATH'] = VENV_BIN + os.pathsep + os.environ.get('PATH', '')
YTDLP = os.path.join(VENV_BIN, 'yt-dlp') if HAVE_VENV else (shutil.which('yt-dlp') or 'yt-dlp')

import gi  # noqa: E402
gi.require_version('Gtk', '4.0')
gi.require_version('Adw', '1')
from gi.repository import Adw, Gdk, Gio, GLib, GObject, Graphene, Gsk, Gtk, Pango  # noqa: E402

CONFIG_DIR = os.path.join(GLib.get_user_config_dir(), 'smedio')
CONFIG_FILE = os.path.join(CONFIG_DIR, 'config.json')
THUMB_DIR = os.path.join(GLib.get_user_cache_dir(), 'smedio', 'thumbs')
RSS_DIR = os.path.join(GLib.get_user_cache_dir(), 'smedio', 'rss')
DATA_DIR = os.path.join(GLib.get_user_data_dir(), 'smedio-library')
DB_FILE = os.path.join(DATA_DIR, 'library.db')
MPV_SOCKET = os.path.join(GLib.get_user_runtime_dir(), 'smedio-mpv.sock')
DEFAULT_DOWNLOAD_DIR = os.path.join(
    GLib.get_user_special_dir(GLib.UserDirectory.DIRECTORY_VIDEOS) or os.path.expanduser('~/Videos'),
    'Smedio')

QUALITIES = [360, 480, 720, 1080]  # 1440p and 2160p too where the hardware decodes VP9 or AV1: see qualities()
SPEEDS = [0.5, 0.75, 1.0, 1.25, 1.5, 2.0]
# The YouTube captions language the viewer picked last (a YouTube code like 'en'; '' = off). The
# players add that track to every YouTube video that has it.
CAPTION_PREF = ''


def yt_captions(info):
    """Captions YouTube has for a video, from yt-dlp's info: subtitles uploaded with it in every
    language, and the automatic ones in the video's own language and in English.
    Each is {lang, name, url, auto}; nothing is downloaded until one is picked."""
    def vtt(fmts):
        f = next((f for f in fmts or [] if f.get('ext') == 'vtt' and f.get('url')), None)
        return f['url'] if f else None

    out, seen = [], set()
    for lang, fmts in sorted((info.get('subtitles') or {}).items()):
        url = vtt(fmts)
        if lang == 'live_chat' or not url:
            continue
        out.append({'lang': lang, 'name': (fmts[0].get('name') or lang), 'url': url, 'auto': False})
        seen.add(lang)
    auto = info.get('automatic_captions') or {}
    for code in [c for c in auto if c.endswith('-orig')] + ['en']:
        lang = code[:-5] if code.endswith('-orig') else code
        url = vtt(auto.get(code))
        if lang in seen or not url:
            continue
        name = auto[code][0].get('name') or lang
        out.append({'lang': lang, 'name': name if 'auto' in name.lower() else f'{name} (auto-generated)',
                    'url': url, 'auto': True})
        seen.add(lang)
    return out


def pick_caption(stream):
    """The caption track to load with this stream, by CAPTION_PREF, or None."""
    if not CAPTION_PREF:
        return None
    caps = (stream or {}).get('captions') or []
    return next((c for c in caps if c['lang'] == CAPTION_PREF), None) or \
        next((c for c in caps if c['lang'].split('-')[0] == CAPTION_PREF.split('-')[0]), None)
PAGE = 24
LIST_FIRST = 72   # cards shown at first on long lists; more as you scroll
QUEUE_MAX = 200   # videos lined up after the one you click in a list
THUMB_W, THUMB_H = 240, 135
GRID_COLUMNS = ((None, 499, 1), (500, 749, 2), (750, 1099, 3))  # page width (px) -> cards a row; wider: 4
# The watch page fits itself to the screen (see WatchColumns): Up next's thumbnails are as tall as
# lets about UPNEXT_ROWS rows show, its column is as wide as they need (at most UPNEXT_SHARE of the
# page), and the player takes the rest, at most PLAYER_VH of the visible height.
ROW_W, ROW_H = 288, 162   # Up next thumbnail: its 16:9 shape and natural size; it scales
UPNEXT_ROWS, UPNEXT_SHARE, PLAYER_VH = 5.5, 0.36, 0.8
WATCH_GAP = 28            # between the player column and Up next
SIDE_BELOW = 999          # page width (px) up to which Up next goes under the video instead
SHORT_W, SHORT_H = 162, 288
RESOLVE_TTL = 20 * 60   # stream URLs stay valid for hours; keep lookups for 20 min
PREVIEW_TTL = 60 * 60
YT_RED = '#cc181e'      # the 2012-era player red
# The app mark (same as dev.smedio.Smedio.svg): a white S on a red tile, with a play arrow.
LOGO_SVG = ('<svg xmlns="http://www.w3.org/2000/svg" width="128" height="128" viewBox="0 0 128 128"> <defs> <linearGradient id="tile" x1="0" y1="0" x2="1" y2="1"> <stop offset="0" stop-color="#ff5a3c"/> <stop offset="1" stop-color="#c4161c"/> </linearGradient> </defs> <rect x="8" y="8" width="112" height="112" rx="30" fill="url(#tile)"/> <path d="M86 40 C80 30 63 28 53 33 C41 39 43 54 57 58 L71 62 C85 66 87 83 72 91 C64 95 54 94 47 89" fill="none" stroke="#fff" stroke-width="13" stroke-linecap="round"/> <path d="M24 76 L44 88 L24 100 Z" fill="#fff" stroke="#fff" stroke-width="6" stroke-linejoin="round"/> </svg>')

BROWSERS = {  # yt-dlp name -> (label, profile folders that show it is installed)
    'firefox': ('Firefox', ['~/.mozilla/firefox', '~/snap/firefox/common/.mozilla/firefox',
                            '~/.config/mozilla/firefox', '~/.var/app/org.mozilla.firefox/.mozilla/firefox']),
    'brave': ('Brave', ['~/.config/BraveSoftware/Brave-Browser']),
    'chromium': ('Chromium', ['~/.config/chromium', '~/snap/chromium/common/chromium']),
    'chrome': ('Google Chrome', ['~/.config/google-chrome']),
    'edge': ('Microsoft Edge', ['~/.config/microsoft-edge']),
    'vivaldi': ('Vivaldi', ['~/.config/vivaldi']),
}

VIDEO_URL_RE = re.compile(
    r'(?:youtube\.com/(?:watch\?(?:.*&)?v=|shorts/|live/|embed/)|youtu\.be/)([\w-]{11})')
ANSI_RE = re.compile(r'\x1b\[[0-9;]*m')
NETWORK_ERROR_RE = re.compile(r'name resolution|timed out|Connection (reset|refused|aborted)|'
                              r'Network is unreachable|Remote end closed|TransportError', re.I)
URL_RE = re.compile(r'https?://[^\s<>"]+')
STOPWORDS = set('''
a an the and or but if then for to of in on at by with from up down out over under again once here there
when where why how all any both each few more most other some such no nor not only own same so than too very
can will just should now is are was were be been being have has had do does did this that these those
i me my we our you your he him his she her it its they them their what which who whom into about after
before first last ever every video videos official full new episode part live music song songs feat
lyrics lyric audio trailer shorts short vs best top ep hindi english telugu tamil 2023 2024 2025 2026
'''.split())


# mpv's hardware decoders, best first: VA-API (Intel/AMD PCs), then V4L2 mem2mem (ARM SoCs, e.g.
# Qualcomm Venus; mpv's auto-safe doesn't try it), then whatever mpv considers safe.
HWDEC = 'vaapi,vaapi-copy,v4l2m2m-copy,auto-safe'


# Smedio asks the hardware once which codecs it decodes and picks YouTube formats from those, so the CPU never has to decode video. YouTube sends H.264 up to 1080p, VP9 and AV1
# up to 4K; older GPUs decode only H.264.

# VA-API profile numbers (va.h) -> codec; only the ones YouTube and video releases use
VA_PROFILES = {0: 'mpeg2', 1: 'mpeg2', 5: 'h264', 6: 'h264', 7: 'h264', 13: 'h264', 14: 'vp8',
               17: 'hevc', 18: 'hevc10', 19: 'vp9', 21: 'vp9-10', 32: 'av1'}


def vaapi_decoders():
    """(codecs, driver name) the GPU decodes through VA-API (Intel, AMD), asked like vainfo does."""
    try:
        va, drm = ctypes.CDLL('libva.so.2'), ctypes.CDLL('libva-drm.so.2')
    except OSError:
        return set(), None
    vp, ip = ctypes.c_void_p, ctypes.POINTER(ctypes.c_int)
    drm.vaGetDisplayDRM.restype, drm.vaGetDisplayDRM.argtypes = vp, [ctypes.c_int]
    va.vaSetInfoCallback.argtypes = [vp, vp, vp]
    va.vaInitialize.argtypes = [vp, ip, ip]
    va.vaMaxNumProfiles.argtypes = va.vaMaxNumEntrypoints.argtypes = va.vaTerminate.argtypes = [vp]
    va.vaQueryConfigProfiles.argtypes = [vp, ip, ip]
    va.vaQueryConfigEntrypoints.argtypes = [vp, ctypes.c_int, ip, ip]
    va.vaQueryVendorString.restype, va.vaQueryVendorString.argtypes = ctypes.c_char_p, [vp]
    for node in sorted(glob.glob('/dev/dri/renderD*')):
        try:
            fd = os.open(node, os.O_RDWR)
        except OSError:
            continue
        try:
            dpy = drm.vaGetDisplayDRM(fd)
            if not dpy:
                continue
            va.vaSetInfoCallback(dpy, None, None)  # no "libva info: ..." lines on the terminal
            major, minor = ctypes.c_int(), ctypes.c_int()
            if va.vaInitialize(dpy, ctypes.byref(major), ctypes.byref(minor)) != 0:
                continue
            try:
                n = ctypes.c_int()
                profiles = (ctypes.c_int * max(va.vaMaxNumProfiles(dpy), 1))()
                va.vaQueryConfigProfiles(dpy, profiles, ctypes.byref(n))
                found = set()
                entry = (ctypes.c_int * max(va.vaMaxNumEntrypoints(dpy), 1))()
                for p in profiles[:n.value]:
                    m = ctypes.c_int()
                    if p in VA_PROFILES and va.vaQueryConfigEntrypoints(dpy, p, entry, ctypes.byref(m)) == 0 \
                            and 1 in entry[:m.value]:  # VAEntrypointVLD: decoding
                        found.add(VA_PROFILES[p])
                name = (va.vaQueryVendorString(dpy) or b'').decode(errors='replace')
                return found, re.sub(r'\s*\(\)$', '', name) or 'VA-API'  # 'Intel iHD driver … - 26.1.2 ()'
            finally:
                va.vaTerminate(dpy)
        finally:
            os.close(fd)
    return set(), None


def v4l2_decoder_formats():
    """The compressed formats (fourccs such as 'H264', 'VP90') that the V4L2 mem2mem decoders of
    this machine take, read from the kernel. Empty on PCs, which decode through VA-API."""
    import fcntl
    found = set()
    for dev in sorted(glob.glob('/dev/video*')):
        try:
            fd = os.open(dev, os.O_RDWR | os.O_NONBLOCK)
        except OSError:
            continue
        try:
            cap = bytearray(104)                                    # struct v4l2_capability
            fcntl.ioctl(fd, 0x80685600, cap)                        # VIDIOC_QUERYCAP
            caps = struct.unpack_from('<I', cap, 88)[0] or struct.unpack_from('<I', cap, 84)[0]
            if not caps & 0xC000:                                   # V4L2_CAP_VIDEO_M2M(_MPLANE)
                continue
            for buf_type in (10, 2):                                # OUTPUT_MPLANE, OUTPUT
                for index in range(32):
                    desc = bytearray(64)                            # struct v4l2_fmtdesc
                    struct.pack_into('<II', desc, 0, index, buf_type)
                    try:
                        fcntl.ioctl(fd, 0xC0405602, desc)           # VIDIOC_ENUM_FMT
                    except OSError:
                        break
                    if struct.unpack_from('<I', desc, 8)[0] & 1:    # V4L2_FMT_FLAG_COMPRESSED
                        found.add(desc[44:48].decode('ascii', 'replace'))
        except OSError:
            pass
        finally:
            os.close(fd)
    return found


V4L2_CODECS = {'H264': 'h264', 'HEVC': 'hevc', 'VP90': 'vp9', 'AV1F': 'av1', 'VP80': 'vp8', 'MPG2': 'mpeg2'}
CODEC_NAMES = {'h264': 'H.264', 'hevc': 'HEVC', 'hevc10': 'HEVC 10-bit', 'vp9': 'VP9', 'vp9-10': 'VP9 10-bit',
               'av1': 'AV1', 'vp8': 'VP8', 'mpeg2': 'MPEG-2'}
ASSUMED_CODECS = {'h264', 'hevc'}  # when the hardware can't be asked (e.g. NVIDIA's own driver)
_HW = None


def hw_decoders():
    """(codecs, how they were found): VA-API on PCs, V4L2 mem2mem decoders on ARM boards.
    Asked once per process (~10 ms)."""
    global _HW
    if _HW is None:
        codecs, how = vaapi_decoders()
        if not codecs:
            codecs = {V4L2_CODECS[f] for f in v4l2_decoder_formats() if f in V4L2_CODECS}
            how = 'V4L2 video decoder' if codecs else None
        _HW = (codecs, how) if codecs else (set(ASSUMED_CODECS), None)
    return _HW


def hw_codecs():
    return hw_decoders()[0]


def qualities():
    """The quality menu: above 1080p YouTube has only VP9 and AV1."""
    return QUALITIES + ([1440, 2160] if hw_codecs() & {'vp9', 'av1'} else [])


def video_format(height, playback=True):
    """yt-dlp's format choice: the best codec the GPU decodes (AV1, then VP9, both 8-bit SDR), then
    H.264 + AAC, anything else only as a last resort. Downloads (playback=False) stay H.264 + AAC,
    which every player opens. Vertical videos (Shorts) are limited by their short side, so
    "1080p" means 1080x1920."""
    codecs = hw_codecs() if playback else set()
    sel = []
    for key, vc in (('av1', 'av01'), ('vp9', 'vp9'), ('vp9', 'vp09.00')):  # DASH ('vp9') before HLS
        if key in codecs:
            sel += [f'bv*[vcodec^={vc}][dynamic_range=SDR][aspect_ratio<1][width<={height}]+ba',
                    f'bv*[vcodec^={vc}][dynamic_range=SDR][height<={height}]+ba']
    sel += [f'bv*[vcodec^=avc1][aspect_ratio<1][width<={height}]+ba[ext=m4a]',
            f'bv*[vcodec^=avc1][height<={height}]+ba[ext=m4a]', f'b[vcodec^=avc1][height<={height}]',
            f'bv*[height<={height}]+ba', f'b[height<={height}]', 'b']
    return '/'.join(sel)


AUDIO_FORMAT = 'ba[ext=m4a]/ba/b'
# Which YouTube apps yt-dlp poses as when asking for stream links. YouTube keeps changing which
# ones it refuses (403 Forbidden, e.g. tv_samsung in Nov 2026), so every lookup tests its link and
# moves down this list when refused; the set that worked is tried first next time. visionos alone
# needs no player JS (no Deno challenge): ~1.5 s a lookup instead of ~5 s with web_embedded.
YT_CLIENTS = [['visionos'], ['visionos', 'web_embedded'], ['default'], ['tv_simply', 'web_safari'], ['mweb']]
YT_CLIENTS_ARG = 'youtube:player_client=visionos,web_embedded'  # for yt-dlp run as a command


def background_pool(workers, name, confine=True):
    """A thread pool for work that must never disturb playback. Its threads run at low CPU
    priority and, with `confine`, only on the last CPU thread. On Linux both settings are per
    thread and inherited by child processes, so yt-dlp's Deno solver and ffmpeg stay there too.
    Low priority alone isn't enough on hyper-threaded CPUs: a busy sibling thread still slows the
    core drawing the video. With the work on one CPU thread, the scheduler keeps playback on an
    idle core."""
    cpus = sorted(os.sched_getaffinity(0))

    def setup():
        try:
            os.setpriority(os.PRIO_PROCESS, threading.get_native_id(), 10)
            if confine and len(cpus) >= 4:
                os.sched_setaffinity(0, {cpus[-1]})
        except OSError:
            pass
    return ThreadPoolExecutor(workers, thread_name_prefix=name, initializer=setup)


def in_batches(items, build, size=3):
    """Create widgets a few at a time between frames, so building a long list never makes
    the video miss its display slot."""
    it = iter(items)

    def step():
        for _ in range(size):
            item = next(it, None)
            if item is None:
                return GLib.SOURCE_REMOVE
            build(item)
        return GLib.SOURCE_CONTINUE

    GLib.idle_add(step, priority=GLib.PRIORITY_LOW)


PLAYER_LOG = os.path.join(GLib.get_user_cache_dir(), 'smedio', 'player.log')
_log_lock = threading.Lock()


def player_log(level, component, message):
    """mpv's warnings and errors, plus Smedio's own notes on streams (about 1 MB kept), for
    working out afterwards why something stopped."""
    try:
        with _log_lock:
            os.makedirs(os.path.dirname(PLAYER_LOG), exist_ok=True)
            if os.path.exists(PLAYER_LOG) and os.path.getsize(PLAYER_LOG) > 1_000_000:
                os.replace(PLAYER_LOG, PLAYER_LOG + '.old')
            with open(PLAYER_LOG, 'a') as f:
                f.write(f'{datetime.now():%Y-%m-%d %H:%M:%S} {level} {component}: {str(message).rstrip()}\n')
    except OSError:
        pass


def idle(fn, *args):
    """Run fn(*args) once on the GTK main thread. (A bare GLib.idle_add repeats forever
    whenever the callback returns something truthy, e.g. grab_focus() or a tuple.)"""
    def once():
        fn(*args)
        return GLib.SOURCE_REMOVE
    GLib.idle_add(once)

# ---------------------------------------------------------------- networking

NET_READY = threading.Event()
IPV4_ONLY = False


def check_network():
    """Fall back to IPv4 when IPv6 is advertised but broken (common on phone hotspots).

    Browsers race both protocols, but Python tries IPv6 first and waits ~20 s per
    request before giving up. YouTube stream URLs are tied to the client IP, so yt-dlp
    and mpv must use the same family; forcing IPv4 here keeps them consistent.
    """
    try:
        try:
            addr = socket.getaddrinfo('www.youtube.com', 443, socket.AF_INET6, socket.SOCK_STREAM)[0][4]
            with socket.socket(socket.AF_INET6, socket.SOCK_STREAM) as s:
                s.settimeout(1.5)
                s.connect(addr)
            return
        except OSError:
            pass
        force_ipv4()
    finally:
        NET_READY.set()


def force_ipv4():
    global IPV4_ONLY
    IPV4_ONLY = True
    real_getaddrinfo = socket.getaddrinfo

    def ipv4_first(host, *args, **kwargs):
        res = real_getaddrinfo(host, *args, **kwargs)
        return [r for r in res if r[0] == socket.AF_INET] or res

    socket.getaddrinfo = ipv4_first


_dead = {}  # server address -> when it last failed to connect


def _connect_quickly(address, timeout=socket._GLOBAL_DEFAULT_TIMEOUT, source_address=None, **_):
    """socket.create_connection, but each server address gets only 3 s to answer and recently
    dead ones are tried last. (Some servers publish an address that doesn't answer on some
    networks; the stock version waited out the whole timeout on it first.)"""
    host, port = address
    infos = socket.getaddrinfo(host, port, 0, socket.SOCK_STREAM)
    infos.sort(key=lambda r: time.time() - _dead.get(r[4][0], 0) < 600)
    full = None if timeout is socket._GLOBAL_DEFAULT_TIMEOUT else timeout
    error = None
    for family, kind, proto, _, addr in infos:
        sock = socket.socket(family, kind, proto)
        try:
            sock.settimeout(min(3, full) if full else 3)
            if source_address:
                sock.bind(source_address)
            sock.connect(addr)
            sock.settimeout(full)
            _dead.pop(addr[0], None)
            return sock
        except OSError as e:
            error = e
            _dead[addr[0]] = time.time()
            sock.close()
    raise error or OSError(f'no addresses for {host}')


socket.create_connection = _connect_quickly


def http_get(url, timeout=15):
    NET_READY.wait(5)
    req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0 (X11; Linux x86_64)',
                                               'Accept-Encoding': 'gzip'})
    for attempt in (1, 2):
        try:
            with urllib.request.urlopen(req, timeout=timeout) as r:
                data = r.read()
                return gzip.decompress(data) if r.headers.get('Content-Encoding') == 'gzip' else data
        except OSError as e:
            if attempt == 2 or not NETWORK_ERROR_RE.search(str(e)):
                raise
            time.sleep(1)


def fetch_image(urls, path):
    """Download the first URL that works into the thumbnail cache; return a texture."""
    if not os.path.exists(path):
        os.makedirs(THUMB_DIR, exist_ok=True)
        for url in urls:
            try:
                data = http_get(url)
            except OSError:
                continue
            tmp = f'{path}.{threading.get_ident()}.tmp'
            with open(tmp, 'wb') as f:
                f.write(data)
            os.replace(tmp, path)
            break
        else:
            return None
    return Gdk.Texture.new_from_filename(path)


def cover_art(video):
    """The video's cached thumbnail cut to 16:9 for mpv's audio-only picture (YouTube's 480x360
    one has black bars above and below), or None if there is no thumbnail yet."""
    src = video.thumb_path()
    if not os.path.exists(src):
        return None
    dst = src[:-4] + '_cover.jpg'
    if os.path.exists(dst):
        return dst
    try:
        gi.require_version('GdkPixbuf', '2.0')
        from gi.repository import GdkPixbuf
        pb = GdkPixbuf.Pixbuf.new_from_file(src)
        w, h = pb.get_width(), pb.get_height()
        ch = min(h, round(w * 9 / 16))
        if ch == h:
            return src
        pb.new_subpixbuf(0, (h - ch) // 2, w, ch).savev(dst, 'jpeg', ['quality'], ['92'])
        return dst
    except Exception:  # noqa: BLE001 - the uncropped picture will do
        return src

# ---------------------------------------------------------------- formatting


def fmt_duration(sec):
    if not sec:
        return ''
    sec = int(sec)
    h, rem = divmod(sec, 3600)
    m, s = divmod(rem, 60)
    return f'{h}:{m:02}:{s:02}' if h else f'{m}:{s:02}'


def parse_duration(text):
    if not text or not re.fullmatch(r'\d+(:\d{2}){1,2}', text.strip()):
        return None
    secs = 0
    for part in text.strip().split(':'):
        secs = secs * 60 + int(part)
    return secs


def fmt_count(n):
    if n is None:
        return ''
    for div, suffix in ((1e9, 'B'), (1e6, 'M'), (1e3, 'K')):
        if n >= div:
            v = n / div
            return (f'{v:.1f}'.rstrip('0').rstrip('.') if v < 10 else f'{v:.0f}') + suffix
    return str(n)


def fmt_age(ts):
    if not ts:
        return ''
    d = time.time() - ts
    for unit, sec in (('year', 31536000), ('month', 2592000), ('week', 604800), ('day', 86400),
                      ('hour', 3600), ('minute', 60)):
        if d >= sec:
            n = int(d // sec)
            return f'{n} {unit}{"s" if n > 1 else ""} ago'
    return 'just now'


AGE_UNITS = {'s': 'second', 'sec': 'second', 'm': 'minute', 'min': 'minute', 'h': 'hour', 'hr': 'hour',
             'd': 'day', 'w': 'week', 'wk': 'week', 'mo': 'month', 'y': 'year', 'yr': 'year'}


def youtube_age(text):
    """YouTube's short ages, spelled out as on its pages: '3mo ago' -> '3 months ago',
    'Streamed 1d ago' -> 'Streamed 1 day ago'. Anything else is left as it is."""
    m = re.match(r'^(.*?)(\d+)\s*([a-z]+)\s+ago$', text or '')
    unit = AGE_UNITS.get(m.group(3)) if m else None
    if not unit:
        return text
    n = int(m.group(2))
    return f'{m.group(1)}{n} {unit}{"s" if n != 1 else ""} ago'


def date_age(yyyymmdd):
    """'20261115' -> '9 days ago' (YouTube's day-precise upload date)."""
    days = (datetime.now().date() - datetime.strptime(yyyymmdd, '%Y%m%d').date()).days
    if days <= 0:
        return 'today'
    for unit, size in (('year', 365), ('month', 30), ('week', 7), ('day', 1)):
        if days >= size:
            n = days // size
            return f'{n} {unit}{"s" if n != 1 else ""} ago'


def fmt_size(n):
    if not n:
        return '?'
    for unit in ('B', 'KB', 'MB', 'GB'):
        if n < 1024 or unit == 'GB':
            return f'{n:.0f} {unit}' if unit in ('B', 'KB') else f'{n:.1f} {unit}'
        n /= 1024


def country_flag(code):
    """'IN' -> 🇮🇳 (iptv-org writes the United Kingdom as UK)."""
    code = {'UK': 'GB'}.get(code, code)
    return ''.join(chr(0x1F1E6 + ord(c) - 65) for c in code) if re.fullmatch(r'[A-Z]{2}', code or '') else code


def clean_error(exc):
    msg = ANSI_RE.sub('', str(exc)).replace('ERROR: ', '')
    return msg.split('\n')[0][:220]


def linkify(text):
    out, last = [], 0
    for m in URL_RE.finditer(text):
        out.append(GLib.markup_escape_text(text[last:m.start()]))
        url = GLib.markup_escape_text(m.group(0))
        out.append(f'<a href="{url}">{url}</a>')
        last = m.end()
    out.append(GLib.markup_escape_text(text[last:]))
    return ''.join(out)


def is_channel_url(url):
    return bool(re.match(r'https?://(?:www\.|m\.)?youtube\.com/(?:@[^/?#]+|channel/[^/?#]+|c/[^/?#]+|user/[^/?#]+)'
                         r'(?:/videos)?/?$', url or ''))


def channel_root(url):
    m = re.match(r'(https?://(?:www\.|m\.)?youtube\.com/(?:@[^/?#]+|channel/[^/?#]+|c/[^/?#]+|user/[^/?#]+))',
                 url or '')
    return m.group(1) if m else (url or '').rstrip('/')

# ---------------------------------------------------------------- data model


class Video:
    """A video, short, playlist or channel as shown on a card."""
    FIELDS = ('id', 'title', 'channel', 'channel_id', 'channel_url', 'duration', 'views', 'views_text',
              'live', 'published', 'age', 'short', 'kind', 'link', 'thumb', 'count', 'anim')
    __slots__ = FIELDS

    def __init__(self, id, title=None, **kw):  # noqa: A002 - mirrors yt-dlp's field name
        self.id = id
        self.title = title or id
        for f in self.FIELDS[2:]:
            setattr(self, f, kw.get(f))
        self.channel = self.channel or ''
        self.kind = self.kind or 'video'
        self.live = bool(self.live)
        self.short = bool(self.short)

    @classmethod
    def from_dict(cls, d):
        return cls(**{k: v for k, v in d.items() if k in cls.FIELDS})

    def to_dict(self):
        return {f: getattr(self, f) for f in self.FIELDS if getattr(self, f) not in (None, '', False)}

    @classmethod
    def from_entry(cls, e, channel=None, channel_url=None, channel_id=None):
        """Build from a yt-dlp flat entry (search result, feed item, playlist item...)."""
        url = e.get('url') or e.get('webpage_url') or ''
        eid = e.get('id') or ''
        if e.get('ie_key') == 'YoutubeTab' or (len(eid) != 11 and 'watch?v=' not in url):
            thumbs = [t.get('url') for t in e.get('thumbnails') or [] if t.get('url')]
            thumb = thumbs[-1] if thumbs else None
            if thumb and thumb.startswith('//'):
                thumb = 'https:' + thumb
            if eid.startswith('UC') or '/channel/' in url or '/@' in url:
                return cls(eid, e.get('title') or e.get('channel') or eid, kind='channel', thumb=thumb,
                           link=url or f'https://www.youtube.com/channel/{eid}', channel=e.get('title') or '',
                           channel_id=eid if eid.startswith('UC') else None, channel_url=url)
            if not eid:
                return None
            return cls(eid, e.get('title') or eid, kind='playlist', link=url, thumb=thumb,
                       count=e.get('playlist_count'), channel=e.get('channel') or e.get('uploader') or '')
        if len(eid) != 11:
            return None
        return cls(eid, e.get('title'),
                   channel=e.get('channel') or e.get('uploader') or channel or '',
                   channel_id=e.get('channel_id') or channel_id,
                   channel_url=e.get('channel_url') or e.get('uploader_url') or channel_url,
                   duration=e.get('duration'), views=e.get('view_count'),
                   live=e.get('live_status') == 'is_live',
                   published=e.get('timestamp') or e.get('release_timestamp'),
                   short='/shorts/' in url)

    @property
    def url(self):
        return self.link or f'https://www.youtube.com/watch?v={self.id}'

    @property
    def channel_link(self):
        if self.channel_url:
            return channel_root(self.channel_url)
        return f'https://www.youtube.com/channel/{self.channel_id}' if self.channel_id else None

    def thumb_urls(self, vertical=False, large=False):
        if self.kind != 'video':
            return [self.thumb] if self.thumb else []
        base = f'https://i.ytimg.com/vi/{self.id}/'
        if large:
            return [base + 'hq720.jpg', base + 'hqdefault.jpg']
        if vertical:
            return [base + 'oardefault.jpg', base + 'hqdefault.jpg']
        # 480x360 (4:3 with bars; the 16:9 cards crop them off): sharp on cards up to ~480 px wide
        return [base + 'hqdefault.jpg', base + 'mqdefault.jpg']

    def thumb_path(self, vertical=False, large=False):
        key = self.id if self.kind == 'video' else hashlib.md5((self.thumb or self.id).encode()).hexdigest()
        size = '_v' if vertical else '_l' if large else '_hq' if self.kind == 'video' else ''
        return os.path.join(THUMB_DIR, f'{key}{size}.jpg')

    def meta(self):
        if self.kind == 'channel':
            return 'Channel'
        if self.kind == 'live':
            sources = f'{self.count} sources' if self.count else None
            return ' · '.join(b for b in (self.channel, country_flag(self.views_text), sources) if b) or 'Live'
        if self.kind in ('playlist', 'localpl'):
            return ' · '.join(b for b in (self.channel, f'{self.count} videos' if self.count else 'Playlist') if b)
        bits = [self.channel]
        if self.views:
            bits.append(f'{fmt_count(self.views)} views')
        elif self.views_text:
            bits.append(self.views_text if re.search(r'[a-z]{3,}', self.views_text) else f'{self.views_text} views')
        age = fmt_age(self.published) if self.published else youtube_age(self.age)
        if age:
            bits.append(age)
        return ' · '.join(b for b in bits if b)


class Library:
    """Everything kept on this computer: lists, history, subscriptions, playlists, downloads.
    (The progress table is the full edition's Movies & TV; kept so library backups move between them.)"""

    def __init__(self, path):
        os.makedirs(os.path.dirname(path), exist_ok=True)
        self.db = sqlite3.connect(path, check_same_thread=False)
        self.lock = threading.RLock()
        with self.lock, self.db:
            self.db.executescript('''
                CREATE TABLE IF NOT EXISTS videos(id TEXT PRIMARY KEY, data TEXT NOT NULL);
                CREATE TABLE IF NOT EXISTS lists(list TEXT, id TEXT, added REAL, PRIMARY KEY(list, id));
                CREATE TABLE IF NOT EXISTS history(id TEXT PRIMARY KEY, watched REAL, count INTEGER DEFAULT 1);
                CREATE TABLE IF NOT EXISTS subs(channel_id TEXT PRIMARY KEY, name TEXT, url TEXT, added REAL);
                CREATE TABLE IF NOT EXISTS hidden(kind TEXT, value TEXT, PRIMARY KEY(kind, value));
                CREATE TABLE IF NOT EXISTS playlists(name TEXT PRIMARY KEY, added REAL);
                CREATE TABLE IF NOT EXISTS downloads(path TEXT PRIMARY KEY, id TEXT, title TEXT, audio INTEGER,
                                                     added REAL);
                CREATE TABLE IF NOT EXISTS progress(key TEXT PRIMARY KEY, title_id TEXT, pos REAL, duration REAL,
                                                    updated REAL, finished INTEGER, data TEXT);
            ''')

    def _q(self, sql, args=()):
        with self.lock:
            return self.db.execute(sql, args).fetchall()

    def _w(self, sql, args=()):
        with self.lock, self.db:
            self.db.execute(sql, args)

    def save(self, v):
        if v.kind not in ('video', 'live'):
            return
        with self.lock, self.db:
            row = self.db.execute('SELECT data FROM videos WHERE id=?', (v.id,)).fetchone()
            data = json.loads(row[0]) if row else {}
            fresh = v.to_dict()
            if fresh.get('title') == v.id and data.get('title'):
                fresh.pop('title')  # never replace a real title with a placeholder
            data.update(fresh)
            self.db.execute('INSERT OR REPLACE INTO videos VALUES (?, ?)', (v.id, json.dumps(data)))

    @staticmethod
    def _videos(rows):
        return [Video.from_dict(json.loads(r[0])) for r in rows]

    # lists: 'liked', 'later', 'pl:<playlist name>'
    def add(self, lst, v):
        self.save(v)
        self._w('INSERT OR REPLACE INTO lists VALUES (?, ?, ?)', (lst, v.id, time.time()))

    def remove(self, lst, vid):
        self._w('DELETE FROM lists WHERE list=? AND id=?', (lst, vid))

    def has(self, lst, vid):
        return bool(self._q('SELECT 1 FROM lists WHERE list=? AND id=?', (lst, vid)))

    def items(self, lst, limit=1000):
        return self._videos(self._q('SELECT v.data FROM lists l JOIN videos v ON v.id=l.id '
                                    'WHERE l.list=? ORDER BY l.added DESC LIMIT ?', (lst, limit)))

    def watched(self, v, when=None):
        self.save(v)
        self._w('INSERT INTO history VALUES (?, ?, 1) ON CONFLICT(id) DO UPDATE SET '
                'watched=excluded.watched, count=count+1', (v.id, when or time.time()))

    def history(self, limit=300):
        return self._videos(self._q('SELECT v.data FROM history h JOIN videos v ON v.id=h.id '
                                    'ORDER BY h.watched DESC LIMIT ?', (limit,)))

    def history_ids(self):
        return {r[0] for r in self._q('SELECT id FROM history')}

    def forget(self, vid):
        self._w('DELETE FROM history WHERE id=?', (vid,))

    def clear_history(self):
        self._w('DELETE FROM history')

    def subscribe(self, channel_id, name, url=None):
        self._w('INSERT OR REPLACE INTO subs VALUES (?, ?, ?, ?)',
                (channel_id, name, url or f'https://www.youtube.com/channel/{channel_id}', time.time()))

    def unsubscribe(self, channel_id):
        self._w('DELETE FROM subs WHERE channel_id=?', (channel_id,))

    def is_subscribed(self, channel_id):
        return bool(channel_id) and bool(self._q('SELECT 1 FROM subs WHERE channel_id=?', (channel_id,)))

    def subs(self):
        return [{'channel_id': r[0], 'name': r[1], 'url': r[2]}
                for r in self._q('SELECT channel_id, name, url FROM subs ORDER BY name COLLATE NOCASE')]

    def hide(self, kind, value):
        if value:
            self._w('INSERT OR IGNORE INTO hidden VALUES (?, ?)', (kind, value))

    def hidden(self):
        rows = self._q('SELECT kind, value FROM hidden')
        return {v for k, v in rows if k == 'video'}, {v for k, v in rows if k == 'channel'}

    def create_playlist(self, name):
        self._w('INSERT OR IGNORE INTO playlists VALUES (?, ?)', (name, time.time()))

    def delete_playlist(self, name):
        self._w('DELETE FROM playlists WHERE name=?', (name,))
        self._w('DELETE FROM lists WHERE list=?', ('pl:' + name,))

    def playlists(self):
        out = []
        for (name,) in self._q('SELECT name FROM playlists ORDER BY added DESC'):
            n = self._q('SELECT COUNT(*) FROM lists WHERE list=?', ('pl:' + name,))[0][0]
            first = self._q('SELECT id FROM lists WHERE list=? ORDER BY added DESC LIMIT 1', ('pl:' + name,))
            thumb = f'https://i.ytimg.com/vi/{first[0][0]}/mqdefault.jpg' if first else None
            out.append(Video(name, name, kind='localpl', count=n, thumb=thumb))
        return out

    def add_download(self, path, v, audio):
        self.save(v)
        self._w('INSERT OR REPLACE INTO downloads VALUES (?, ?, ?, ?, ?)',
                (path, v.id, v.title, int(audio), time.time()))

    def downloads(self):
        return self._q('SELECT path, id, title, audio FROM downloads ORDER BY added DESC')

    def remove_download(self, path):
        self._w('DELETE FROM downloads WHERE path=?', (path,))

    def export(self, path):
        with self.lock:
            dump = {'app': 'Smedio', 'version': 1, 'exported': time.time()}
            for table in ('videos', 'lists', 'history', 'subs', 'hidden', 'playlists', 'progress'):
                dump[table] = [list(r) for r in self.db.execute(f'SELECT * FROM {table}')]
        with open(path, 'w') as f:
            json.dump(dump, f)

    def import_backup(self, path):
        with open(path) as f:
            dump = json.load(f)
        if dump.get('app') not in ('TubeLite', 'Smedio'):  # backups from before the rename too
            raise ValueError('Not a Smedio backup file')
        cols = {'videos': 2, 'lists': 3, 'history': 3, 'subs': 4, 'hidden': 2, 'playlists': 2, 'progress': 7}
        with self.lock, self.db:
            for table, n in cols.items():
                rows = [r for r in dump.get(table, []) if len(r) == n]
                self.db.executemany(f'INSERT OR IGNORE INTO {table} VALUES ({",".join("?" * n)})', rows)
        return len(dump.get('subs', [])), len(dump.get('lists', []))

    def import_takeout(self, path):
        """Google Takeout CSVs: subscriptions.csv or a playlist CSV with a 'Video ID' column.
        Returns (message, ids_needing_titles)."""
        with open(path, newline='', encoding='utf-8-sig') as f:
            rows = [r for r in csv.reader(f) if r]
        if not rows:
            return 'That file is empty.', []
        header = [h.strip().lower() for h in rows[0]]
        if 'channel id' in header:
            ci = header.index('channel id')
            ui = header.index('channel url') if 'channel url' in header else None
            ti = header.index('channel title') if 'channel title' in header else None
            n = 0
            for r in rows[1:]:
                if len(r) > ci and r[ci].strip().startswith('UC'):
                    self.subscribe(r[ci].strip(), r[ti].strip() if ti is not None and len(r) > ti else r[ci],
                                   r[ui].strip() if ui is not None and len(r) > ui else None)
                    n += 1
            return f'Imported {n} subscriptions.', []
        if 'video id' in header:
            vi = header.index('video id')
            name = re.sub(r'(-videos)?\.csv$', '', os.path.basename(path), flags=re.I).strip()
            low = name.lower()
            lst, label = ('liked', 'Liked') if low.startswith('liked') else \
                ('later', 'Watch later') if low.startswith('watch later') else ('pl:' + name, name)
            if lst.startswith('pl:'):
                self.create_playlist(name)
            ids = [r[vi].strip() for r in rows[1:] if len(r) > vi and len(r[vi].strip()) == 11]
            now = time.time()
            for i, vid in enumerate(reversed(ids)):
                self.save(Video(vid))
                self._w('INSERT OR REPLACE INTO lists VALUES (?, ?, ?)', (lst, vid, now + i * 0.001))
            return f'Imported {len(ids)} videos into {label}.', ids
        return 'Not a recognised Google Takeout file (expected subscriptions.csv or a playlist CSV).', []

# ---------------------------------------------------------------- YouTube access


def _walk(o):
    if isinstance(o, dict):
        yield o
        for v in o.values():
            yield from _walk(v)
    elif isinstance(o, list):
        for v in o:
            yield from _walk(v)


def _text(o):
    if not o:
        return ''
    if isinstance(o, str):
        return o
    if 'simpleText' in o:
        return o['simpleText']
    if 'runs' in o:
        return ''.join(r.get('text', '') for r in o['runs'])
    return o.get('content', '')


def parse_related(data):
    """Pull 'up next' videos out of an innertube /next response (new and old layouts)."""
    out, seen = [], set()
    for d in _walk(data or {}):
        v = None
        lv = d.get('lockupViewModel')
        if isinstance(lv, dict) and lv.get('contentType') == 'LOCKUP_CONTENT_TYPE_VIDEO':
            md = (lv.get('metadata') or {}).get('lockupMetadataViewModel') or {}
            rows = ((md.get('metadata') or {}).get('contentMetadataViewModel') or {}).get('metadataRows') or []
            parts = [(p.get('text') or {}).get('content') for r in rows for p in (r.get('metadataParts') or [])]
            parts = [p for p in parts if p]
            badge = next((x['text'] for x in _walk(lv.get('contentImage'))
                          if isinstance(x.get('text'), str) and x.get('text')), '')
            browse = next((x['browseId'] for x in _walk(lv) if str(x.get('browseId', '')).startswith('UC')), None)
            v = Video(lv.get('contentId'), _text(md.get('title')),
                      channel=parts[0] if parts else '', views_text=parts[1] if len(parts) > 1 else None,
                      age=parts[2] if len(parts) > 2 else None, duration=parse_duration(badge),
                      live=badge.strip().upper() == 'LIVE', channel_id=browse)
        cv = d.get('compactVideoRenderer')
        if isinstance(cv, dict) and cv.get('videoId'):
            runs = (cv.get('longBylineText') or {}).get('runs') or [{}]
            browse = ((runs[0].get('navigationEndpoint') or {}).get('browseEndpoint') or {}).get('browseId')
            v = Video(cv['videoId'], _text(cv.get('title')), channel=_text(cv.get('longBylineText')),
                      views_text=_text(cv.get('shortViewCountText')) or None,
                      age=_text(cv.get('publishedTimeText')) or None,
                      duration=parse_duration(_text(cv.get('lengthText'))), channel_id=browse)
        if v and v.id and len(v.id) == 11 and v.id not in seen:
            if v.channel_id:
                v.channel_url = f'https://www.youtube.com/channel/{v.channel_id}'
            seen.add(v.id)
            out.append(v)
    return out


def summarize_formats(info):
    """The qualities in codecs the GPU decodes, with approximate download sizes (video + best AAC
    audio)."""
    fmts = info.get('formats') or []

    def size(f):
        return (f or {}).get('filesize') or (f or {}).get('filesize_approx') or 0

    audio = max((f for f in fmts if f.get('vcodec') == 'none' and f.get('ext') == 'm4a'),
                key=lambda f: f.get('abr') or 0, default=None)
    best, codecs = {}, hw_codecs()
    ok = ('avc1',) + (('vp9', 'vp09.00') if 'vp9' in codecs else ()) + (('av01',) if 'av1' in codecs else ())
    for f in fmts:
        if (f.get('vcodec') or '').startswith(ok) and f.get('dynamic_range') in (None, 'SDR') \
                and f.get('acodec') == 'none' and f.get('height'):
            h = min(f['height'], f.get('width') or f['height'])  # quality = short side
            if h not in best or size(f) > size(best[h]):
                best[h] = f
    videos = [{'height': h, 'id': f['format_id'], 'fps': f.get('fps'), 'size': size(f) + size(audio)}
              for h, f in sorted(best.items(), reverse=True)]
    return {'video': videos,
            'audio': {'id': audio['format_id'], 'size': size(audio), 'abr': audio.get('abr')} if audio else None}


class YouTube:
    """yt-dlp wrapper. YoutubeDL instances are per worker thread (so lookups run in
    parallel) and per purpose/format, because yt-dlp compiles the format choice when
    the instance is created; changing params['format'] later has no effect."""

    FEEDS = {'home': ':ytrec', 'subs': ':ytsubs', 'liked': ':ytfav', 'later': ':ytwatchlater',
             'history': ':ythis', 'playlists': 'https://www.youtube.com/feed/playlists',
             'channels': 'https://www.youtube.com/feed/channels'}

    def __init__(self):
        self._local = threading.local()
        self.browser = None
        self._auth_gen = 0

    def set_browser(self, browser):
        self.browser = browser
        self._auth_gen += 1

    def _ydl(self, kind='flat', fmt=None, clients=None):
        NET_READY.wait(5)
        cache = self._local.__dict__.setdefault('ydls', {})
        key = (kind, fmt, self._auth_gen if kind == 'auth' else 0, tuple(clients or ()))
        ydl = cache.get(key)
        if ydl is None:
            import yt_dlp
            opts = {'quiet': True, 'no_warnings': True, 'noprogress': True, 'skip_download': True,
                    'socket_timeout': 15}
            if IPV4_ONLY:
                opts['source_address'] = '0.0.0.0'
            if kind == 'flat':
                opts['extract_flat'] = 'in_playlist'
            elif kind == 'auth':
                if not self.browser:
                    raise RuntimeError('No YouTube account connected (Preferences → YouTube account)')
                opts.update(extract_flat='in_playlist', cookiesfrombrowser=(self.browser, None, None, None),
                            extractor_args={'youtubetab': {'skip': ['authcheck']}})
            elif kind == 'details':
                # Comments don't need stream URLs: skipping the player JS (and its Deno solver)
                # cuts this lookup to about a third of the CPU.
                opts.update(format='b/bv*/ba', getcomments=True, ignore_no_formats_error=True,
                            extractor_args={'youtube': {'max_comments': ['40', '40', '0', '0'],
                                                        'comment_sort': ['top'], 'player_skip': ['js'],
                                                        'player_client': ['web']}})
            else:
                opts['format'] = fmt
                if clients and clients != ['default']:
                    opts['extractor_args'] = {'youtube': {'player_client': list(clients)}}
            ydl = cache[key] = yt_dlp.YoutubeDL(opts)
        return ydl

    def warm_up(self):
        check_network()
        self._ydl()

    def warm_up_worker(self):
        self._ydl()  # imports yt-dlp and builds the first extractor inside the helper process

    @staticmethod
    def _extract(ydl, url):
        # Phone hotspots drop DNS/connections now and then; one quiet retry hides most blips.
        for attempt in (1, 2):
            try:
                return ydl.extract_info(url, download=False)
            except Exception as e:  # noqa: BLE001
                if attempt == 2 or not NETWORK_ERROR_RE.search(str(e)):
                    raise
                time.sleep(1)

    def _flat(self, url, limit=None, auth=False):
        ydl = self._ydl('auth' if auth else 'flat')
        ydl.params['playlistend'] = limit
        return self._extract(ydl, url)

    @staticmethod
    def videos(info):
        out, seen = [], set()
        ch, ch_url, ch_id = info.get('channel') or info.get('uploader'), info.get('channel_url'), info.get('channel_id')
        for e in info.get('entries') or []:
            v = e and Video.from_entry(e, ch, ch_url, ch_id)
            if v and v.id not in seen:
                seen.add(v.id)
                out.append(v)
        return out

    def search(self, query, count):
        return self.videos(self._flat(f'ytsearch{count}:{query}'))

    def listing(self, url, limit=60, auth=False):
        url = url.rstrip('/')
        mix = re.search(r'[?&]list=(RD([\w-]{11}))(?:&|$)', url)
        if mix and 'watch?' not in url:
            # Saved Mixes can't be opened as playlist pages; rebuild them from their seed video.
            url = f'https://www.youtube.com/watch?v={mix.group(2)}&list={mix.group(1)}'
        is_channel = is_channel_url(url)
        if is_channel and not url.endswith('/videos'):
            url += '/videos'
        info = self._flat(url, limit, auth)
        name = (info.get('channel') or info.get('uploader')) if is_channel else info.get('title')
        return {'title': name or info.get('title') or 'Videos', 'items': self.videos(info),
                'channel_id': info.get('channel_id'), 'channel_url': info.get('channel_url')}

    def feed(self, name, limit=60):
        return self.videos(self._flat(self.FEEDS[name], limit, auth=True))

    def channel_shorts(self, channel_url, limit=6):
        vids = self.videos(self._flat(channel_root(channel_url) + '/shorts', limit))
        for v in vids:
            v.short = True
        return vids

    def channel_id_for(self, url):
        info = self._flat(channel_root(url) + '/videos', 1)
        return info.get('channel_id'), info.get('channel') or info.get('uploader')

    clients_ok = 0  # index in YT_CLIENTS of the set that last gave working links (per process)
    clients_ok_since = 0.0  # when a slower set took over; the fast first one is tried again later

    @staticmethod
    def _link_ok(f):
        """Does YouTube actually serve this link? (A 2-byte request; refusals come back as 403.)"""
        headers = {'Range': 'bytes=0-1'}
        ua = (f.get('http_headers') or {}).get('User-Agent')
        if ua:
            headers['User-Agent'] = ua
        try:
            with urllib.request.urlopen(urllib.request.Request(f['url'], headers=headers), timeout=10) as r:
                return r.status < 400
        except urllib.error.HTTPError as e:
            return e.code not in (401, 403, 404, 410)
        except OSError:
            return True  # can't tell (slow network): let the player try

    def resolve(self, video_id, fmt):
        """Direct stream URLs for mpv: {url, audio, title, ua, formats}."""
        url, error = f'https://www.youtube.com/watch?v={video_id}', None
        if YouTube.clients_ok and time.monotonic() - YouTube.clients_ok_since > 10 * 60:
            YouTube.clients_ok = 0  # one video the fast set couldn't do shouldn't slow all the rest
        first = YouTube.clients_ok
        for i in list(range(first, len(YT_CLIENTS))) + list(range(first)):
            try:
                info = self._extract(self._ydl('play', fmt, YT_CLIENTS[i]), url)
            except Exception as e:  # noqa: BLE001 - try the next kind of client
                error = e
                continue
            parts = info.get('requested_formats') or [info]
            video = next((f for f in parts if f.get('vcodec') not in (None, 'none')), parts[0])
            audio = next((f for f in parts if f is not video), None)
            with ThreadPoolExecutor(2) as probe:  # both links at once
                if all(probe.map(self._link_ok, [f for f in (video, audio) if f is not None])):
                    if i != YouTube.clients_ok:
                        YouTube.clients_ok, YouTube.clients_ok_since = i, time.monotonic()
                    break
            error = RuntimeError('YouTube refused the stream (403 Forbidden)')
        else:
            raise error
        # A small H.264 stream (ideally 240p, video only) from the same lookup, for hover previews.
        small = [f for f in info.get('formats') or [] if f.get('url') and (f.get('vcodec') or '').startswith('avc1')
                 and 144 <= (f.get('height') or 0) <= 360]
        preview = min(small, key=lambda f: (abs((f.get('height') or 0) - 240), f.get('acodec') != 'none'),
                      default=None)
        return {'url': video['url'], 'audio': audio['url'] if audio else None,
                'title': info.get('title') or video_id, 'height': video.get('height'),
                'ua': (video.get('http_headers') or {}).get('User-Agent'), 'formats': summarize_formats(info),
                'video_itag': video.get('format_id'), 'audio_itag': audio.get('format_id') if audio else None,
                'meta': {'views': info.get('view_count'), 'likes': info.get('like_count'),
                         'upload_date': info.get('upload_date'), 'followers': info.get('channel_follower_count'),
                         'description': info.get('description') or '', 'comment_count': info.get('comment_count'),
                         'channel': info.get('channel') or info.get('uploader'), 'channel_id': info.get('channel_id'),
                         'channel_url': info.get('channel_url'), 'duration': info.get('duration')},
                'preview': preview['url'] if preview else None, 'captions': yt_captions(info),
                'chapters': [{'start': c.get('start_time') or 0,  # yt-dlp's '<Untitled Chapter 1>' -> no name
                              'title': '' if (c.get('title') or '').startswith('<Untitled') else c.get('title') or ''}
                             for c in info.get('chapters') or []]}

    def moving_thumbs(self, query):
        """YouTube's animated 3-second thumbnails for a search ({video id: webp url}); ~50 KB."""
        ie = self._ydl('flat').get_info_extractor('Youtube')
        out = {}
        for d in _walk(ie._call_api('search', {'query': query}, 'search', fatal=False) or {}):
            vr = d.get('videoRenderer')
            if isinstance(vr, dict) and vr.get('videoId'):
                moving = ((vr.get('richThumbnail') or {}).get('movingThumbnailRenderer') or {})
                for t in (moving.get('movingThumbnailDetails') or {}).get('thumbnails') or []:
                    if t.get('url'):
                        out[vr['videoId']] = t['url']
                        break
        return out

    def details(self, video_id):
        info = self._extract(self._ydl('details'), f'https://www.youtube.com/watch?v={video_id}')
        comments = [{'author': c.get('author') or '', 'text': c.get('text') or '', 'likes': c.get('like_count'),
                     'time': c.get('_time_text') or '', 'pinned': c.get('is_pinned'),
                     'uploader': c.get('author_is_uploader')}
                    for c in info.get('comments') or [] if c.get('parent') in (None, 'root')]
        v = Video(video_id, info.get('title'), channel=info.get('channel') or info.get('uploader') or '',
                  channel_id=info.get('channel_id'), channel_url=info.get('channel_url'),
                  duration=info.get('duration'), views=info.get('view_count'),
                  live=bool(info.get('is_live')), published=info.get('timestamp'))
        return {'video': v, 'likes': info.get('like_count'), 'description': info.get('description') or '',
                'upload_date': info.get('upload_date'), 'comments': comments,
                'comment_count': info.get('comment_count'), 'followers': info.get('channel_follower_count')}

    def related(self, video_id):
        ie = self._ydl('flat').get_info_extractor('Youtube')
        return parse_related(ie._call_api('next', {'videoId': video_id}, video_id, fatal=False))

    @staticmethod
    def rss_ttl(videos):
        """How long a channel's feed stays fresh: busy channels are re-checked more often."""
        newest = max((v.published or 0 for v in videos), default=0)
        days = (time.time() - newest) / 86400
        return 30 * 60 if days < 2 else 3 * 3600 if days < 14 else 12 * 3600 if days < 90 else 24 * 3600

    @staticmethod
    def rss_cached(channel_id):
        """(videos, fetched_at) from the disk cache, or (None, 0)."""
        try:
            with open(os.path.join(RSS_DIR, f'{channel_id}.json')) as f:
                d = json.load(f)
            return [Video.from_dict(v) for v in d['videos']], d['fetched']
        except (OSError, ValueError, KeyError, TypeError):
            return None, 0

    def rss(self, channel_id, max_age=None):
        """A channel's latest uploads, from the cache while fresh, otherwise from YouTube."""
        videos, fetched = self.rss_cached(channel_id)
        if videos is not None:
            ttl = self.rss_ttl(videos) if max_age is None else max_age
            if time.time() - fetched < ttl:
                return videos
        return self.rss_fetch(channel_id)

    def rss_fetch(self, channel_id):
        fetched = time.time()
        try:
            videos = self._rss_download(channel_id)
        except urllib.error.HTTPError as e:
            if e.code not in (404, 500, 502, 503):
                raise
            # YouTube's feeds fail now and then (even for active channels), and deleted channels 404
            # for good. Either way: keep what we had and look again in an hour, instead of
            # retrying on every visit or hiding a live channel's uploads for a day.
            videos = self.rss_cached(channel_id)[0] or []
            fetched = time.time() - self.rss_ttl(videos) + 3600
        os.makedirs(RSS_DIR, exist_ok=True)
        tmp = os.path.join(RSS_DIR, f'{channel_id}.json.{threading.get_ident()}')
        with open(tmp, 'w') as f:
            json.dump({'fetched': fetched, 'videos': [v.to_dict() for v in videos]}, f)
        os.replace(tmp, os.path.join(RSS_DIR, f'{channel_id}.json'))
        return videos

    _rss_gate = threading.Semaphore(3)  # YouTube throttles bursts of feed requests

    def _rss_download(self, channel_id):
        """Latest uploads of a channel from YouTube's public feed (no login; ~4 KB compressed)."""
        ns = {'a': 'http://www.w3.org/2005/Atom', 'yt': 'http://www.youtube.com/xml/schemas/2015',
              'media': 'http://search.yahoo.com/mrss/'}
        with self._rss_gate:
            data = http_get(f'https://www.youtube.com/feeds/videos.xml?channel_id={channel_id}')
        root = ET.fromstring(data)
        author = root.findtext('a:title', default='', namespaces=ns)
        out = []
        for en in root.findall('a:entry', ns):
            link_el = en.find('a:link', ns)
            link = (link_el.get('href') if link_el is not None else '') or ''
            stats = en.find('media:group/media:community/media:statistics', ns)
            try:
                published = datetime.fromisoformat(en.findtext('a:published', namespaces=ns)).timestamp()
            except (TypeError, ValueError):
                published = None
            out.append(Video(en.findtext('yt:videoId', namespaces=ns), en.findtext('a:title', namespaces=ns),
                             channel=author, channel_id=channel_id,
                             channel_url=f'https://www.youtube.com/channel/{channel_id}',
                             views=int(stats.get('views')) if stats is not None and stats.get('views') else None,
                             published=published, short='/shorts/' in link))
        return out

    @staticmethod
    def oembed(video_id):
        d = json.loads(http_get('https://www.youtube.com/oembed?format=json&url='
                                f'https://www.youtube.com/watch?v={video_id}'))
        return d.get('title'), d.get('author_name'), d.get('author_url')

# ---------------------------------------------------------------- lookups in helper processes
# yt-dlp parses megabytes of HTML/JSON in pure Python. In the GTK process that holds Python's
# GIL, and the video's per-frame draw callback (also Python) has to wait: frames get dropped.
# So every YouTube lookup runs in a small pool of helper processes instead.

_WORKER_YT = None


def _worker_init(ipv4, background, app_pid):
    global _WORKER_YT

    def watchdog():  # exit if Smedio is gone (quit or crashed), never linger
        while True:
            time.sleep(3)
            try:
                os.kill(app_pid, 0)
            except OSError:
                os._exit(0)

    threading.Thread(target=watchdog, daemon=True).start()
    try:
        os.setpriority(os.PRIO_PROCESS, 0, 10 if background else 4)
        cpus = sorted(os.sched_getaffinity(0))
        if background and len(cpus) >= 4:
            os.sched_setaffinity(0, {cpus[-1]})  # keep heavy parsing off the cores drawing video
    except OSError:
        pass
    if ipv4:
        force_ipv4()
    NET_READY.set()
    _WORKER_YT = YouTube()


def _worker_call(browser, method, args):
    if _WORKER_YT.browser != browser:
        _WORKER_YT.set_browser(browser)
    try:
        return getattr(_WORKER_YT, method)(*args)
    except Exception as e:  # noqa: BLE001 - yt-dlp errors don't always pickle; send the message
        raise RuntimeError(clean_error(e)) from None


class Lookups:
    """Same interface as YouTube, but run in helper processes: 'fast' (1 process, for the
    video you clicked) and 'background' (2 low-priority processes confined to one CPU thread,
    for everything else). RSS feeds are tiny and stay in-process."""

    IDLE_SHUTDOWN = 180  # seconds without lookups before the background helpers exit (~140 MB)

    def __init__(self):
        self.browser = None
        self.local = YouTube()
        self._pools = {}
        self._lock = threading.Lock()
        self._busy, self._last_used = 0, time.monotonic()
        threading.Thread(target=self._reaper, daemon=True).start()

    def _reaper(self):
        while True:
            time.sleep(30)
            with self._lock:
                idle_for = time.monotonic() - self._last_used
                if True not in self._pools or self._busy or idle_for < self.IDLE_SHUTDOWN:
                    continue
                # Only the background helpers go; the one for clicked videos stays ready (~60 MB).
                pools = {True: self._pools.pop(True)}
            self._stop(pools)

    def set_browser(self, browser):
        self.browser = browser
        self.local.set_browser(browser)

    def _pool(self, background):
        with self._lock:
            if background not in self._pools:
                NET_READY.wait(5)
                self._pools[background] = ProcessPoolExecutor(
                    2 if background else 1, mp_context=multiprocessing.get_context('forkserver'),
                    initializer=_worker_init, initargs=(IPV4_ONLY, background, os.getpid()))
            return self._pools[background]

    def _call(self, method, *args, background=True):
        with self._lock:
            self._busy += 1
        try:
            return self._pool(background).submit(_worker_call, self.browser, method, args).result()
        finally:
            with self._lock:
                self._busy -= 1
                self._last_used = time.monotonic()

    def warm_up(self):
        check_network()
        for bg in (False, True):  # start the helpers now so the first lookup isn't slowed by it
            self._pool(bg).submit(_worker_call, None, 'warm_up_worker', ())

    def shutdown(self):
        with self._lock:
            pools, self._pools = self._pools, {}
        self._stop(pools)

    @staticmethod
    def _stop(pools):
        for pool in pools.values():
            for proc in list((getattr(pool, '_processes', None) or {}).values()):
                proc.terminate()
            pool.shutdown(wait=False, cancel_futures=True)

    def resolve(self, video_id, fmt):
        return self._call('resolve', video_id, fmt, background=False)

    def resolve_bg(self, video_id, fmt):
        return self._call('resolve', video_id, fmt)

    def __getattr__(self, name):
        if name in ('search', 'listing', 'feed', 'channel_shorts', 'channel_id_for', 'details', 'related',
                    'moving_thumbs'):
            return lambda *args: self._call(name, *args)
        if name in ('rss', 'rss_fetch', 'rss_cached', 'rss_ttl', 'oembed'):
            return getattr(self.local, name)
        raise AttributeError(name)


# ---------------------------------------------------------------- recommendations (local)


def title_keywords(videos_with_weights, n=3):
    score = Counter()
    for v, w in videos_with_weights:
        words = {t for t in re.split(r'[\s|\-–—:;,.!?()\[\]{}#"\'/&+*@]+', (v.title or '').lower())
                 if len(t) >= 3 and not t.isdigit() and t not in STOPWORDS}
        for t in words:
            score[t] += w
    return [w for w, _ in score.most_common(n)]


def recommend(lib, yt, pool, limit=60):
    """'For you', computed on this device from likes, history and subscriptions:
    related videos of recent favourites, fresh uploads from subscribed channels,
    and searches for the topics you watch most. Watched/hidden videos are skipped."""
    watched = lib.history_ids()
    hidden_v, hidden_c = lib.hidden()
    likes, hist, subs = lib.items('liked', 60), lib.history(150), lib.subs()
    now = time.time()

    seeds, seen = [], set()
    for v in likes[:3] + hist[:5]:
        if v.id not in seen:
            seen.add(v.id)
            seeds.append(v)
    seeds = seeds[:6]

    affinity = Counter()
    for v in hist:
        affinity[v.channel_id or v.channel] += 1
    for v in likes:
        affinity[v.channel_id or v.channel] += 3
    for s in subs:
        affinity[s['channel_id']] += 4

    kws = title_keywords([(v, 3) for v in likes] + [(v, 1) for v in hist], 3)
    queries = [kws[0], ' '.join(kws[1:3])] if len(kws) >= 3 else kws[:1]
    sub_ids = sorted((s['channel_id'] for s in subs), key=lambda c: -affinity[c])[:30]
    futures = {pool.submit(yt.related, s.id): ('related', i) for i, s in enumerate(seeds)}
    futures.update({pool.submit(yt.rss, c): ('rss', c) for c in sub_ids})
    futures.update({pool.submit(yt.search, q, 12): ('search', q) for q in queries if q})

    picked = {}

    def add(v, score):
        if (v.kind != 'video' or v.short or v.id in watched or v.id in hidden_v
                or (v.channel_id and v.channel_id in hidden_c) or v.channel in hidden_c):
            return
        if v.id in picked:
            picked[v.id][1] += score
        else:
            picked[v.id] = [v, score]

    try:
        for fut in as_completed(futures, timeout=45):
            kind, src = futures[fut]
            try:
                res = fut.result()
            except Exception:  # noqa: BLE001 - one failed source shouldn't sink the page
                continue
            if kind == 'related':
                for rank, v in enumerate(res[:20]):
                    add(v, 3.0 * (1.0 - src * 0.1) * max(0.25, 1 - rank / 20))
            elif kind == 'rss':
                for v in res:
                    days = (now - (v.published or 0)) / 86400
                    if days <= 14:
                        add(v, 2.5 * math.exp(-days / 5))
            else:
                for rank, v in enumerate(res):
                    add(v, 1.2 * max(0.3, 1 - rank / 12))
    except FutureTimeout:
        pass

    for item in picked.values():
        item[1] += 0.5 * min(affinity[item[0].channel_id or item[0].channel], 6)
    ranked = sorted(picked.values(), key=lambda it: it[1] * random.uniform(0.85, 1.15), reverse=True)
    per_channel, out = Counter(), []
    for v, _ in ranked:
        key = v.channel_id or v.channel
        if per_channel[key] >= 3:
            continue
        per_channel[key] += 1
        out.append(v)
        if len(out) >= limit:
            break
    return out


def recommend_more(lib, yt, pool, shown, state, want=30):
    """The next part of 'For you' as you scroll down: related videos of older favourites and of
    what the feed already shows, and further search results for your topics. `state` (a dict,
    emptied when the feed reloads) remembers the seeds used so every part is new."""
    watched = lib.history_ids()
    hidden_v, hidden_c = lib.hidden()
    likes, hist = lib.items('liked', 200), lib.history(300)
    used = state.setdefault('seeds', set())
    rnd = state['round'] = state.get('round', 0) + 1
    shown_ids = {v.id for v in shown}
    own = [v for v in likes[3:] + hist[5:] if v.id not in used]          # older favourites
    feed = [v for v in shown if v.id not in used and v.kind == 'video']  # what the feed found
    seeds = own[:3] + random.sample(feed, min(3, len(feed)))
    used.update(v.id for v in seeds)
    kws = title_keywords([(v, 3) for v in likes] + [(v, 1) for v in hist], 8)
    query = kws[rnd % len(kws)] if kws else None
    futures = {pool.submit(yt.related, v.id): 'related' for v in seeds}
    if query:
        futures[pool.submit(yt.search, query, 12 + 12 * rnd)] = 'search'

    picked = {}
    try:
        for fut in as_completed(futures, timeout=45):
            try:
                res = fut.result()
            except Exception:  # noqa: BLE001 - one failed source shouldn't end the feed
                continue
            if futures[fut] == 'search':
                res = res[12 * rnd:] or res  # the part the earlier rounds didn't reach
            for rank, v in enumerate(res[:20]):
                if (v.kind != 'video' or v.short or v.id in watched or v.id in shown_ids or v.id in hidden_v
                        or (v.channel_id and v.channel_id in hidden_c) or v.channel in hidden_c):
                    continue
                score = max(0.25, 1 - rank / 20) * random.uniform(0.85, 1.15)
                picked[v.id] = (v, picked[v.id][1] + score if v.id in picked else score)
    except FutureTimeout:
        pass
    per_channel, out = Counter(), []
    for v, _ in sorted(picked.values(), key=lambda it: -it[1]):
        key = v.channel_id or v.channel
        if per_channel[key] < 3:
            per_channel[key] += 1
            out.append(v)
            if len(out) >= want:
                break
    return out


def shorts_feed(lib, yt, pool, google_channels=None, limit=48):
    """Shorts from channels you follow or watch, plus shorts about your topics."""
    watched = lib.history_ids()
    hidden_v, hidden_c = lib.hidden()
    hist, likes = lib.history(150), lib.items('liked', 60)
    affinity = Counter()
    for v in hist + likes:
        if v.channel_link:
            affinity[v.channel_link] += 1
    for s in lib.subs():
        affinity[channel_root(s['url'])] += 3
    for c in google_channels or []:
        affinity[channel_root(c)] += 3
    channels = [c for c, _ in affinity.most_common(10)]
    kws = title_keywords([(v, 3) for v in likes] + [(v, 1) for v in hist], 2) or ['trending']
    futures = [pool.submit(yt.channel_shorts, c, 5) for c in channels]
    futures += [pool.submit(yt.search, f'{k} #shorts', 20) for k in kws]
    buckets = []
    try:
        for fut in as_completed(futures, timeout=40):
            try:
                res = fut.result()
            except Exception:  # noqa: BLE001
                continue
            res = [v for v in res if v.short or (v.duration and v.duration <= 180)]
            for v in res:
                v.short = True
            buckets.append(res)
    except FutureTimeout:
        pass
    out, seen = [], set()
    for group in itertools.zip_longest(*buckets):  # interleave sources for variety
        for v in group:
            if (v and v.id not in seen and v.id not in watched and v.id not in hidden_v
                    and (v.channel_id or '') not in hidden_c):
                seen.add(v.id)
                out.append(v)
    return out[:limit]

def copy_google_account(lib, yt, pool, log=lambda *_: None):
    """Copy subscriptions, likes, Watch later, playlists and recent history from the connected
    YouTube account into the local library. Returns (copied, failed) summaries."""
    done, failed = [], []

    def grab(name, fn):
        try:
            return fn()
        except Exception as e:  # noqa: BLE001
            failed.append(f'{name} ({clean_error(e)[:100]})')
            return []

    log('reading subscriptions…')
    chans = [c for c in grab('subscriptions', lambda: yt.feed('channels', None)) if c.kind == 'channel']
    missing = [c for c in chans if not c.channel_id and c.link]
    for c, res in zip(missing, pool.map(lambda c: grab(c.title, lambda: yt.channel_id_for(c.link)), missing)):
        if res:
            c.channel_id = res[0]
    subscribed = 0
    for c in chans:
        if c.channel_id:
            lib.subscribe(c.channel_id, c.title, c.link)
            subscribed += 1
    done.append(f'{subscribed} subscriptions')
    for name, label in (('liked', 'liked'), ('later', 'Watch later')):
        log(f'{", ".join(done)} copied · reading {label} videos (large lists take a few minutes)…')
        vids = [v for v in grab(label, lambda name=name: yt.feed(name, 5000)) if v.kind == 'video']
        for v in reversed(vids):  # oldest first, so the newest ends up on top
            lib.add(name, v)
        done.append(f'{len(vids)} {label}')
    log(f'{", ".join(done)} copied · reading history…')
    hist = [v for v in grab('history', lambda: yt.feed('history', 300)) if v.kind == 'video']
    now = time.time()
    for i, v in enumerate(hist):
        lib.watched(v, when=now - i * 60)
    done.append(f'{len(hist)} history')
    log(f'{", ".join(done)} copied · reading playlists…')
    pls = [p for p in grab('playlists', lambda: yt.feed('playlists', None))
           if p.kind == 'playlist' and p.id not in ('LL', 'WL', 'LM')]  # liked / later are copied above
    copied_items = 0
    for i, p in enumerate(pls, 1):
        log(f'{", ".join(done)} copied · playlist {i} of {len(pls)}…')
        items = grab(p.title, lambda p=p: yt.listing(p.url, 5000 if not p.id.startswith('RD') else 200,
                                                     auth=not p.id.startswith('RD'))['items'])
        lib.create_playlist(p.title)
        for v in reversed(items):
            if v.kind == 'video':
                lib.add('pl:' + p.title, v)
                copied_items += 1
    done.append(f'{len(pls)} playlists ({copied_items} videos)')
    return done, failed

# ---------------------------------------------------------------- embedded player (libmpv)


def load_mpv_module():
    """python-mpv finds libmpv by name; fall back to the copy install.sh unpacked from
    Ubuntu's libmpv2 package when the system one isn't installed."""
    real = ctypes.util.find_library
    if not real('mpv') and os.path.exists(BUNDLED_LIBMPV):
        ctypes.util.find_library = lambda n: BUNDLED_LIBMPV if n == 'mpv' else real(n)
    try:
        import mpv
        return mpv
    except (ImportError, OSError):
        return None
    finally:
        ctypes.util.find_library = real


def mpv_quote(value):
    """mpv's length-prefixed quoting, so stream URLs with commas survive option lists."""
    value = str(value)
    return f'%{len(value.encode())}%{value}'


class GL:
    egl = gl = None

    @classmethod
    def init(cls):
        if cls.egl is None:
            cls.egl = ctypes.CDLL('libEGL.so.1')
            cls.egl.eglGetProcAddress.restype = ctypes.c_void_p
            cls.egl.eglGetProcAddress.argtypes = [ctypes.c_char_p]
            for name in ('libOpenGL.so.0', 'libGL.so.1', 'libGLESv2.so.2'):  # glvnd, Mesa without it, GLES
                try:
                    cls.gl = ctypes.CDLL(name)
                    break
                except OSError:
                    if name == 'libGLESv2.so.2':
                        raise
            cls.gl.glGetIntegerv.argtypes = [ctypes.c_uint, ctypes.POINTER(ctypes.c_int)]

    @staticmethod
    def wayland_display():
        """Native wl_display pointer, which lets mpv use zero-copy VA-API frames."""
        try:
            gi.require_version('GdkWayland', '4.0')
            from gi.repository import GdkWayland
            disp = Gdk.Display.get_default()
            if not isinstance(disp, GdkWayland.WaylandDisplay):
                return None
            get_ptr = ctypes.pythonapi.PyCapsule_GetPointer
            get_ptr.restype, get_ptr.argtypes = ctypes.c_void_p, [ctypes.py_object, ctypes.c_char_p]
            gtk = ctypes.CDLL('libgtk-4.so.1')
            gtk.gdk_wayland_display_get_wl_display.restype = ctypes.c_void_p
            gtk.gdk_wayland_display_get_wl_display.argtypes = [ctypes.c_void_p]
            return gtk.gdk_wayland_display_get_wl_display(get_ptr(disp.__gpointer__, None))
        except Exception:  # noqa: BLE001 - copy-back decoding still works without it
            return None


class Engine:
    """One libmpv instance for the whole app, drawn into the watch page's VideoArea."""

    WATCH = ('time-pos', 'duration', 'pause', 'demuxer-cache-time', 'paused-for-cache', 'idle-active',
             'eof-reached', 'playlist-pos', 'playlist-count', 'volume', 'mute', 'seeking', 'speed', 'height')

    def __init__(self, mpvmod, on_event, volume):
        locale.setlocale(locale.LC_NUMERIC, 'C')  # libmpv requirement
        self.mpvmod = mpvmod
        # video-timing-offset=0 + non-blocking render: GTK paces frames. mpv's default (render 50 ms
        # early, then block until display time) froze GTK's main thread and caused dropped frames.
        self.m = mpvmod.MPV(vo='libmpv', hwdec=HWDEC, profile='fast', idle='yes',
                            log_handler=player_log, loglevel='warn',
                            video_timing_offset=0,
                            keep_open='yes', cache='yes', demuxer_max_bytes='64MiB', demuxer_readahead_secs=20,
                            osd_level=0, volume=volume, input_default_bindings=False, ytdl='yes',
                            script_opts=f'ytdl_hook-ytdl_path={YTDLP}')
        if IPV4_ONLY:
            self.m['ytdl-raw-options'] = 'force-ipv4='
        self.m.command('change-list', 'ytdl-raw-options', 'append', f'extractor-args={YT_CLIENTS_ARG}')
        last = {}

        def observe(name, val):
            # time-pos / cache-time change every frame; the UI only needs ~4 updates a second
            # (but never miss a jump, e.g. a seek).
            if name in ('time-pos', 'demuxer-cache-time') and val is not None:
                t, prev = last.get(name, (0, None))
                now = time.monotonic()
                if now - t < 0.25 and prev is not None and abs(val - prev) < 1:
                    return
                last[name] = (now, val)
            idle(on_event, name, val)

        for prop in self.WATCH:
            self.m.observe_property(prop, observe)

        @self.m.event_callback('end-file')
        def ended(event):  # a stream that fails at once never shows up in idle-active
            if event.data.reason == mpvmod.MpvEventEndFile.ERROR:
                idle(on_event, 'load-error', event.data.error)
        self.queue = []          # Video objects in mpv playlist order
        self.lock = threading.Lock()

    def load(self, url, mode, title, audio=None, ua=None, cover=None, start=None, opts=None):
        opts = [f'force-media-title={mpv_quote(title)}', 'sub-delay=0'] + list(opts or [])  # timing is per video
        if audio:
            opts.append(f'audio-file={mpv_quote(audio)}')
        if ua:
            opts.append(f'user-agent={mpv_quote(ua)}')
        if cover:
            opts.append(f'cover-art-file={mpv_quote(cover)}')
        if start:
            opts.append(f'start={mpv_quote(f"{start:.1f}")}')
        self.m.command('loadfile', url, mode, -1, ','.join(opts))

    def load_stream(self, stream, mode, cover=None, start=None):
        cap = pick_caption(stream)
        opts = [f'sub-file={mpv_quote(cap["url"])}', 'sid=auto'] if cap else None
        self.load(stream['url'], mode, stream['title'], stream.get('audio'), stream.get('ua'), cover, start, opts)

    def add_caption(self, cap):
        """A caption track now (the gear menu): selected, or the one already loaded."""
        for t in self.m.track_list or []:
            if t.get('type') == 'sub' and t.get('external-filename') == cap['url']:
                self.m.sid = t['id']
                return
        self.m.command('sub-add', cap['url'], 'select', cap['name'], cap['lang'])

    def swap_video(self, quick_url, stream):
        """Upgrade a quick-started 360p stream to the full one without restarting."""
        if quick_url and self.m.path != quick_url:
            return  # the user already moved on
        try:
            self.m.command('video-add', stream['url'], 'select', f'{stream.get("height") or "HD"}p')
            if quick_url and stream.get('audio'):
                self.m.command('audio-add', stream['audio'], 'select', 'HD')
            cap = pick_caption(stream)
            if cap:
                self.add_caption(cap)
        except Exception:  # noqa: BLE001 - fall back to reloading at the same position
            self.load_stream(stream, 'replace', start=self.m.time_pos or 0)

    def stop(self):
        with self.lock:
            self.queue = []
        self.m.command('stop')


class VideoArea(Gtk.GLArea):
    """Draws mpv frames with OpenGL; 16:9 in the page, fills the screen in fullscreen."""

    def __init__(self, engine):
        super().__init__(hexpand=True)
        self.engine, self.ctx, self.fill = engine, None, False
        self._saved_vid = None
        self._proc = engine.mpvmod.MpvGlGetProcAddressFn(lambda _c, name: GL.egl.eglGetProcAddress(name))
        self.connect('realize', self._realize)
        self.connect('unrealize', self._unrealize)
        self.connect('render', self._render)

    def do_get_request_mode(self):
        return Gtk.SizeRequestMode.HEIGHT_FOR_WIDTH

    def do_measure(self, orientation, for_size):
        if orientation == Gtk.Orientation.HORIZONTAL:
            return 240, 854, -1, -1
        if self.fill:
            return 100, 100, -1, -1
        w = for_size if for_size > 0 else 854
        root = self.get_root()
        cap = int(root.get_height() * 0.74) if root and root.get_height() > 0 else 720
        h = max(135, min(int(w * 9 / 16), cap))
        return h, h, -1, -1

    def _realize(self, area):
        area.make_current()
        if area.get_error():
            return
        params = {'opengl_init_params': {'get_proc_address': self._proc}}
        wl = GL.wayland_display()
        if wl:
            params['wl_display'] = ctypes.c_void_p(wl)
        self.ctx = self.engine.mpvmod.MpvRenderContext(self.engine.m, 'opengl', **params)
        self.ctx.update_cb = lambda: idle(self._on_mpv_update)
        hz = self.refresh_rate()
        if hz:
            self.engine.m['display-fps-override'] = hz
        if self._saved_vid not in (None, False, 'no') and not self.engine.m.idle_active:
            try:
                self.engine.m.vid = self._saved_vid
            except Exception:  # noqa: BLE001
                pass
        self._saved_vid = None

    def refresh_rate(self):
        try:
            mon = Gdk.Display.get_default().get_monitor_at_surface(self.get_native().get_surface())
            return mon.get_refresh_rate() / 1000 if mon and mon.get_refresh_rate() else None
        except Exception:  # noqa: BLE001
            return None

    def _on_mpv_update(self):
        # mpv_render_context_update() must run after every update callback: besides saying whether a
        # new frame is ready, it services mpv's requests to the renderer (e.g. display-fps queries).
        # Skipping it left those requests waiting forever.
        if self.ctx and self.ctx.update():
            self.queue_render()

    def _unrealize(self, area):
        # Leaving the watch page: mpv drops video (saving power) but keeps playing audio.
        if self.ctx:
            self._saved_vid = self.engine.m.vid
            area.make_current()
            self.ctx.free()
            self.ctx = None

    def _render(self, area, _glctx):
        if not self.ctx:
            return False
        fbo = ctypes.c_int()
        GL.gl.glGetIntegerv(0x8CA6, ctypes.byref(fbo))  # GL_DRAW_FRAMEBUFFER_BINDING
        s = self.get_scale_factor()
        self.ctx.render(flip_y=True, block_for_target_time=False,
                        opengl_fbo={'w': self.get_width() * s, 'h': self.get_height() * s, 'fbo': fbo.value})
        return True


class PreviewClip:
    """Muted, video-only GStreamer playback into a GTK paintable for hover previews.
    Audio is never decoded or sent to a sound device."""
    _gst = None

    def __init__(self, url, start=0, ua=None):
        if PreviewClip._gst is None:
            gi.require_version('Gst', '1.0')
            from gi.repository import Gst
            Gst.init(None)
            PreviewClip._gst = Gst
        Gst = PreviewClip._gst
        self.sink = Gst.ElementFactory.make('gtk4paintablesink')
        self.paintable = self.sink.get_property('paintable')
        self.pipe = Gst.ElementFactory.make('playbin3')
        self.pipe.set_property('uri', url)
        self.pipe.set_property('video-sink', self.sink)
        Gst.util_set_object_arg(self.pipe, 'flags', 'video')
        if ua:
            self.pipe.connect('source-setup', lambda _p, src: src.find_property('user-agent')
                              and src.set_property('user-agent', ua))
        self.start = start
        self.bus = self.pipe.get_bus()
        self.bus.add_signal_watch()
        self.bus.connect('message', self._on_message)
        self.pipe.set_state(Gst.State.PLAYING)

    def _on_message(self, _bus, msg):
        Gst = PreviewClip._gst
        if msg.type == Gst.MessageType.ASYNC_DONE and self.start:
            start, self.start = self.start, 0  # skip intros on longer videos, once
            self.pipe.seek_simple(Gst.Format.TIME, Gst.SeekFlags.FLUSH | Gst.SeekFlags.KEY_UNIT,
                                  int(start * Gst.SECOND))
        elif msg.type == Gst.MessageType.EOS:
            self.pipe.seek_simple(Gst.Format.TIME, Gst.SeekFlags.FLUSH | Gst.SeekFlags.KEY_UNIT, 0)

    def position(self):
        ok, pos = self.pipe.query_position(PreviewClip._gst.Format.TIME)
        return pos / 1e9 if ok else 0.0

    def stop(self):
        self.bus.remove_signal_watch()
        self.pipe.set_state(PreviewClip._gst.State.NULL)


def pixbuf_texture(pb):
    fmt = Gdk.MemoryFormat.R8G8B8A8 if pb.get_has_alpha() else Gdk.MemoryFormat.R8G8B8
    return Gdk.MemoryTexture.new(pb.get_width(), pb.get_height(), fmt, pb.read_pixel_bytes(), pb.get_rowstride())


class AnimClip:
    """YouTube's animated WebP thumbnail, stepped with a timer (no video decoding at all)."""

    def __init__(self, anim, picture):
        self.it, self.picture, self.src = anim.get_iter(None), picture, 0
        self._show()

    def _show(self):
        self.picture.set_paintable(pixbuf_texture(self.it.get_pixbuf()))
        delay = self.it.get_delay_time()
        if delay >= 0:
            self.src = GLib.timeout_add(max(delay, 20), self._tick)

    def _tick(self):
        self.src = 0
        self.it.advance(None)
        self._show()
        return GLib.SOURCE_REMOVE

    def stop(self):
        if self.src:
            GLib.source_remove(self.src)
            self.src = 0


class ExternalPlayer:
    """Separate mpv window driven over its JSON IPC socket (fallback / pop-out)."""

    def __init__(self):
        self._ids = itertools.count(1)
        self._lock = threading.Lock()

    def command(self, cmd, timeout=3.0):
        rid = next(self._ids)
        with socket.socket(socket.AF_UNIX) as s:
            s.settimeout(timeout)
            s.connect(MPV_SOCKET)
            s.sendall(json.dumps({'command': cmd, 'request_id': rid}).encode() + b'\n')
            buf = b''
            while True:
                chunk = s.recv(65536)
                if not chunk:
                    raise ConnectionError('mpv closed the connection')
                buf += chunk
                while b'\n' in buf:
                    line, buf = buf.split(b'\n', 1)
                    try:
                        reply = json.loads(line)
                    except ValueError:
                        continue
                    if reply.get('request_id') == rid:
                        if reply.get('error') != 'success':
                            raise RuntimeError(f"mpv: {reply.get('error')}")
                        return reply.get('data')

    def _alive(self):
        try:
            self.command(['get_property', 'pid'], timeout=0.5)
            return True
        except (OSError, RuntimeError):
            return False

    def ensure(self, fmt, fullscreen=True):
        with self._lock:
            if self._alive():
                return
            if os.path.exists(MPV_SOCKET):
                os.unlink(MPV_SOCKET)
            args = ['mpv', '--idle=yes', '--force-window=immediate', f'--input-ipc-server={MPV_SOCKET}',
                    f'--hwdec={HWDEC}', '--profile=fast', '--keep-open=no', '--cache=yes',
                    '--fs' if fullscreen else '--autofit=85%x85%',
                    '--title=${?media-title:${media-title}}${!media-title:Smedio player}',
                    f'--script-opts=ytdl_hook-ytdl_path={YTDLP}',
                    f'--ytdl-format={fmt}']
            if IPV4_ONLY:
                args.append('--ytdl-raw-options-append=force-ipv4=')
            args.append(f'--ytdl-raw-options-append=extractor-args={YT_CLIENTS_ARG}')
            proc = subprocess.Popen(args, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                                    stderr=subprocess.DEVNULL, start_new_session=True)
            deadline = time.monotonic() + 6
            while time.monotonic() < deadline:
                if proc.poll() is not None:
                    raise RuntimeError('mpv exited during startup')
                if self._alive():
                    return
                time.sleep(0.05)
            raise RuntimeError('mpv did not start')

    def load(self, stream, flags='replace', start=None):
        opts = {'force-media-title': stream['title']}
        if stream.get('audio'):
            opts['audio-file'] = stream['audio']
        if stream.get('ua'):
            opts['user-agent'] = stream['ua']
        if start:
            opts['start'] = f'{start:.1f}'
        cap = pick_caption(stream)
        if cap:
            opts['sub-file'] = cap['url']
        self.command({'name': 'loadfile', 'url': stream['url'], 'flags': flags, 'options': opts})

# ---------------------------------------------------------------- downloads


class Download:
    def __init__(self, video, audio, fmt, label):
        self.video, self.audio, self.fmt, self.label = video, audio, fmt, label
        self.status, self.progress, self.detail = 'Queued', 0.0, 'Waiting…'
        self.path, self.cancelled, self.proc = None, False, None


class Downloads:
    def __init__(self, win):
        self.win = win
        self.items = []
        self.listeners = set()
        self.pool = background_pool(2, 'download')

    def start(self, video, audio=False, fmt=None, label=None):
        fmt = fmt or (AUDIO_FORMAT if audio else video_format(self.win.config['quality'], playback=False))
        d = Download(video, audio, fmt, label or ('Audio' if audio else f'{self.win.config["quality"]}p'))
        self.items.insert(0, d)
        self._changed(d)
        self.pool.submit(self._run, d)
        return d

    def _changed(self, d):
        for cb in list(self.listeners):
            cb(d)

    def _run(self, d):
        """Download with the yt-dlp program in its own process, so its parsing never competes
        with the video for Python's GIL. The thread running this is low priority and confined
        to one CPU thread; the process (and ffmpeg for merging) inherit that."""
        if d.cancelled:
            return
        folder = self.win.config['download_dir']
        os.makedirs(folder, exist_ok=True)
        cmd = [YTDLP, '--extractor-args', YT_CLIENTS_ARG,
               '--newline', '--progress', '--no-colors', '--no-warnings',
               '-f', d.fmt, '-o', os.path.join(folder, '%(title).120B [%(id)s].%(ext)s'), '--socket-timeout', '20',
               '--progress-template', 'download:TLP %(progress.downloaded_bytes)s|%(progress.total_bytes)s|'
                                      '%(progress.total_bytes_estimate)s|%(progress.speed)s|%(progress.eta)s|'
                                      '%(info.vcodec)s',
               '--print', 'after_move:TLF %(filepath)s']
        if not d.audio:
            cmd += ['--merge-output-format', 'mp4']
        if IPV4_ONLY:
            cmd.append('--force-ipv4')
        cmd.append(d.video.url)
        d.status, d.detail = 'Starting', 'Finding streams…'
        idle(self._changed, d)

        def num(x):
            try:
                return float(x)
            except (TypeError, ValueError):
                return None

        error, last = '', 0.0
        try:
            d.proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                      stderr=subprocess.STDOUT, text=True, bufsize=1)
            for line in d.proc.stdout:
                line = line.strip()
                if line.startswith('TLF '):
                    d.path = line[4:]
                elif line.startswith('TLP '):
                    done, total, estimate, speed, eta, vcodec = (line[4:].split('|') + [''] * 6)[:6]
                    done, total, speed, eta = num(done) or 0, num(total) or num(estimate), num(speed), num(eta)
                    frac = done / total if total else 0
                    is_video = vcodec not in ('none', 'NA', '')
                    d.progress = frac if d.audio else (frac * 0.9 if is_video else 0.9 + frac * 0.1)
                    d.status = 'Downloading'
                    d.detail = (f'{"Video" if is_video else "Audio"} · {fmt_size(done)} of {fmt_size(total)}'
                                + (f' · {fmt_size(speed)}/s' if speed else '') + (f' · {int(eta)} s left' if eta else ''))
                    if time.monotonic() - last > 0.4:
                        last = time.monotonic()
                        idle(self._changed, d)
                elif line.startswith('ERROR:'):
                    error = clean_error(line)
            d.proc.wait()
        except OSError as e:
            error = str(e)
        if d.cancelled:
            d.status, d.detail = 'Cancelled', 'Cancelled'
        elif d.proc and d.proc.returncode == 0 and d.path and os.path.exists(d.path):
            d.status, d.progress = 'Done', 1.0
            d.detail = f'{d.label} · {fmt_size(os.path.getsize(d.path))}'
            self.win.lib.add_download(d.path, d.video, d.audio)
        else:
            d.status, d.detail = 'Failed', error or 'yt-dlp could not download this video'
        idle(self._changed, d)

# ---------------------------------------------------------------- SponsorBlock
SPONSORBLOCK = 'https://sponsor.ajay.app/api/skipSegments/'
SB_CATEGORIES = {'sponsor': 'sponsor', 'selfpromo': 'self-promotion', 'interaction': 'subscribe reminder'}


def sponsor_segments(video_id):
    """Parts of a YouTube video that SponsorBlock users marked as sponsor, self-promotion or
    subscribe reminder: [(start, end, category)]. Asked by the first 4 characters of the ID's
    SHA-256 (with hundreds of other videos), so the server can't tell which video plays."""
    prefix = hashlib.sha256(video_id.encode()).hexdigest()[:4]
    query = urllib.parse.urlencode({'categories': json.dumps(list(SB_CATEGORIES)),
                                    'actionTypes': json.dumps(['skip'])})
    try:
        data = json.loads(http_get(f'{SPONSORBLOCK}{prefix}?{query}', timeout=10))
    except urllib.error.HTTPError as e:
        if e.code == 404:  # nothing marked for any video with this prefix
            return []
        raise
    for item in data:
        if item.get('videoID') == video_id:
            return sorted((float(seg['segment'][0]), float(seg['segment'][1]), seg.get('category'))
                          for seg in item.get('segments') or []
                          if len(seg.get('segment') or []) == 2 and seg.get('category') in SB_CATEGORIES)
    return []

# ---------------------------------------------------------------- widgets


def logo_image(size):
    """The app mark at `size` px (drawn at twice that, so it stays sharp on HiDPI screens)."""
    img = Gtk.Image(pixel_size=size)
    try:
        gi.require_version('GdkPixbuf', '2.0')
        from gi.repository import GdkPixbuf
        stream = Gio.MemoryInputStream.new_from_bytes(GLib.Bytes.new(LOGO_SVG.encode()))
        pb = GdkPixbuf.Pixbuf.new_from_stream_at_scale(stream, size * 2, size * 2, True, None)
        ok, png = pb.save_to_bufferv('png', [], [])
        img.set_from_paintable(Gdk.Texture.new_from_bytes(GLib.Bytes.new(png)))
    except (GLib.Error, ValueError):
        img.set_from_icon_name(APP_ID)  # no SVG loader: the installed icon
    return img


class Thumb(Gtk.Picture):
    """Fixed-size thumbnail, so cards never resize when images arrive. A fluid one keeps the
    w:h shape but takes the width it is given (the YouTube-style grid)."""

    def __init__(self, w, h, fluid=False):
        super().__init__(content_fit=Gtk.ContentFit.COVER, can_shrink=True)
        self._w, self._h, self._fluid = w, h, fluid
        self.add_css_class('tl-thumb')

    def do_get_request_mode(self):
        return Gtk.SizeRequestMode.HEIGHT_FOR_WIDTH if self._fluid else Gtk.SizeRequestMode.CONSTANT_SIZE

    def do_measure(self, orientation, for_size):
        if not self._fluid:
            size = self._w if orientation == Gtk.Orientation.HORIZONTAL else self._h
            return size, size, -1, -1
        if orientation == Gtk.Orientation.HORIZONTAL:
            return self._w // 2, self._w, -1, -1
        size = round((for_size if for_size > 0 else self._w) * self._h / self._w)
        return size, size, -1, -1


class Card(Gtk.FlowBoxChild):
    def __init__(self, video, win, page=None, vertical=False, fluid=False, row=False):
        live = video.kind == 'live'
        # fluid: 16:9 cards as wide as the grid's column (channel logos and Shorts keep their size)
        self.fluid = fluid and not (live or vertical or row)
        super().__init__(halign=Gtk.Align.FILL if self.fluid or row else Gtk.Align.CENTER, valign=Gtk.Align.START)
        self.video, self.win, self.page, self.vertical = video, win, page, vertical
        self.texture = None
        self._hover = False
        self.add_css_class('tl-card')
        self.set_tooltip_text(video.title)

        self.thumb = Thumb(*((LIVE_W, LIVE_H) if live else (SHORT_W, SHORT_H) if vertical else
                             (ROW_W, ROW_H) if row else (THUMB_W, THUMB_H)), fluid=self.fluid or row)
        if video.kind in ('channel', 'live'):
            self.thumb.set_content_fit(Gtk.ContentFit.CONTAIN)
        if live:
            self.thumb.add_css_class('tl-logo-tile')
        overlay = Gtk.Overlay(child=self.thumb, overflow=Gtk.Overflow.HIDDEN)
        overlay.add_css_class('tl-thumb')
        if video.kind == 'video':
            badge_text = 'LIVE' if video.live else fmt_duration(video.duration)
        elif video.kind in ('playlist', 'localpl'):
            badge_text = f'{video.count} videos' if video.count else 'Playlist'
        else:
            badge_text = ''
        if badge_text:
            badge = Gtk.Label(label=badge_text, halign=Gtk.Align.END, valign=Gtk.Align.END,
                              margin_end=6, margin_bottom=6)
            badge.add_css_class('tl-badge')
            if video.live:
                badge.add_css_class('live')
            overlay.add_overlay(badge)
        self.more = Gtk.MenuButton(icon_name='view-more-symbolic', halign=Gtk.Align.END, valign=Gtk.Align.START,
                                   margin_top=6, margin_end=6, opacity=0, tooltip_text='More')
        self.more.add_css_class('osd')
        self.more.add_css_class('circular')
        self.more.set_create_popup_func(lambda b: b.set_menu_model(self._menu()))
        self.more.connect('notify::active', lambda b, _p: b.set_opacity(1 if b.get_active() or self._hover else 0))
        overlay.add_overlay(self.more)

        title = Gtk.Label(label=video.title, xalign=0, wrap=True, wrap_mode=Pango.WrapMode.WORD_CHAR,
                          lines=2, ellipsize=Pango.EllipsizeMode.END, max_width_chars=1, hexpand=True)
        title.add_css_class('tl-title')
        meta = Gtk.Label(label=video.meta(), xalign=0, ellipsize=Pango.EllipsizeMode.END,
                         max_width_chars=1, hexpand=True)
        meta.add_css_class('dim-label')
        meta.add_css_class('caption')
        if row:  # thumbnail on the left, the text beside it (Up next): a big title, channel, views · age
            title.set_lines(3)
            channel, _, stats_text = video.meta().partition(' · ')
            meta.set_label(channel)
            meta.remove_css_class('caption')
            stats = Gtk.Label(label=stats_text, xalign=0, ellipsize=Pango.EllipsizeMode.END, max_width_chars=1,
                              hexpand=True, visible=bool(stats_text), css_classes=['dim-label'])
            text = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=2, valign=Gtk.Align.START)
            text.append(title)
            meta.set_margin_top(4)
            text.append(meta)
            text.append(stats)
            box = Gtk.Grid(column_homogeneous=True, column_spacing=10)  # thumbnail 7/12, text 5/12
            box.attach(overlay, 0, 0, 7, 1)
            box.attach(text, 7, 0, 5, 1)
            self.add_css_class('tl-row')
        else:
            box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=6)
            box.append(overlay)
            box.append(title)
            box.append(meta)
        self.set_child(box)
        self.insert_action_group('card', self._actions())

        click = Gtk.GestureClick(button=0)
        click.connect('pressed', self._on_click)
        self.add_controller(click)
        motion = Gtk.EventControllerMotion()
        motion.connect('enter', self._on_enter)
        motion.connect('leave', self._on_leave)
        self.add_controller(motion)

    def _actions(self):
        g, v, w = Gio.SimpleActionGroup(), self.video, self.win
        for name, cb in (
                ('open', lambda: w.activate_card(self)), ('play', lambda: w.play(v)),
                ('queue', lambda: w.play(v, queue=True)), ('audio', lambda: w.play(v, audio=True)),
                ('mpv', lambda: w.play_external(v)), ('download', lambda: w.download(v)),
                ('download-audio', lambda: w.download(v, audio=True)),
                ('like', lambda: w.toggle_list('liked', v, self)), ('later', lambda: w.toggle_list('later', v, self)),
                ('playlist', lambda: w.save_to_playlist(v)), ('channel', lambda: w.open_channel(v)),
                ('subscribe', lambda: w.toggle_subscription(v)), ('hide', lambda: w.hide_video(v, self)),
                ('hide-channel', lambda: w.hide_channel(v)), ('copy', lambda: w.copy_link(v)),
                ('remove', lambda: w.remove_from_page(self)), ('delete-playlist', lambda: w.delete_playlist(v, self)),
                ('fav', lambda: w.toggle_channel_fav(v, self))):
            action = Gio.SimpleAction.new(name, None)
            action.connect('activate', lambda _a, _p, cb=cb: cb())
            g.add_action(action)
        return g

    def _menu(self):
        v, lib = self.video, self.win.lib
        m = Gio.Menu()

        def section(*items):
            s = Gio.Menu()
            for label, action in items:
                if label:
                    s.append(label, action)
            if s.get_n_items():
                m.append_section(None, s)

        ch_name = v.channel or 'this channel'
        subscribed = lib.is_subscribed(v.channel_id)
        if v.kind == 'video':
            section(('Play', 'card.play'), ('Add to queue', 'card.queue'), ('Play audio only', 'card.audio'),
                    ('Open in separate mpv window', 'card.mpv'))
            section(('Unlike' if lib.has('liked', v.id) else 'Like', 'card.like'),
                    ('Remove from Watch later' if lib.has('later', v.id) else 'Save to Watch later', 'card.later'),
                    ('Save to playlist…', 'card.playlist'))
            section(('Download video', 'card.download'), ('Download audio', 'card.download-audio'))
            has_ch = bool(v.channel_link)
            section((f'More from {ch_name}' if has_ch else None, 'card.channel'),
                    ((f'Unsubscribe from {ch_name}' if subscribed else f'Subscribe to {ch_name}') if has_ch else None,
                     'card.subscribe'),
                    ('Not interested', 'card.hide'),
                    ("Don't recommend this channel" if has_ch else None, 'card.hide-channel'))
        elif v.kind == 'channel':
            section(('Open channel', 'card.open'), ('Unsubscribe' if subscribed else 'Subscribe', 'card.subscribe'))
        elif v.kind == 'live':
            on_fav_page = self.page is not None and self.page.list_name == 'tvfav'
            section(('Play', 'card.open'),
                    ('Add to favourites' if not lib.has('tvfav', v.id) else
                     None if on_fav_page else 'Remove from favourites', 'card.fav'))
        else:
            section(('Open', 'card.open'))
        list_label = self.page.list_label if self.page and self.page.list_name else None
        section(('Copy stream link' if v.kind == 'live' else 'Copy link' if v.kind != 'localpl' else None, 'card.copy'),
                (f'Remove from {list_label}' if list_label else None, 'card.remove'),
                ('Delete playlist' if v.kind == 'localpl' else None, 'card.delete-playlist'))
        return m

    def _on_click(self, gesture, n_press, x, y):
        button = gesture.get_current_button()
        if button == Gdk.BUTTON_MIDDLE and self.video.kind == 'video':
            self.win.play(self.video, queue=True)
        elif button == Gdk.BUTTON_SECONDARY:
            pop = Gtk.PopoverMenu.new_from_model(self._menu())
            pop.set_parent(self)
            pop.set_has_arrow(False)
            rect = Gdk.Rectangle()
            rect.x, rect.y, rect.width, rect.height = int(x), int(y), 1, 1
            pop.set_pointing_to(rect)
            pop.connect('closed', lambda p: idle(p.unparent))
            pop.popup()

    def _on_enter(self, *_):
        self._hover = True
        self.more.set_opacity(1)
        if self.video.kind == 'video':
            self.win.hover_start(self)

    def _on_leave(self, *_):
        self._hover = False
        if not self.more.get_active():
            self.more.set_opacity(0)
        self.win.hover_end(self)

    def set_texture(self, texture):
        self.texture = texture
        if not (self.win.preview and self.win.preview[0] is self):
            self.thumb.set_paintable(texture)


PAGES_DIR = os.path.join(GLib.get_user_cache_dir(), 'smedio', 'pages')        # loaded pages (For you, Shorts…)
CHANNELS_DIR = os.path.join(GLib.get_user_cache_dir(), 'smedio', 'channels')  # IPTV channel lists


def _cache_path(folder, key):
    return os.path.join(folder, re.sub(r'[^\w.-]', '_', key)[:60] + '-' + hashlib.md5(key.encode()).hexdigest()[:8] + '.json')


def cache_read(folder, key):
    try:
        with open(_cache_path(folder, key)) as f:
            return json.load(f)
    except (OSError, ValueError):
        return None


def cache_write(folder, key, data):
    try:
        os.makedirs(folder, exist_ok=True)
        path = _cache_path(folder, key)
        with open(path + '.tmp', 'w') as f:
            json.dump(data, f)
        os.replace(path + '.tmp', path)
    except OSError:
        pass


def cache_drop(folder, key):
    try:
        os.unlink(_cache_path(folder, key))
    except OSError:
        pass


class GridFlow(Gtk.FlowBox):
    """The card grid. With fluid cards (YouTube's 16:9 ones) it shows `columns` cards a row,
    stretched to the row's width, like YouTube; otherwise as many fixed-size cards as fit."""
    columns = GObject.Property(type=int, default=4)

    def __init__(self, **kw):
        super().__init__(homogeneous=True, selection_mode=Gtk.SelectionMode.NONE,
                         activate_on_single_click=True, **kw)
        self.fluid = False
        self.connect('notify::columns', lambda *_: self.set_fluid(self.fluid))
        self.set_fluid(False)

    def set_fluid(self, fluid):
        self.fluid = fluid
        n = self.props.columns
        self.set_min_children_per_line(n if fluid else 1)
        self.set_max_children_per_line(n if fluid else 14)


class GridPage(Adw.NavigationPage):
    """A titled, scrollable grid of cards filled by `fetch` in the background. With `cache_key`
    (a string, or a function for pages with filters) the result is saved on disk and shown from
    there next time — on later starts too — until ↻ is pressed; `keep` just shows how old it is."""

    def __init__(self, win, title, fetch, *, more=None, vertical=False, list_name=None, list_label=None,
                 actions=(), empty=None, cache_key=None, keep=False):
        super().__init__(title=title)
        self.win, self.fetch, self.more_fn, self.vertical = win, fetch, more, vertical
        self.cache_key, self.keep = cache_key, keep or cache_key is not None
        self.updated = self.data_time = None
        self.forcing = False
        self.play_queue = None  # set on lists that keep playing (Liked, Watch later, playlists)
        self.list_name, self.list_label = list_name, list_label or title
        self.empty = empty or ('Nothing here yet', '', None)
        self.cards, self.ids, self.gen = [], set(), 0
        self.can_more, self.loading_more = False, False
        self._preload_src = 0

        heading = Gtk.Box(spacing=6, margin_start=24, margin_end=18, margin_top=10, margin_bottom=4)
        self.title_label = Gtk.Label(label=title, xalign=0, hexpand=True, ellipsize=Pango.EllipsizeMode.END)
        self.title_label.add_css_class('title-2')
        heading.append(self.title_label)
        for w in actions:
            heading.append(w)
        self.age_label = Gtk.Label(visible=False)
        self.age_label.add_css_class('dim-label')
        self.age_label.add_css_class('caption')
        heading.append(self.age_label)
        refresh = Gtk.Button(icon_name='view-refresh-symbolic', tooltip_text='Refresh: load the latest')
        refresh.add_css_class('flat')
        refresh.connect('clicked', lambda *_: self.reload(force=True))
        heading.append(refresh)
        self.connect('showing', lambda *_: self._show_age())

        self.flow = GridFlow(column_spacing=6, row_spacing=10, valign=Gtk.Align.START,
                             margin_start=12, margin_end=12, margin_top=4, margin_bottom=12)
        self.flow.connect('child-activated', lambda _f, card: win.activate_card(card))
        self.more_spinner = Adw.Spinner(width_request=32, height_request=32, margin_bottom=24, visible=False)
        self.content = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)
        self.content.append(self.flow)
        self.content.append(self.more_spinner)
        self.scroller = Gtk.ScrolledWindow(child=self.content, hscrollbar_policy=Gtk.PolicyType.NEVER, vexpand=True)
        self.scroller.connect('edge-reached', self._on_edge)
        self.scroller.get_vadjustment().connect('value-changed', lambda *_: self._schedule_preload())

        self.status = Adw.StatusPage(vexpand=True)
        loading = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, valign=Gtk.Align.CENTER, vexpand=True)
        loading.append(Adw.Spinner(width_request=48, height_request=48))
        self.stack = Gtk.Stack(transition_type=Gtk.StackTransitionType.CROSSFADE, transition_duration=120)
        self.stack.add_named(loading, 'loading')
        self.stack.add_named(self.scroller, 'results')
        self.stack.add_named(self.status, 'status')
        outer = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)
        outer.append(heading)
        outer.append(self.stack)
        bin_ = Adw.BreakpointBin(child=outer, width_request=300, height_request=200)
        for lo, hi, n in GRID_COLUMNS:
            cond = ' and '.join(c for c in (lo and f'min-width: {lo}px', hi and f'max-width: {hi}px') if c)
            bp = Adw.Breakpoint.new(Adw.BreakpointCondition.parse(cond))
            bp.add_setter(self.flow, 'columns', n)
            bin_.add_breakpoint(bp)
        self.set_child(bin_)
        self.reload()

    def reload(self, force=False):
        self.gen += 1
        gen = self.gen
        self.forcing = force
        key = self.cache_key() if callable(self.cache_key) else self.cache_key
        if key and not force:
            hit = cache_read(PAGES_DIR, key)
            try:
                items = [Video.from_dict(d) for d in hit['items']] if hit else None
            except (KeyError, TypeError):
                items = None
            if items:
                self._loaded(gen, items, None, hit.get('saved'))
                return
        self.stack.set_visible_child_name('loading')

        def work():
            self.data_time = None
            try:
                items = self.fetch()
                if key and items:
                    cache_write(PAGES_DIR, key, {'saved': time.time(), 'items': [v.to_dict() for v in items]})
                idle(self._loaded, gen, items, None, self.data_time or time.time())
            except Exception as e:  # noqa: BLE001 - surface any yt-dlp/network failure
                idle(self._loaded, gen, None, clean_error(e))

        self.win.search_pool.submit(work)

    def _show_age(self):
        if self.keep and self.updated:
            self.age_label.set_label(f'Updated {fmt_age(self.updated)}')
            self.age_label.set_visible(True)

    def _loaded(self, gen, items, error, updated=None):
        if gen != self.gen:
            return
        if error is None:
            self.updated = updated
            self._show_age()
        if error is not None:
            self._show_status('dialog-warning-symbolic', 'Couldn’t load this page',
                              GLib.markup_escape_text(error) + '\n\n' + self.win.error_hint(), None)
            return
        self.can_more = bool(self.more_fn) and len(items) >= PAGE
        self.flow.remove_all()
        self.cards, self.ids = [], set()
        self._append(items)
        if not self.cards:
            title, desc, extra = self.empty
            self._show_status('folder-open-symbolic', title, desc, extra)
            return
        self.scroller.get_vadjustment().set_value(0)
        self.stack.set_visible_child_name('results')
        self._schedule_preload(400)

    def _show_status(self, icon, title, desc, extra):
        self.status.set_icon_name(icon)
        self.status.set_title(title)
        self.status.set_description(desc)
        self.status.set_child(extra() if extra else None)
        self.stack.set_visible_child_name('status')

    def _append(self, items):
        hidden_v, hidden_c = self.win.lib.hidden()
        for video in items:
            if video.id in self.ids or video.id in hidden_v or (video.channel_id and video.channel_id in hidden_c):
                continue
            self.ids.add(video.id)
            card = Card(video, self.win, self, self.vertical, fluid=True)
            self.cards.append(card)
            self.flow.append(card)
            self.win.load_thumb(card)
        self.flow.set_fluid(bool(self.cards) and all(c.fluid for c in self.cards))

    def remove_card(self, card):
        if card in self.cards:
            self.cards.remove(card)
            self.ids.discard(card.video.id)
            self.flow.remove(card)
        if not self.cards:
            title, desc, extra = self.empty
            self._show_status('folder-open-symbolic', title, desc, extra)

    def _on_edge(self, _sw, pos):
        if pos != Gtk.PositionType.BOTTOM or not self.can_more or self.loading_more:
            return
        self.loading_more = True
        self.more_spinner.set_visible(True)
        gen, count = self.gen, len(self.cards) + PAGE

        def work():
            try:
                result = self.more_fn(count)
            except Exception as e:  # noqa: BLE001
                result = clean_error(e)
            idle(done, result)

        def done(result):
            self.loading_more = False
            self.more_spinner.set_visible(False)
            if gen != self.gen:
                return
            if isinstance(result, str):
                self.win.toast(f'Couldn’t load more: {result}')
                return
            before = len(self.cards)
            self._append(result)
            self.can_more = len(self.cards) > before
            self._schedule_preload()

        self.win.search_pool.submit(work)

    def _schedule_preload(self, delay=300):
        if self._preload_src:
            GLib.source_remove(self._preload_src)
        self._preload_src = GLib.timeout_add(delay, self._preload)

    def _preload(self):
        self._preload_src = 0
        adj = self.scroller.get_vadjustment()
        top, bottom = adj.get_value() - 100, adj.get_value() + adj.get_page_size() + 300
        visible = []
        for card in self.cards:
            ok, rect = card.compute_bounds(self.content)
            if ok and rect.get_y() + rect.get_height() >= top and rect.get_y() <= bottom:
                visible.append(card)
        self.win.preload_previews(visible or self.cards[:12])
        return GLib.SOURCE_REMOVE


def player_button(icon, tooltip, cb=None, toggle=False):
    b = (Gtk.ToggleButton if toggle else Gtk.Button)(icon_name=icon, tooltip_text=tooltip,
                                                      valign=Gtk.Align.CENTER, focusable=False)
    b.add_css_class('tl-pbtn')
    if cb:
        b.connect('toggled' if toggle else 'clicked', lambda *_: cb())
    return b


class ControlBar(Gtk.Box):
    """2012-style player bar: red progress with a white knob, then play, volume, time,
    quality gear, Watch later clock, download, the wordmark and fullscreen."""

    def __init__(self, page):
        super().__init__(orientation=Gtk.Orientation.VERTICAL, valign=Gtk.Align.END)
        self.page = page
        self.add_css_class('tl-player-bar')
        self._dur = 0.0

        self.progress = Gtk.Scale(orientation=Gtk.Orientation.HORIZONTAL, draw_value=False, hexpand=True,
                                  show_fill_level=True, restrict_to_fill_level=False, focusable=False)
        self.progress.set_range(0, 1)
        self.progress.add_css_class('tl-progress')
        self.progress.connect('change-value', lambda _s, _scroll, value: page.seek_to(value) or False)
        hover = Gtk.EventControllerMotion()
        hover.connect('motion', self._progress_hover)
        self.progress.add_controller(hover)
        self._chapters = []
        self.chapter_gaps = Gtk.DrawingArea(can_target=False)  # YouTube-style gaps where chapters begin
        self.chapter_gaps.set_draw_func(self._draw_chapter_gaps)
        bar = Gtk.Overlay(child=self.progress)
        bar.add_overlay(self.chapter_gaps)
        self.append(bar)

        row = Gtk.Box(spacing=2)
        row.add_css_class('tl-controls')
        self.play_btn = player_button('media-playback-pause-symbolic', 'Pause (k)', page.toggle_pause)
        self.next_btn = player_button('media-skip-forward-symbolic', 'Next (n)', page.next)
        self.next_btn.set_visible(False)
        self.vol_btn = player_button('audio-volume-high-symbolic', 'Mute (m)', page.toggle_mute)
        self.vol = Gtk.Scale(orientation=Gtk.Orientation.HORIZONTAL, draw_value=False, width_request=72,
                             valign=Gtk.Align.CENTER, focusable=False)
        self.vol.set_range(0, 100)
        self.vol.add_css_class('tl-volume')
        self.vol.connect('change-value', lambda _s, _scroll, value: page.set_volume(value) or False)
        self.time = Gtk.Label(label='0:00')
        self.time.add_css_class('tl-time')
        for w in (self.play_btn, self.next_btn, self.vol_btn, self.vol, self.time):
            row.append(w)
        row.append(Gtk.Box(hexpand=True))

        self.gear = Gtk.MenuButton(icon_name='emblem-system-symbolic', tooltip_text='Quality & speed',
                                   valign=Gtk.Align.CENTER, focusable=False, popover=Gtk.Popover())
        self.gear.get_popover().connect('show', lambda p: p.set_child(page.quality_menu()))
        self.later = player_button('alarm-symbolic', 'Watch later', toggle=True)
        self.later_handler = self.later.connect('toggled', lambda b: page.set_later(b.get_active()))
        self.dl = Gtk.MenuButton(icon_name='folder-download-symbolic', tooltip_text='Download',
                                 valign=Gtk.Align.CENTER, focusable=False, popover=Gtk.Popover())
        self.dl.get_popover().connect('show', lambda p: p.set_child(page.download_menu()))
        for b in (self.gear, self.dl):
            b.add_css_class('tl-pbtn')
        brand = Gtk.Box(spacing=6, valign=Gtk.Align.CENTER)
        brand.append(logo_image(18))
        brand.append(Gtk.Label(label='Smedio'))
        brand.add_css_class('tl-brand')
        self.fs_btn = player_button('view-fullscreen-symbolic', 'Fullscreen (f)', page.toggle_fullscreen)
        for w in (self.gear, self.later, self.dl, brand, self.fs_btn):
            row.append(w)
        self.append(row)

    def set_chapters(self, chapters):
        """YouTube chapters: a gap in the bar where each begins, the name in the time label."""
        self._chapters = chapters
        self.chapter_gaps.queue_draw()

    def _draw_chapter_gaps(self, _area, cr, w, h):
        if not self._dur or len(self._chapters) < 2:
            return
        cr.set_source_rgba(0, 0, 0, 0.85)
        knob = 2 + self.progress.get_value() / self._dur * (w - 4)
        for c in self._chapters[1:]:
            x = 2 + c['start'] / self._dur * (w - 4)  # the bar's trough is inset 2 px each side
            if abs(x - knob) > 8:  # not across the knob
                cr.rectangle(round(x) - 1, h / 2 - 5, 2, 10)
        cr.fill()

    def chapter_at(self, t):
        title = None
        for c in self._chapters:
            if c['start'] > t:
                break
            title = c['title']
        return title

    def _progress_hover(self, _ctl, x, _y):
        w = self.progress.get_width()
        if self._dur and w:
            t = max(0.0, min(1.0, x / w)) * self._dur
            chapter = self.chapter_at(t)
            self.progress.set_tooltip_text((fmt_duration(t) or '0:00') + (f' · {chapter}' if chapter else ''))

    def update(self, name, value, engine):
        if name == 'time-pos' and value is not None and self.page.video is not None and self.page.video.kind == 'live':
            self.time.set_label('● LIVE')
        elif name == 'time-pos' and value is not None:
            if self._dur:
                self.progress.set_value(value)
            chapter = self.chapter_at(value)
            if len(self._chapters) > 1:
                self.chapter_gaps.queue_draw()  # keep the gaps off the knob
            self.time.set_label((f'{fmt_duration(value) or "0:00"} / {fmt_duration(self._dur) or "0:00"}'
                                 if self._dur else fmt_duration(value) or '0:00') + (f'  ·  {chapter}' if chapter else ''))
        elif name == 'duration':
            self._dur = value or 0.0
            self.progress.set_range(0, max(self._dur, 1))
            self.chapter_gaps.queue_draw()
        elif name == 'demuxer-cache-time' and value is not None:
            self.progress.set_fill_level(value)
        elif name == 'pause':
            self.play_btn.set_icon_name('media-playback-start-symbolic' if value else 'media-playback-pause-symbolic')
            self.play_btn.set_tooltip_text('Play (k)' if value else 'Pause (k)')
        elif name in ('volume', 'mute'):
            vol, muted = engine.m.volume or 0, engine.m.mute
            self.vol.set_value(vol)
            icon = 'audio-volume-muted-symbolic' if muted or vol == 0 else \
                'audio-volume-low-symbolic' if vol < 34 else \
                'audio-volume-medium-symbolic' if vol < 67 else 'audio-volume-high-symbolic'
            self.vol_btn.set_icon_name(icon)
        elif name in ('playlist-pos', 'playlist-count'):
            pos, count = engine.m.playlist_pos, engine.m.playlist_count
            self.next_btn.set_visible((pos is not None and count is not None and pos + 1 < count)
                                      or self.page.can_zap())


class StatsPanel(Gtk.Box):
    """YouTube-style "Stats for nerds" for the in-app player, refreshed twice a second."""

    ROWS = (('Video ID', 'id'), ('Viewport / Frames', 'frames'), ('Current / Optimal Res', 'res'),
            ('Volume', 'vol'), ('Codecs', 'codecs'), ('Decoding', 'hw'), ('Connection Speed', 'speed'),
            ('Buffer Health', 'buffer'), ('A/V sync', 'sync'), ('Display', 'display'),
            ('App CPU', 'cpu'), ('Network', 'net'), ('Date', 'date'))

    def __init__(self, page):
        super().__init__(orientation=Gtk.Orientation.VERTICAL, spacing=4, halign=Gtk.Align.START,
                         valign=Gtk.Align.START, margin_top=12, margin_start=12, visible=False)
        self.page, self.src = page, 0
        self._cpu = None
        self._busy = False
        self.add_css_class('tl-stats')
        head = Gtk.Box(spacing=8)
        title = Gtk.Label(label='Stats for nerds', xalign=0, hexpand=True)
        title.add_css_class('tl-stats-title')
        close = Gtk.Button(label='[X]', tooltip_text='Close (I)')
        close.add_css_class('tl-stats-btn')
        close.connect('clicked', lambda *_: self.stop())
        head.append(title)
        head.append(close)
        self.append(head)
        grid = Gtk.Grid(column_spacing=10, row_spacing=1)
        self.values, self.bars = {}, {}
        for i, (name, key) in enumerate(self.ROWS):
            k = Gtk.Label(label=name, xalign=1)
            k.add_css_class('tl-stats-key')
            v = Gtk.Label(xalign=0, ellipsize=Pango.EllipsizeMode.END, max_width_chars=58)
            v.add_css_class('tl-stats-val')
            grid.attach(k, 0, i, 1, 1)
            if key in ('speed', 'buffer'):
                bar = Gtk.LevelBar(min_value=0, max_value=1, width_request=110, valign=Gtk.Align.CENTER)
                bar.add_css_class('tl-stats-bar')
                bar.remove_offset_value(Gtk.LEVEL_BAR_OFFSET_LOW)
                bar.remove_offset_value(Gtk.LEVEL_BAR_OFFSET_HIGH)
                bar.remove_offset_value(Gtk.LEVEL_BAR_OFFSET_FULL)
                row = Gtk.Box(spacing=8)
                row.append(bar)
                row.append(v)
                grid.attach(row, 1, i, 1, 1)
                self.bars[key] = bar
            else:
                grid.attach(v, 1, i, 1, 1)
            self.values[key] = v
        self.append(grid)
        self.mpv_btn = Gtk.ToggleButton(label='mpv frame-timing overlay', halign=Gtk.Align.START,
                                        tooltip_text='mpv’s own detailed stats, drawn on the video')
        self.mpv_btn.add_css_class('tl-stats-btn')
        self.mpv_btn.connect('toggled', lambda b: self._mpv_overlay(b.get_active()))
        self.append(self.mpv_btn)

    def _mpv_overlay(self, on):
        try:
            self.page.engine.m.command('script-binding', 'stats/display-stats-toggle')
        except Exception:  # noqa: BLE001
            self.page.win.toast('mpv’s stats overlay is not available')

    def toggle(self):
        if self.src:
            self.stop()
        else:
            self.start()

    def start(self):
        self.set_visible(True)
        self._cpu = None
        self.update()
        if not self.src:
            self.src = GLib.timeout_add(500, self._tick)

    def stop(self):
        if self.src:
            GLib.source_remove(self.src)
            self.src = 0
        if self.mpv_btn.get_active():
            self.mpv_btn.set_active(False)
        self.set_visible(False)

    def _tick(self):
        self.update()
        return GLib.SOURCE_CONTINUE  # keeps refreshing until stop() removes the timer

    PROPS = ('video-params', 'container-fps', 'estimated-vf-fps', 'frame-drop-count', 'decoder-frame-drop-count',
             'estimated-frame-number', 'demuxer-cache-state', 'cache-speed', 'demuxer-cache-duration',
             'hwdec-current', 'audio-params', 'avsync', 'media-title', 'volume', 'mute', 'speed', 'video-format',
             'audio-codec-name', 'current-vo')

    def update(self):
        # Some of these (display-fps, ...) ask the video renderer, which runs on this (GTK) thread;
        # reading them here would deadlock, so collect on a worker and draw the result here.
        if self._busy:
            return
        self._busy = True
        m = self.page.engine.m

        def collect():
            data = {}
            for name in self.PROPS:
                try:
                    data[name] = getattr(m, name.replace('-', '_'))  # live property (m['x'] reads options)
                except Exception:  # noqa: BLE001 - property not available right now
                    data[name] = None
            idle(self._apply, data)

        threading.Thread(target=collect, daemon=True).start()

    def _apply(self, data):
        self._busy = False
        if not self.get_visible():
            return
        page = self.page

        def get(name, default=None):
            value = data.get(name)
            return default if value is None else value

        stream, video = page.stream or {}, page.video
        vp = get('video-params', {}) or {}
        w, h = vp.get('w'), vp.get('h')
        fps = get('container-fps') or get('estimated-vf-fps')
        scale = page.area.get_scale_factor()
        vo_drops, dec_drops = get('frame-drop-count', 0), get('decoder-frame-drop-count', 0)
        frames = get('estimated-frame-number', 0)
        cache = get('demuxer-cache-state', {}) or {}
        speed = get('cache-speed', 0)
        buffered = get('demuxer-cache-duration', 0.0)
        hw = get('hwdec-current', 'no')
        hw_text = {'vaapi': 'vaapi — GPU decode, zero-copy',
                   'vaapi-copy': 'vaapi-copy — GPU decode, frames copied back',
                   'v4l2m2m-copy': 'v4l2m2m-copy — hardware decoder (V4L2), frames copied back'}.get(
            hw, 'software (CPU) — no GPU decoding!' if hw in ('no', '') else hw)
        now_t, cpu_t = time.monotonic(), sum(os.times()[:2])
        cpu = ''
        if self._cpu:
            dt = now_t - self._cpu[0]
            if dt > 0:
                cpu = f'{(cpu_t - self._cpu[1]) / dt * 100:.0f}% of one core (whole app)'
        self._cpu = (now_t, cpu_t)
        audio = get('audio-params', {}) or {}
        sync = get('avsync')
        values = {
            'id': f'{video.id if video else "—"}  ·  {get("media-title", "")}',
            'frames': f'{page.area.get_width()}x{page.area.get_height()}*{scale:.2f} / '
                      f'{vo_drops + dec_drops} dropped of {frames}'
                      + (f'  (decoder {dec_drops}, display {vo_drops})' if vo_drops + dec_drops else ''),
            'res': (f'{w}x{h}@{fps:.0f}' if w and fps else f'{w}x{h}' if w else '—')
                   + f' / {page.win.config["quality"]}p chosen'
                   + (f', {max(v["height"] for v in stream["formats"]["video"])}p max (H.264)'
                      if stream.get('formats') and stream['formats']['video'] else ''),
            'vol': f'{get("volume", 0):.0f}%' + (' (muted)' if get('mute') else '')
                   + (f' · speed {get("speed", 1):g}×' if get('speed', 1) != 1 else ''),
            'codecs': f'{get("video-format", "?")} ({vp.get("pixelformat", "?")})'
                      + (f' itag {stream["video_itag"]}' if stream.get('video_itag') else '')
                      + f' / {get("audio-codec-name", "?")} {audio.get("samplerate", "")}Hz'
                      + (f' itag {stream["audio_itag"]}' if stream.get('audio_itag') else ''),
            'hw': hw_text,
            'speed': f'{speed * 8 / 1000:.0f} Kbps' if speed else 'idle (buffer full)',
            'buffer': f'{buffered:.2f} s',
            'sync': f'{sync * 1000:+.0f} ms' if isinstance(sync, (int, float)) else '—',
            'display': (f'{page.area.refresh_rate():.0f} Hz' if page.area.refresh_rate() else '— Hz')
                       + f' · {get("current-vo", "?")} renderer, GTK-paced',
            'cpu': cpu or 'measuring…',
            'net': ('IPv4 (IPv6 broken on this network)' if IPV4_ONLY else 'IPv4/IPv6')
                   + (f' · {fmt_size(cache.get("total-bytes"))} in buffer' if cache.get('total-bytes') else ''),
            'date': datetime.now().strftime('%a %b %d %Y %H:%M:%S'),
        }
        for key, text in values.items():
            self.values[key].set_label(text)
        self.values['hw'].remove_css_class('tl-stats-bad')
        if hw in ('no', ''):
            self.values['hw'].add_css_class('tl-stats-bad')
        self.bars['speed'].set_value(min(1.0, math.log10(1 + speed * 8 / 1000) / 4.5) if speed else 0)
        self.bars['buffer'].set_value(min(1.0, buffered / 60))


class WatchColumns(Gtk.Widget):
    """The player column and Up next beside it, fitted to the screen: Up next's thumbnails are as
    tall as lets about UPNEXT_ROWS rows show in the visible height, its column as wide as they
    need (at most UPNEXT_SHARE of the page), and the player takes the rest, at most PLAYER_VH of
    the visible height; the pair is centred. `below` (a breakpoint, on narrow pages) puts Up next
    under the details; fullscreen gives the player everything. Widths never depend on the height
    offered (GTK asked that, and long comments then pushed Up next off-screen)."""
    below = GObject.Property(type=bool, default=False)

    def __init__(self, page, body, side):
        super().__init__()
        self.page, self.body, self.side = page, body, side
        body.set_parent(self)
        side.set_parent(self)
        self._vh = 0
        self.connect('notify::below', lambda *_: self.queue_resize())

    def viewport_changed(self, height):
        if abs(height - self._vh) > 4:
            self._vh = height
            GLib.idle_add(lambda: self.queue_resize() and False)

    def _sizes(self, width):
        """(player column width, Up next width, left offset); Up next width 0 when hidden."""
        vh = self._vh or 800
        if self.page.is_fullscreen:
            return width, 0, 0
        player_max = round(vh * PLAYER_VH * 16 / 9)
        if not self.side.get_visible() or self.below:
            body = min(width, player_max)
            return body, (body if self.side.get_visible() else 0), (width - body) // 2
        thumb_h = vh / UPNEXT_ROWS - 22                       # row padding and spacing
        side = round(thumb_h * 16 / 9 * 12 / 7 + 18)          # the thumbnail is 7/12 of a row
        side = max(300, min(side, round(width * UPNEXT_SHARE)))
        body = max(1, min(width - WATCH_GAP - side, player_max))
        return body, side, max(0, (width - body - WATCH_GAP - side) // 2)

    def do_get_request_mode(self):
        return Gtk.SizeRequestMode.HEIGHT_FOR_WIDTH

    def do_measure(self, orientation, for_size):
        side_on = self.side.get_visible()
        if orientation == Gtk.Orientation.HORIZONTAL:
            bmin, bnat = self.body.measure(orientation, -1)[:2]
            if not side_on:
                return bmin, bnat, -1, -1
            smin = self.side.measure(orientation, -1)[0]
            if self.below:
                return max(bmin, smin), max(bnat, smin), -1, -1
            return bmin + WATCH_GAP + max(smin, 300), bnat + WATCH_GAP + 500, -1, -1
        body, side, _ = self._sizes(for_size if for_size > 0 else 1100)
        bmin, bnat = self.body.measure(orientation, body)[:2]
        if not side_on:
            return bmin, bnat, -1, -1
        smin, snat = self.side.measure(orientation, side)[:2]
        if self.below:
            return bmin + WATCH_GAP + smin, bnat + WATCH_GAP + snat, -1, -1
        top = self._top(side)
        return max(bmin + top, smin), max(bnat + top, snat), -1, -1

    def _top(self, side):
        """How far down the first Up next thumbnail starts (below its heading): the player column
        starts there too, so the two line up."""
        title = self.page.side_title
        return title.measure(Gtk.Orientation.VERTICAL, side)[1] + self.side.get_spacing() + 4  # + row padding

    @staticmethod
    def _place(child, x, y, w, h):
        child.allocate(w, h, -1, Gsk.Transform.new().translate(Graphene.Point().init(x, y)))

    def do_size_allocate(self, width, height, baseline):
        body, side, x = self._sizes(width)
        if not self.side.get_visible():
            self._place(self.body, x, 0, body, height)
        elif self.below:
            bh = max(self.body.measure(Gtk.Orientation.VERTICAL, body)[1], 1)
            self._place(self.body, x, 0, body, bh)
            self._place(self.side, x, bh + WATCH_GAP, side, max(1, height - bh - WATCH_GAP))
        else:
            top = self._top(side)
            self._place(self.body, x, top, body, max(1, height - top))
            self._place(self.side, x + body + WATCH_GAP, 0, side, height)

    def do_dispose(self):
        for child in (self.body, self.side):
            if child is not None and child.get_parent() is self:
                child.unparent()
        self.body = self.side = None
        Gtk.Widget.do_dispose(self)


class WatchPage(Adw.NavigationPage):
    """The in-app player plus the video's details, like a YouTube watch page."""

    def __init__(self, win):
        super().__init__(title='Watch', tag='watch')
        self.win = win
        self.engine = win.engine
        self.video = None
        self.stream = None
        self.is_fullscreen = False
        self._state = {}
        self._hide_src = 0
        self._gen = 0

        self.area = VideoArea(self.engine)
        self.controls = ControlBar(self)
        self.revealer = Gtk.Revealer(child=self.controls, reveal_child=True, valign=Gtk.Align.END,
                                     transition_type=Gtk.RevealerTransitionType.CROSSFADE)
        self.spinner = Adw.Spinner(width_request=48, height_request=48, halign=Gtk.Align.CENTER,
                                   valign=Gtk.Align.CENTER, visible=False, can_target=False)
        self.loading = False  # a channel is still being found (mpv has nothing to play yet)
        self.load_error = False
        self.buffer_label = Gtk.Label(halign=Gtk.Align.CENTER, valign=Gtk.Align.CENTER, margin_top=100,
                                      visible=False, can_target=False, wrap=True, justify=Gtk.Justification.CENTER)
        self.buffer_label.add_css_class('tl-buffer')
        self.fs_title = Gtk.Label(xalign=0, valign=Gtk.Align.START, ellipsize=Pango.EllipsizeMode.END,
                                  can_target=False)
        self.fs_title.add_css_class('tl-fs-title')
        self.top = Gtk.Revealer(child=self.fs_title, reveal_child=False, valign=Gtk.Align.START,
                                transition_type=Gtk.RevealerTransitionType.CROSSFADE, can_target=False)
        self.player = Gtk.Overlay(child=self.area, overflow=Gtk.Overflow.HIDDEN)  # clips to the rounded corners
        self.player.add_css_class('tl-player')
        self.stats = StatsPanel(self)
        for w in (self.top, self.spinner, self.buffer_label, self.revealer, self.stats):
            self.player.add_overlay(w)
        click = Gtk.GestureClick()
        click.connect('pressed', self._on_video_click)
        self.area.add_controller(click)
        menu_click = Gtk.GestureClick(button=Gdk.BUTTON_SECONDARY)
        menu_click.connect('pressed', self._on_video_menu)
        self.area.add_controller(menu_click)
        self.connect('hidden', lambda *_: self._pause_stats(True))
        self.connect('showing', lambda *_: self._pause_stats(False))
        self._stats_was_open = False
        motion = Gtk.EventControllerMotion()
        motion.connect('motion', self._on_motion)
        motion.connect('leave', lambda *_: self._schedule_hide(800))
        self.player.add_controller(motion)
        self._last_xy = None

        self.info = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=12, margin_top=14, margin_bottom=24,
                            margin_start=6, margin_end=6)
        self.body = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)
        self.body.append(self.player)
        self.body.append(self.info)
        # Up next (YouTube) or more channels (live TV): a column beside the player on wide windows,
        # below the details on narrow ones; hidden in fullscreen and for movies.
        self.side_title = Gtk.Label(xalign=0)
        self.side_title.add_css_class('title-4')
        self.side_spinner = Adw.Spinner(width_request=32, height_request=32, visible=False)
        self.related = Gtk.FlowBox(homogeneous=True, selection_mode=Gtk.SelectionMode.NONE,
                                   activate_on_single_click=True, min_children_per_line=1, max_children_per_line=1,
                                   column_spacing=12, row_spacing=12, valign=Gtk.Align.START)
        self.related.connect('child-activated', lambda _f, card: win.activate_card(card))
        self.side = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=8, valign=Gtk.Align.START,
                            margin_bottom=24, visible=False)
        for w in (self.side_title, self.side_spinner, self.related):
            self.side.append(w)
        self._side_on = False
        self.columns = WatchColumns(self, self.body, self.side)
        self.clamp = Adw.Clamp(maximum_size=100000, child=self.columns, margin_start=12, margin_end=12,
                               margin_top=8)  # WatchColumns sizes and centres everything
        self.scroller = Gtk.ScrolledWindow(child=self.clamp, hscrollbar_policy=Gtk.PolicyType.NEVER)
        self.scroller.get_vadjustment().connect(
            'notify::page-size', lambda adj, _p: self.columns.viewport_changed(adj.get_page_size()))
        self._start_details = None
        self.scroller.get_vadjustment().connect(
            'value-changed', lambda adj: adj.get_value() > 40 and self._start_details and self._start_details())
        bin_ = Adw.BreakpointBin(child=self.scroller, width_request=300, height_request=200)
        narrow = Adw.Breakpoint.new(Adw.BreakpointCondition.parse(f'max-width: {SIDE_BELOW}px'))
        narrow.add_setter(self.columns, 'below', True)
        narrow.add_setter(self.related, 'max-children-per-line', 2)
        bin_.add_breakpoint(narrow)
        self.set_child(bin_)

        group = Gio.SimpleActionGroup()
        for name, cb in (('download', lambda: win.download(self.video)),
                         ('download-audio', lambda: win.download(self.video, audio=True)),
                         ('mpv', lambda: win.play_external(self.video, start=self.engine.m.time_pos)),
                         ('playlist', lambda: win.save_to_playlist(self.video)),
                         ('copy', lambda: win.copy_link(self.video)),
                         ('copy-time', self.copy_link_at_time),
                         ('stats', lambda: self.stats.toggle()),
                         ('loop', self.toggle_loop),
                         ('screenshot', self.screenshot)):
            a = Gio.SimpleAction.new(name, None)
            a.connect('activate', lambda *_a, cb=cb: cb())
            group.add_action(a)
        self.insert_action_group('watch', group)

    # ---- state from the engine ----------------------------------------------------
    def on_event(self, name, value):
        self.controls.update(name, value, self.engine)
        st = self._state
        st[name] = value
        if name == 'time-pos' and value is not None and self.segments:
            self._skip_sponsor(value)
        # Channels: 'wait' (finding the stream) -> 'ready' (handed to mpv) -> 'opening'
        # (mpv is loading it) -> False once it plays. Back to idle while opening = it failed.
        if name == 'idle-active' and self.loading == 'ready' and value is False:
            self.loading = 'opening'
        elif (name == 'idle-active' and self.loading == 'opening' and value) or \
                (name == 'load-error' and self.loading in ('ready', 'opening')):
            self.win.load_failed(self.win.play_gen)
        if name == 'time-pos' and value is not None and self.loading in ('ready', 'opening'):
            self.loading = False
        if name in ('paused-for-cache', 'seeking', 'idle-active', 'time-pos'):
            # from the values mpv already sent: no synchronous queries on the drawing thread
            busy = bool(st.get('paused-for-cache')) or bool(st.get('seeking')) or (
                not st.get('idle-active', True) and st.get('time-pos') is None) or bool(self.loading)
            self.spinner.set_visible(busy and self.video is not None and not self.load_error)
            special = self.video is not None and self.video.kind == 'live'
            self.buffer_label.set_visible(special and (busy or self.load_error))
        if name == 'pause':
            if value:
                self.poke(keep=True)
            else:
                self._schedule_hide()

    def show_video(self, video, stream=None):
        """Fill the details below the player (the engine is driven by the window)."""
        self.video, self.stream = video, stream
        self._gen += 1
        self.segments, self._skipped, self._sb_for = [], set(), None
        self.controls.set_chapters([])
        self.set_title(video.title)
        self.fs_title.set_label(video.title)
        live = video.kind == 'live'
        if not live:
            self.loading = False
        self.load_error = False
        lib = self.win.lib
        self.controls.later.handler_block(self.controls.later_handler)
        self.controls.later.set_active(lib.has('tvfav', video.id) if live else lib.has('later', video.id))
        self.controls.later.handler_unblock(self.controls.later_handler)
        self.controls.later.set_tooltip_text('Favourite channel' if live else 'Watch later')
        self.controls.later.set_icon_name('starred-symbolic' if live else 'alarm-symbolic')
        self.controls.gear.set_tooltip_text('Quality, audio & subtitles' if live else 'Quality, captions & speed')
        self.controls.dl.set_visible(not live)
        self.controls.progress.set_visible(not live)
        self.buffer_label.set_label('Tuning in…')
        self.buffer_label.set_visible(live)
        self.spinner.set_visible(True)
        self._build_info(video)
        if live:
            self.controls.next_btn.set_visible(self.can_zap())
        self.scroller.get_vadjustment().set_value(0)
        self.poke()

    def set_stream(self, video, stream):
        if self.video is video:
            self.stream = stream
            if stream.get('meta') and getattr(self, 'show_meta', None):
                self.show_meta(stream['meta'])
            self.controls.set_chapters(stream.get('chapters') or [])
            if self.win.config['sponsorblock'] and video.kind == 'video' and not video.live \
                    and self._sb_for != video.id:
                self._sb_for, gen = video.id, self._gen

                def work():
                    try:
                        segs = sponsor_segments(video.id)
                    except Exception:  # noqa: BLE001 - SponsorBlock is optional
                        return
                    idle(lambda: gen == self._gen and setattr(self, 'segments', segs))

                self.win.feed_pool.submit(work)

    def _skip_sponsor(self, t):
        for start, end, cat in self.segments:
            if start <= t < end - 0.5 and (start, end) not in self._skipped:
                self._skipped.add((start, end))  # once: seeking back into it plays it
                try:
                    self.engine.m.command('seek', end, 'absolute', 'exact')
                except Exception:  # noqa: BLE001
                    return
                self.win.toast(f'Skipped {SB_CATEGORIES.get(cat, cat)} ({round(end - start)} s) · SponsorBlock')
                return

    def screenshot(self):
        """The current frame as a PNG in Pictures/Smedio (S)."""
        if self.video is None or self.engine.m.idle_active:
            return
        folder = os.path.join(GLib.get_user_special_dir(GLib.UserDirectory.DIRECTORY_PICTURES)
                              or os.path.expanduser('~/Pictures'), 'Smedio')
        t = self.engine.m.time_pos or 0
        name = re.sub(r'[\\/:*?"<>|]+', ' ', self.video.title or 'Smedio').strip()[:80] or 'Smedio'
        path = os.path.join(folder, f'{name} {(fmt_duration(t) or "0:00").replace(":", ".")}.png')
        try:
            os.makedirs(folder, exist_ok=True)
            self.engine.m.command('screenshot-to-file', path, 'video')
        except Exception as e:  # noqa: BLE001
            self.win.toast(f'Couldn’t save a screenshot: {clean_error(e)}')
            return
        self.win.toast(f'Screenshot saved in {folder}')

    # ---- player controls ----------------------------------------------------------
    def toggle_pause(self):
        self.engine.m.pause = not self.engine.m.pause

    # Exact, not 'keyframes': YouTube's audio is a separate stream that seeks to the exact time
    # while the video went back to its keyframe, so the sound stayed off for seconds.
    def seek_to(self, value):
        try:
            self.engine.m.command('seek', max(0.0, value), 'absolute', 'exact')
        except Exception:  # noqa: BLE001
            pass

    def seek_by(self, delta):
        try:
            self.engine.m.command('seek', delta, 'relative', 'exact')
        except Exception:  # noqa: BLE001
            pass
        self.poke()

    def set_volume(self, value):
        self.engine.m.volume = max(0.0, min(100.0, value))
        self.engine.m.mute = False
        self.win.config['volume'] = round(self.engine.m.volume)
        self.win.save_config()

    def toggle_mute(self):
        self.engine.m.mute = not self.engine.m.mute

    def next(self):
        if self._live():
            self.win.zap(1)
            return
        try:
            self.engine.m.command('playlist-next')
        except Exception:  # noqa: BLE001
            pass

    def set_later(self, on):
        if self._live():
            self.win.set_channel_fav(self.video, on)  # the clock button is a star for channels
        elif self.video:
            self.win.set_in_list('later', self.video, on)

    def toggle_fullscreen(self):
        self.set_fullscreen(not self.is_fullscreen)

    def set_fullscreen(self, on):
        if on == self.is_fullscreen:
            return
        self.is_fullscreen = on
        self.info.set_visible(not on)
        self.area.fill = on
        self.area.set_vexpand(on)
        (self.player.add_css_class if on else self.player.remove_css_class)('fullscreen')  # square corners
        self.show_side(self._side_on)
        for side in ('start', 'end', 'top'):
            getattr(self.clamp, f'set_margin_{side}')(0 if on else (8 if side == 'top' else 12))
        self.scroller.set_policy(Gtk.PolicyType.NEVER, Gtk.PolicyType.NEVER if on else Gtk.PolicyType.AUTOMATIC)
        self.top.set_reveal_child(on)
        self.controls.fs_btn.set_icon_name('view-restore-symbolic' if on else 'view-fullscreen-symbolic')
        self.win.set_immersive(on)
        self.area.queue_resize()
        self.poke()

    def show_side(self, on):
        """Up next beside the player (or below it on narrow pages); WatchColumns does the sizes."""
        self._side_on = on
        self.side.set_visible(on and not self.is_fullscreen)
        self.columns.queue_resize()

    def _on_motion(self, _ctl, x, y):
        # GTK sends a synthetic motion event when the bar hides; only real movement should wake it.
        if self._last_xy and abs(x - self._last_xy[0]) < 2 and abs(y - self._last_xy[1]) < 2:
            return
        self._last_xy = (x, y)
        self.poke()

    def poke(self, keep=False):
        """Show the controls (and cursor); hide them again after a pause while playing."""
        self.revealer.set_reveal_child(True)
        self.top.set_reveal_child(self.is_fullscreen)
        self.area.set_cursor(None)
        if not keep:
            self._schedule_hide()

    def _schedule_hide(self, delay=2500):
        if self._hide_src:
            GLib.source_remove(self._hide_src)
        self._hide_src = GLib.timeout_add(delay, self._hide_controls)

    def _hide_controls(self):
        self._hide_src = 0
        popovers_open = self.controls.gear.get_active() or self.controls.dl.get_active()
        if not self.engine.m.pause and not popovers_open and self.video is not None:
            self.revealer.set_reveal_child(False)
            self.top.set_reveal_child(False)
            if self.is_fullscreen:
                self.area.set_cursor(Gdk.Cursor.new_from_name('none'))
        return GLib.SOURCE_REMOVE

    def _on_video_menu(self, _gesture, _n, x, y):
        m = Gio.Menu()
        m.append('Hide stats for nerds' if self.stats.src else 'Stats for nerds', 'watch.stats')
        m.append('Loop: on' if self.engine.m.loop_file in ('inf', True) else 'Loop', 'watch.loop')
        m.append('Save a screenshot (S)', 'watch.screenshot')
        if self._live():
            m.append('Copy stream link', 'watch.copy')
        else:
            m.append('Copy video URL', 'watch.copy')
            m.append('Copy video URL at current time', 'watch.copy-time')
        pop = Gtk.PopoverMenu.new_from_model(m)
        pop.set_parent(self.area)
        pop.set_has_arrow(False)
        rect = Gdk.Rectangle()
        rect.x, rect.y, rect.width, rect.height = int(x), int(y), 1, 1
        pop.set_pointing_to(rect)
        pop.connect('closed', lambda p: idle(p.unparent))
        pop.popup()

    def _pause_stats(self, hidden):
        # Leaving the page stops the 2×/s refresh; coming back resumes it if it was open.
        if hidden:
            self._stats_was_open = bool(self.stats.src)
            if self.stats.src:
                GLib.source_remove(self.stats.src)
                self.stats.src = 0
        elif self._stats_was_open:
            self.stats.start()

    def toggle_loop(self):
        looping = self.engine.m.loop_file in ('inf', True)
        self.engine.m.loop_file = 'no' if looping else 'inf'
        self.win.toast('Loop off' if looping else 'Looping this video')

    def copy_link_at_time(self):
        if self.video:
            t = int(self.engine.m.time_pos or 0)
            self.win.get_clipboard().set_content(Gdk.ContentProvider.new_for_bytes(
                'text/plain;charset=utf-8', GLib.Bytes.new(f'https://youtu.be/{self.video.id}?t={t}'.encode())))
            self.win.toast(f'Link copied (starts at {fmt_duration(t) or "0:00"})')

    def _on_video_click(self, gesture, n_press, _x, _y):
        if n_press == 2:
            self.toggle_fullscreen()
        self.toggle_pause()  # a double-click toggles twice, leaving playback as it was

    # ---- popovers -----------------------------------------------------------------
    def _menu_box(self, title):
        box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=2, margin_top=6, margin_bottom=6,
                      margin_start=6, margin_end=6)
        if title:
            label = Gtk.Label(label=title, xalign=0, margin_start=8, margin_bottom=4)
            label.add_css_class('heading')
            box.append(label)
        return box

    def _menu_item(self, box, text, cb, current=False, popover=None):
        b = Gtk.Button(child=Gtk.Label(label=('✓  ' if current else '     ') + text, xalign=0))
        b.add_css_class('flat')
        b.connect('clicked', lambda *_: (popover.popdown() if popover else None, cb()))
        box.append(b)

    def quality_menu(self):
        pop = self.controls.gear.get_popover()
        box = self._tracks_menu(pop) if self._live() else self._quality_items(pop)
        self._menu_item(box, 'Stats for nerds (I)', self.stats.toggle, current=bool(self.stats.src), popover=pop)
        box.append(Gtk.Separator(margin_top=4, margin_bottom=4))
        speed_title = Gtk.Label(label='Speed', xalign=0, margin_start=8)
        speed_title.add_css_class('heading')
        box.append(speed_title)
        speeds = Gtk.Box(spacing=2, homogeneous=True)
        speed_now = self.engine.m.speed or 1.0
        for s in SPEEDS:
            b = Gtk.ToggleButton(label=f'{s:g}×', active=abs(s - speed_now) < 0.01)
            b.add_css_class('flat')
            b.connect('clicked', lambda _b, s=s: (setattr(self.engine.m, 'speed', s), pop.popdown()))
            speeds.append(b)
        box.append(speeds)
        return box

    def _quality_items(self, pop):
        box = self._menu_box('Quality')
        heights = [v['height'] for v in (self.stream or {}).get('formats', {}).get('video', [])] or qualities()[::-1]
        vp = self.engine.m.video_params or {}
        current = min(vp.get('w') or 0, vp.get('h') or 0) or self.engine.m.height  # short side, like the labels
        audio_mode = self.win.config['audio_only']
        for h in heights:
            if h > 1080 or h < 144:
                continue
            self._menu_item(box, f'{h}p', lambda h=h: self.win.change_quality(h),
                            current=not audio_mode and current == h, popover=pop)
        self._menu_item(box, 'Audio only', lambda: self.win.change_quality(None), current=audio_mode, popover=pop)
        caps = (self.stream or {}).get('captions') or []
        if caps:
            box.append(Gtk.Separator(margin_top=4, margin_bottom=4))
            heading = Gtk.Label(label='Captions', xalign=0, margin_start=8)
            heading.add_css_class('heading')
            box.append(heading)
            try:
                showing = next((t for t in self.engine.m.track_list or []
                                if t.get('type') == 'sub' and t.get('selected')), None)
            except Exception:  # noqa: BLE001
                showing = None
            inner = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=2)
            self._menu_item(inner, 'Off', lambda: self.set_caption(None), current=showing is None, popover=pop)
            for c in caps:
                self._menu_item(inner, c['name'], lambda c=c: self.set_caption(c),
                                current=bool(showing and showing.get('external-filename') == c['url']), popover=pop)
            box.append(Gtk.ScrolledWindow(child=inner, propagate_natural_height=True, max_content_height=220,
                                          hscrollbar_policy=Gtk.PolicyType.NEVER))
        return box

    def set_caption(self, cap):
        """YouTube captions on (that track) or off; remembered for the next videos."""
        global CAPTION_PREF
        CAPTION_PREF = self.win.config['yt_captions'] = cap['lang'] if cap else ''
        self.win.save_config()
        if cap:
            self.engine.add_caption(cap)
        else:
            self.engine.m.sid = 'no'

    def _tracks_menu(self, pop):
        """Live channels: qualities, sources, and subtitle and audio tracks."""
        live = self._live()
        box = self._menu_box('Quality' if live else 'Subtitles')
        if live:
            for h in qualities()[::-1]:
                self._menu_item(box, f'Up to {h}p', lambda h=h: self.win.set_live_quality(h),
                                current=self.win.config['quality'] == h, popover=pop)
            sources = self.win.live_sources(self.video)
            if len(sources) > 1:
                box.append(Gtk.Separator(margin_top=4, margin_bottom=4))
                heading = Gtk.Label(label='Source', xalign=0, margin_start=8)
                heading.add_css_class('heading')
                box.append(heading)
                for i, a in enumerate(sources):
                    host = urllib.parse.urlsplit(a['url']).hostname or ''
                    self._menu_item(box, f'Source {i + 1} · {host}', lambda i=i: self.win.set_live_source(i),
                                    current=live['alt'] == i, popover=pop)
            box.append(Gtk.Separator(margin_top=4, margin_bottom=4))
            heading = Gtk.Label(label='Subtitles', xalign=0, margin_start=8)
            heading.add_css_class('heading')
            box.append(heading)
        try:
            tracks = self.engine.m.track_list or []
        except Exception:  # noqa: BLE001
            tracks = []
        subs = [t for t in tracks if t.get('type') == 'sub']
        audios, seen = [], {}
        for t in tracks:  # HLS repeats each audio language once per video variant: list it once
            if t.get('type') == 'audio':
                key = (t.get('lang'), t.get('title'), t.get('codec'))
                if key not in seen:
                    seen[key] = len(audios)
                    audios.append(t)
                elif t.get('selected'):
                    audios[seen[key]] = t

        def name(t):
            title, lang = t.get('title') or '', t.get('lang') or ''
            return (title if lang in title else ' · '.join(b for b in (title, lang) if b)) or f'Track {t.get("id")}'

        inner = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=2)
        self._menu_item(inner, 'Off', lambda: setattr(self.engine.m, 'sid', 'no'),
                        current=not any(t.get('selected') for t in subs), popover=pop)
        for t in subs:
            self._menu_item(inner, name(t), lambda i=t['id']: setattr(self.engine.m, 'sid', i),
                            current=bool(t.get('selected')), popover=pop)
        box.append(Gtk.ScrolledWindow(child=inner, propagate_natural_height=True, max_content_height=260,
                                      hscrollbar_policy=Gtk.PolicyType.NEVER))
        if subs:
            timing = Gtk.Box(spacing=2, margin_start=8, margin_top=4)
            label = Gtk.Label(label=self._sub_delay_text(), hexpand=True, xalign=0)
            label.add_css_class('caption')
            timing.append(label)
            for text, tip, step in (('−0.5 s', 'Show subtitles earlier (Z)', -0.5), ('+0.5 s', 'Show subtitles later (X)', 0.5),
                                    ('0', 'Reset timing', None)):
                b = Gtk.Button(label=text, tooltip_text=tip)
                b.add_css_class('flat')
                b.connect('clicked', lambda _b, step=step: (self.shift_subs(step), label.set_label(self._sub_delay_text())))
                timing.append(b)
            box.append(timing)
        if len(audios) > 1:
            box.append(Gtk.Separator(margin_top=4, margin_bottom=4))
            heading = Gtk.Label(label='Audio', xalign=0, margin_start=8)
            heading.add_css_class('heading')
            box.append(heading)
            for t in audios:
                label = name(t) + (f' ({t["codec"]})' if t.get('codec') else '')
                self._menu_item(box, label, lambda i=t['id']: setattr(self.engine.m, 'aid', i),
                                current=bool(t.get('selected')), popover=pop)
        return box

    def download_menu(self):
        pop = self.controls.dl.get_popover()
        box = self._menu_box('Download')
        video = self.video
        formats = (self.stream or {}).get('formats')
        if not video:
            return box
        if formats and formats['video']:
            for f in formats['video']:
                fps = f' {int(f["fps"])}fps' if f.get('fps') and f['fps'] > 30 else ''
                label = f'{f["height"]}p{fps} · H.264 · {fmt_size(f["size"]) if f["size"] else "size unknown"}'
                spec = f'{f["id"]}+bestaudio[ext=m4a]/{f["id"]}+bestaudio'
                self._menu_item(box, label, lambda spec=spec, h=f['height']: self.win.downloads_start(
                    video, fmt=spec, label=f'{h}p'), popover=pop)
            best = 'bestvideo+bestaudio[ext=m4a]/bestvideo+bestaudio/best'
            self._menu_item(box, 'Best quality (any codec, may be VP9/AV1)',
                            lambda: self.win.downloads_start(video, fmt=best, label='Best'), popover=pop)
            a = formats.get('audio')
            if a:
                self._menu_item(box, f'Audio only · M4A {int(a["abr"] or 128)} kbps · {fmt_size(a["size"])}',
                                lambda: self.win.downloads_start(video, audio=True, fmt=a['id'], label='Audio'),
                                popover=pop)
        else:
            self._menu_item(box, f'Video ({self.win.config["quality"]}p, H.264)',
                            lambda: self.win.download(video), popover=pop)
            self._menu_item(box, 'Audio only (M4A)', lambda: self.win.download(video, audio=True), popover=pop)
            note = Gtk.Label(label='Exact sizes appear once the video has loaded.', xalign=0, margin_start=8,
                             margin_top=4, wrap=True, max_width_chars=30)
            note.add_css_class('dim-label')
            note.add_css_class('caption')
            box.append(note)
        return box

    # ---- details under the player ------------------------------------------------
    def _build_info(self, video):
        # Wrapping labels here get max_width_chars=1: their natural width would otherwise be their
        # whole text on one line, and a long comment made the details column push Up next off-screen.
        win, lib, gen = self.win, self.win.lib, self._gen
        while (child := self.info.get_first_child()):
            self.info.remove(child)
        self.related.remove_all()
        self.side_spinner.set_visible(False)
        self.show_side(False)
        if video.kind == 'file':  # a downloaded file: nothing to look up online
            title = Gtk.Label(label=video.title, xalign=0, wrap=True, max_width_chars=1)
            title.add_css_class('tl-watch-title')
            self.info.append(title)
            return
        if video.kind == 'live':
            self._build_live_info(video)
            return

        title = Gtk.Label(label=video.title, xalign=0, wrap=True, max_width_chars=1)
        title.add_css_class('tl-watch-title')
        self.info.append(title)
        self.title_label = title

        row = Gtk.Box(spacing=8)
        self.channel_btn = Gtk.Button(label=video.channel or 'Channel')
        self.channel_btn.add_css_class('flat')
        self.channel_btn.add_css_class('heading')
        self.channel_btn.connect('clicked', lambda *_: win.open_channel(self.video))
        row.append(self.channel_btn)
        self.sub_btn = SubscribeButton(win, lambda: (self.video.channel_id, self.video.channel,
                                                     self.video.channel_link))
        row.append(self.sub_btn)
        self.meta_label = Gtk.Label(label=video.meta(), xalign=1, hexpand=True, wrap=True, max_width_chars=1)
        self.meta_label.add_css_class('dim-label')
        row.append(self.meta_label)
        self.info.append(row)

        actions = Gtk.Box(spacing=6)
        like = Gtk.ToggleButton(child=Adw.ButtonContent(label='Like', icon_name='emblem-favorite-symbolic'),
                                active=lib.has('liked', video.id))
        like.connect('toggled', lambda b: win.set_in_list('liked', self.video, b.get_active()))
        actions.append(like)
        menu = Gio.Menu()
        menu.append('Download video', 'watch.download')
        menu.append('Download audio', 'watch.download-audio')
        actions.append(Gtk.MenuButton(child=Adw.ButtonContent(label='Download', icon_name='folder-download-symbolic'),
                                      menu_model=menu))
        save = Gtk.Button(child=Adw.ButtonContent(label='Save', icon_name='list-add-symbolic'))
        save.connect('clicked', lambda *_: win.save_to_playlist(self.video))
        actions.append(save)
        more = Gio.Menu()
        more.append('Copy link', 'watch.copy')
        more.append('Open in separate mpv window', 'watch.mpv')
        actions.append(Gtk.MenuButton(icon_name='view-more-symbolic', menu_model=more, tooltip_text='More'))
        self.info.append(actions)

        self.desc = Gtk.Label(xalign=0, wrap=True, max_width_chars=1, selectable=True, focusable=False, use_markup=True,
                              wrap_mode=Pango.WrapMode.WORD_CHAR)
        self.desc_expander = Gtk.Expander(label='Description', child=self.desc, visible=False)
        self.info.append(self.desc_expander)

        self.side_title.set_label('Up next')
        self.side_spinner.set_visible(True)  # the list comes a few seconds after the video starts
        self.show_side(True)

        self.comments_label = Gtk.Label(label='Comments', xalign=0)
        self.comments_label.add_css_class('title-4')
        self.info.append(self.comments_label)
        comments_spinner = Adw.Spinner(width_request=32, height_request=32, visible=False)
        self.info.append(comments_spinner)
        comments_hint = Gtk.Label(label='Comments load when you scroll down here.', xalign=0)
        comments_hint.add_css_class('dim-label')
        self.info.append(comments_hint)
        self.comments = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=14)
        self.info.append(self.comments)

        def related_work():
            try:
                items = win.yt.related(video.id)
            except Exception:  # noqa: BLE001
                items = []
            idle(show_related, items)

        def show_related(items):
            if gen != self._gen:
                return
            self.side_spinner.set_visible(False)
            hidden_v, _ = lib.hidden()
            self.show_side(any(v.id not in hidden_v for v in items))

            def add_card(v):
                if gen == self._gen:
                    card = Card(v, win, row=True)
                    self.related.append(card)
                    win.load_thumb(card)

            in_batches([v for v in items[:18] if v.id not in hidden_v], add_card)

        def show_meta(meta):
            if gen != self._gen:
                return
            for field, key in (('channel', 'channel'), ('channel_id', 'channel_id'), ('channel_url', 'channel_url'),
                               ('duration', 'duration'), ('views', 'views')):
                if meta.get(key):
                    setattr(self.video, field, meta[key])
            self.channel_btn.set_label(self.video.channel or 'Channel')
            self.sub_btn.refresh()
            bits = [f'{fmt_count(meta["views"])} views' if meta.get('views') else None,
                    f'👍 {fmt_count(meta["likes"])}' if meta.get('likes') else None]
            if meta.get('upload_date'):
                try:  # '9 days ago', the date itself on hover (as on YouTube)
                    bits.append(date_age(meta['upload_date']))
                    self.meta_label.set_tooltip_text(
                        datetime.strptime(meta['upload_date'], '%Y%m%d').strftime('Uploaded %d %B %Y'))
                except ValueError:
                    pass
            if meta.get('followers'):
                bits.append(f'{fmt_count(meta["followers"])} subscribers')
            self.meta_label.set_label(' · '.join(b for b in bits if b))
            if meta.get('description') and not self.desc_expander.get_visible():
                self.desc.set_markup(linkify(meta['description']))
                self.desc_expander.set_visible(True)
            if meta.get('comment_count'):
                self.comments_label.set_label(f'Comments ({fmt_count(meta["comment_count"])})')

        self.show_meta = show_meta
        if self.stream and self.stream.get('meta'):
            show_meta(self.stream['meta'])

        def details_work():
            try:
                d = win.yt.details(video.id)
                idle(show_comments, d, None)
            except Exception as e:  # noqa: BLE001
                idle(show_comments, None, clean_error(e))

        def show_comments(d, error):
            if gen != self._gen:
                return
            comments_spinner.set_visible(False)
            if error:
                self.comments_label.set_label('Comments unavailable')
                return
            v = d['video']
            if v.title and self.video.title == self.video.id:
                self.video.title = v.title
                self.title_label.set_label(v.title)
                self.set_title(v.title)
            show_meta({'views': v.views, 'likes': d.get('likes'), 'upload_date': d.get('upload_date'),
                       'followers': d.get('followers'), 'description': d.get('description'),
                       'comment_count': d.get('comment_count'), 'channel': v.channel, 'channel_id': v.channel_id,
                       'channel_url': v.channel_url, 'duration': v.duration})

            def add_comment(c):
                if gen != self._gen:
                    return
                item = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=2)
                head = (f'<b>{GLib.markup_escape_text(c["author"])}</b>'
                        + (' <span alpha="60%">(creator)</span>' if c['uploader'] else '')
                        + f'  <span alpha="60%">{GLib.markup_escape_text(c["time"])}'
                        + (f' · 👍 {fmt_count(c["likes"])}' if c['likes'] else '')
                        + (' · 📌 pinned' if c['pinned'] else '') + '</span>')
                item.append(Gtk.Label(label=head, use_markup=True, xalign=0, wrap=True, max_width_chars=1))
                item.append(Gtk.Label(label=c['text'], xalign=0, wrap=True, max_width_chars=1, selectable=True, focusable=False,
                                      wrap_mode=Pango.WrapMode.WORD_CHAR))
                self.comments.append(item)

            in_batches(d['comments'], add_comment, 4)
            if not d['comments']:
                self.comments.append(Gtk.Label(label='No comments to show.', xalign=0, css_classes=['dim-label']))

        # Nothing extra while the video starts (that is when frames get dropped): Up next after
        # a few seconds; comments (a second full YouTube lookup) only when you scroll down to them.
        def start_related():
            if gen == self._gen:
                win.feed_pool.submit(related_work)
            return GLib.SOURCE_REMOVE

        def start_details():
            if gen == self._gen and not self._details_started:
                self._details_started = True
                comments_hint.set_visible(False)
                comments_spinner.set_visible(True)
                win.search_pool.submit(details_work)
            return GLib.SOURCE_REMOVE

        self._details_started = False
        self._start_details = start_details  # runs when you scroll down to the comments
        GLib.timeout_add_seconds(5, start_related)

    def show_load_error(self, msg):
        self.load_error = True
        self.spinner.set_visible(False)
        if self._live():
            self.buffer_label.set_label('This channel didn’t start.\nIt may be off air, or need a login.')
        else:
            self.buffer_label.set_label(f'Couldn’t start this stream.\n{msg}' if msg else 'Couldn’t start this stream.')
        self.buffer_label.set_visible(True)

    def _sub_delay_text(self):
        delay = self.engine.m.sub_delay or 0
        return 'Subtitle timing: in sync' if abs(delay) < 0.05 else \
            f'Subtitles {abs(delay):.1f} s {"later" if delay > 0 else "earlier"}'

    def shift_subs(self, step):
        """Nudge subtitle timing (step None = reset); for subtitles that are a little off."""
        m = self.engine.m
        m.sub_delay = 0 if step is None else round((m.sub_delay or 0) + step, 2)
        self.win.toast(self._sub_delay_text(), 1)

    def ready_to_load(self, gen):
        if gen == self.win.play_gen and self.loading:
            self.loading = 'ready'

    # ---- live channels ------------------------------------------------------------------
    def _live(self):
        nl = self.win.now_live
        return nl if nl and self.video is not None and nl['video'] is self.video else None

    def can_zap(self):
        nl = self._live()
        return bool(nl and len(nl['siblings']) > 1)

    def refresh_fav(self):
        if not self._live():
            return
        on = self.win.lib.has('tvfav', self.video.id)
        for button, handler in ((self.controls.later, self.controls.later_handler),
                                (getattr(self, 'fav_btn', None), getattr(self, 'fav_handler', None))):
            if button is not None:
                button.handler_block(handler)
                button.set_active(on)
                button.handler_unblock(handler)

    def _build_live_info(self, video):
        win, nl, gen = self.win, self.win.now_live, self._gen
        self.show_meta = self._start_details = None
        title = Gtk.Label(label=video.title, xalign=0, wrap=True, max_width_chars=1)
        title.add_css_class('tl-watch-title')
        self.title_label = title
        src = (win.live_index.get(video.id) or {}).get('source')
        source = next((pl['name'] for pl in win.config['iptv'] if pl['url'] == src), 'IPTV')
        self.meta_label = Gtk.Label(label=' · '.join(b for b in (source, video.channel, video.views_text) if b),
                                    xalign=0, wrap=True, max_width_chars=1)
        self.meta_label.add_css_class('dim-label')
        actions = Gtk.Box(spacing=6)
        self.fav_btn = Gtk.ToggleButton(child=Adw.ButtonContent(label='Favourite', icon_name='starred-symbolic'),
                                        active=win.lib.has('tvfav', video.id))
        self.fav_handler = self.fav_btn.connect('toggled', lambda b: win.set_channel_fav(video, b.get_active()))
        actions.append(self.fav_btn)
        if self.can_zap():
            for label, icon, step in (('Previous channel', 'go-previous-symbolic', -1),
                                      ('Next channel', 'go-next-symbolic', 1)):
                b = Gtk.Button(icon_name=icon, tooltip_text=f'{label} (PgUp / PgDn)')
                b.connect('clicked', lambda _b, step=step: win.zap(step))
                actions.append(b)
        for w in (title, self.meta_label, actions):
            self.info.append(w)
        siblings = nl['siblings'] if nl else []
        if len(siblings) > 1:
            ids = [s.id for s in siblings]
            i = ids.index(video.id) if video.id in ids else 0
            nearby = (siblings[i + 1:] + siblings[:i])[:24]
            self.side_title.set_label('More channels')
            self.show_side(True)

            def add(v):
                if gen == self._gen:
                    card = Card(v, win, row=True)
                    self.related.append(card)
                    win.load_thumb(card)

            GLib.timeout_add_seconds(3, lambda: (in_batches(nearby, add, 4), False)[1])  # after the stream starts

class DownloadsPage(Adw.NavigationPage):
    def __init__(self, win):
        super().__init__(title='Downloads')
        self.win = win
        self.rows = {}
        heading = Gtk.Box(spacing=6, margin_start=24, margin_end=18, margin_top=10, margin_bottom=4)
        title = Gtk.Label(label='Downloads', xalign=0, hexpand=True)
        title.add_css_class('title-2')
        heading.append(title)
        open_btn = Gtk.Button(child=Adw.ButtonContent(label='Open folder', icon_name='folder-open-symbolic'))
        open_btn.connect('clicked', lambda *_: win.open_folder(win.config['download_dir']))
        heading.append(open_btn)
        self.list = Gtk.ListBox(selection_mode=Gtk.SelectionMode.NONE, valign=Gtk.Align.START)
        self.list.add_css_class('boxed-list')
        self.empty = Adw.StatusPage(icon_name='folder-download-symbolic', title='No downloads yet',
                                    description='Use the download button in the player, or a video’s ⋮ menu.\n'
                                                f'Files are saved to {win.config["download_dir"]}', vexpand=True)
        body = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, margin_start=18, margin_end=18, margin_bottom=18)
        body.append(self.list)
        body.append(self.empty)
        outer = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)
        outer.append(heading)
        outer.append(Gtk.ScrolledWindow(child=Adw.Clamp(maximum_size=900, child=body), vexpand=True,
                                        hscrollbar_policy=Gtk.PolicyType.NEVER))
        self.set_child(outer)
        for d in reversed(win.downloads.items):
            self._update(d)
        active = {d.path for d in win.downloads.items if d.path}
        for path, _vid, title_text, audio in win.lib.downloads():
            if path not in active and os.path.exists(path):
                self._past_row(path, title_text, audio)
        self._refresh_empty()
        win.downloads.listeners.add(self._update)
        self.connect('hidden', lambda *_: win.downloads.listeners.discard(self._update))
        self.connect('showing', lambda *_: win.downloads.listeners.add(self._update))

    def _refresh_empty(self):
        has = self.list.get_first_child() is not None
        self.list.set_visible(has)
        self.empty.set_visible(not has)

    def _buttons(self, title, path_fn, cancel_fn=None, remove_fn=None):
        box = Gtk.Box(spacing=4, valign=Gtk.Align.CENTER)
        play = Gtk.Button(icon_name='media-playback-start-symbolic', tooltip_text='Play')
        play.connect('clicked', lambda *_: path_fn() and self.win.play_file(path_fn(), title))
        folder = Gtk.Button(icon_name='folder-open-symbolic', tooltip_text='Show in folder')
        folder.connect('clicked', lambda *_: path_fn() and self.win.show_file(path_fn()))
        extra = Gtk.Button(icon_name='process-stop-symbolic' if cancel_fn else 'edit-clear-symbolic',
                           tooltip_text='Cancel' if cancel_fn else 'Remove from list (keeps the file)')
        extra.connect('clicked', lambda *_: (cancel_fn or remove_fn)())
        for b in (play, folder, extra):
            b.add_css_class('flat')
            box.append(b)
        return box, play, folder, extra

    def _past_row(self, path, title, audio):
        row = Adw.ActionRow(title=GLib.markup_escape_text(title or os.path.basename(path)),
                            subtitle=('Audio' if audio else 'Video') + ' · ' + fmt_size(os.path.getsize(path)))
        row.add_prefix(Gtk.Image(icon_name='audio-x-generic-symbolic' if audio else 'video-x-generic-symbolic'))

        def remove():
            self.win.lib.remove_download(path)
            self.list.remove(row)
            self._refresh_empty()

        box, *_ = self._buttons(title, lambda: path, remove_fn=remove)
        row.add_suffix(box)
        self.list.append(row)

    def _update(self, d):
        entry = self.rows.get(id(d))
        if not entry:
            row = Adw.ActionRow(title=GLib.markup_escape_text(d.video.title))
            row.add_prefix(Gtk.Image(icon_name='audio-x-generic-symbolic' if d.audio else 'video-x-generic-symbolic'))
            bar = Gtk.ProgressBar(valign=Gtk.Align.CENTER, width_request=140)
            row.add_suffix(bar)

            def cancel():
                d.cancelled = True
                d.detail = 'Cancelling…'
                if d.proc and d.proc.poll() is None:
                    d.proc.terminate()
                self._update(d)

            box, play, folder, cancel_btn = self._buttons(d.video.title, lambda: d.path, cancel_fn=cancel)
            row.add_suffix(box)
            self.list.prepend(row)
            entry = self.rows[id(d)] = (row, bar, play, folder, cancel_btn)
        row, bar, play, folder, cancel_btn = entry
        active = d.status in ('Queued', 'Starting', 'Downloading')
        row.set_subtitle(GLib.markup_escape_text(d.detail if d.status == 'Done' else f'{d.label} · {d.status} · {d.detail}'))
        bar.set_fraction(d.progress)
        bar.set_visible(active)
        play.set_visible(d.status == 'Done')
        folder.set_visible(d.status == 'Done')
        cancel_btn.set_visible(active)
        self._refresh_empty()


class SubscribeButton(Gtk.Button):
    """Local subscribe toggle. `info()` returns (channel_id, name, url); the id is
    looked up in the background when only a URL is known."""

    def __init__(self, win, info):
        super().__init__(valign=Gtk.Align.CENTER)
        self.win, self.info = win, info
        self.connect('clicked', lambda *_: win.toggle_channel(*self.info(), done=self.refresh))
        self.refresh()

    def refresh(self):
        subscribed = self.win.lib.is_subscribed(self.info()[0])
        self.set_label('Subscribed' if subscribed else 'Subscribe')
        if subscribed:
            self.remove_css_class('tl-subscribe')
        else:
            self.add_css_class('tl-subscribe')
        self.set_tooltip_text('Saved on this device')


# ---------------------------------------------------------------- live TV
# Any IPTV playlist (M3U link or file), and iptv-org's country and region lists. Channels play in
# the same hardware-decoding player.

IPTV_DEAD_FILE = os.path.join(GLib.get_user_cache_dir(), 'smedio', 'iptv-unavailable.json')
IPTV_CHECK_DAYS = 3  # dead IPTV channels stay hidden this long; each list is re-checked as often
LIVE_W, LIVE_H = 176, 99
LIVE_FIRST = 72  # channels shown at first; more as you scroll
# Highest HLS variant to pick for each quality setting (bits/s); 1080 = no limit.
LIVE_BITRATE = {360: 1_000_000, 480: 1_800_000, 720: 4_000_000, 1080: None}


IPTV_ORG = 'https://iptv-org.github.io/iptv/'
IPTV_ORG_INDEX = 'https://raw.githubusercontent.com/iptv-org/iptv/master/PLAYLISTS.md'
IPTV_DEFAULT = IPTV_ORG + 'countries/in.m3u'


def parse_iptv_org_index(text):
    """iptv-org's list of playlists by country, then by region ('- 🇮🇳 India <code>…/in.m3u</code>')."""
    text = text.replace('\r', '')
    area = text[text.find('#### Countries'):]
    out = []
    for name, url, kind in re.findall(r'^- (.+?) <code>(https://iptv-org\.github\.io/iptv/(countries|regions)/[^<]+)</code>',
                                      area, re.M):
        name = name.strip()
        if kind == 'countries' and name.split()[-1].lower() == 'undefined':
            continue
        out.append({'name': name if kind == 'countries' else f'🌐 {name}', 'url': url})
    return out


def parse_m3u(text, source):
    """Channels from an M3U playlist: name, logo, group, language, stream URL, and the user agent
    or referrer some IPTV lists need (#EXTVLCOPT lines, or Kodi-style 'url|User-Agent=…')."""
    channels, cur, opts = [], None, {}
    for line in text.splitlines():
        line = line.strip()
        if line.startswith('#EXTINF'):
            attrs = dict(re.findall(r'([\w-]+)="([^"]*)"', line))
            rest = re.sub(r'[\w-]+="[^"]*"', '', line)
            name = rest.split(',', 1)[1].strip() if ',' in rest else ''
            cur = {'name': name or attrs.get('tvg-name') or 'Channel', 'logo': attrs.get('tvg-logo') or None,
                   'group': attrs.get('group-title') or attrs.get('tvg-type') or '',
                   'lang': attrs.get('tvg-language') or '', 'tvg_id': attrs.get('tvg-id') or ''}
            opts = {}
        elif line.startswith('#EXTVLCOPT:'):
            key, _, value = line[11:].partition('=')
            opts[key.strip().lower()] = value.strip()
        elif line.startswith('#EXTGRP:') and cur is not None and not cur['group']:
            cur['group'] = line[8:].strip()
        elif line and not line.startswith('#'):
            url, _, extra = line.partition('|')
            for part in extra.split('&') if extra else []:
                key, _, value = part.partition('=')
                key = key.strip().lower()
                if key in ('user-agent', 'referer', 'referrer'):
                    opts['http-user-agent' if key == 'user-agent' else 'http-referrer'] = urllib.parse.unquote(value)
            ch = cur or {'name': url.rstrip('/').rsplit('/', 1)[-1], 'logo': None, 'group': '', 'lang': '', 'tvg_id': ''}
            ch.update(url=url, ua=opts.get('http-user-agent'), referrer=opts.get('http-referrer'), source=source)
            channels.append(ch)
            cur, opts = None, {}
    return channels


def merge_channels(chans):
    """One channel per name and tvg-id. Community lists (iptv-org and the like) repeat a channel
    once per stream source; those become fallbacks, tried in order when one is dead. Different
    channels that share a name (Nick Jr. India / Nick Jr. Russia) stay apart. Categories such as
    'Animation;Kids' are split, and the country comes from tvg-id ('Name.in@SD' -> IN)."""
    merged = {}
    for ch in chans:
        key = (ch['name'], re.sub(r'@.*', '', ch.get('tvg_id') or '').lower())  # '@SD'/'@HD' = feeds of one channel
        m = merged.get(key)
        if m is None:
            m = merged[key] = dict(ch, alts=[], groups=[])
            country = re.search(r'\.([a-z]{2})(?:@|$)', ch.get('tvg_id') or '')
            m['country'] = country.group(1).upper() if country else ''
        if all(a['url'] != ch['url'] for a in m['alts']):
            m['alts'].append({'url': ch['url'], 'ua': ch['ua'], 'referrer': ch['referrer']})
        for g in re.split(r'\s*;\s*', ch['group'] or ''):
            if g and g not in m['groups']:
                m['groups'].append(g)
        m['logo'] = m['logo'] or ch['logo']
    names = Counter(name for name, _ in merged)
    for (name, base), m in merged.items():
        m['id_extra'] = base if names[name] > 1 else ''  # only shared names need the tvg-id in their id
    return list(merged.values())


def channel_video(ch):
    # stable across playlist refreshes, even when stream URLs carry changing tokens
    extra = f'|{ch["id_extra"]}' if ch.get('id_extra') else ''
    vid = 'iptv:' + hashlib.md5(f'{ch["source"]}|{ch["name"]}{extra}'.encode()).hexdigest()[:12]
    alts = ch.get('alts') or [{'url': ch['url']}]
    return Video(vid, ch['name'], kind='live', thumb=ch['logo'], channel=', '.join(ch.get('groups') or [ch['group']]),
                 views_text=ch['lang'] or ch.get('country') or None, link=alts[0]['url'],
                 count=len(alts) if len(alts) > 1 else None)


def probe_stream(alt, timeout=10):
    """'ok', 'dead', or None when it can't tell (slow server, not a web link) for one stream link.
    Reads only the start of the playlist (a KB or two)."""
    url = alt['url']
    if not url.startswith(('http://', 'https://')):
        return None
    headers = {'User-Agent': alt.get('ua') or 'Mozilla/5.0 (X11; Linux x86_64)'}
    if alt.get('referrer'):
        headers['Referer'] = alt['referrer']
    try:
        with urllib.request.urlopen(urllib.request.Request(url, headers=headers), timeout=timeout) as r:
            r.read(1024)
            return 'ok'
    except urllib.error.HTTPError as e:
        return 'dead' if e.code in (400, 401, 403, 404, 410, 451) or e.code >= 500 else None
    except (TimeoutError, socket.timeout):
        return None
    except urllib.error.URLError as e:  # no such server, refused, broken TLS…
        return None if isinstance(e.reason, (TimeoutError, socket.timeout)) or 'timed out' in str(e.reason) else 'dead'
    except (OSError, ValueError):
        return 'dead'


class LiveMixin:
    """The window's Live TV side: IPTV playlists, favourites, and playing channels."""

    def _live_init(self):
        self.now_live = None     # the channel playing, and the list it came from (for zapping)
        self._live_cache = {}    # source (a playlist URL or file) -> (fetched, [Video])
        self.live_index = {}     # channel id -> parsed channel (stream URL, user agent, referrer)
        try:  # IPTV channels found dead (id -> when) and when each list was last checked
            with open(IPTV_DEAD_FILE) as f:
                saved = json.load(f)
            fresh = lambda d: {k: t for k, t in d.items() if time.time() - t < IPTV_CHECK_DAYS * 86400}  # noqa: E731
            self.iptv_dead, self.iptv_checked = fresh(saved.get('dead', {})), fresh(saved.get('checked', {}))
        except (OSError, ValueError, AttributeError):
            self.iptv_dead, self.iptv_checked = {}, {}
        self._checking = set()
        self.check_pool = None

    def live_sections(self):
        return [('tv:iptv', 'IPTV', 'network-workgroup-symbolic'),
                ('tv:fav', 'Favourite channels', 'starred-symbolic')]

    def _migrate_iptv(self):
        """iptv-org country links saved as playlists are now picked from the IPTV page's menu."""
        org = [pl for pl in self.config['iptv'] if pl['url'].startswith(IPTV_ORG)]
        if org:
            self.config['iptv'] = [pl for pl in self.config['iptv'] if not pl['url'].startswith(IPTV_ORG)]
            if self.config['iptv_source'] == IPTV_DEFAULT:
                self.config['iptv_source'] = org[0]['url']
            self.save_config()

    def iptv_country_names(self):
        """{'IN': '🇮🇳 India', …} from iptv-org's list."""
        entries = (cache_read(CHANNELS_DIR, 'iptv-org-index') or {}).get('entries') or []
        return {e['url'].rsplit('/', 1)[-1][:-4].upper(): e['name'] for e in entries if '/countries/' in e['url']}

    def iptv_sources(self, force=False):
        """Your own playlists, then every iptv-org country and region: [{'name', 'url'}]."""
        index = None if force else cache_read(CHANNELS_DIR, 'iptv-org-index')
        if not index:
            try:
                index = {'saved': time.time(),
                         'entries': parse_iptv_org_index(http_get(IPTV_ORG_INDEX, 30).decode('utf-8', 'replace'))}
                if index['entries']:
                    cache_write(CHANNELS_DIR, 'iptv-org-index', index)
            except OSError:
                index = cache_read(CHANNELS_DIR, 'iptv-org-index') or {'entries': []}
        mine = [{'name': f'★ {pl["name"]}', 'url': pl['url']} for pl in self.config['iptv']]
        return mine + (index.get('entries') or [{'name': '🇮🇳 India', 'url': IPTV_DEFAULT}])
    def _make_live_section(self, key):
        if key == 'tv:fav':
            return GridPage(self, 'Favourite channels', lambda: self.lib.items('tvfav'), list_name='tvfav',
                            list_label='Favourite channels',
                            empty=('No favourite channels', 'Use ⋮ → Add to favourites on a channel, or the star '
                                   'button in the player.', None))
        if key == 'tv:iptv':
            return self._channel_page('IPTV')
        raise KeyError(key)

    def load_channels(self, source, force=False):
        """Channels of a playlist (URL or file). Saved on disk and reused until you
        refresh; a playlist file is read again when it changes."""
        hit = self._live_cache.get(source)
        if hit and not force:
            return hit[1]
        merged = saved = None
        if not force:
            disk = cache_read(CHANNELS_DIR, source)
            if disk and not source.startswith(('http://', 'https://')):
                try:
                    if os.path.getmtime(os.path.expanduser(source)) > disk['saved']:
                        disk = None
                except OSError:
                    disk = None
            if disk and disk.get('channels'):
                merged, saved = disk['channels'], disk['saved']
        if merged is None:
            if source.startswith(('http://', 'https://')):
                chans = parse_m3u(http_get(source, 40).decode('utf-8', 'replace'), source)
            else:
                with open(os.path.expanduser(source), encoding='utf-8', errors='replace') as f:
                    chans = parse_m3u(f.read(), source)
            merged, saved = merge_channels(chans), time.time()
            if merged:
                cache_write(CHANNELS_DIR, source, {'saved': saved, 'channels': merged, 'source': source})
        videos = []
        for ch in merged:
            v = channel_video(ch)
            self.live_index[v.id] = ch
            videos.append(v)
        self._live_cache[source] = (saved, videos)
        return videos

    def forget_channels(self, source):
        self._live_cache.pop(source, None)
        cache_drop(CHANNELS_DIR, source)

    def _channel_page(self, title):
        """The IPTV page: pick a country, region or your own playlist from the menu at the top; it
        is remembered."""
        state = {'group': None, 'lang': None, 'groups': [], 'langs': [], 'updating': False, 'all': [],
                 'source': self.config['iptv_source'], 'sources': []}
        groups = Gtk.DropDown.new_from_strings(['All categories'])
        langs = Gtk.DropDown.new_from_strings(['All languages'])
        picker = Gtk.DropDown(model=Gtk.StringList.new(['Loading…']), enable_search=True,
                              tooltip_text='Country, region or your own playlist (type to search)')
        picker.set_expression(Gtk.PropertyExpression.new(Gtk.StringObject, None, 'string'))
        picker.set_search_match_mode(Gtk.StringFilterMatchMode.SUBSTRING)
        menu = Gio.Menu()
        menu.append('Show all channels (also ones that aren’t working)', 'win.iptv-all')
        menu.append('Check this list for dead channels again', 'win.iptv-recheck')
        more = Gtk.MenuButton(icon_name='view-more-symbolic', menu_model=menu, tooltip_text='More',
                              valign=Gtk.Align.CENTER)
        more.add_css_class('flat')
        actions = [picker, groups, langs, more]
        self._iptv_state = state
        for d in actions:
            d.set_valign(Gtk.Align.CENTER)

        def groups_of(v):
            return (self.live_index.get(v.id) or {}).get('groups') or ()

        def filtered():
            dead = self.hidden_channels(state['source'])
            return [v for v in state['all'] if (not state['group'] or state['group'] in groups_of(v))
                    and (not state['lang'] or v.views_text == state['lang']) and v.id not in dead]

        def fetch():
            if not state['sources'] or page.forcing:
                entries = self.iptv_sources(force=page.forcing)
                idle(set_sources, entries)
            src = state['source']
            state['all'] = self.load_channels(src, force=page.forcing)
            page.data_time = self._live_cache[src][0]
            gs = sorted({g for v in state['all'] for g in groups_of(v)}, key=str.lower)
            ls = sorted({v.views_text for v in state['all'] if v.views_text}, key=str.lower)
            countries = not any((self.live_index.get(v.id) or {}).get('lang') for v in state['all'])
            if countries:  # full names with flags, in name order
                names = self.iptv_country_names()
                ls = sorted(ls, key=lambda c: names.get(c, c)[2:].lower() if c in names else c)
            one_country = src.startswith(IPTV_ORG + 'countries/')  # its own menu entry already says which
            if gs != state['groups'] or ls != state['langs'] or one_country != state.get('one_country'):
                state['one_country'] = one_country
                idle(set_models, gs, ls, countries, one_country)
            idle(self.check_channels, src, list(state['all']), page)
            return filtered()[:LIVE_FIRST]

        def set_models(gs, ls, countries, one_country=False):
            state['updating'] = True
            state['groups'], state['langs'] = gs, ls
            groups.set_model(Gtk.StringList.new(['All categories'] + gs))
            names = self.iptv_country_names() if countries else {}
            labels = [names.get(c) or (f'{country_flag(c)} {c}' if countries else c) for c in ls]
            langs.set_model(Gtk.StringList.new(['From all countries' if countries else 'All languages'] + labels))
            langs.set_tooltip_text('Where the channels come from' if countries else 'Language')
            if one_country:
                state['lang'] = None
            groups.set_selected(gs.index(state['group']) + 1 if state['group'] in gs else 0)
            langs.set_selected(ls.index(state['lang']) + 1 if state['lang'] in ls else 0)
            groups.set_visible(len(gs) > 1)
            langs.set_visible(len(ls) > 1 and not one_country)
            state['updating'] = False

        def set_sources(entries):
            state['updating'] = True
            state['sources'] = entries
            picker.set_model(Gtk.StringList.new([e['name'] for e in entries]))
            urls = [e['url'] for e in entries]
            picker.set_selected(urls.index(state['source']) if state['source'] in urls else Gtk.INVALID_LIST_POSITION)
            state['updating'] = False

        page = GridPage(self, title, fetch, more=lambda n: filtered()[:n], actions=actions, keep=True,
                        empty=('No channels', 'Nothing in this category here — try another one, or ↻.', None))

        def changed(*_):
            if state['updating']:
                return
            g, lang = groups.get_selected(), langs.get_selected()
            state['group'] = state['groups'][g - 1] if g else None
            state['lang'] = state['langs'][lang - 1] if lang else None
            page.reload()

        def source_changed(*_):
            i = picker.get_selected()
            if state['updating'] or i >= len(state['sources']):
                return
            state['source'] = self.config['iptv_source'] = state['sources'][i]['url']
            self.save_config()
            state['group'] = state['lang'] = None  # categories differ between countries
            page.reload()

        groups.connect('notify::selected', changed)
        langs.connect('notify::selected', changed)
        picker.connect('notify::selected', source_changed)
        return page

    def search_channels(self, text):
        sources = list(dict.fromkeys([pl['url'] for pl in self.config['iptv']] + [self.config['iptv_source']]
                                     + list(self._live_cache)))
        words = text.lower().split()

        def fetch():
            out, errors = [], []
            for src in sources:
                try:
                    dead = self.hidden_channels(src)
                    out += [v for v in self.load_channels(src) if all(w in v.title.lower() for w in words)
                            and v.id not in dead]
                except Exception as e:  # noqa: BLE001 - search the sources that work
                    errors.append(clean_error(e))
            if not out and errors:
                raise RuntimeError(errors[0])
            return out

        page = GridPage(self, f'Channels: “{text}”', fetch,
                        empty=('No channels found', 'Try part of the name, e.g. “news” or “sports”.', None))
        self.nav.replace([page])
        self._select_sidebar(None)

    # ---- favourites ---------------------------------------------------------------------
    def set_channel_fav(self, v, on):
        if on == self.lib.has('tvfav', v.id):
            return
        if on:
            self.lib.add('tvfav', v)
            self.toast(f'{v.title} added to favourites')
        else:
            self.lib.remove('tvfav', v.id)
            self.toast(f'{v.title} removed from favourites')
        if self.watch:
            self.watch.refresh_fav()

    def toggle_channel_fav(self, v, card=None):
        on = not self.lib.has('tvfav', v.id)
        self.set_channel_fav(v, on)
        if not on and card and card.page and card.page.list_name == 'tvfav':
            card.page.remove_card(card)

    # ---- playing --------------------------------------------------------------------------
    def play_live(self, v, siblings=None, alt=0):
        inapp = bool(self.config['inapp'] and self.ensure_engine())
        self._leave_live()
        self.play_gen += 1
        gen = self.play_gen
        self.stop_preview()
        self.now_live = {'video': v, 'siblings': list(siblings or []), 'gen': gen, 'started': False, 'alt': alt,
                         'tried': 0}
        if inapp:
            self.engine.stop()
            with self.engine.lock:
                self.engine.queue = [v]
            self.watch.loading = 'wait'
            self.watch.show_video(v)
            self.show_watch()
            if self.config['fullscreen'] and not self.watch.is_fullscreen:
                self.watch.set_fullscreen(True)
        else:
            self.toast(f'Opening {v.title}…', 3)
        self.play_pool.submit(self._live_worker, gen, v, inapp, alt)

    def zap(self, step):
        nl = self.now_live
        if not nl or len(nl['siblings']) < 2:
            return
        ids = [s.id for s in nl['siblings']]
        i = ids.index(nl['video'].id) if nl['video'].id in ids else -1
        self.play_live(nl['siblings'][(i + step) % len(ids)], nl['siblings'])

    def live_sources(self, v):
        return (self.live_index.get(v.id) or {}).get('alts') or []

    def _live_url(self, v, alt=0):
        ch = self.live_index.get(v.id)
        if ch is None:  # a favourite whose list isn't loaded yet this session: try the saved lists
            for path in glob.glob(os.path.join(CHANNELS_DIR, '*.json')):
                src = None
                try:
                    with open(path) as f:
                        src = json.load(f).get('source')
                except (OSError, ValueError):
                    pass
                if src and src not in self._live_cache:
                    try:
                        self.load_channels(src)
                    except Exception:  # noqa: BLE001
                        pass
                if v.id in self.live_index:
                    break
            ch = self.live_index.get(v.id)
        if not ch:
            return v.link, None, None
        a = ch['alts'][alt % len(ch['alts'])]
        return a['url'], a.get('ua'), a.get('referrer')

    def _live_worker(self, gen, v, inapp, alt=0):
        try:
            url, ua, referrer = self._live_url(v, alt)
        except Exception as e:  # noqa: BLE001
            idle(self.load_failed, gen, clean_error(e))
            return
        if gen != self.play_gen:
            return
        cap = LIVE_BITRATE.get(self.config['quality'])
        opts = [f'hls-bitrate={cap or "max"}']
        if referrer:
            opts.append(f'referrer={mpv_quote(referrer)}')
        try:
            if inapp:
                idle(self.watch.ready_to_load, gen)
                self.engine.load(url, 'replace', v.title, ua=ua, opts=opts)
                idle(self._live_watchdog, gen, alt)
            else:
                self.external.ensure(self.current_format(), fullscreen=True)
                self.external.load({'url': url, 'title': v.title, 'ua': ua}, 'replace')
        except Exception as e:  # noqa: BLE001
            idle(self.load_failed, gen, clean_error(e))

    def _live_event(self, name, value):
        nl = self.now_live
        if not nl or not self.watch or self.watch.video is not nl['video']:
            return
        if name == 'time-pos' and value is not None and not nl['started']:
            nl['started'] = True
            gen = nl['gen']

            def check(attempt):  # warn if this channel ended up on the CPU decoder (seen twice, 5 s apart)
                try:
                    hw = self.engine.m.hwdec_current if self.engine.m.video_params else None
                except Exception:  # noqa: BLE001
                    return
                if hw != 'no' or gen != self.play_gen:
                    return  # GPU, audio only, or the decoder still starting: nothing to say
                if attempt == 1:
                    GLib.timeout_add_seconds(5, lambda: (self.play_pool.submit(check, 2), False)[1])
                else:
                    idle(lambda: gen == self.play_gen and self.toast(
                        'This channel is being decoded on the CPU (its format isn’t one the hardware decodes), so it may stutter', 8))

            GLib.timeout_add_seconds(5, lambda: (self.play_pool.submit(check, 1), False)[1])

    def load_failed(self, gen, msg=None):
        """Called when a channel couldn't start (see WatchPage.on_event)."""
        if gen != self.play_gen:
            return
        if self.watch:
            self.watch.loading = False
            self.watch.show_load_error(msg)
        nl = self.now_live
        if nl and nl['tried'] + 1 < len(self.live_sources(nl['video'])):
            # a dead source (common in community playlists): go on to the next one
            n = len(self.live_sources(nl['video']))
            nl['tried'] += 1
            nl['alt'] = (nl['alt'] + 1) % n
            self.toast(f'Source didn’t work, trying source {nl["alt"] + 1} of {n}…', 3)
            if self.watch:
                self.watch.loading, self.watch.load_error = 'wait', False
                self.watch.spinner.set_visible(True)
                self.watch.buffer_label.set_label(f'Trying source {nl["alt"] + 1} of {n}…')
            self.play_pool.submit(self._live_worker, gen, nl['video'], self.watch is not None, nl['alt'])
            return
        if nl and nl['video'].id.startswith('iptv:'):
            self.iptv_dead[nl['video'].id] = time.time()  # every source failed: hide it for a few days
            self._save_iptv_dead()
            if not self.config['iptv_all']:
                msg = (msg or 'no source worked') + f'; hidden from the list for {IPTV_CHECK_DAYS} days'
        if self.now_live:
            self.toast(f'Couldn’t play {self.now_live["video"].title}' + (f': {msg}' if msg else ''), 8)

    def hidden_channels(self, source):
        return {} if self.config['iptv_all'] else self.iptv_dead

    def _save_iptv_dead(self):
        try:
            os.makedirs(os.path.dirname(IPTV_DEAD_FILE), exist_ok=True)
            with open(IPTV_DEAD_FILE, 'w') as f:
                json.dump({'dead': self.iptv_dead, 'checked': self.iptv_checked}, f)
        except OSError:
            pass

    def check_channels(self, source, videos, page):
        """Test every channel of an IPTV list in the background (at most every few days) and hide
        the ones none of whose links answer. Unclear answers count as working."""
        if source in self._checking or time.time() - self.iptv_checked.get(source, 0) < IPTV_CHECK_DAYS * 86400:
            return
        self._checking.add(source)
        if self.check_pool is None:
            self.check_pool = background_pool(4, 'check')
        chans = [(v.id, (self.live_index.get(v.id) or {}).get('alts') or []) for v in videos]

        def one(item):
            vid, alts = item
            verdicts = []
            for a in alts:
                verdict = probe_stream(a)
                if verdict == 'ok':
                    return vid, 'ok'
                verdicts.append(verdict)
            return vid, 'dead' if verdicts and all(v == 'dead' for v in verdicts) else None

        def work():
            futures = [self.check_pool.submit(one, c) for c in chans]
            results = [f.result() for f in futures]
            idle(done, [vid for vid, verdict in results if verdict == 'dead'])

        def done(dead):
            self._checking.discard(source)
            if chans and len(dead) > 0.9 * len(chans) and len(chans) > 30:
                return  # nearly everything failed: more likely our connection than the channels
            now = time.time()
            for vid in dead:
                self.iptv_dead[vid] = now
            self.iptv_checked[source] = now
            self._save_iptv_dead()
            if dead and not self.config['iptv_all'] and self.nav.get_visible_page() is page:
                page.reload()
                self.toast(f'Hid {len(dead)} channel{"s" if len(dead) != 1 else ""} that aren’t working right now '
                           '(⋮ shows them)', 6)

        threading.Thread(target=work, daemon=True).start()

    def _iptv_toggle_all(self):
        self.config['iptv_all'] = not self.config['iptv_all']
        self.save_config()
        self.toast('Showing every channel, working or not' if self.config['iptv_all'] else
                   'Hiding channels that aren’t working', 4)
        self.forget_pages('tv:iptv')
        self.open_section('tv:iptv')

    def _iptv_recheck(self):
        state = getattr(self, '_iptv_state', None)
        if not state:
            return
        source = state['source']
        ids = {v.id for v in state['all']}
        self.iptv_dead = {k: t for k, t in self.iptv_dead.items() if k not in ids}
        self.iptv_checked.pop(source, None)
        self._save_iptv_dead()
        self.toast('Checking every channel in this list again…', 3)
        self.forget_pages('tv:iptv')
        self.open_section('tv:iptv')

    def _live_watchdog(self, gen, alt):
        """A source that opens but never sends a picture counts as dead after 25 s."""
        def check():
            nl = self.now_live
            if (gen == self.play_gen and nl and nl['alt'] == alt and self.watch
                    and self.watch.loading in ('ready', 'opening')):
                self.engine.m.command('stop')
                self.load_failed(gen, 'no picture after 25 s')
            return GLib.SOURCE_REMOVE
        GLib.timeout_add_seconds(25, check)

    def _leave_live(self):
        """Something else plays (or playback stops)."""
        self.now_live = None

    def set_live_source(self, alt):
        nl = self.now_live
        if nl:
            self.play_live(nl['video'], nl['siblings'], alt)

    def add_playlist(self):
        dlg = Adw.AlertDialog(heading='Add IPTV playlist',
                              body='An M3U / M3U8 playlist link from your IPTV provider, or a playlist file.')
        box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=8)
        name = Gtk.Entry(placeholder_text='Name (e.g. My IPTV)')
        url = Gtk.Entry(placeholder_text='https://…/playlist.m3u', hexpand=True, activates_default=True)
        pick = Gtk.Button(icon_name='document-open-symbolic', tooltip_text='Choose a playlist file')
        row = Gtk.Box(spacing=6)
        row.append(url)
        row.append(pick)
        box.append(name)
        box.append(row)
        dlg.set_extra_child(box)

        def choose(*_):
            def done(d, res):
                try:
                    url.set_text(d.open_finish(res).get_path())
                except GLib.Error:
                    pass
            Gtk.FileDialog(title='Choose a playlist', filters=self._file_filter(
                'Playlists', ['*.m3u', '*.m3u8', '*.M3U', '*.M3U8'])).open(self, None, done)

        pick.connect('clicked', choose)
        dlg.add_response('cancel', 'Cancel')
        dlg.add_response('add', 'Add')
        dlg.set_response_appearance('add', Adw.ResponseAppearance.SUGGESTED)
        dlg.set_default_response('add')
        dlg.connect('response', lambda _d, r: r == 'add' and self._add_playlist(name.get_text().strip(),
                                                                                  url.get_text().strip()))
        dlg.present(self)

    def _add_playlist(self, name, url):
        if not url:
            return
        self.toast('Checking the playlist…', 2)

        def work():
            try:
                n, err = len(self.load_channels(url, force=True)), None
            except Exception as e:  # noqa: BLE001
                n, err = 0, clean_error(e)
            idle(done, n, err)

        def done(n, err):
            if not n:
                self.toast(f'Couldn’t read that playlist: {err}' if err else 'No channels found in that playlist', 8)
                return
            label = name or (os.path.basename(url.split('?')[0]) or 'IPTV').rsplit('.', 1)[0] or 'IPTV'
            self.config['iptv'].append({'name': label, 'url': url})
            self.config['iptv_source'] = url
            self.save_config()
            self.forget_pages('tv:iptv')
            self.open_section('tv:iptv')
            self.toast(f'Added {label}: {n} channels', 4)

        self.search_pool.submit(work)

    def remove_playlist(self, i):
        pl = self.config['iptv'][i]

        def remove():
            self.config['iptv'] = [p for p in self.config['iptv'] if p['url'] != pl['url']]
            if self.config['iptv_source'] == pl['url']:
                self.config['iptv_source'] = IPTV_DEFAULT
            self.save_config()
            self.forget_channels(pl['url'])
            self.forget_pages('tv:iptv')
            lb, row = self.lists.get('tv:iptv', (None, None))
            if lb is not None and lb.get_selected_row() is row:
                self.open_section('tv:iptv')  # it's on screen: show the change now
            self.toast(f'Removed {pl["name"]}')

        self.confirm(f'Remove “{pl["name"]}”?', 'Its favourite channels stay in Favourites.', 'Remove', remove)

    def _live_actions(self):
        for name, cb in (('iptv-all', self._iptv_toggle_all), ('iptv-recheck', self._iptv_recheck)):
            a = Gio.SimpleAction.new(name, None)
            a.connect('activate', lambda *_a, cb=cb: cb())
            self.add_action(a)


CSS = f"""
.tl-thumb {{ border-radius: 10px; background-color: alpha(currentColor, 0.08); }}
.tl-badge {{ background-color: rgba(0, 0, 0, 0.78); color: white; border-radius: 5px;
            padding: 1px 6px; font-size: 0.8em; font-weight: bold; font-feature-settings: "tnum"; }}
.tl-badge.live {{ background-color: {YT_RED}; }}
.tl-title {{ font-weight: 600; }}
.tl-section {{ font-weight: bold; font-size: 0.85em; opacity: 0.6; margin: 12px 12px 2px 12px; }}
.tl-subscribe {{ background-color: {YT_RED}; color: white; }}
flowboxchild.tl-card {{ padding: 6px; border-radius: 14px; }}
flowboxchild.tl-card:hover {{ background-color: alpha(currentColor, 0.06); }}
flowboxchild.tl-row {{ padding: 4px; border-radius: 10px; }}
flowboxchild.tl-row .tl-title {{ font-size: 1.2em; font-weight: 700; line-height: 1.2; }}
.tl-watch-title {{ font-size: 1.7em; font-weight: 800; line-height: 1.25; }}

/* 2012-style player */
.tl-player {{ background-color: black; border-radius: 12px; }}
.tl-player.fullscreen {{ border-radius: 0; }}
.tl-player-bar {{ background-image: linear-gradient(to bottom, rgba(0,0,0,0), rgba(0,0,0,0.75) 35%, rgba(0,0,0,0.92));
                 padding: 14px 6px 2px 6px; color: #d8d8d8; }}
.tl-progress {{ padding: 6px 0; margin: 0 2px; }}
.tl-progress trough {{ min-height: 4px; border-radius: 0; background-color: rgba(255,255,255,0.2); }}
.tl-progress trough fill {{ min-height: 4px; border-radius: 0; background-color: rgba(255,255,255,0.45); }}
.tl-progress trough highlight {{ min-height: 4px; border-radius: 0; background-color: {YT_RED}; }}
.tl-progress slider {{ min-width: 14px; min-height: 14px; margin: -6px; border-radius: 50%; border: none;
                      background-color: white; box-shadow: 0 0 4px rgba(0,0,0,0.7); outline: none; }}
.tl-progress:hover trough, .tl-progress:hover trough fill, .tl-progress:hover trough highlight {{ min-height: 7px; }}
.tl-controls button {{ color: #c8c8c8; background: none; min-width: 34px; min-height: 30px; padding: 2px;
                      border-radius: 3px; box-shadow: none; }}
.tl-controls button:hover {{ color: white; background-color: rgba(255,255,255,0.12); }}
.tl-controls button:checked {{ color: {YT_RED}; background: none; }}
.tl-volume trough {{ min-height: 4px; border-radius: 0; background-color: rgba(255,255,255,0.25); }}
.tl-volume trough highlight {{ border-radius: 0; background-color: {YT_RED}; }}
.tl-volume slider {{ min-width: 5px; min-height: 15px; margin: -6px -2px; border-radius: 1px; border: none;
                    background-color: white; box-shadow: none; outline: none; }}
.tl-time {{ color: #e8e8e8; font-feature-settings: "tnum"; font-size: 0.92em; margin: 0 10px; }}
.tl-brand {{ color: white; font-weight: 800; font-size: 14px; letter-spacing: -0.3px; margin: 0 8px; }}
.tl-stats {{ background-color: rgba(28,28,28,0.82); color: #f0f0f0; padding: 8px 12px; border-radius: 4px;
             font-family: "DejaVu Sans Mono", monospace; font-size: 11.5px; }}
.tl-stats-title {{ font-weight: bold; font-size: 12px; }}
.tl-stats-key {{ font-weight: bold; color: #ffffff; }}
.tl-stats-val {{ color: #e6e6e6; }}
.tl-stats-bad {{ color: #ff6b6b; font-weight: bold; }}
.tl-stats-btn {{ background: none; color: #cfcfcf; min-height: 0; padding: 0 4px; font-size: 11px; box-shadow: none; }}
.tl-stats-btn:checked {{ color: #7fd4ff; }}
.tl-stats-bar trough {{ min-height: 8px; background-color: rgba(255,255,255,0.15); border-radius: 0; border: none; }}
.tl-stats-bar block.filled {{ background-color: #7fd4ff; border-radius: 0; }}
.tl-logo {{ padding: 2px 6px; }}
.tl-logo-name {{ font-weight: 800; font-size: 18px; letter-spacing: -0.4px; }}
.tl-fs-title {{ color: white; font-size: 1.15em; font-weight: bold; padding: 14px 18px 30px 18px;
               background-image: linear-gradient(to top, rgba(0,0,0,0), rgba(0,0,0,0.8)); }}

/* channels */
.tl-buffer {{ color: white; font-weight: bold; background-color: rgba(0,0,0,0.6); border-radius: 6px;
             padding: 4px 12px; font-feature-settings: "tnum"; }}
.tl-logo-tile {{ background-color: alpha(currentColor, 0.05); padding: 10px; }}
"""

GOOGLE_SECTIONS = [('g:home', 'Home', 'go-home-symbolic'), ('g:subs', 'Subscriptions', 'view-list-symbolic'),
                   ('g:liked', 'Liked videos', 'emblem-favorite-symbolic'), ('g:later', 'Watch later', 'alarm-symbolic'),
                   ('g:playlists', 'Playlists', 'view-list-bullet-symbolic'),
                   ('g:history', 'History', 'document-open-recent-symbolic')]
LOCAL_SECTIONS = [('l:foryou', 'For you', 'starred-symbolic'), ('shorts', 'Shorts', 'phone-symbolic'),
                  ('l:subs', 'Subscriptions', 'view-list-symbolic'), ('l:liked', 'Liked', 'emblem-favorite-symbolic'),
                  ('l:later', 'Watch later', 'alarm-symbolic'), ('l:playlists', 'Playlists', 'view-list-bullet-symbolic'),
                  ('l:history', 'History', 'document-open-recent-symbolic'),
                  ('downloads', 'Downloads', 'folder-download-symbolic')]


class Window(LiveMixin, Adw.ApplicationWindow):
    def __init__(self, app):
        super().__init__(application=app, title='Smedio', default_width=1180, default_height=740, maximized=True)
        self.set_size_request(400, 360)
        self.app = app
        self.config = self._load_config()
        global CAPTION_PREF
        CAPTION_PREF = self.config['yt_captions']
        self.lib = Library(DB_FILE)
        self.yt = Lookups()
        self.yt.set_browser(self.config['browser'])
        self.external = ExternalPlayer()
        self.engine = None
        self.engine_error = None
        self.watch = None
        self.downloads = Downloads(self)
        self.search_pool = background_pool(4, 'search')  # page loads: mostly waiting on the network
        self.feed_pool = background_pool(6, 'feed')
        self.resolve_pool = background_pool(2, 'resolve', confine=False)  # you're waiting on these
        self.preload_pool = background_pool(2, 'preload')
        self.upcoming_pool = background_pool(1, 'upcoming')
        self.play_pool = ThreadPoolExecutor(2, thread_name_prefix='play')
        self.thumb_pool = background_pool(6, 'thumb')
        self.upcoming, self._inflight = [], 0   # Shorts still to queue; lookups in progress
        self.resolved = {}       # (video id, format) -> (future, created)
        self.preview = None      # (card, AnimClip | PreviewClip) playing on hover
        self._rss_refreshing = False
        self._preloading = set()
        self.prefetching = None
        self.play_gen = 0
        self._hover_card = None
        self._hover_src = 0
        self._dwell_src = 0
        self._sidebar_before_fs = True
        self.search_mode = 'youtube'
        self._live_init()
        self._migrate_iptv()

        # Header
        self.entry = Gtk.SearchEntry(placeholder_text='Search YouTube or paste a link', hexpand=True)
        self.entry.connect('activate', self._on_search)
        self.entry.set_key_capture_widget(self)
        header = Adw.HeaderBar(title_widget=Adw.Clamp(maximum_size=620, child=self.entry))
        self.sidebar_btn = Gtk.ToggleButton(icon_name='sidebar-show-symbolic', tooltip_text='Sidebar', active=True)
        header.pack_start(self.sidebar_btn)
        self.back_btn = Gtk.Button(icon_name='go-previous-symbolic', tooltip_text='Back (Alt+←)', visible=False)
        self.back_btn.connect('clicked', lambda *_: self.nav.pop())
        header.pack_start(self.back_btn)
        menu = Gio.Menu()
        look = Gio.Menu()
        for label, value in (('Follow system style', 'system'), ('Light', 'light'), ('Dark', 'dark')):
            look.append(label, f'win.theme::{value}')
        menu.append_section(None, look)
        menu.append('Preferences', 'app.preferences')
        menu.append('Update yt-dlp', 'app.update')
        menu.append('About Smedio', 'app.about')
        header.pack_end(Gtk.MenuButton(icon_name='open-menu-symbolic', menu_model=menu, primary=True,
                                       tooltip_text='Menu'))
        self.audio_btn = Gtk.ToggleButton(icon_name='audio-x-generic-symbolic',
                                          tooltip_text='Audio only: no video, uses far less data',
                                          active=self.config['audio_only'])
        self.audio_btn.connect('toggled', self._on_settings_changed)
        header.pack_end(self.audio_btn)
        self.theme_btn = Gtk.Button()
        self.theme_btn.connect('clicked', lambda *_: self.set_theme('light' if Adw.StyleManager.get_default().get_dark()
                                                                    else 'dark'))
        header.pack_end(self.theme_btn)
        theme = Gio.SimpleAction.new_stateful('theme', GLib.VariantType.new('s'), GLib.Variant('s', self.config['theme']))
        theme.connect('activate', lambda _a, value: self.set_theme(value.get_string()))
        self.add_action(theme)
        Adw.StyleManager.get_default().connect('notify::dark', lambda *_: self._update_theme_button())
        self.set_theme(self.config['theme'])
        self.quality = Gtk.DropDown.new_from_strings([f'{q}p' for q in qualities()])
        self.quality.set_tooltip_text('Video quality (H.264, GPU decoded)')
        self.quality.set_selected(qualities().index(self.config['quality']))
        self.quality.connect('notify::selected', self._on_settings_changed)
        header.pack_end(self.quality)

        # Content: navigation stack, toasts, and a "now playing" bar when the video is off-screen
        self.nav = Adw.NavigationView()
        self.nav.connect('notify::visible-page', self._on_page_changed)
        self.toasts = Adw.ToastOverlay(child=self.nav)
        self.content = Adw.ToolbarView(content=self.toasts)
        self.content.add_top_bar(header)
        self.banner = Adw.Banner(revealed=False)
        self._banner_action = None
        self.banner.connect('button-clicked', lambda b: (b.set_revealed(False),
                                                         self._banner_action and self._banner_action()))
        self.content.add_top_bar(self.banner)
        self._importing = False
        self.mini_title = Gtk.Label(xalign=0, hexpand=True, ellipsize=Pango.EllipsizeMode.END)
        self.mini_play = Gtk.Button(icon_name='media-playback-pause-symbolic', tooltip_text='Play / pause')
        self.mini_play.connect('clicked', lambda *_: self.engine and setattr(self.engine.m, 'pause',
                                                                             not self.engine.m.pause))
        open_btn = Gtk.Button(icon_name='view-fullscreen-symbolic', tooltip_text='Back to the video')
        open_btn.connect('clicked', lambda *_: self.show_watch())
        close_btn = Gtk.Button(icon_name='window-close-symbolic', tooltip_text='Stop')
        close_btn.connect('clicked', lambda *_: self.stop_playback())
        mini = Gtk.Box(spacing=6, margin_start=12, margin_end=6, margin_top=4, margin_bottom=4)
        mini.append(Gtk.Image(icon_name='media-playback-start-symbolic'))
        mini.append(self.mini_title)
        for b in (self.mini_play, open_btn, close_btn):
            b.add_css_class('flat')
            mini.append(b)
        self.mini = Gtk.Revealer(child=mini, reveal_child=False)
        self.content.add_bottom_bar(self.mini)

        # Sidebar
        self.sidebar_box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)
        self.lists = {}
        self._pages = {}  # sections whose content comes from the internet: shown as you left them
        self._build_sidebar()
        sidebar_view = Adw.ToolbarView(content=Gtk.ScrolledWindow(child=self.sidebar_box,
                                                                  hscrollbar_policy=Gtk.PolicyType.NEVER))
        logo_box = Gtk.Box(spacing=8)
        logo_box.append(logo_image(24))
        name = Gtk.Label(label='Smedio')
        name.add_css_class('tl-logo-name')
        logo_box.append(name)
        logo = Gtk.Button(child=logo_box, tooltip_text='Home')
        logo.add_css_class('flat')
        logo.add_css_class('tl-logo')
        logo.connect('clicked', lambda *_: self.open_section('g:home' if self.config['browser'] else 'l:foryou'))
        sidebar_header = Adw.HeaderBar(show_title=False)
        sidebar_header.pack_start(logo)
        sidebar_view.add_top_bar(sidebar_header)
        self.split = Adw.OverlaySplitView(sidebar=sidebar_view, content=self.content, min_sidebar_width=190,
                                          max_sidebar_width=230)
        self.sidebar_btn.bind_property('active', self.split, 'show-sidebar',
                                       GObject.BindingFlags.BIDIRECTIONAL | GObject.BindingFlags.SYNC_CREATE)
        bp = Adw.Breakpoint.new(Adw.BreakpointCondition.parse('max-width: 860sp'))
        bp.add_setter(self.split, 'collapsed', True)
        self.add_breakpoint(bp)
        self.set_content(self.split)

        focus = Gio.SimpleAction.new('focus-search', None)
        focus.connect('activate', lambda *_: self.entry.grab_focus())
        self.add_action(focus)
        keys = Gtk.EventControllerKey(propagation_phase=Gtk.PropagationPhase.CAPTURE)
        keys.connect('key-pressed', self._on_key)
        self.add_controller(keys)
        self.connect('notify::fullscreened', self._on_fullscreened)

        self._live_actions()
        self.search_pool.submit(self.yt.warm_up)
        self.thumb_pool.submit(self._prune_thumbs)
        self.open_section('g:home' if self.config['browser'] else 'l:foryou')

    # ---- settings ----------------------------------------------------------------
    @staticmethod
    def _load_config():
        cfg = {'quality': 720, 'audio_only': False, 'inapp': True, 'fullscreen': False, 'hover_preview': True,
               'preload_previews': False, 'sponsorblock': True, 'browser': None, 'download_dir': DEFAULT_DOWNLOAD_DIR, 'volume': 100,
               'iptv': [], 'iptv_source': IPTV_DEFAULT, 'iptv_all': False, 'list_order': {},
               'theme': 'system', 'yt_captions': ''}
        try:
            with open(CONFIG_FILE) as f:
                cfg.update(json.load(f))
        except (OSError, ValueError):
            pass
        if cfg['quality'] not in qualities():
            cfg['quality'] = 720
        if cfg['browser'] not in BROWSERS:
            cfg['browser'] = None
        return cfg

    def save_config(self):
        try:
            os.makedirs(CONFIG_DIR, exist_ok=True)
            with open(CONFIG_FILE, 'w') as f:
                json.dump(self.config, f, indent=1)
        except OSError:
            pass

    def _on_settings_changed(self, *_):
        self.config['quality'] = qualities()[self.quality.get_selected()]
        self.config['audio_only'] = self.audio_btn.get_active()
        self.save_config()

    def current_format(self, audio=None):
        audio = self.config['audio_only'] if audio is None else audio
        return AUDIO_FORMAT if audio else video_format(self.config['quality'])

    def set_browser(self, browser):
        self.config['browser'] = browser
        self.save_config()
        self.yt.set_browser(browser)
        self._pages.clear()  # another account: nothing saved still applies
        shutil.rmtree(PAGES_DIR, ignore_errors=True)
        self._build_sidebar()
        self.open_section('g:home' if browser else 'l:foryou')

    def toast(self, text, timeout=3, button=None, action=None):
        t = Adw.Toast(title=GLib.markup_escape_text(text), timeout=timeout)
        if button and action:
            t.set_button_label(button)
            t.connect('button-clicked', lambda *_: action())
        self.toasts.add_toast(t)

    def error_hint(self):
        if self.config['browser']:
            name = BROWSERS[self.config['browser']][0]
            return (f'If this is a YouTube account page: make sure you are signed in to YouTube in {name}. '
                    'Otherwise check your connection, or try Menu → Update yt-dlp.')
        return 'Check your connection, or try Menu → Update yt-dlp.'

    # ---- sidebar & navigation ----------------------------------------------------
    def _build_sidebar(self):
        while (child := self.sidebar_box.get_first_child()):
            self.sidebar_box.remove(child)
        self.lists = {}
        groups = []
        if self.config['browser']:
            groups.append((f'YouTube · {BROWSERS[self.config["browser"]][0]}', GOOGLE_SECTIONS))
        groups.append(('YouTube · local', LOCAL_SECTIONS))
        groups.append(('Live TV', self.live_sections()))
        for title, sections in groups:
            label = Gtk.Label(label=title, xalign=0, ellipsize=Pango.EllipsizeMode.END)
            label.add_css_class('tl-section')
            self.sidebar_box.append(label)
            lb = Gtk.ListBox(selection_mode=Gtk.SelectionMode.SINGLE)
            lb.add_css_class('navigation-sidebar')
            for key, name, icon in sections:
                row = Gtk.ListBoxRow()
                row.key = key
                box = Gtk.Box(spacing=12, margin_start=6, margin_top=2, margin_bottom=2)
                box.append(Gtk.Image(icon_name=icon))
                box.append(Gtk.Label(label=name, xalign=0))
                row.set_child(box)
                lb.append(row)
                self.lists[key] = (lb, row)
            lb.connect('row-activated', lambda _lb, row: self.open_section(row.key))
            self.sidebar_box.append(lb)

    def _select_sidebar(self, key):
        for k, (lb, row) in self.lists.items():
            if k == key:
                lb.select_row(row)
        for lb in {lb for lb, _ in self.lists.values()}:
            sel = lb.get_selected_row()
            if sel is not None and getattr(sel, 'key', None) != key:
                lb.unselect_all()

    def _watch_visible(self):
        return self.watch is not None and self.nav.get_visible_page() is self.watch

    def _on_page_changed(self, *_):
        self.back_btn.set_visible(self.nav.get_navigation_stack().get_n_items() > 1)
        self.stop_preview()
        watching = self._watch_visible()
        # Typing should search everywhere except on the player, where letters are shortcuts.
        self.entry.set_key_capture_widget(None if watching else self)
        if not watching and self.watch and self.watch.is_fullscreen:
            self.watch.set_fullscreen(False)
        self._update_mini()

    def _update_mini(self):
        playing = (self.engine is not None and self.watch is not None and self.watch.video is not None
                   and not self.engine.m.idle_active)
        self.mini.set_reveal_child(playing and not self._watch_visible())
        if playing:
            self.mini_title.set_label(self.watch.video.title)

    def open_section(self, key):
        self.set_search_mode('live' if key.startswith('tv:') else 'youtube')
        page = self._pages.get(key)
        if page is None:
            page = self._make_section(key)
            if key in ('l:foryou', 'shorts', 'l:subs', 'tv:iptv') or \
                    key.startswith('g:'):
                self._pages[key] = page  # your own lists (Liked, History…) are always rebuilt fresh
        self.nav.replace([page])
        self._select_sidebar(key)
        if self.split.get_collapsed():
            self.split.set_show_sidebar(False)

    def set_search_mode(self, mode):
        self.search_mode = mode
        self.entry.set_placeholder_text('Search channels' if mode == 'live' else 'Search YouTube or paste a link')

    def stop_playback(self):
        self._leave_live()
        if self.engine:
            self.engine.stop()

    def push(self, page):
        self.nav.push(page)

    def forget_pages(self, *prefixes):
        for key in [k for k in self._pages if k.startswith(prefixes)]:
            del self._pages[key]

    def _make_section(self, key):
        lib, yt = self.lib, self.yt
        if key.startswith('tv:'):
            return self._make_live_section(key)
        if key.startswith('g:'):
            name, title, limit = {'g:home': ('home', 'Home', 60), 'g:subs': ('subs', 'Subscriptions', 60),
                                  'g:liked': ('liked', 'Liked videos', 200), 'g:later': ('later', 'Watch later', 200),
                                  'g:playlists': ('playlists', 'Playlists', None),
                                  'g:history': ('history', 'History', 60)}[key]
            return GridPage(self, title, lambda: yt.feed(name, limit), cache_key=key)
        if key == 'l:foryou':
            ref, state = {}, {}  # more as you scroll: recommend_more() continues the feed
            ref['page'] = GridPage(
                self, 'For you', lambda: (state.clear(), recommend(lib, yt, self.feed_pool))[1], cache_key='l:foryou',
                more=lambda _n: recommend_more(lib, yt, self.feed_pool, [c.video for c in ref['page'].cards], state),
                empty=('Nothing to recommend yet',
                       'Watch, like or subscribe to a few things and Smedio will learn what you like — '
                       'all on this device. Or bring your subscriptions and likes from Google.',
                       self._onboarding_buttons))
            return ref['page']
        if key == 'shorts':
            return GridPage(self, 'Shorts', self._shorts_fetch, vertical=True, cache_key='shorts',
                            empty=('No Shorts found', 'Subscribe to channels or watch a few videos first.', None))
        if key == 'l:subs':
            channels = Gtk.Button(child=Adw.ButtonContent(label='Channels', icon_name='system-users-symbolic'))
            channels.connect('clicked', lambda *_: self.push(GridPage(
                self, 'Your channels', lambda: [Video(s['channel_id'], s['name'], kind='channel', link=s['url'],
                                                      channel=s['name'], channel_id=s['channel_id'],
                                                      channel_url=s['url']) for s in lib.subs()],
                empty=('No subscriptions yet', 'Open a channel and press Subscribe.', None))))
            ref = {}
            ref['page'] = GridPage(self, 'Subscriptions', lambda: self._local_subs_feed(ref), actions=[channels], keep=True,
                                   empty=('No subscriptions yet',
                                          'Open a channel and press Subscribe, or import your subscriptions.',
                                          self._onboarding_buttons))
            return ref['page']
        if key == 'l:liked':
            return self._list_page('Liked', 'liked', 'Liked',
                                   ('No liked videos', 'Press Like under a video, or use its ⋮ menu.', None))
        if key == 'l:later':
            return self._list_page('Watch later', 'later', 'Watch later',
                                   ('Nothing saved', 'Use the clock button in the player, or ⋮ → Save to Watch later.',
                                    None))
        if key == 'l:playlists':
            new = Gtk.Button(child=Adw.ButtonContent(label='New playlist', icon_name='list-add-symbolic'))
            page = GridPage(self, 'Playlists', lib.playlists, actions=[new],
                            empty=('No playlists', 'Use Save under a video, or ⋮ → Save to playlist…', None))
            new.connect('clicked', lambda *_: self.ask_text('New playlist', 'Name', 'Create',
                                                            lambda name: (lib.create_playlist(name), page.reload())))
            return page
        if key == 'l:history':
            clear = Gtk.Button(child=Adw.ButtonContent(label='Clear', icon_name='user-trash-symbolic'))
            page = GridPage(self, 'History', lambda: lib.history(300), list_name='history', list_label='History',
                            actions=[clear], empty=('No history', 'Videos you play show up here.', None))
            clear.connect('clicked', lambda *_: self.confirm(
                'Clear watch history?', 'This also resets what “For you” has learned from it.', 'Clear',
                lambda: (lib.clear_history(), page.reload())))
            return page
        if key == 'downloads':
            return DownloadsPage(self)
        raise KeyError(key)

    def _onboarding_buttons(self):
        box = Gtk.Box(spacing=12, halign=Gtk.Align.CENTER)
        b1 = Gtk.Button(label='Copy from my YouTube account…')
        b1.add_css_class('pill')
        b1.add_css_class('suggested-action')
        b1.connect('clicked', lambda *_: self.show_preferences())
        b2 = Gtk.Button(label='Import Google Takeout file…')
        b2.add_css_class('pill')
        b2.connect('clicked', lambda *_: self.import_takeout())
        box.append(b1)
        box.append(b2)
        return box

    def _local_subs_feed(self, page_ref):
        """Uploads from local subscriptions. Shown straight from the cache; only channels never
        fetched before are waited for, and out-of-date ones refresh in the background."""
        subs, now = self.lib.subs(), time.time()
        out, missing, stale = [], [], []
        for s in subs:
            videos, fetched = self.yt.rss_cached(s['channel_id'])
            if videos is None:
                missing.append(s['channel_id'])
                continue
            out.extend(videos)
            if now - fetched >= self.yt.rss_ttl(videos):
                stale.append(s['channel_id'])
        if len(out) < 30 and missing:
            # Nothing much cached yet (first visit): wait for a first batch of channels only.
            first, missing = missing[:60], missing[60:]
            try:
                for fut in as_completed([self.feed_pool.submit(self.yt.rss_fetch, c) for c in first], timeout=90):
                    try:
                        out.extend(fut.result())
                    except Exception:  # noqa: BLE001 - skip channels whose feed failed
                        pass
            except FutureTimeout:
                pass
        if subs and not out:
            raise RuntimeError('Couldn’t reach YouTube’s channel feeds')
        stale = missing + stale  # everything else fills in in the background
        if stale and not self._rss_refreshing:
            self._rss_refreshing = True
            threading.Thread(target=self._refresh_stale_rss, args=(stale, {v.id for v in out}, page_ref),
                             daemon=True).start()
        out.sort(key=lambda v: v.published or 0, reverse=True)
        return [v for v in out if not v.short][:150]

    def _refresh_stale_rss(self, channel_ids, known, page_ref):
        new = 0
        for fut in as_completed([self.feed_pool.submit(self.yt.rss_fetch, c) for c in channel_ids]):
            try:
                new += sum(1 for v in fut.result() if v.id not in known and not v.short)
            except Exception:  # noqa: BLE001
                pass
        self._rss_refreshing = False
        page = page_ref.get('page')

        def done():
            if new and page is not None and self.nav.get_visible_page() is page:
                self.toast(f'{new} new video{"s" if new > 1 else ""} from your subscriptions', 8,
                           button='Show', action=page.reload)

        idle(done)

    def _shorts_fetch(self):
        google_channels = []
        if self.config['browser']:
            try:
                google_channels = [c.link for c in self.yt.feed('channels', 30) if c.kind == 'channel']
            except Exception:  # noqa: BLE001
                pass
        return shorts_feed(self.lib, self.yt, self.feed_pool, google_channels)

    # ---- searching & opening things ------------------------------------------------
    def _on_search(self, entry):
        text = entry.get_text().strip()
        if not text:
            return
        if re.match(r'https?://|(www\.|m\.)?(youtube\.com|youtu\.be)/', text):
            m = VIDEO_URL_RE.search(text)
            if m:
                self.play(Video(m.group(1)))
            else:
                self.open_listing(text if text.startswith('http') else 'https://' + text)
            return
        if self.search_mode == 'live':
            self.search_channels(text)
            return
        anims = {}

        def fetch():
            moving = self.feed_pool.submit(self.yt.moving_thumbs, text)
            items = self.yt.search(text, PAGE)
            try:
                anims.update(moving.result(timeout=8))
            except Exception:  # noqa: BLE001 - animated thumbnails are optional
                pass
            return self._with_anims(items, anims)

        page = GridPage(self, f'Results for “{text}”', fetch,
                        more=lambda n: self._with_anims(self.yt.search(text, n), anims))
        self.nav.replace([page])
        self._select_sidebar(None)

    @staticmethod
    def _with_anims(items, anims):
        for v in items:
            v.anim = anims.get(v.id)
        return items

    def open_listing(self, url, title=None):
        def fetch():
            res = self.yt.listing(url, 100)
            idle(page.title_label.set_label, title or res['title'])
            return res['items']

        page = GridPage(self, title or 'Loading…', fetch)
        self.push(page)

    def open_channel(self, v):
        url = v.channel_link or (v.link if v.kind == 'channel' else None)
        if not url:
            self.toast('Channel unknown for this video')
            return
        holder = {'id': v.channel_id, 'name': v.channel or v.title, 'url': url}

        def fetch():
            res = self.yt.listing(url, 60)
            holder['id'] = holder['id'] or res['channel_id']
            holder['name'] = res['title'] or holder['name']
            idle(lambda: (page.title_label.set_label(holder['name']), sub.refresh()))
            return res['items']

        sub = SubscribeButton(self, lambda: (holder['id'], holder['name'], holder['url']))
        shorts = Gtk.Button(child=Adw.ButtonContent(label='Shorts', icon_name='phone-symbolic'))
        shorts.connect('clicked', lambda *_: self.push(GridPage(
            self, f'Shorts · {holder["name"]}', lambda: self.yt.channel_shorts(url, 60), vertical=True)))
        page = GridPage(self, holder['name'] or 'Channel', fetch, actions=[shorts, sub])
        self.push(page)

    def open_local_playlist(self, name):
        self.push(self._list_page(name, 'pl:' + name, name, ('Empty playlist', 'Use Save under any video.', None)))

    def _list_page(self, title, lst, label, empty):
        """Liked, Watch later and playlists: shuffled by default (or newest / oldest first), the
        whole list loading as you scroll. Clicking a video keeps playing the rest in this order."""
        orders = [('shuffle', 'Shuffled'), ('newest', 'Newest first'), ('oldest', 'Oldest first')]
        state = {'order': self.config['list_order'].get(lst, 'shuffle'), 'items': []}
        if state['order'] not in [k for k, _ in orders]:
            state['order'] = 'shuffle'
        sort = Gtk.DropDown.new_from_strings([name for _, name in orders])
        sort.set_selected([k for k, _ in orders].index(state['order']))
        sort.set_valign(Gtk.Align.CENTER)
        sort.set_tooltip_text('Order (↻ shuffles again)')
        play_all = Gtk.Button(child=Adw.ButtonContent(label='Play all'), valign=Gtk.Align.CENTER)
        play_all.add_css_class('suggested-action')

        def update_button():
            play_all.get_child().set_icon_name('media-playlist-shuffle-symbolic' if state['order'] == 'shuffle'
                                               else 'media-playback-start-symbolic')

        def fetch():
            items = self.lib.items(lst, limit=1_000_000)
            if state['order'] == 'shuffle':
                random.shuffle(items)
            elif state['order'] == 'oldest':
                items.reverse()
            state['items'] = items
            return items[:LIST_FIRST]

        page = GridPage(self, title, fetch, more=lambda n: state['items'][:n], list_name=lst, list_label=label,
                        actions=[sort, play_all], empty=empty)
        page.play_queue = lambda: state['items']

        def changed(*_):
            state['order'] = orders[sort.get_selected()][0]
            self.config['list_order'][lst] = state['order']
            self.save_config()
            update_button()
            page.reload()

        sort.connect('notify::selected', changed)
        play_all.connect('clicked', lambda *_: state['items'] and self.play(
            state['items'][0], playlist=state['items'][1:1 + QUEUE_MAX]))
        update_button()
        return page

    def activate_card(self, card):
        v = card.video
        if v.kind == 'video':
            page = card.page
            if v.short and page and page.vertical:
                videos = [c.video for c in page.cards]
                i = videos.index(v)
                self.play(v, playlist=videos[i + 1:i + 16])
            elif page is not None and page.play_queue:  # a list: carry on with the rest of it
                videos = page.play_queue()
                ids = [x.id for x in videos]
                i = ids.index(v.id) if v.id in ids else len(ids)
                self.play(v, playlist=videos[i + 1:i + 1 + QUEUE_MAX])
            else:
                self.play(v)
        elif v.kind == 'channel':
            self.open_channel(v)
        elif v.kind == 'playlist':
            self.open_listing(v.url, v.title)
        elif v.kind == 'localpl':
            self.open_local_playlist(v.title)
        elif v.kind == 'live':
            self.play_live(v, [c.video for c in card.page.cards] if card.page else
                           (self.now_live or {}).get('siblings'))

    # ---- thumbnails ----------------------------------------------------------------
    def load_thumb(self, card):
        v = card.video

        def work():
            try:
                tex = fetch_image(v.thumb_urls(card.vertical), v.thumb_path(card.vertical))
            except Exception:  # noqa: BLE001 - a missing thumbnail is not worth an error
                return
            if tex:
                idle(card.set_texture, tex)

        self.thumb_pool.submit(work)

    @staticmethod
    def _prune_thumbs():
        cutoff = time.time() - 14 * 86400
        for path in glob.glob(os.path.join(THUMB_DIR, '*.jpg')):
            try:
                if os.path.getmtime(path) < cutoff:
                    os.unlink(path)
            except OSError:
                pass

    # ---- hover previews ------------------------------------------------------------
    # Touching a card first shows YouTube's animated thumbnail (when the search provided
    # one: instant, ~200 KB). Resting on it starts the normal stream lookup (~4 s), which
    # then plays a muted 240p clip in the thumbnail and makes a click start immediately.
    def preload_previews(self, cards):
        if not self.config['preload_previews']:
            return
        fmt = self.current_format()
        wanted = [c.video for c in cards if c.video.kind == 'video' and not c.video.live][:8]
        for fut in list(self._preloading):
            if not fut.running() and not fut.done():
                fut.cancel()
        self._preloading = {self._lookup(v, fmt, self.preload_pool, background=True) for v in wanted}

    def _video_on_screen(self):
        return bool(self.engine and self._watch_visible() and not self.engine.m.idle_active
                    and not self.engine.m.pause)

    def hover_start(self, card):
        self._hover_card = card
        self._cancel_hover_timers()
        if not self.config['hover_preview'] or card.video.live or self._video_on_screen():
            return  # while a video plays, keep the CPU for it: no previews or lookups
        if card.video.anim:
            self._hover_src = GLib.timeout_add(80, self._hover_anim_fire, card)
        self._dwell_src = GLib.timeout_add(350, self._hover_dwell_fire, card)

    def hover_end(self, card):
        if self._hover_card is card:
            self._hover_card = None
            self._cancel_hover_timers()
        self.stop_preview(card)

    def _cancel_hover_timers(self):
        for attr in ('_hover_src', '_dwell_src'):
            src = getattr(self, attr)
            if src:
                GLib.source_remove(src)
                setattr(self, attr, 0)

    def _hover_anim_fire(self, card):
        self._hover_src = 0
        if card is not self._hover_card:
            return GLib.SOURCE_REMOVE
        url, path = card.video.anim, os.path.join(THUMB_DIR, f'{card.video.id}_anim.webp')

        def work():
            try:
                if not os.path.exists(path):
                    os.makedirs(THUMB_DIR, exist_ok=True)
                    data = http_get(url)
                    with open(path + '.tmp', 'wb') as f:
                        f.write(data)
                    os.replace(path + '.tmp', path)
                gi.require_version('GdkPixbuf', '2.0')
                from gi.repository import GdkPixbuf
                anim = GdkPixbuf.PixbufAnimation.new_from_file(path)
            except Exception:  # noqa: BLE001 - fall back to the stream preview
                return
            idle(self._start_anim, card, anim)

        self.thumb_pool.submit(work)
        return GLib.SOURCE_REMOVE

    def _start_anim(self, card, anim):
        if card is not self._hover_card or (self.preview and self.preview[0] is card):
            return  # left already, or the real video preview is playing
        self.stop_preview()
        self.preview = (card, AnimClip(anim, card.thumb))

    def _hover_dwell_fire(self, card):
        self._dwell_src = 0
        if card is self._hover_card:
            fut = self.prefetch(card.video)
            fut.add_done_callback(lambda f: idle(self._start_preview_from, card, f))
        return GLib.SOURCE_REMOVE

    def _start_preview_from(self, card, fut):
        if card is not self._hover_card or fut.cancelled() or fut.exception() is not None:
            return
        stream = fut.result()
        if stream.get('preview') and not (self.preview and isinstance(self.preview[1], PreviewClip)
                                          and self.preview[0] is card):
            self.start_preview(card, stream['preview'], stream.get('ua'))

    def start_preview(self, card, url, ua=None):
        self.stop_preview()
        try:
            clip = PreviewClip(url, 0, ua)
        except Exception:  # noqa: BLE001 - previews are a nicety; never break browsing
            return
        card.thumb.set_paintable(clip.paintable)
        self.preview = (card, clip)

    def stop_preview(self, card=None):
        if not self.preview or (card is not None and self.preview[0] is not card):
            return
        c, clip = self.preview
        self.preview = None
        clip.stop()
        c.thumb.set_paintable(c.texture)

    # ---- the in-app player -----------------------------------------------------------
    def ensure_engine(self):
        if self.engine or self.engine_error:
            return self.engine
        mpvmod = load_mpv_module()
        if not mpvmod:
            self.engine_error = 'libmpv is not available'
            return None
        try:
            GL.init()
            self.engine = Engine(mpvmod, self._on_engine_event, self.config['volume'])
            self.watch = WatchPage(self)
        except Exception as e:  # noqa: BLE001
            self.engine_error = clean_error(e)
            self.engine = None
        return self.engine

    def _on_engine_event(self, name, value):
        if not self.watch:
            return
        self.watch.on_event(name, value)
        self._live_event(name, value)
        if name == 'playlist-pos' and value is not None and value >= 0:
            with self.engine.lock:
                video = self.engine.queue[value] if value < len(self.engine.queue) else None
            if video and video is not self.watch.video:
                self.lib.watched(video)
                self.watch.show_video(video)
                hit = self.resolved.get((video.id, self.current_format()))
                if hit and hit[0].done() and not hit[0].cancelled() and hit[0].exception() is None:
                    self.watch.set_stream(video, hit[0].result())
            self._top_up(self.play_gen)
        if name == 'pause':
            self.mini_play.set_icon_name('media-playback-start-symbolic' if value else 'media-playback-pause-symbolic')
        if name in ('idle-active', 'playlist-pos'):
            self._update_mini()

    def show_watch(self):
        if not self.watch:
            return
        stack = self.nav.get_navigation_stack()
        if any(stack.get_item(i) is self.watch for i in range(stack.get_n_items())):
            self.nav.pop_to_page(self.watch)
        else:
            self.nav.push(self.watch)

    def set_immersive(self, on):
        """Fullscreen for the player: hide the header and sidebar."""
        if on:
            self._sidebar_before_fs = self.split.get_show_sidebar()
            self.split.set_show_sidebar(False)
            self.content.set_reveal_top_bars(False)
            self.fullscreen()
        else:
            self.content.set_reveal_top_bars(True)
            self.split.set_show_sidebar(self._sidebar_before_fs)
            self.unfullscreen()

    def _on_fullscreened(self, *_):
        if not self.is_fullscreen() and self.watch and self.watch.is_fullscreen:
            self.watch.set_fullscreen(False)

    def _on_key(self, _ctl, keyval, _code, state):
        if not self._watch_visible():
            return False
        focus = self.get_focus()
        if isinstance(focus, (Gtk.Text, Gtk.Editable)) or state & (Gdk.ModifierType.CONTROL_MASK |
                                                                    Gdk.ModifierType.ALT_MASK):
            return False
        w = self.watch
        name = Gdk.keyval_name(keyval) or ''
        actions = {'space': w.toggle_pause, 'k': w.toggle_pause, 'f': w.toggle_fullscreen,
                   'm': w.toggle_mute, 'n': w.next, 'Left': lambda: w.seek_by(-5), 'Right': lambda: w.seek_by(5),
                   'j': lambda: w.seek_by(-10), 'l': lambda: w.seek_by(10),
                   'Up': lambda: w.set_volume((self.engine.m.volume or 0) + 5),
                   'Down': lambda: w.set_volume((self.engine.m.volume or 0) - 5), 'i': w.stats.toggle,
                   'Page_Up': lambda: self.zap(-1), 'Page_Down': lambda: self.zap(1),
                   'z': lambda: w.shift_subs(-0.1), 'x': lambda: w.shift_subs(0.1), 's': w.screenshot}
        if name == 'Escape' and w.is_fullscreen:
            w.set_fullscreen(False)
            return True
        if name in actions:
            actions[name]()
            return True
        return False

    # ---- playback ----------------------------------------------------------------
    def _lookup(self, video, fmt, pool=None, background=False):
        key = (video.id, fmt)
        hit = self.resolved.get(key)
        if hit:
            fut, created = hit
            stale = time.monotonic() - created > RESOLVE_TTL
            failed = fut.cancelled() or (fut.done() and fut.exception() is not None)
            if not stale and not failed:
                return fut
        resolve = self.yt.resolve_bg if background else self.yt.resolve  # clicks get the fast helper
        fut = (pool or self.resolve_pool).submit(resolve, video.id, fmt)
        self.resolved[key] = (fut, time.monotonic())
        if len(self.resolved) > 60:
            oldest = min(self.resolved, key=lambda k: self.resolved[k][1])
            self.resolved.pop(oldest, None)
        return fut

    def prefetch(self, video):
        if self.prefetching and not self.prefetching.running():
            self.prefetching.cancel()  # drop a queued lookup for a card the pointer already left
        self.prefetching = self._lookup(video, self.current_format(), background=True)
        return self.prefetching

    def play(self, video, queue=False, audio=None, playlist=None):
        if not self.config['inapp'] or not self.ensure_engine():
            if self.config['inapp'] and self.engine_error:
                self.toast(f'In-app player unavailable ({self.engine_error}); using a separate mpv window', 5)
            return self.play_external(video, queue=queue, audio=audio)
        audio = self.config['audio_only'] if audio is None else audio
        fmt = self.current_format(audio)
        fut = self._lookup(video, fmt)
        if fut is self.prefetching:
            self.prefetching = None  # a click now depends on it, so hovering must not cancel it
        if queue and self.watch.video is not None and not self.engine.m.idle_active:
            self.play_pool.submit(self._append_worker, video, fmt, fut, None)
            self.toast(f'Queued: {video.title}')
            return fut
        quick = None
        self._leave_live()
        self.play_gen += 1
        gen = self.play_gen
        self.stop_preview()
        self.lib.watched(video)
        with self.engine.lock:
            self.engine.queue = [video]
        self.watch.show_video(video)
        self.show_watch()
        if self.config['fullscreen'] and not self.watch.is_fullscreen:
            self.watch.set_fullscreen(True)
        cover = cover_art(video) if audio else None
        self.upcoming, self._inflight = list(playlist or []), 0
        self.play_pool.submit(self._play_worker, video, fmt, fut, gen, cover, quick, playlist or [])
        return fut

    def _play_worker(self, video, fmt, fut, gen, cover, quick, playlist):
        eng = self.engine
        started_quick = False
        if quick and not fut.done():
            try:
                eng.load(quick, 'replace', video.title)
                started_quick = True
            except Exception:  # noqa: BLE001
                pass
        err = ''
        try:
            stream = fut.result(timeout=60)
            if video.title == video.id:
                video.title = stream['title']
                idle(self.lib.save, video)
        except Exception as e:  # noqa: BLE001
            stream, err = None, clean_error(e)
        if gen != self.play_gen:
            return  # a newer click replaced this one
        try:
            if stream:
                idle(self.watch.set_stream, video, stream)
                if started_quick:
                    eng.swap_video(quick, stream)
                else:
                    eng.load_stream(stream, 'replace', cover)
            elif not started_quick:
                eng.m['ytdl-format'] = fmt
                eng.load(video.url, 'replace', video.title)
                idle(self.toast, f'Quick load failed, trying slower route: {err}', 5)
        except Exception as e:  # noqa: BLE001
            idle(self.toast, f'Playback failed: {clean_error(e)}', 6)
            return
        idle(self._top_up, gen)  # queue the next Shorts (if any), a couple at a time

    def _top_up(self, gen, delay=10):
        """Keep the next Short (or the next video of a list) queued. Its lookup waits until the current
        one has been playing a few seconds: on a 2-core CPU, lookups during start-up cost dropped frames."""
        if delay:
            GLib.timeout_add_seconds(delay, lambda: (self._top_up(gen, 0), False)[1])
            return
        if gen != self.play_gen or not self.engine or self._inflight or not self.upcoming:
            return
        pos = self.engine.m.playlist_pos or 0
        with self.engine.lock:
            ahead = len(self.engine.queue) - (pos + 1)
        if ahead >= 1:
            return
        video = self.upcoming.pop(0)
        fmt = self.current_format()
        self._inflight = 1
        fut = self._lookup(video, fmt, self.upcoming_pool, background=True)

        def work():
            try:
                self._append_worker(video, fmt, fut, gen)
            finally:
                idle(self._upcoming_done, gen)

        self.play_pool.submit(work)

    def _upcoming_done(self, gen):
        if gen == self.play_gen:
            self._inflight = 0

    def _append_worker(self, video, fmt, fut, gen):
        try:
            stream = fut.result(timeout=60)
        except Exception as e:  # noqa: BLE001
            if gen is None:
                idle(self.toast, f'Couldn’t queue {video.title}: {clean_error(e)}', 5)
            return
        if gen is not None and gen != self.play_gen:
            return
        with self.engine.lock:
            self.engine.load_stream(stream, 'append-play')
            self.engine.queue.append(video)
        idle(self.watch.controls.update, 'playlist-count', None, self.engine)

    def change_quality(self, height):
        """From the player's gear menu: switch the current video and remember the choice."""
        if height is None:
            self.audio_btn.set_active(True)
        else:
            self.audio_btn.set_active(False)
            self.quality.set_selected(qualities().index(height) if height in qualities() else
                                      max(i for i, q in enumerate(qualities()) if q <= max(height, 360)))
        video = self.watch.video if self.watch else None
        if not video:
            return
        fmt = AUDIO_FORMAT if height is None else video_format(height)
        fut = self._lookup(video, fmt)
        gen = self.play_gen
        pos = self.engine.m.time_pos or 0

        def work():
            try:
                stream = fut.result(timeout=60)
            except Exception as e:  # noqa: BLE001
                idle(self.toast, f'Couldn’t switch quality: {clean_error(e)}', 5)
                return
            if gen != self.play_gen:
                return
            idle(self.watch.set_stream, video, stream)
            if height is None:
                cover = cover_art(video)
                self.engine.load_stream(stream, 'replace', cover, start=self.engine.m.time_pos or pos)
            else:
                self.engine.swap_video(None, stream)

        self.play_pool.submit(work)
        self.toast('Switching to audio only…' if height is None else f'Switching to {height}p…')

    def play_external(self, video, queue=False, audio=None, start=None):
        audio = self.config['audio_only'] if audio is None else audio
        fmt = self.current_format(audio)
        fut = self._lookup(video, fmt)
        if self.engine and not self.engine.m.idle_active:
            self.engine.m.pause = True
        self.lib.watched(video)

        def work():
            try:
                self.external.ensure(fmt, fullscreen=True)
                stream = fut.result(timeout=60)
                self.external.load(stream, 'append-play' if queue else 'replace', start)
            except FileNotFoundError:
                idle(self.toast, 'mpv is not installed (sudo apt install mpv)', 6)
            except Exception as e:  # noqa: BLE001
                idle(self.toast, f'Playback failed: {clean_error(e)}', 6)

        self.play_pool.submit(work)
        if queue:
            self.toast(f'Queued: {video.title}')
        return fut

    def play_file(self, path, title=None):
        title = title or os.path.basename(path)
        self._leave_live()
        if self.config['inapp'] and self.ensure_engine():
            video = Video(hashlib.md5(path.encode()).hexdigest()[:11], title, kind='file')
            with self.engine.lock:
                self.engine.queue = [video]
            self.play_gen += 1
            self.watch.show_video(video)
            self.show_watch()
            self.engine.load(path, 'replace', title)
            return
        self.play_pool.submit(lambda: (self.external.ensure(self.current_format()),
                                       self.external.load({'url': path, 'title': title})))

    # ---- library actions -----------------------------------------------------------
    def set_in_list(self, lst, v, on):
        if v.kind != 'video':
            return
        label = {'liked': 'Liked', 'later': 'Watch later'}.get(lst, lst[3:])
        if on == self.lib.has(lst, v.id):
            return
        if on:
            self.lib.add(lst, v)
            self.toast(f'Saved to {label}')
        else:
            self.lib.remove(lst, v.id)
            self.toast(f'Removed from {label}')

    def set_live_quality(self, height):
        self.quality.set_selected(qualities().index(height))  # saved like the header's quality menu
        nl = self.now_live
        if nl:
            self.play_live(nl['video'], nl['siblings'], nl['alt'])

    def set_theme(self, theme):
        if theme not in ('system', 'light', 'dark'):
            theme = 'system'
        self.config['theme'] = theme
        self.save_config()
        Adw.StyleManager.get_default().set_color_scheme({'light': Adw.ColorScheme.FORCE_LIGHT,
                                                         'dark': Adw.ColorScheme.FORCE_DARK}.get(
            theme, Adw.ColorScheme.DEFAULT))
        action = self.lookup_action('theme')
        if action:
            action.set_state(GLib.Variant('s', theme))
        self._update_theme_button()

    def _update_theme_button(self):
        dark = Adw.StyleManager.get_default().get_dark()
        self.theme_btn.set_icon_name('weather-clear-symbolic' if dark else 'weather-clear-night-symbolic')
        self.theme_btn.set_tooltip_text('Day mode' if dark else 'Dark mode')

    def toggle_list(self, lst, v, card=None):
        on = not self.lib.has(lst, v.id)
        self.set_in_list(lst, v, on)
        if not on and card and card.page and card.page.list_name == lst:
            card.page.remove_card(card)

    def remove_from_page(self, card):
        page, v = card.page, card.video
        if page.list_name == 'history':
            self.lib.forget(v.id)
        else:
            self.lib.remove(page.list_name, v.id)
        page.remove_card(card)

    def toggle_channel(self, channel_id, name, url, done=None):
        def apply(cid, nm):
            if not cid:
                self.toast('Couldn’t identify this channel')
                return
            if self.lib.is_subscribed(cid):
                self.lib.unsubscribe(cid)
                self.toast(f'Unsubscribed from {nm}')
            else:
                self.lib.subscribe(cid, nm or cid, url)
                self.toast(f'Subscribed to {nm} (saved on this device)')
            if done:
                done()

        if channel_id:
            apply(channel_id, name)
            return

        def work():
            try:
                cid, nm = self.yt.channel_id_for(url)
            except Exception:  # noqa: BLE001
                cid, nm = None, name
            idle(apply, cid, name or nm)

        self.search_pool.submit(work)

    def toggle_subscription(self, v):
        if v.kind == 'channel':
            self.toggle_channel(v.channel_id, v.title, v.link)
        else:
            self.toggle_channel(v.channel_id, v.channel, v.channel_link)

    def hide_video(self, v, card):
        self.lib.hide('video', v.id)
        if card.page:
            card.page.remove_card(card)
        self.toast('Got it — you won’t see this video again')

    def hide_channel(self, v):
        key = v.channel_id or v.channel
        self.lib.hide('channel', key)
        page = self.nav.get_visible_page()
        if isinstance(page, GridPage):
            for c in [c for c in page.cards if (c.video.channel_id or c.video.channel) == key]:
                page.remove_card(c)
        self.toast(f'Smedio won’t recommend {v.channel or "this channel"} anymore')

    def copy_link(self, v):
        self.get_clipboard().set_content(Gdk.ContentProvider.new_for_bytes(
            'text/plain;charset=utf-8', GLib.Bytes.new(v.url.encode())))
        self.toast('Link copied')

    def delete_playlist(self, v, card):
        self.confirm(f'Delete playlist “{v.title}”?', 'The videos themselves are not affected.', 'Delete',
                     lambda: (self.lib.delete_playlist(v.title), card.page and card.page.remove_card(card)))

    def save_to_playlist(self, v):
        names = [p.title for p in self.lib.playlists()]
        dlg = Adw.AlertDialog(heading='Save to playlist')
        box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=8)
        drop = Gtk.DropDown.new_from_strings(names + ['New playlist…'])
        entry = Gtk.Entry(placeholder_text='New playlist name', visible=not names, activates_default=True)
        drop.connect('notify::selected', lambda d, _p: entry.set_visible(d.get_selected() == len(names)))
        if names:
            box.append(drop)
        box.append(entry)
        dlg.set_extra_child(box)
        dlg.add_response('cancel', 'Cancel')
        dlg.add_response('save', 'Save')
        dlg.set_response_appearance('save', Adw.ResponseAppearance.SUGGESTED)
        dlg.set_default_response('save')

        def on_response(_d, response):
            if response != 'save':
                return
            idx = drop.get_selected() if names else len(names)
            name = names[idx] if idx < len(names) else entry.get_text().strip()
            if name:
                self.lib.create_playlist(name)
                self.lib.add('pl:' + name, v)
                self.toast(f'Saved to {name}')

        dlg.connect('response', on_response)
        dlg.present(self)

    def ask_text(self, heading, placeholder, ok_label, callback):
        dlg = Adw.AlertDialog(heading=heading)
        entry = Gtk.Entry(placeholder_text=placeholder, activates_default=True)
        dlg.set_extra_child(entry)
        dlg.add_response('cancel', 'Cancel')
        dlg.add_response('ok', ok_label)
        dlg.set_response_appearance('ok', Adw.ResponseAppearance.SUGGESTED)
        dlg.set_default_response('ok')
        dlg.connect('response', lambda _d, r: r == 'ok' and entry.get_text().strip()
                    and callback(entry.get_text().strip()))
        dlg.present(self)

    def confirm(self, heading, body, ok_label, callback):
        dlg = Adw.AlertDialog(heading=heading, body=body)
        dlg.add_response('cancel', 'Cancel')
        dlg.add_response('ok', ok_label)
        dlg.set_response_appearance('ok', Adw.ResponseAppearance.DESTRUCTIVE)
        dlg.connect('response', lambda _d, r: r == 'ok' and callback())
        dlg.present(self)

    def downloads_start(self, video, audio=False, fmt=None, label=None):
        self.downloads.start(video, audio, fmt, label)
        self.toast(f'Downloading {label or ("audio" if audio else "video")}: {video.title}', button='Show',
                   action=lambda: self.open_section('downloads'))

    def download(self, v, audio=False):
        self.downloads_start(v, audio)

    def open_folder(self, path):
        os.makedirs(path, exist_ok=True)
        Gtk.FileLauncher.new(Gio.File.new_for_path(path)).launch(self, None, None)

    def show_file(self, path):
        Gtk.FileLauncher.new(Gio.File.new_for_path(path)).open_containing_folder(self, None, None)

    # ---- import / export -------------------------------------------------------------
    def show_banner(self, text, button=None, action=None):
        self._banner_action = action
        self.banner.set_title(GLib.markup_escape_text(text))
        self.banner.set_button_label(button)
        self.banner.set_revealed(True)

    def import_from_google(self):
        if not self.config['browser']:
            self.toast('Choose your browser under “YouTube account” first', 5)
            return
        if self._importing:
            self.toast('Already copying from YouTube — see the bar at the top')
            return
        self._importing = True
        name = BROWSERS[self.config['browser']][0]
        self.show_banner(f'Copying the YouTube account that is active in {name}… starting')

        def work():
            done, failed = copy_google_account(
                self.lib, self.yt, self.feed_pool,
                log=lambda msg: idle(self.show_banner, f'Copying from YouTube ({name}): {msg}'))
            msg = 'Merged into your library: ' + ', '.join(done) + '.'
            if failed:
                msg += f' {len(failed)} item(s) could not be read.'
            idle(finish, msg)

        def finish(msg):
            self._importing = False
            self.show_banner(msg, 'Dismiss')

        threading.Thread(target=work, daemon=True).start()

    @staticmethod
    def _file_filter(name, patterns):
        f = Gtk.FileFilter(name=name)
        for p in patterns:
            f.add_pattern(p)
        store = Gio.ListStore.new(Gtk.FileFilter)
        store.append(f)
        return store

    def import_takeout(self):
        dlg = Gtk.FileDialog(title='Import Google Takeout file (subscriptions.csv or a playlist CSV)',
                             filters=self._file_filter('CSV files', ['*.csv']))

        def done(d, res):
            try:
                path = d.open_finish(res).get_path()
            except GLib.Error:
                return
            try:
                msg, ids = self.lib.import_takeout(path)
            except Exception as e:  # noqa: BLE001
                self.toast(f'Import failed: {clean_error(e)}', 6)
                return
            self.toast(msg, 6)
            if ids:
                self.search_pool.submit(self._fill_titles, ids)

        dlg.open(self, None, done)

    def _fill_titles(self, ids):
        def one(vid):
            try:
                title, author, author_url = self.yt.oembed(vid)
                self.lib.save(Video(vid, title, channel=author or '', channel_url=author_url))
            except Exception:  # noqa: BLE001 - deleted/private videos simply keep their id
                pass

        list(self.feed_pool.map(one, ids[:600]))
        idle(self.toast, 'Video titles updated')

    def export_library(self):
        dlg = Gtk.FileDialog(title='Export library', initial_name='smedio-library.json')

        def done(d, res):
            try:
                path = d.save_finish(res).get_path()
                self.lib.export(path)
                self.toast(f'Library saved to {path}', 5)
            except GLib.Error:
                return
            except Exception as e:  # noqa: BLE001
                self.toast(f'Export failed: {clean_error(e)}', 6)

        dlg.save(self, None, done)

    def import_library(self):
        dlg = Gtk.FileDialog(title='Import Smedio library backup',
                             filters=self._file_filter('Smedio backup', ['*.json']))

        def done(d, res):
            try:
                path = d.open_finish(res).get_path()
                subs, items = self.lib.import_backup(path)
                self.toast(f'Imported {subs} subscriptions and {items} saved videos', 5)
            except GLib.Error:
                return
            except Exception as e:  # noqa: BLE001
                self.toast(f'Import failed: {clean_error(e)}', 6)

        dlg.open(self, None, done)

    # ---- preferences -------------------------------------------------------------
    def show_preferences(self):
        dlg = Adw.PreferencesDialog(title='Preferences')
        page = Adw.PreferencesPage(title='General', icon_name='preferences-system-symbolic')
        dlg.add(page)

        def switch(group, title, subtitle, key):
            row = Adw.SwitchRow(title=title, subtitle=subtitle, active=self.config[key])
            row.connect('notify::active', lambda r, _p: (self.config.__setitem__(key, r.get_active()),
                                                         self.save_config()))
            group.add(row)

        g = Adw.PreferencesGroup(title='Appearance')
        themes = ['system', 'light', 'dark']
        look = Adw.ComboRow(title='Style', model=Gtk.StringList.new(['Follow system', 'Light (day mode)', 'Dark']))
        look.set_selected(themes.index(self.config['theme']))
        look.connect('notify::selected', lambda r, _p: self.set_theme(themes[r.get_selected()]))
        g.add(look)
        page.add(g)

        g = Adw.PreferencesGroup(title='Playback')
        switch(g, 'Play inside Smedio', 'Off: use a separate mpv window instead', 'inapp')
        switch(g, 'Start videos fullscreen', 'F toggles fullscreen, Esc leaves it', 'fullscreen')
        codecs, how = hw_decoders()
        names = ', '.join(CODEC_NAMES[c] for c in CODEC_NAMES if c in codecs)
        g.add(Adw.ActionRow(
            title='Hardware video decoding',
            subtitle=(f'{names} — asked from {how}. YouTube videos are picked in these formats.' if how else
                      f'Couldn’t ask the GPU (no VA-API or V4L2 decoder found); assuming {names}.'),
            subtitle_selectable=True))
        switch(g, 'Preview videos on hover', 'Plays a muted 360p clip inside the thumbnail', 'hover_preview')
        switch(g, 'Preload visible videos', 'Looks up on-screen videos in advance so previews and clicks start '
               'instantly. Uses about 0.5 MB per video — best on Wi-Fi, not on a phone hotspot',
               'preload_previews')
        switch(g, 'Skip sponsors (SponsorBlock)', 'Skips sponsor segments, self-promotion and subscribe reminders '
               'that SponsorBlock users marked. Asked by a hash prefix: the server can’t tell which video you watch',
               'sponsorblock')
        page.add(g)

        g = Adw.PreferencesGroup(
            title='YouTube account',
            description='Smedio never asks for your password. It reads the YouTube login of a browser where you '
                        'are already signed in, only to show your feeds — likes, subscriptions and playlists you '
                        'make here stay on this device. Using an account with third-party tools carries a small '
                        'risk of YouTube flagging it.')
        browsers = [b for b in BROWSERS if any(os.path.isdir(os.path.expanduser(d)) for d in BROWSERS[b][1])]
        options = [None] + browsers
        combo = Adw.ComboRow(title='Account', model=Gtk.StringList.new(
            ['Not connected — local library only'] + [f'Use my login from {BROWSERS[b][0]}' for b in browsers]))
        combo.set_selected(options.index(self.config['browser']) if self.config['browser'] in options else 0)
        combo.connect('notify::selected', lambda r, _p: self.set_browser(options[r.get_selected()]))
        g.add(combo)
        page.add(g)

        g = Adw.PreferencesGroup(title='Library on this device', description=f'Stored in {DATA_DIR}')
        for title, cb in (('Copy everything from my YouTube account', self.import_from_google),
                          ('Import Google Takeout file…', self.import_takeout),
                          ('Export library backup…', self.export_library),
                          ('Import library backup…', self.import_library)):
            row = Adw.ButtonRow(title=title)
            if cb == self.import_from_google:
                row.set_tooltip_text('Copies the account currently active on youtube.com in that browser. '
                                     'Switch accounts there and run it again to merge another account.')
            row.connect('activated', lambda _r, cb=cb: cb())
            g.add(row)
        page.add(g)

        g = Adw.PreferencesGroup(
            title='Live TV',
            description='The IPTV page has every country and region from iptv-org; playlists you add here (any '
                        'M3U link or file) appear at the top of its menu.')
        for i, pl in enumerate(self.config['iptv']):
            row = Adw.ActionRow(title=GLib.markup_escape_text(pl['name']), subtitle=GLib.markup_escape_text(pl['url']))
            row.set_subtitle_lines(1)
            rm = Gtk.Button(icon_name='user-trash-symbolic', valign=Gtk.Align.CENTER, tooltip_text='Remove')
            rm.add_css_class('flat')

            def remove(_b, i=i):
                dlg.close()
                self.remove_playlist(i)

            rm.connect('clicked', remove)
            row.add_suffix(rm)
            g.add(row)
        add = Adw.ButtonRow(title='Add IPTV playlist…', start_icon_name='list-add-symbolic')
        add.connect('activated', lambda *_: (dlg.close(), self.add_playlist()))
        g.add(add)
        page.add(g)

        g = Adw.PreferencesGroup(title='Downloads')
        row = Adw.ActionRow(title='Folder', subtitle=self.config['download_dir'])
        change = Gtk.Button(label='Change…', valign=Gtk.Align.CENTER)

        def pick(*_):
            def done(d, res):
                try:
                    path = d.select_folder_finish(res).get_path()
                except GLib.Error:
                    return
                self.config['download_dir'] = path
                self.save_config()
                row.set_subtitle(path)

            Gtk.FileDialog(title='Choose download folder').select_folder(self, None, done)

        change.connect('clicked', pick)
        row.add_suffix(change)
        g.add(row)
        page.add(g)
        dlg.present(self)


class App(Adw.Application):
    def __init__(self):
        super().__init__(application_id=APP_ID, flags=Gio.ApplicationFlags.DEFAULT_FLAGS)
        self.win = None

    def do_startup(self):
        Adw.Application.do_startup(self)
        provider = Gtk.CssProvider()
        provider.load_from_string(CSS)
        Gtk.StyleContext.add_provider_for_display(Gdk.Display.get_default(), provider,
                                                  Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION)
        for name, cb, accels in (('quit', lambda *_: self.quit(), ['<Control>q']),
                                 ('preferences', lambda *_: self.win.show_preferences(), ['<Control>comma']),
                                 ('about', self._about, []),
                                 ('update', self._update, [])):
            action = Gio.SimpleAction.new(name, None)
            action.connect('activate', cb)
            self.add_action(action)
            if accels:
                self.set_accels_for_action(f'app.{name}', accels)
        self.set_accels_for_action('win.focus-search', ['<Control>l', '<Control>f'])
        self.set_accels_for_action('window.close', ['<Control>w'])

    def do_activate(self):
        if not self.win:
            self.win = Window(self)
        self.win.present()

    def _about(self, *_):
        Adw.AboutDialog(application_name='Smedio', application_icon=APP_ID, version=VERSION,
                        comments='Lightweight, ad-free YouTube for low-end laptops and ARM tablets. Plays '
                                 'what the hardware decodes in an embedded mpv: VA-API on PCs, V4L2 on '
                                 'ARM (e.g. Qualcomm Venus).',
                        license_type=Gtk.License.MIT_X11).present(self.win)

    def _update(self, *_):
        if not HAVE_VENV:
            self.win.toast('yt-dlp comes from your system: update it with your package manager.', 6)
            return
        self.win.toast('Updating yt-dlp…')

        def work():
            pip = os.path.join(VENV_BIN, 'pip')
            r = subprocess.run([pip, 'install', '-q', '--upgrade', 'yt-dlp[default,secretstorage]', 'deno'],
                               capture_output=True, text=True)
            if r.returncode == 0:
                msg = 'yt-dlp is up to date. Restart Smedio if it was updated.'
            else:
                msg = 'Update failed: ' + (r.stderr.strip().splitlines() or ['unknown error'])[-1]
            idle(self.win.toast, msg, 6)

        threading.Thread(target=work, daemon=True).start()


def cli_import_google():
    """`smedio --import-google`: same as Preferences → Copy everything from my YouTube account."""
    cfg = Window._load_config()
    if not cfg['browser']:
        print('No YouTube account connected (Preferences → YouTube account).')
        return 1
    yt = YouTube()
    yt.set_browser(cfg['browser'])
    yt.warm_up()
    done, failed = copy_google_account(Library(DB_FILE), yt, ThreadPoolExecutor(6),
                                       log=lambda msg: print('Copying', msg, flush=True))
    print('Copied ' + ', '.join(done) + '.')
    for f in failed:
        print('Could not read:', f)
    return 0


def migrate_from_tubelite():
    """First start after the rename: copy TubeLite's library, settings and channel-feed cache.
    The originals stay where they were (~/.local/share/tubelite-library can go once you're happy)."""
    old_db = os.path.join(GLib.get_user_data_dir(), 'tubelite-library', 'library.db')
    if not os.path.exists(DB_FILE) and os.path.exists(old_db):
        os.makedirs(DATA_DIR, exist_ok=True)
        src, dst = sqlite3.connect(old_db), sqlite3.connect(DB_FILE)
        try:
            src.backup(dst)  # a consistent copy even if TubeLite is open
        finally:
            src.close()
            dst.close()
    old_cfg = os.path.join(GLib.get_user_config_dir(), 'tubelite', 'config.json')
    if not os.path.exists(CONFIG_FILE) and os.path.exists(old_cfg):
        os.makedirs(CONFIG_DIR, exist_ok=True)
        shutil.copy2(old_cfg, CONFIG_FILE)
    old_rss = os.path.join(GLib.get_user_cache_dir(), 'tubelite', 'rss')
    if not os.path.exists(RSS_DIR) and os.path.isdir(old_rss):
        shutil.copytree(old_rss, RSS_DIR)


def main():
    # Started as `import smedio; smedio.main()` (see the launcher), so the helper processes
    # import this module by name instead of re-running a script.
    migrate_from_tubelite()
    if '--import-google' in sys.argv:
        os._exit(cli_import_google())
    app = App()
    status = app.run(sys.argv)
    if app.win:
        app.win.yt.shutdown()  # stop the lookup helper processes
    os._exit(status)  # don't wait for in-flight thumbnail/lookup threads


if __name__ == '__main__':
    main()
