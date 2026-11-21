#!/bin/sh
# Smedio installer, for your user only (no root needed).
#
#   ./install.sh             install or update
#   ./install.sh --venv      use a private, up-to-date yt-dlp even if the system has one
#   ./install.sh --system    use the system's yt-dlp and python-mpv (no private copy)
#   ./install.sh --uninstall remove the app (your library and settings stay)
#
# GTK 4, libadwaita (1.6 or newer) and libmpv come from your distribution; when one is missing
# this prints the command that installs them. yt-dlp changes every few weeks as YouTube does:
# if your distribution's copy is older than 4 months (or missing), Smedio gets its own up-to-date
# copy in a private folder, which Menu -> Update yt-dlp keeps current.
set -eu

here=$(cd "$(dirname "$0")" && pwd)
data=${XDG_DATA_HOME:-$HOME/.local/share}
app=$data/smedio
bin=$HOME/.local/bin
mode=auto

say() { printf '%s\n' "$*"; }
die() { printf 'smedio: %s\n' "$*" >&2; exit 1; }

case "${1:-}" in
"") ;;
--venv) mode=venv ;;
--system) mode=system ;;
--uninstall)
	rm -rf "$app" "$bin/smedio" "$data/applications/dev.smedio.Smedio.desktop" \
		"$data/icons/hicolor/scalable/apps/dev.smedio.Smedio.svg"
	say "Smedio removed. Your library and settings are still in $data/smedio-library and"
	say "${XDG_CONFIG_HOME:-$HOME/.config}/smedio; delete those too for a clean slate."
	exit 0 ;;
*) die "unknown option $1 (see the top of this script)" ;;
esac

python=$(command -v python3) || die "python3 is missing"

. /etc/os-release 2>/dev/null || true
packages() {
	case " ${ID:-} ${ID_LIKE:-} " in
	*" alpine "* | *" postmarketos "*)
		say "  sudo apk add py3-gobject3 gtk4.0 libadwaita mpv py3-mpv yt-dlp   (or doas)" ;;
	*" debian "* | *" ubuntu "*)
		say "  sudo apt install python3-gi gir1.2-gtk-4.0 gir1.2-adw-1 libmpv2 python3-venv" ;;
	*" fedora "*)
		say "  sudo dnf install python3-gobject gtk4 libadwaita mpv-libs" ;;
	*" arch "*)
		say "  sudo pacman -S python-gobject gtk4 libadwaita mpv python-mpv yt-dlp deno" ;;
	*)
		say "  Python GObject bindings, GTK 4, libadwaita 1.6+ and libmpv, from your package manager" ;;
	esac
}

# What the system has: GTK and libadwaita (required), libmpv (required), and whether its
# python-mpv, yt-dlp and a JavaScript runtime for yt-dlp are good enough to skip the private copy.
check=$("$python" - <<'EOF'
import ctypes.util, datetime, shutil, subprocess
try:
    import gi
    gi.require_version('Gtk', '4.0')
    gi.require_version('Adw', '1')
    from gi.repository import Adw
    adw = (Adw.MAJOR_VERSION, Adw.MINOR_VERSION) >= (1, 6)
    print('gtk ok' if adw else 'gtk old-adw')
except (ImportError, ValueError):
    print('gtk missing')
print('libmpv', 'ok' if ctypes.util.find_library('mpv') else 'missing')
try:
    import mpv  # noqa: F401
    print('pympv ok')
except (ImportError, OSError):
    print('pympv missing')
fresh = 'missing'
ytdlp = shutil.which('yt-dlp')
if ytdlp:
    try:
        v = subprocess.run([ytdlp, '--version'], capture_output=True, text=True, timeout=30).stdout.strip()
        y, m, d = (int(x) for x in v.split('.')[:3])
        fresh = 'ok' if (datetime.date.today() - datetime.date(y, m, d)).days <= 120 else 'old'
    except (OSError, ValueError, subprocess.TimeoutExpired):
        fresh = 'old'
print('ytdlp', fresh)
print('js', 'ok' if any(shutil.which(n) for n in ('deno', 'node', 'bun', 'qjs')) else 'missing')
print('ffmpeg', 'ok' if shutil.which('ffmpeg') else 'missing')
EOF
)
has() { printf '%s\n' "$check" | grep -qx "$1"; }

if ! has 'gtk ok' || ! has 'libmpv ok'; then
	has 'gtk missing' && say "Missing: GTK 4 or libadwaita for Python."
	has 'gtk old-adw' && say "libadwaita is older than 1.6 (e.g. Ubuntu 24.04); Smedio needs 1.6 or newer."
	has 'libmpv missing' && say "Missing: libmpv."
	say "Install them with:"
	packages
	exit 1
fi

if [ "$mode" = auto ]; then
	if has 'pympv ok' && has 'ytdlp ok' && has 'js ok'; then mode=system; else mode=venv; fi
fi
if [ "$mode" = system ] && ! { has 'pympv ok' && ! has 'ytdlp missing'; }; then
	say "--system needs python-mpv and yt-dlp from your distribution:"
	packages
	exit 1
fi

mkdir -p "$app" "$bin" "$data/applications" "$data/icons/hicolor/scalable/apps"
if [ "$mode" = venv ]; then
	say "Setting up a private yt-dlp in $app/venv…"
	[ -d "$app/venv" ] || "$python" -m venv "$app/venv" ||
		die "couldn't create a Python venv (on Debian and Ubuntu: sudo apt install python3-venv)"
	"$app/venv/bin/pip" install -q --upgrade pip
	"$app/venv/bin/pip" install -q --upgrade 'yt-dlp[default]' mpv
	if ! has 'js ok'; then  # yt-dlp needs a JavaScript runtime for YouTube
		"$app/venv/bin/pip" install -q --upgrade deno ||
			say "Couldn't get Deno for this system; install deno or nodejs from your package manager."
	fi
else
	rm -rf "$app/venv"
fi

install -m 644 "$here/smedio.py" "$app/smedio.py"
rm -rf "$app/__pycache__"
cat >"$bin/smedio" <<EOF
#!/bin/sh
exec $python -c 'import sys; sys.path.insert(0, "$app"); import smedio; smedio.main()' "\$@"
EOF
chmod 755 "$bin/smedio"
sed "s|^Exec=.*|Exec=$bin/smedio|" "$here/dev.smedio.Smedio.desktop" >"$data/applications/dev.smedio.Smedio.desktop"
install -m 644 "$here/dev.smedio.Smedio.svg" "$data/icons/hicolor/scalable/apps/"
command -v update-desktop-database >/dev/null && update-desktop-database -q "$data/applications" || true
command -v gtk4-update-icon-cache >/dev/null && gtk4-update-icon-cache -q -t "$data/icons/hicolor" 2>/dev/null || true

has 'ffmpeg missing' && say "Note: ffmpeg is missing. Playback works without it; downloads need it (yt-dlp joins
the video and audio with it). Install the ffmpeg package to download."
say "Smedio installed ($([ "$mode" = venv ] && echo "private yt-dlp" || echo "system yt-dlp")). Start it from"
say "your app menu, or run: $bin/smedio"
