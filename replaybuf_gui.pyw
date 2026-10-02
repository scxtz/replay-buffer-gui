#!/usr/bin/env python3
"""
Replay Buffer GUI - replay buffer minimalista para Windows (FFmpeg + AMD AMF).

- Activa / desactiva el buffer con un boton
- Segundos del buffer (cuanto se mantiene en memoria/disco temporal)
- Segundos del clip (cuanto se guarda al pulsar el hotkey, <= buffer)
- Fuente: pantalla completa (elige monitor) o una ventana concreta
- Hotkey global, codec (H.264/HEVC/AV1), fps, bitrate, calidad, audio opcional

Requisitos: Windows 10/11, Python 3.8+ (solo libreria estandar) y ffmpeg
"full build" (gyan.dev) en el PATH o junto a este archivo (ffmpeg.exe).

Doble clic en el .pyw para abrirlo sin consola.
"""
import ctypes
import ctypes.wintypes as wt
import json
import math
import os
import queue
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
from datetime import datetime
from pathlib import Path

import tkinter as tk
from tkinter import filedialog, messagebox, ttk

APP_TITLE = "Replay Buffer"
if getattr(sys, "frozen", False):          # ejecutado como .exe (PyInstaller)
    APP_DIR = Path(sys.executable).resolve().parent
else:
    APP_DIR = Path(__file__).resolve().parent
CONFIG_PATH = Path(os.environ.get("APPDATA", str(Path.home()))) / "ReplayBuf" / "config.json"

CREATE_NO_WINDOW = 0x08000000
NORMAL_PRIORITY_CLASS = 0x00000020
WM_HOTKEY = 0x0312
WM_QUIT = 0x0012
MOD_NOREPEAT = 0x4000
MODS = {"alt": 0x1, "ctrl": 0x2, "control": 0x2, "shift": 0x4, "win": 0x8}
HLS_TIME = 0.9  # un poco menos que el GOP (1 s): cada keyframe abre un segmento nuevo
CAPTURE_MODES = {
    "copy": "ddagrab + copia a CPU (compatible)",
    "gdi": "GDI (más lento, muy compatible)",
}
RES_MODES = {
    "native": "Nativa (sin escalar)",
    "1080": "1080p",
    "720": "720p",
}
SCALERS = {
    "fast_bilinear": "Rápido",
    "bicubic": "Equilibrado",
    "lanczos": "Nítido",
}
FPS_VALUES = ["30", "60", "120"]
# Mbps sugeridos para AV1 segun (altura, fps); H.264 / HEVC necesitan mas
BITRATE_AV1 = {(720, 30): 5, (720, 60): 8, (720, 120): 12,
               (1080, 30): 8, (1080, 60): 12, (1080, 120): 20}
BITRATE_FACTOR = {"av1": 1.0, "hevc": 1.3, "h264": 1.8}

DEFAULTS = {
    "buffer_s": 30, "clip_s": 30, "fps": 30, "bitrate": 5,
    "codec": "av1", "quality": "high_quality", "bframes": 0, "hotkey": "f9",
    "mouse": False, "capture": "copy", "res": "720", "scaler": "bicubic",
    "audio_buf": 100, "audio": "",
    "out_dir": str(Path.home() / "Videos" / "Clips"), "ffmpeg": "",
}

# ==========================================================================
# Dark Theme
# ==========================================================================
def apply_dark_theme(root):
    """Aplica tema oscuro a toda la interfaz."""
    try:
        style = ttk.Style(root)
        style.theme_use("clam")

        root.configure(bg="#1a1a1a")

        style.configure(".", background="#1a1a1a", foreground="#e0e0e0",
                        fieldbackground="#252525", borderwidth=1)

        style.configure("TFrame", background="#1a1a1a")
        style.configure("TLabel", background="#1a1a1a", foreground="#e0e0e0")
        style.configure("TButton", background="#2d2d2d", foreground="#ffffff",
                        padding=(10, 7), borderwidth=1, relief="flat")
        style.map("TButton",
                  background=[("active", "#404040"), ("pressed", "#1f5fbf")],
                  foreground=[("active", "#ffffff"), ("pressed", "#ffffff")])

        style.configure("TEntry", fieldbackground="#252525", foreground="#e0e0e0",
                        borderwidth=1, relief="solid", padding=4)
        style.configure("TCombobox", fieldbackground="#252525", foreground="#e0e0e0",
                        borderwidth=1, padding=2)
        style.map("TCombobox",
                  fieldbackground=[("readonly", "#252525")],
                  foreground=[("readonly", "#e0e0e0")])

        style.configure("TLabelframe", background="#1a1a1a", foreground="#e0e0e0",
                        borderwidth=1, relief="groove")
        style.configure("TLabelframe.Label", background="#1a1a1a", foreground="#e0e0e0",
                        font=("Segoe UI", 9, "bold"))
        style.configure("TSpinbox", fieldbackground="#252525", foreground="#e0e0e0",
                        borderwidth=1, relief="solid")
        style.configure("TRadiobutton", background="#1a1a1a", foreground="#e0e0e0")
        style.configure("TCheckbutton", background="#1a1a1a", foreground="#e0e0e0",
                        font=("Segoe UI", 9))

        style.configure("Horizontal.TScrollbar", background="#2d2d2d",
                        troughcolor="#1a1a1a")
    except Exception:
        pass


# ==========================================================================
# Windows API
# ==========================================================================
class MONITORINFO(ctypes.Structure):
    _fields_ = [("cbSize", wt.DWORD), ("rcMonitor", wt.RECT),
                ("rcWork", wt.RECT), ("dwFlags", wt.DWORD)]


if os.name == "nt":
    # Coordenadas en pixeles reales (necesario para capturar la region correcta)
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass

    user32 = ctypes.WinDLL("user32", use_last_error=True)
    dwm = ctypes.WinDLL("dwmapi")
    kernel32 = ctypes.WinDLL("kernel32")

    WNDENUMPROC = ctypes.WINFUNCTYPE(wt.BOOL, wt.HWND, wt.LPARAM)
    MONITORENUMPROC = ctypes.WINFUNCTYPE(wt.BOOL, wt.HANDLE, wt.HDC,
                                         ctypes.POINTER(wt.RECT), wt.LPARAM)

    user32.EnumWindows.argtypes = [WNDENUMPROC, wt.LPARAM]
    user32.IsWindowVisible.argtypes = [wt.HWND]
    user32.IsWindow.argtypes = [wt.HWND]
    user32.IsIconic.argtypes = [wt.HWND]
    user32.GetWindowTextLengthW.argtypes = [wt.HWND]
    user32.GetWindowTextW.argtypes = [wt.HWND, wt.LPWSTR, ctypes.c_int]
    user32.GetWindowRect.argtypes = [wt.HWND, ctypes.POINTER(wt.RECT)]
    user32.MonitorFromWindow.argtypes = [wt.HWND, wt.DWORD]
    user32.MonitorFromWindow.restype = wt.HANDLE
    user32.GetMonitorInfoW.argtypes = [wt.HANDLE, ctypes.POINTER(MONITORINFO)]
    user32.EnumDisplayMonitors.argtypes = [wt.HDC, ctypes.POINTER(wt.RECT),
                                           MONITORENUMPROC, wt.LPARAM]
    user32.RegisterHotKey.argtypes = [wt.HWND, ctypes.c_int, wt.UINT, wt.UINT]
    user32.UnregisterHotKey.argtypes = [wt.HWND, ctypes.c_int]
    user32.PeekMessageW.argtypes = [ctypes.POINTER(wt.MSG), wt.HWND, wt.UINT, wt.UINT, wt.UINT]
    user32.GetMessageW.argtypes = [ctypes.POINTER(wt.MSG), wt.HWND, wt.UINT, wt.UINT]
    user32.PostThreadMessageW.argtypes = [wt.DWORD, wt.UINT, wt.WPARAM, wt.LPARAM]
    dwm.DwmGetWindowAttribute.argtypes = [wt.HWND, wt.DWORD, ctypes.c_void_p, wt.DWORD]


def _window_title(hwnd):
    n = user32.GetWindowTextLengthW(hwnd)
    if n <= 0:
        return ""
    buf = ctypes.create_unicode_buffer(n + 1)
    user32.GetWindowTextW(hwnd, buf, n + 1)
    return buf.value


def _frame_rect(hwnd):
    """Rectangulo real de la ventana (sin sombras invisibles)."""
    r = wt.RECT()
    if dwm.DwmGetWindowAttribute(hwnd, 9, ctypes.byref(r), ctypes.sizeof(r)) != 0:
        user32.GetWindowRect(hwnd, ctypes.byref(r))
    return r.left, r.top, r.right, r.bottom


def list_monitors():
    """Monitores; el principal primero (suele coincidir con output_idx 0 de ddagrab)."""
    mons = []

    def cb(hmon, hdc, lprc, lparam):
        mi = MONITORINFO()
        mi.cbSize = ctypes.sizeof(MONITORINFO)
        user32.GetMonitorInfoW(hmon, ctypes.byref(mi))
        r = mi.rcMonitor
        mons.append({"hmon": hmon, "left": r.left, "top": r.top,
                     "w": r.right - r.left, "h": r.bottom - r.top,
                     "primary": bool(mi.dwFlags & 1)})
        return True

    proc = MONITORENUMPROC(cb)
    user32.EnumDisplayMonitors(None, None, proc, 0)
    mons.sort(key=lambda m: not m["primary"])
    return mons


def list_windows():
    out = []

    def cb(hwnd, lparam):
        if not user32.IsWindowVisible(hwnd) or user32.IsIconic(hwnd):
            return True
        title = _window_title(hwnd)
        if not title or title in ("Program Manager", APP_TITLE):
            return True
        cloaked = wt.DWORD(0)
        dwm.DwmGetWindowAttribute(hwnd, 14, ctypes.byref(cloaked), 4)
        if cloaked.value:
            return True
        l, t, r, b = _frame_rect(hwnd)
        if r - l < 64 or b - t < 64:
            return True
        out.append({"hwnd": hwnd, "title": title, "w": r - l, "h": b - t})
        return True

    proc = WNDENUMPROC(cb)
    user32.EnumWindows(proc, 0)
    return out


def window_region(hwnd):
    """(monitor_idx, x, y, w, h) de la ventana relativo a su monitor, con tamano par."""
    l, t, r, b = _frame_rect(hwnd)
    hmon = user32.MonitorFromWindow(hwnd, 2)  # MONITOR_DEFAULTTONEAREST
    mons = list_monitors()
    idx = next((i for i, m in enumerate(mons) if m["hmon"] == hmon), 0)
    m = mons[idx]
    l, t = max(l, m["left"]), max(t, m["top"])
    r, b = min(r, m["left"] + m["w"]), min(b, m["top"] + m["h"])
    w, h = (r - l) // 2 * 2, (b - t) // 2 * 2
    if w < 64 or h < 64:
        raise ValueError("ventana fuera del monitor")
    return idx, l - m["left"], t - m["top"], w, h


# ==========================================================================
# Utilidades
# ==========================================================================
def load_config():
    cfg = dict(DEFAULTS)
    try:
        cfg.update(json.loads(CONFIG_PATH.read_text(encoding="utf-8")))
    except Exception:
        pass
    if str(cfg.get("fps")) not in FPS_VALUES:
        cfg["fps"] = 60
    if cfg.get("res") not in RES_MODES:
        cfg["res"] = "native"
    if cfg.get("capture") not in CAPTURE_MODES:
        cfg["capture"] = "copy"
    if cfg.get("scaler") not in SCALERS:
        cfg["scaler"] = "bicubic"
    if cfg.get("quality") not in ("speed", "balanced", "quality", "high_quality"):
        cfg["quality"] = "balanced"
    if cfg.get("bframes") not in (0, 2):
        cfg["bframes"] = 0
    return cfg


def save_config(cfg):
    try:
        CONFIG_PATH.parent.mkdir(parents=True, exist_ok=True)
        CONFIG_PATH.write_text(json.dumps(cfg, indent=2), encoding="utf-8")
    except OSError:
        pass


def parse_hotkey(text):
    parts = [p.strip().lower() for p in text.split("+") if p.strip()]
    if not parts:
        raise ValueError("hotkey vacio")
    mods, key = 0, parts[-1]
    for m in parts[:-1]:
        if m not in MODS:
            raise ValueError(f"modificador desconocido: {m}")
        mods |= MODS[m]
    if key.startswith("f") and key[1:].isdigit() and 1 <= int(key[1:]) <= 24:
        vk = 0x70 + int(key[1:]) - 1
    elif len(key) == 1 and key.isalnum():
        vk = ord(key.upper())
    else:
        raise ValueError(f"tecla no soportada: {key} (usa F1-F24, letras o numeros)")
    return mods, vk


def find_ffmpeg(cfg):
    for c in (cfg.get("ffmpeg"), shutil.which("ffmpeg"), str(APP_DIR / "ffmpeg.exe"),
              str(APP_DIR / "ffmpeg" / "bin" / "ffmpeg.exe")):
        if c and os.path.isfile(c):
            return c
    return None


_preflight_ok = set()


def preflight(ffmpeg, codec, capture):
    """Devuelve None si todo OK, o un texto de error."""
    key = (ffmpeg, codec, capture)
    if key in _preflight_ok:
        return None
    try:
        enc = subprocess.run([ffmpeg, "-hide_banner", "-encoders"], capture_output=True,
                             text=True, creationflags=CREATE_NO_WINDOW).stdout
        flt = subprocess.run([ffmpeg, "-hide_banner", "-filters"], capture_output=True,
                             text=True, creationflags=CREATE_NO_WINDOW).stdout
    except OSError as e:
        return f"No se pudo ejecutar ffmpeg: {e}"
    if f"{codec}_amf" not in enc:
        extra = " (AV1 necesita ffmpeg 6.1 o superior)" if codec == "av1" else ""
        return f"Tu ffmpeg no incluye {codec}_amf{extra}. Descarga una build 'full'."
    if capture != "gdi" and "ddagrab" not in flt:
        return ("Tu ffmpeg no tiene ddagrab (necesita ffmpeg 6.0 o superior).\n"
                "Actualiza ffmpeg o elige la captura 'GDI'.")
    _preflight_ok.add(key)
    return None


def list_audio(ffmpeg):
    try:
        r = subprocess.run([ffmpeg, "-hide_banner", "-list_devices", "true", "-f", "dshow",
                            "-i", "dummy"], capture_output=True, text=True,
                           creationflags=CREATE_NO_WINDOW)
    except OSError:
        return []
    names = re.findall(r'"([^"]+)"\s+\(audio\)', r.stderr or "")
    return list(dict.fromkeys(names))


def tail(path, n=12):
    try:
        with open(path, "r", errors="replace") as f:
            lines = [l for l in f.read().replace("\r", "\n").split("\n") if l.strip()]
        return "\n".join(lines[-n:]).strip()
    except OSError:
        return "(sin log)"


# ==========================================================================
# Hotkey global (hilo propio con bucle de mensajes)
# ==========================================================================
class HotkeyListener:
    def __init__(self, callback):
        self.callback = callback
        self.thread = None
        self.tid = None
        self.ok = False

    def start(self, mods, vk):
        self.stop()
        ready = threading.Event()

        def run():
            self.tid = kernel32.GetCurrentThreadId()
            msg = wt.MSG()
            user32.PeekMessageW(ctypes.byref(msg), None, 0, 0, 0)  # crea la cola de mensajes
            self.ok = bool(user32.RegisterHotKey(None, 1, mods | MOD_NOREPEAT, vk))
            ready.set()
            if not self.ok:
                return
            while user32.GetMessageW(ctypes.byref(msg), None, 0, 0) > 0:
                if msg.message == WM_HOTKEY:
                    try:
                        self.callback()
                    except Exception:
                        pass
            user32.UnregisterHotKey(None, 1)

        self.thread = threading.Thread(target=run, daemon=True)
        self.thread.start()
        ready.wait(2)
        return self.ok

    def stop(self):
        if self.thread and self.thread.is_alive() and self.tid:
            user32.PostThreadMessageW(self.tid, WM_QUIT, 0, 0)
            self.thread.join(1)
        self.thread = None
        self.ok = False


# ==========================================================================
# Grabador (ffmpeg en segmentos + buffer circular)
# ==========================================================================
class Recorder:
    def __init__(self, limits):
        self.limits = limits          # {"buffer": s, "clip": s}  (editable en vivo)
        self.proc = None
        self.lock = threading.Lock()
        self.busy = threading.Event()
        self.stop_evt = threading.Event()
        self.seg_dir = None
        self.log_path = None
        self.log = None

    # ---- comando ffmpeg
    @staticmethod
    def hls_args(seg_dir):
        """Salida: fMP4 (HLS) sin temp_file para buffer en vivo."""
        return ["-f", "hls", "-hls_time", str(HLS_TIME), "-hls_list_size", "700",
                "-hls_segment_type", "fmp4",
                "-hls_flags", "independent_segments",
                "-hls_fmp4_init_filename", "init.mp4",
                "-hls_segment_filename", str(Path(seg_dir) / "seg_%08d.m4s"),
                str(Path(seg_dir) / "live.m3u8")]

    @staticmethod
    def build_cmd(ffmpeg, cfg, src, seg_dir):
        fps, mouse = cfg["fps"], int(cfg["mouse"])
        mode, codec, res = cfg["capture"], cfg["codec"], cfg.get("res", "native")
        # info + stats cada 5 s: el log muestra fps reales, dup, drop y speed
        cmd = [ffmpeg, "-hide_banner", "-loglevel", "info", "-stats", "-stats_period", "5", "-y"]

        # escalado por CPU (solo si se pide una resolucion; nunca agranda)
        scale = ""
        if res != "native":
            scale = (f"scale=-2:'min({int(res)},ih)':flags={cfg.get('scaler', 'bicubic')}"
                     ":out_color_matrix=bt709:out_range=tv")

        if mode == "gdi":
            target = f"title={src['title']}" if src["kind"] == "window" else "desktop"
            cmd += ["-f", "gdigrab", "-framerate", str(fps), "-draw_mouse", str(mouse),
                    "-i", target]
            vf = ["-vf", ",".join([scale or "scale=trunc(iw/2)*2:trunc(ih/2)*2:out_color_matrix=bt709:out_range=tv", "format=nv12"])]
        else:
            dd = f"ddagrab=output_idx={src.get('monitor', 0)}:framerate={fps}:draw_mouse={mouse}"
            if "x" in src:  # region de una ventana
                dd += f":video_size={src['w']}x{src['h']}:offset_x={src['x']}:offset_y={src['y']}"
            cmd += ["-f", "lavfi", "-i", dd]
            # si la fuente ya es <= a la resolucion pedida, no se escala ni convierte en CPU
            sh = src.get("sh")
            need_scale = bool(scale) and not (sh and sh <= int(res))
            chain = ["hwdownload", "format=bgra"] + ([scale, "format=nv12"] if need_scale else [])
            vf = ["-vf", ",".join(chain)]

        if cfg["audio"]:
            # buffer de audio moderado (100 ms por defecto) y cola grande: evita que el audio en rafagas
            # retrase al resto del pipeline
            cmd += ["-thread_queue_size", "1024", "-rtbufsize", "64M", "-f", "dshow",
                    "-audio_buffer_size", str(cfg.get("audio_buf", 100)), "-i", f"audio={cfg['audio']}"]
        cmd += ["-map", "0:v"]
        if cfg["audio"]:
            cmd += ["-map", "1:a"]

        q = cfg["quality"]
        if codec != "av1" and q == "high_quality":   # 'high_quality' solo existe en av1_amf
            q = "quality"
        cmd += ["-c:v", f"{codec}_amf", "-quality", q,
                "-rc", "cbr", "-b:v", f"{cfg['bitrate']}M", "-g", str(fps),
                "-bf", str(cfg.get("bframes", 0))]
        if codec != "av1":
            cmd += ["-forced_idr", "1"]
        # etiquetas de color: el clip se interpreta como BT.709 (igual que la conversion)
        cmd += ["-colorspace", "bt709", "-color_primaries", "bt709", "-color_trc", "bt709",
                "-color_range", "tv"]
        cmd += vf
        cmd += ["-fps_mode", "vfr"]   # conserva los tiempos reales de captura

        if cfg["audio"]:
            cmd += ["-c:a", "aac", "-b:a", "160k"]

        cmd += Recorder.hls_args(seg_dir)
        return cmd

    def playlist(self):
        """[(duracion_s, Path)] de los segmentos COMPLETOS, del mas antiguo al mas reciente.
        Si la playlist HLS no está lista todavía, usa los .m4s reales del directorio como fallback."""
        if not self.seg_dir:
            return []

        txt = ""
        for _ in range(20):
            try:
                txt = (self.seg_dir / "live.m3u8").read_text(encoding="utf-8", errors="replace")
                if txt.strip():
                    break
            except OSError:
                pass
            time.sleep(0.05)

        out, dur = [], None
        seen = set()

        for line in txt.splitlines():
            line = line.strip()
            if not line or line.startswith("#"):
                if line.startswith("#EXTINF:"):
                    try:
                        dur = float(line[8:].split(",")[0])
                    except (ValueError, IndexError):
                        dur = None
                continue

            if not line.lower().endswith(".m4s"):
                continue

            p = self.seg_dir / line
            if not p.exists():
                continue

            if p.name in seen:
                continue
            seen.add(p.name)

            if dur is not None:
                out.append((dur, p))
            dur = None

        if out:
            return out

        # Fallback: si la playlist aún no está lista, usa los segmentos reales del directorio
        files = sorted(self.seg_dir.glob("seg_*.m4s"), key=lambda f: f.name)
        for f in files:
            if f.name in seen:
                continue
            out.append((HLS_TIME, f))

        return out

    def buffered_seconds(self):
        return min(int(sum(d for d, _ in self.playlist())), self.limits["buffer"])

    def alive(self):
        return self.proc is not None and self.proc.poll() is None

    # ---- start / stop
    def start(self, ffmpeg, cfg, src):
        pid = os.getpid()
        self.seg_dir = Path(tempfile.gettempdir()) / f"replaybuf_{pid}"
        shutil.rmtree(self.seg_dir, ignore_errors=True)
        self.seg_dir.mkdir(parents=True, exist_ok=True)
        self.log_path = self.seg_dir.parent / f"replaybuf_{pid}.log"
        cmd = self.build_cmd(ffmpeg, cfg, src, self.seg_dir)
        self.log = open(self.log_path, "w", encoding="utf-8", errors="replace")
        self.log.write(" ".join(cmd) + "\n\n")
        self.log.flush()
        self.proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=self.log,
                                     stderr=self.log,
                                     creationflags=CREATE_NO_WINDOW | NORMAL_PRIORITY_CLASS)
        self.stop_evt = threading.Event()
        threading.Thread(target=self._cleaner, args=(self.stop_evt,), daemon=True).start()

    def stop(self):
        self.stop_evt.set()
        if self.proc is not None:
            if self.proc.poll() is None:
                try:
                    self.proc.stdin.write(b"q")
                    self.proc.stdin.flush()
                    self.proc.wait(timeout=5)
                except Exception:
                    self.proc.kill()
            self.proc = None
        if self.log:
            self.log.close()
            self.log = None
        if self.seg_dir:
            shutil.rmtree(self.seg_dir, ignore_errors=True)

    def _cleaner(self, stop_evt):
        """Buffer circular: conserva solo los ultimos N segundos (segun duracion real)."""
        while not stop_evt.wait(1.0):
            with self.lock:
                need, total, first_keep = self.limits["buffer"] + 3, 0.0, None
                for dur, path in reversed(self.playlist()):
                    total += dur
                    first_keep = path
                    if total >= need:
                        break
                if first_keep is None:
                    continue
                for f in self.seg_dir.glob("seg_*.m4s"):
                    if f.name < first_keep.name:
                        try:
                            f.unlink()
                        except OSError:
                            pass

    # ---- guardar clip
    def save_clip(self, ffmpeg, out_dir):
        """Devuelve (ok, ruta_o_mensaje)."""
        if self.busy.is_set():
            return False, "Ya se está guardando un clip."
        self.busy.set()
        try:
            with self.lock:
                entries = self.playlist()
                init = self.seg_dir / "init.mp4" if self.seg_dir else None

                if not entries or not init or not init.exists():
                    return False, "El buffer está vacío. Espera a que se llene y vuelve a intentarlo."

                total = sum(d for d, _ in entries)
                if total < 1.0:
                    return False, "Todavía no hay suficiente video en el buffer."

                chosen, clip_total = [], 0.0
                for dur, path in reversed(entries):
                    chosen.append(path)
                    clip_total += dur
                    if clip_total >= self.limits["clip"]:
                        break

                chosen.reverse()

                Path(out_dir).mkdir(parents=True, exist_ok=True)
                out = Path(out_dir) / f"clip_{datetime.now():%Y-%m-%d_%H-%M-%S}.mp4"
                join = self.seg_dir / "join.mp4"
                err = ""

                try:
                    with open(join, "wb") as w:
                        for part in [init] + chosen:
                            with open(part, "rb") as r:
                                shutil.copyfileobj(r, w, 1 << 20)

                    res = subprocess.run(
                        [ffmpeg, "-hide_banner", "-loglevel", "error", "-y",
                         "-i", str(join),
                         "-c", "copy", "-movflags", "+faststart", str(out)],
                        capture_output=True, text=True, creationflags=CREATE_NO_WINDOW
                    )
                    ok = res.returncode == 0 and out.exists()
                    if not ok:
                        err_line = (res.stderr or "").strip().splitlines()
                        err = err_line[-1] if err_line else "No se pudo crear el clip."

                except OSError as e:
                    ok, err = False, str(e)
                finally:
                    try:
                        join.unlink()
                    except OSError:
                        pass

            if ok:
                try:
                    import winsound
                    winsound.Beep(1000, 120)
                except Exception:
                    pass
                return True, str(out)

            return False, "No se pudo crear el clip. " + err

        finally:
            self.busy.clear()


# ==========================================================================
# Interfaz
# ==========================================================================
class App:
    SCREEN_LABEL = "Pantalla completa"

    def __init__(self):
        self.cfg = load_config()
        self.root = tk.Tk()
        apply_dark_theme(self.root)
        self.root.title(APP_TITLE)
        self.root.resizable(False, False)
        self.root.configure(bg="#1a1a1a")

        self.events = queue.Queue()
        self.limits = {"buffer": 30, "clip": 30}
        self.rec = Recorder(self.limits)
        self.hotkey = HotkeyListener(self.request_save)
        self.running = False
        self.windows = []
        self.monitors = list_monitors()
        self.out_dir = self.cfg["out_dir"]
        self.ffmpeg = find_ffmpeg(self.cfg)
        self.audio_devices = list_audio(self.ffmpeg) if self.ffmpeg else []
        self.locked = []

        self._build_ui()
        self.refresh_windows()
        self._sync_limits()
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.root.after(500, self.tick)

    # ---------------------------------------------------------------- UI
    def _build_ui(self):
        c = self.cfg
        main = ttk.Frame(self.root, padding=12)
        main.grid(sticky="nsew")

        top = ttk.Frame(main)
        top.grid(row=0, column=0, sticky="ew", pady=(0, 12))
        self.btn_toggle = ttk.Button(top, text="▶ Activar replay buffer", width=24,
                                     command=self.toggle)
        self.btn_toggle.grid(row=0, column=0, padx=(0, 12))
        self.lbl_status = tk.Label(top, text="● Desactivado", fg="#666666", anchor="w",
                                   font=("Segoe UI", 10, "bold"), bg="#1a1a1a")
        self.lbl_status.grid(row=0, column=1, padx=12)

        f = ttk.LabelFrame(main, text="⏱ Duración", padding=10)
        f.grid(row=1, column=0, sticky="ew", pady=(0, 8))
        self.v_buffer = tk.StringVar(value=str(c["buffer_s"]))
        self.v_clip = tk.StringVar(value=str(c["clip_s"]))
        self.v_hotkey = tk.StringVar(value=c["hotkey"])
        ttk.Label(f, text="Buffer (s):").grid(row=0, column=0, sticky="w")
        ttk.Spinbox(f, from_=5, to=600, width=6, textvariable=self.v_buffer).grid(row=0, column=1, padx=8)
        ttk.Label(f, text="Clip a guardar (s):").grid(row=0, column=2, sticky="w", padx=(12, 0))
        ttk.Spinbox(f, from_=5, to=600, width=6, textvariable=self.v_clip).grid(row=0, column=3, padx=8)
        ttk.Label(f, text="Hotkey:").grid(row=1, column=0, sticky="w", pady=(8, 0))
        e = ttk.Entry(f, width=14, textvariable=self.v_hotkey)
        e.grid(row=1, column=1, columnspan=2, sticky="w", padx=8, pady=(8, 0))
        self.locked.append(e)
        self.v_buffer.trace_add("write", self._sync_limits)
        self.v_clip.trace_add("write", self._sync_limits)

        f = ttk.LabelFrame(main, text="📹 Qué clipear", padding=10)
        f.grid(row=2, column=0, sticky="ew", pady=(0, 8))
        self.cb_source = ttk.Combobox(f, state="readonly", width=48)
        self.cb_source.grid(row=0, column=0, columnspan=2, sticky="ew")
        self.cb_source.bind("<<ComboboxSelected>>", lambda e: self._on_source_change())
        b = ttk.Button(f, text="↻ Refrescar", width=10, command=self.refresh_windows)
        b.grid(row=0, column=2, padx=(8, 0))
        self.locked += [self.cb_source, b]

        ttk.Label(f, text="Monitor:").grid(row=1, column=0, sticky="w", pady=(8, 0))
        labels = [f"Monitor {i + 1} ({m['w']}x{m['h']})" + (" [principal]" if m["primary"] else "")
                  for i, m in enumerate(self.monitors)] or ["Monitor 1"]
        self.cb_monitor = ttk.Combobox(f, state="readonly", width=30, values=labels)
        self.cb_monitor.current(0)
        self.cb_monitor.grid(row=1, column=1, sticky="w", pady=(8, 0))
        self.locked.append(self.cb_monitor)

        self.v_mouse = tk.BooleanVar(value=c["mouse"])
        cm = ttk.Checkbutton(f, text="Mostrar cursor", variable=self.v_mouse)
        cm.grid(row=2, column=0, columnspan=3, sticky="w", pady=(8, 0))
        ttk.Label(f, text="Captura:").grid(row=3, column=0, sticky="w", pady=(8, 0))
        self.cb_capture = ttk.Combobox(f, state="readonly", width=42,
                                       values=list(CAPTURE_MODES.values()))
        self.cb_capture.set(CAPTURE_MODES.get(c.get("capture"), CAPTURE_MODES["copy"]))
        self.cb_capture.grid(row=3, column=1, columnspan=2, sticky="w", pady=(8, 0))
        self.locked += [cm, self.cb_capture]

        f = ttk.LabelFrame(main, text="⚙ Calidad de grabación", padding=10)
        f.grid(row=3, column=0, sticky="ew", pady=(0, 8))
        self.v_codec = tk.StringVar(value=c["codec"])
        self.v_fps = tk.StringVar(value=str(c["fps"]))
        self.v_bitrate = tk.StringVar(value=str(c["bitrate"]))
        self.v_quality = tk.StringVar(value=c["quality"])
        self.v_audio = tk.StringVar(value=c["audio"] or "(sin audio)")

        ttk.Label(f, text="Codec:").grid(row=0, column=0, sticky="w")
        w1 = ttk.Combobox(f, state="readonly", width=7, textvariable=self.v_codec,
                          values=["av1", "h264", "hevc"])
        w1.grid(row=0, column=1, padx=8)
        ttk.Label(f, text="FPS:").grid(row=0, column=2, sticky="w", padx=(12, 0))
        w2 = ttk.Combobox(f, state="readonly", width=5, textvariable=self.v_fps, values=FPS_VALUES)
        w2.grid(row=0, column=3, padx=8)
        ttk.Label(f, text="Bitrate (Mbps):").grid(row=1, column=0, sticky="w", pady=(8, 0))
        w3 = ttk.Spinbox(f, from_=2, to=200, width=6, textvariable=self.v_bitrate)
        w3.grid(row=1, column=1, padx=8, pady=(8, 0))
        ttk.Label(f, text="Preset:").grid(row=1, column=2, sticky="w", padx=(12, 0), pady=(8, 0))
        w4 = ttk.Combobox(f, state="readonly", width=12, textvariable=self.v_quality,
                          values=["speed", "balanced", "quality", "high_quality"])
        w4.grid(row=1, column=3, padx=8, pady=(8, 0))

        ttk.Label(f, text="Resolución:").grid(row=2, column=0, sticky="w", pady=(8, 0))
        self.cb_res = ttk.Combobox(f, state="readonly", width=19, values=list(RES_MODES.values()))
        self.cb_res.set(RES_MODES.get(c.get("res"), RES_MODES["native"]))
        self.cb_res.grid(row=2, column=1, sticky="w", padx=8, pady=(8, 0))
        ttk.Label(f, text="Escalado:").grid(row=2, column=2, sticky="w", padx=(12, 0), pady=(8, 0))
        self.cb_scaler = ttk.Combobox(f, state="readonly", width=11, values=list(SCALERS.values()))
        self.cb_scaler.set(SCALERS.get(c.get("scaler"), SCALERS["bicubic"]))
        self.cb_scaler.grid(row=2, column=3, padx=8, pady=(8, 0))

        ttk.Label(f, text="Audio:").grid(row=3, column=0, sticky="w", pady=(8, 0))
        self.cb_audio = ttk.Combobox(f, state="readonly", width=40, textvariable=self.v_audio,
                                     values=["(sin audio)"] + self.audio_devices)
        self.cb_audio.grid(row=3, column=1, columnspan=3, sticky="w", padx=8, pady=(8, 0))

        ttk.Label(f, text="B-frames:").grid(row=4, column=0, sticky="w", pady=(8, 0))
        self.v_bf = tk.StringVar(value=str(c.get("bframes", 0)))
        cb_bf = ttk.Combobox(f, state="readonly", width=5, textvariable=self.v_bf, values=["0", "2"])
        cb_bf.grid(row=4, column=1, sticky="w", padx=8, pady=(8, 0))
        ttk.Label(f, text="Buffer audio (ms):").grid(row=4, column=2, sticky="w", padx=(12, 0), pady=(8, 0))
        self.v_abuf = tk.StringVar(value=str(c.get("audio_buf", 100)))
        sp_abuf = ttk.Spinbox(f, from_=20, to=1000, increment=20, width=6, textvariable=self.v_abuf)
        sp_abuf.grid(row=4, column=3, sticky="w", padx=8, pady=(8, 0))

        txt_info = tk.Label(f, justify="left", foreground="#999999", wraplength=440,
                           text="💡 Bitrate: más = mejor imagen. Preset: 'balanced' es equilibrado. "
                                "Si ves borroso: escalado 'Nítido' o sin escalar.",
                           bg="#1a1a1a", font=("Segoe UI", 8))
        txt_info.grid(row=5, column=0, columnspan=4, sticky="w", pady=(10, 0))

        self.locked += [w1, w2, w3, w4, self.cb_res, self.cb_scaler, self.cb_audio, cb_bf, sp_abuf]
        self._normal_states = {w: ("readonly" if isinstance(w, ttk.Combobox)
                                   else "normal") for w in self.locked}

        f = ttk.Frame(main)
        f.grid(row=4, column=0, sticky="ew", pady=(8, 0))
        self.lbl_dir = ttk.Label(f, text="", width=44, anchor="w")
        self.lbl_dir.grid(row=0, column=0, sticky="w")
        ttk.Button(f, text="📁 Carpeta…", command=self.choose_dir).grid(row=0, column=1, padx=4)
        ttk.Button(f, text="📂 Abrir", command=self.open_dir).grid(row=0, column=2)
        self._update_dir_label()

        f = ttk.Frame(main)
        f.grid(row=5, column=0, sticky="ew", pady=(12, 0))
        self.btn_save = ttk.Button(f, text="💾 Guardar clip ahora", command=self.request_save, width=24)
        self.btn_save.grid(row=0, column=0, padx=(0, 12))
        self.lbl_msg = tk.Label(f, text="", foreground="#4a9d6f", bg="#1a1a1a",
                               font=("Segoe UI", 9))
        self.lbl_msg.grid(row=0, column=1, padx=10, sticky="w")
        for wdg in (w1, w2, self.cb_res):
            wdg.bind("<<ComboboxSelected>>", self._suggest_bitrate)

    def _suggest_bitrate(self, *_):
        """Sugiere un bitrate segun codec, resolucion y fps (editable despues)."""
        key = next((k for k, v in RES_MODES.items() if v == self.cb_res.get()), "native")
        h = 1080 if key == "native" else int(key)
        base = BITRATE_AV1.get((h, self._int(self.v_fps, 10, 240, 60)), 8)
        factor = BITRATE_FACTOR.get(self.v_codec.get(), 1.0)
        self.v_bitrate.set(str(max(2, round(base * factor))))

    def _update_dir_label(self):
        d = self.out_dir
        self.lbl_dir.config(text=("…" + d[-42:]) if len(d) > 44 else d)

    def choose_dir(self):
        d = filedialog.askdirectory(initialdir=self.out_dir, title="Carpeta de clips")
        if d:
            self.out_dir = d
            self._update_dir_label()

    def open_dir(self):
        Path(self.out_dir).mkdir(parents=True, exist_ok=True)
        os.startfile(self.out_dir)

    def refresh_windows(self):
        self.windows = list_windows()
        values = [self.SCREEN_LABEL] + [f"{w['title'][:55]}  ({w['w']}x{w['h']})"
                                        for w in self.windows]
        self.cb_source.config(values=values)
        self.cb_source.current(0)
        self._on_source_change()

    def _on_source_change(self):
        is_screen = self.cb_source.current() <= 0
        if not self.running:
            self.cb_monitor.config(state="readonly" if is_screen else "disabled")

    def _set_locked(self, locked):
        for w in self.locked:
            if locked:
                w.config(state="disabled")
            else:
                w.config(state=self._normal_states.get(w, "normal"))
        if not locked:
            self._on_source_change()

    @staticmethod
    def _int(var, lo, hi, default):
        try:
            v = int(float(var.get()))
        except (ValueError, tk.TclError):
            return default
        return max(lo, min(hi, v))

    def _sync_limits(self, *_):
        b = self._int(self.v_buffer, 5, 600, 30)
        c = self._int(self.v_clip, 5, 600, 30)
        self.limits["buffer"] = b
        self.limits["clip"] = min(c, b)

    def _read_cfg(self):
        cfg = dict(self.cfg)
        audio = self.v_audio.get()
        cfg.update(
            buffer_s=self.limits["buffer"], clip_s=self.limits["clip"],
            fps=self._int(self.v_fps, 10, 240, 60),
            bitrate=self._int(self.v_bitrate, 2, 200, 20),
            codec=self.v_codec.get(), quality=self.v_quality.get(),
            hotkey=self.v_hotkey.get().strip().lower() or "f9",
            mouse=bool(self.v_mouse.get()),
            bframes=self._int(self.v_bf, 0, 2, 0),
            audio_buf=self._int(self.v_abuf, 20, 1000, 100),
            scaler=next((k for k, v in SCALERS.items() if v == self.cb_scaler.get()), "bicubic"),
            res=next((k for k, v in RES_MODES.items() if v == self.cb_res.get()), "native"),
            capture=next((k for k, v in CAPTURE_MODES.items() if v == self.cb_capture.get()), "copy"),
            audio="" if audio.startswith("(") else audio,
            out_dir=self.out_dir, ffmpeg=self.ffmpeg or "")
        return cfg

    def _resolve_source(self, cfg):
        i = self.cb_source.current()
        if i <= 0:
            mi = max(0, self.cb_monitor.current())
            src = {"kind": "screen", "monitor": mi}
            if mi < len(self.monitors):
                src.update(sw=self.monitors[mi]["w"], sh=self.monitors[mi]["h"])
            return src, None
        w = self.windows[i - 1]
        if not user32.IsWindow(w["hwnd"]) or user32.IsIconic(w["hwnd"]):
            return None, "La ventana ya no está disponible o está minimizada.\nPulsa ↻ para refrescar la lista."
        region = None
        try:
            region = window_region(w["hwnd"])
        except ValueError:
            if cfg["capture"] != "gdi":
                return None, "No se pudo calcular la zona de la ventana (¿está fuera de pantalla?)."
        src = {"kind": "window", "title": w["title"]}
        if region and cfg["capture"] != "gdi":
            src.update(monitor=region[0], x=region[1], y=region[2], w=region[3], h=region[4],
                       sw=region[3], sh=region[4])
        return src, None

    def toggle(self):
        if self.running:
            self.stop()
        else:
            self.start()

    def start(self):
        if not self.ffmpeg:
            path = filedialog.askopenfilename(title="Localiza ffmpeg.exe",
                                              filetypes=[("ffmpeg", "ffmpeg.exe")])
            if not path:
                return
            self.ffmpeg = path
            self.audio_devices = list_audio(path)
            self.cb_audio.config(values=["(sin audio)"] + self.audio_devices)

        cfg = self._read_cfg()
        src, err = self._resolve_source(cfg)
        if err:
            messagebox.showwarning(APP_TITLE, err)
            return
        err = preflight(self.ffmpeg, cfg["codec"], cfg["capture"])
        if err:
            messagebox.showerror(APP_TITLE, err)
            return
        try:
            mods, vk = parse_hotkey(cfg["hotkey"])
        except ValueError as e:
            messagebox.showerror(APP_TITLE, f"Hotkey no válido: {e}")
            return
        if not self.hotkey.start(mods, vk):
            messagebox.showerror(APP_TITLE, f"No se pudo registrar el hotkey '{cfg['hotkey']}'. "
                                            "¿Lo está usando otra aplicación?")
            return

        self.cfg = cfg
        save_config(cfg)
        self.rec.start(self.ffmpeg, cfg, src)
        self.running = True
        self.btn_toggle.config(text="⏹ Desactivar replay buffer")
        self._set_locked(True)
        self._set_status()

    def stop(self):
        self.hotkey.stop()
        self.rec.stop()
        self.running = False
        self.btn_toggle.config(text="▶ Activar replay buffer")
        self._set_locked(False)
        self.lbl_status.config(text="● Desactivado", fg="#666666")

    def request_save(self):
        if not self.running:
            self.events.put(("fail", "Activa el buffer primero."))
            return
        threading.Thread(target=self._save_worker, daemon=True).start()

    def _save_worker(self):
        ok, info = self.rec.save_clip(self.ffmpeg, self.out_dir)
        self.events.put(("ok" if ok else "fail", info))

    def _set_status(self):
        n = self.rec.buffered_seconds()
        self.lbl_status.config(text=f"● Grabando · {n}s en buffer · clip de {self.limits['clip']}s ({self.cfg['hotkey'].upper()})",
                               fg="#4a9d6f")

    def tick(self):
        while True:
            try:
                kind, info = self.events.get_nowait()
            except queue.Empty:
                break
            if kind == "ok":
                self.lbl_msg.config(text=f"✓ {Path(info).name}", foreground="#4a9d6f")
            else:
                self.lbl_msg.config(text=f"✗ {info}", foreground="#d97e7e")

        if self.running:
            if not self.rec.alive():
                log = tail(self.rec.log_path)
                self.stop()
                messagebox.showerror(APP_TITLE,
                    "ffmpeg se cerró inesperadamente. Últimas líneas del log:\n\n" + log +
                    "\n\nPrueba la captura 'GDI' o revisa que tu ffmpeg sea una build 'full'.")
            else:
                self._set_status()
        self.root.after(500, self.tick)

    def on_close(self):
        if self.running:
            self.stop()
        save_config(self._read_cfg())
        self.root.destroy()

    def run(self):
        self.root.mainloop()


def main():
    if os.name != "nt":
        print("Este programa es solo para Windows.")
        sys.exit(1)
    try:
        App().run()
    except Exception as e:
        try:
            messagebox.showerror(APP_TITLE, f"Error inesperado:\n{e}")
        except Exception:
            pass
        raise


if __name__ == "__main__":
    main()
