"""Makima live-wallpaper -> animated GIF, with an interactive CROP UI.

Run it (`python render_wallpaper.py`): a window opens on the real WE background.
Drag the crop box to position it, pick an aspect ratio / size, then 'Render
GIF' to bake the falling-leaves + red-bokeh effect (real WE assets, JSON-matched
motion) onto the crop at native resolution. 'Save crop PNG' exports just the
still. The effect itself is unchanged from the approved version; only the crop
is now chosen in the UI instead of hard-coded.
"""
import os
import math
import random
import threading
import tkinter as tk
from tkinter import ttk, filedialog

import sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from PIL import Image, ImageChops, ImageFilter, ImageTk  # noqa: E402
import ascii_steam  # noqa: E402
import we_tex  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
PKGDIR = os.path.join(HERE, "3558307409_VSTHEMES-ORG", "3558307409")
BG_PATH = os.path.join(PKGDIR, "Makima_source_1920x1080.png")
WE = ("E:/Sonnie/Personal/Steam/steamapps/common/wallpaper_engine/assets/"
      "materials/")
DEFAULT_OUT = os.path.join(HERE, "Makima_portrait.gif")

FRAMES = 90              # 30 fps * 3 s seamless loop
FRAME_MS = 33            # 30 fps, like the real wallpaper
N_LEAVES = 50
N_HALO = 42

# Aspect ratios (width / height). None = free (independent width & height).
RATIOS = {
    "Free": None,
    "Profile bg 506:928": 506 / 928,
    "9:16": 9 / 16,
    "2:3": 2 / 3,
    "3:4": 3 / 4,
    "1:1": 1.0,
    "16:9": 16 / 9,
}

_SPRITES = None


def _sprites():
    global _SPRITES
    if _SPRITES is None:
        _SPRITES = (
            [f.convert("RGBA") for f in we_tex.decode_sprites(WE + "particle/nature/leaves1.tex")],
            [f.convert("RGBA") for f in we_tex.decode_sprites(WE + "particle/nature/leaves2.tex")],
            we_tex.decode_sprites(WE + "particle/halo.tex")[0].convert("RGBA"),
        )
    return _SPRITES


def scaled(spr, target_h, ang=0.0, alpha=1.0):
    w = max(1, int(spr.width * target_h / spr.height))
    out = spr.resize((w, target_h), Image.LANCZOS)
    if ang:
        out = out.rotate(ang, resample=Image.BICUBIC, expand=True)
    if alpha < 1.0:
        a = out.split()[3].point(lambda v: int(v * alpha))
        out.putalpha(a)
    return out


def add_region(base_rgb, glow_rgba, x, y):
    gw, gh = glow_rgba.size
    x0, y0 = int(x - gw / 2), int(y - gh / 2)
    bx0, by0 = max(0, x0), max(0, y0)
    bx1, by1 = min(base_rgb.width, x0 + gw), min(base_rgb.height, y0 + gh)
    if bx1 <= bx0 or by1 <= by0:
        return
    crop = glow_rgba.crop((bx0 - x0, by0 - y0, bx1 - x0, by1 - y0))
    rgb = Image.new("RGB", crop.size, (0, 0, 0))
    rgb.paste(crop, (0, 0), crop)
    region = base_rgb.crop((bx0, by0, bx1, by1))
    base_rgb.paste(ImageChops.add(region, rgb), (bx0, by0))


def render_effect(bg, out_path):
    """Bake the falling-leaves + bokeh effect onto `bg` (PIL RGB) at its native
    resolution and save a seamless animated GIF. Returns (path, mb)."""
    bg = bg.convert("RGB")
    W, H = bg.size
    S = H / 1080.0                       # source(1080 tall) -> this crop's scale
    MARGIN = max(120, int(0.2 * H))
    leaves1, leaves2, halo = _sprites()
    rng = random.Random(7411)
    domX, domY = W + 2 * MARGIN, H + 2 * MARGIN
    loop_s = FRAMES * FRAME_MS / 1000.0

    leaves = []
    for _ in range(N_LEAVES):
        sheet = leaves1 if rng.random() < 0.78 else leaves2
        size19 = rng.uniform(40, 130)
        dof = abs(size19 - 75) / 30.0
        vx19 = -rng.uniform(68, 135)                 # left
        vy19 = rng.uniform(20, 135)                  # down
        leaves.append({
            "sheet": sheet, "h": max(6, int(size19 * S)),
            "blur": min(3.4, dof * 1.5),
            "depth_a": 1.0 if size19 < 95 else 0.84,
            "phase": rng.random(),
            "x0": rng.uniform(0, domX), "y0": rng.uniform(0, domY),
            "travelX": vx19 * loop_s * S, "travelY": vy19 * loop_s * S,
            "swayA": rng.uniform(35, 100) * 0.35 * S,
            "swayCyc": rng.choice([1.5, 2, 2.5, 3]), "swayPh": rng.random(),
            "spin": rng.uniform(-0.5, 0.5), "ang0": rng.uniform(0, 360),
            "animCycles": 3, "animPh": rng.random(),
            "alpha": 0.68 * rng.uniform(0.82, 1.0),
        })

    halos = []
    for _ in range(N_HALO):
        size19 = rng.uniform(50, 200) * 1.97
        r = rng.randint(77, 233)
        glow = Image.new("RGBA", halo.size, (0, 0, 0, 0))
        tint = Image.new("RGBA", halo.size, (r, rng.randint(0, 6), rng.randint(0, 6), 255))
        glow = Image.composite(tint, glow, halo.split()[3])
        ang = rng.uniform(0, 2 * math.pi)
        drift = rng.uniform(15, 50) * loop_s * S
        halos.append({
            "img": glow, "h": max(6, int(size19 * S)),
            "x0": rng.uniform(0, W), "y0": rng.uniform(0, H),
            "vx": math.cos(ang) * drift, "vy": math.sin(ang) * drift,
            "phase": rng.random(), "blur": rng.uniform(2, 6),
            "peak": rng.uniform(0.42, 0.72),
        })

    out_frames, durs = [], []
    for f in range(FRAMES):
        t = f / FRAMES
        frame = bg.copy()
        for h in halos:
            u = (h["phase"] + t) % 1.0
            x = (h["x0"] + h["vx"] * u + MARGIN) % domX - MARGIN
            y = (h["y0"] + h["vy"] * u + MARGIN) % domY - MARGIN
            g = scaled(h["img"], h["h"], alpha=h["peak"] * math.sin(math.pi * u))
            g = g.filter(ImageFilter.GaussianBlur(h["blur"]))
            add_region(frame, g, x, y)
        frame = frame.convert("RGBA")
        for p in leaves:
            u = (p["phase"] + t) % 1.0
            sway = p["swayA"] * math.sin(2 * math.pi * (p["swayCyc"] * u + p["swayPh"]))
            x = (p["x0"] + p["travelX"] * u) % domX - MARGIN
            y = (p["y0"] + p["travelY"] * u) % domY - MARGIN + sway
            fade = min(1.0, u / 0.12, (1.0 - u) / 0.12)
            fi = int((p["animPh"] + p["animCycles"] * u) * len(p["sheet"])) % len(p["sheet"])
            spr = scaled(p["sheet"][fi], p["h"], ang=p["ang0"] + 360 * p["spin"] * u,
                         alpha=p["alpha"] * p["depth_a"] * max(0, fade))
            if p["blur"] > 0.3:
                spr = spr.filter(ImageFilter.GaussianBlur(p["blur"]))
            frame.alpha_composite(spr, (int(x - spr.width / 2), int(y - spr.height / 2)))
        out_frames.append(frame.convert("RGB"))
        durs.append(FRAME_MS)

    ascii_steam._save_animated_gif(out_frames, durs, out_path,
                                   grayscale=False, max_bytes=None)
    return out_path, os.path.getsize(out_path) / (1024 * 1024)


class CropUI:
    DISP_W = 880

    def __init__(self, root):
        self.root = root
        root.title("Makima — crop & render")
        self.src = Image.open(BG_PATH).convert("RGB")
        self.iw, self.ih = self.src.size

        top = ttk.Frame(root, padding=8)
        top.pack(side="top", fill="x")
        ttk.Button(top, text="Open image…", command=self.open_img).pack(side="left")
        ttk.Label(top, text="Ratio:").pack(side="left", padx=(14, 4))
        self.ratio_var = tk.StringVar(value="Profile bg 506:928")
        rb = ttk.Combobox(top, textvariable=self.ratio_var, width=18,
                          state="readonly", values=list(RATIOS))
        rb.pack(side="left")
        rb.bind("<<ComboboxSelected>>", lambda _=None: self._ratio_change())
        ttk.Label(top, text="Width %:").pack(side="left", padx=(14, 2))
        self.wpct = tk.DoubleVar(value=55)
        ttk.Scale(top, from_=10, to=100, variable=self.wpct, length=140,
                  command=lambda _=None: self._size_change("w")).pack(side="left")
        ttk.Label(top, text="Height %:").pack(side="left", padx=(10, 2))
        self.hpct = tk.DoubleVar(value=100)
        self.hscale = ttk.Scale(top, from_=10, to=100, variable=self.hpct, length=140,
                                command=lambda _=None: self._size_change("h"))
        self.hscale.pack(side="left")

        btn = ttk.Frame(root, padding=(8, 0, 8, 6))
        btn.pack(side="top", fill="x")
        ttk.Button(btn, text="Render GIF", command=self.render).pack(side="left")
        ttk.Button(btn, text="Save crop PNG", command=self.save_png).pack(side="left", padx=6)
        self.status = ttk.Label(btn, text="Drag the box to position the crop.")
        self.status.pack(side="left", padx=10)

        self.dscale = min(self.DISP_W / self.iw, 560 / self.ih, 1.0)
        self.dw, self.dh = int(self.iw * self.dscale), int(self.ih * self.dscale)
        self.canvas = tk.Canvas(root, width=self.dw, height=self.dh,
                                bg="#000000", highlightthickness=0)
        self.canvas.pack(side="top", padx=8, pady=8)
        self._photo = ImageTk.PhotoImage(self.src.resize((self.dw, self.dh)))
        self.canvas.bind("<Button-1>", self._drag_start)
        self.canvas.bind("<B1-Motion>", self._drag_move)

        # crop box in IMAGE coords (centre + size)
        self.cx, self.cy = self.iw / 2, self.ih / 2
        self.cw, self.ch = self.iw * 0.55, self.ih
        self._ratio_change()

    # ---- crop geometry --------------------------------------------------
    def _ratio(self):
        return RATIOS[self.ratio_var.get()]

    def _ratio_change(self):
        r = self._ratio()
        self.hscale.state(["disabled"] if r else ["!disabled"])
        self._size_change("w")

    def _clamp(self):
        self.cw = max(20, min(self.cw, self.iw))
        self.ch = max(20, min(self.ch, self.ih))
        self.cx = min(max(self.cx, self.cw / 2), self.iw - self.cw / 2)
        self.cy = min(max(self.cy, self.ch / 2), self.ih - self.ch / 2)

    def _size_change(self, which):
        r = self._ratio()
        self.cw = self.wpct.get() / 100.0 * self.iw
        if r:
            self.ch = self.cw / r
            if self.ch > self.ih:                 # too tall -> limit by height
                self.ch = self.ih
                self.cw = self.ch * r
                self.wpct.set(round(self.cw / self.iw * 100))
            self.hpct.set(round(self.ch / self.ih * 100))
        else:
            self.ch = self.hpct.get() / 100.0 * self.ih
        self._clamp()
        self._redraw()

    def _drag_start(self, e):
        self._d0 = (e.x, e.y, self.cx, self.cy)

    def _drag_move(self, e):
        x0, y0, cx0, cy0 = self._d0
        self.cx = cx0 + (e.x - x0) / self.dscale
        self.cy = cy0 + (e.y - y0) / self.dscale
        self._clamp()
        self._redraw()

    def _box_img(self):
        x0 = int(round(self.cx - self.cw / 2))
        y0 = int(round(self.cy - self.ch / 2))
        return (x0, y0, x0 + int(round(self.cw)), y0 + int(round(self.ch)))

    def _redraw(self):
        self.canvas.delete("all")
        self.canvas.create_image(0, 0, anchor="nw", image=self._photo)
        bx0, by0, bx1, by1 = self._box_img()
        dx0, dy0 = bx0 * self.dscale, by0 * self.dscale
        dx1, dy1 = bx1 * self.dscale, by1 * self.dscale
        for x0, y0, x1, y1 in [(0, 0, self.dw, dy0), (0, dy1, self.dw, self.dh),
                               (0, dy0, dx0, dy1), (dx1, dy0, self.dw, dy1)]:
            self.canvas.create_rectangle(x0, y0, x1, y1, fill="#000000",
                                         stipple="gray50", width=0)
        self.canvas.create_rectangle(dx0, dy0, dx1, dy1, outline="#66c0f4", width=2)
        self.status.configure(
            text=f"Crop {int(self.cw)}x{int(self.ch)} px  @ ({bx0},{by0}).  "
                 f"Drag to move; sliders resize.")

    # ---- actions --------------------------------------------------------
    def open_img(self):
        p = filedialog.askopenfilename(
            title="Choose source image",
            filetypes=[("Images", "*.png *.jpg *.jpeg *.bmp *.webp"), ("All", "*.*")])
        if not p:
            return
        self.src = Image.open(p).convert("RGB")
        self.iw, self.ih = self.src.size
        self.dscale = min(self.DISP_W / self.iw, 560 / self.ih, 1.0)
        self.dw, self.dh = int(self.iw * self.dscale), int(self.ih * self.dscale)
        self.canvas.configure(width=self.dw, height=self.dh)
        self._photo = ImageTk.PhotoImage(self.src.resize((self.dw, self.dh)))
        self.cx, self.cy = self.iw / 2, self.ih / 2
        self._size_change("w")

    def save_png(self):
        out = filedialog.asksaveasfilename(
            title="Save cropped still", defaultextension=".png",
            initialfile="Makima_crop.png", filetypes=[("PNG", "*.png")])
        if out:
            self.src.crop(self._box_img()).save(out)
            self.status.configure(text=f"Saved still: {out}")

    def render(self):
        out = filedialog.asksaveasfilename(
            title="Render animated GIF to…", defaultextension=".gif",
            initialfile=os.path.basename(DEFAULT_OUT), filetypes=[("GIF", "*.gif")])
        if not out:
            return
        crop = self.src.crop(self._box_img())
        self.status.configure(text=f"Rendering {crop.width}x{crop.height} … (~1-2 min)")
        self.root.update_idletasks()

        def work():
            try:
                path, mb = render_effect(crop, out)
                msg = f"Saved {os.path.basename(path)}  {crop.width}x{crop.height}  {mb:.2f} MB"
            except Exception as exc:  # noqa: BLE001
                msg = f"Render failed: {exc}"
            self.root.after(0, lambda: self.status.configure(text=msg))

        threading.Thread(target=work, daemon=True).start()


if __name__ == "__main__":
    root = tk.Tk()
    CropUI(root)
    root.mainloop()
