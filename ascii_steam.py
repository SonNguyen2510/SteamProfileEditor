"""ASCII Steam Art - turn images into Steam-ready ASCII/Braille art, plus a
Steam name generator.

Steam counts text length in UTF-8 *bytes*, not characters: a plain ASCII
char is 1 byte, but the block glyphs (U+2588..U+2591) and Braille glyphs
(U+2800..U+28FF) are 3 bytes each. So a 1000-"character" comment really only
fits ~330 block/Braille glyphs. The status bar reports the true byte cost.

Steam also collapses runs of normal spaces outside of [code] blocks, so the
"Steam-safe" ramps never emit a plain space, and Braille uses U+2800 (a real,
non-collapsing glyph) for blank cells.
"""

import os
import re
import sys
import random
import webbrowser
import urllib.request
import urllib.error
import xml.etree.ElementTree as ET
from io import BytesIO
from collections import deque
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, colorchooser, font as tkfont

from PIL import (Image, ImageOps, ImageFilter, ImageChops, ImageDraw,
                 ImageFont, ImageSequence)

# Monospace text cells are about twice as tall as they are wide.
CELL_ASPECT = 0.5

# Output aspect ratios. Value is height/width of the target image (None keeps
# the source's own ratio). Selecting a fixed ratio stretches the image to it.
RATIOS = {
    "Original": None,
    "Square 1:1": 1.0,
    "Landscape 4:3": 3 / 4,
    "Portrait 3:4": 4 / 3,
    "Wide 16:9": 9 / 16,
    "Tall 9:16": 16 / 9,
    "Photo 3:2": 2 / 3,
    "Photo 2:3": 3 / 2,
}
DEFAULT_RATIO = "Original"

STEAM_BG = "#1b2838"
STEAM_FG = "#c7d5e0"
STEAM_ACCENT = "#66c0f4"
STEAM_BG_RGB = (27, 40, 56)
STEAM_FG_RGB = (199, 213, 224)
PREVIEW_FONT_PX = 16  # fixed preview render size
PREVIEW_LINE_SPACING = 1.25  # Steam adds line-height; taller rows match it

# Transparent pixels (alpha below this) are treated as background = blank.
ALPHA_CUTOFF = 32
BLANK_BRAILLE = "⠀"  # non-collapsing empty glyph, safe to paste on Steam

# --- Rendering styles -------------------------------------------------------
# Ramps run dark -> light: ramp[0] is the densest glyph (drawn for black
# pixels), ramp[-1] the lightest (drawn for white). The "safe" ramp replaces a
# trailing plain space with a visible glyph so Steam will not collapse it.
DETAILED = ("$@B%8&WM#*oahkbdpqwmZO0QLCJUYXzcvunxrjft/\\|()1{}[]?-_+~<>i!lI;:,"
            "\"^`'. ")

STYLES = {
    "Braille (most detail)": {"kind": "braille"},
    "Block (█▓▒░)": {
        "kind": "ramp", "ramp": "█▓▒░ ",
        "safe_ramp": "█▓▒░░"},
    "Classic ASCII": {
        "kind": "ramp", "ramp": "@%#*+=-:. ", "safe_ramp": "@%#*+=-:.."},
    "Detailed ASCII": {
        "kind": "ramp", "ramp": DETAILED, "safe_ramp": DETAILED[:-1] + "."},
}
DEFAULT_STYLE = "Braille (most detail)"

# Decorative frames around the art. Tuple order: (top-left, top, top-right,
# left, right, bottom-left, bottom, bottom-right). "Braille" is built from
# Braille glyphs so it sits in the SAME font as braille art (best match);
# box-drawing frames suit Block/ASCII art (especially inside [code]).
FRAMES = {
    "None": None,
    "Braille": ("⡏", "⠉", "⢹", "⡇", "⢸", "⣇", "⣀", "⣸"),
    "Rounded": ("╭", "─", "╮", "│", "│", "╰", "─", "╯"),
    "Square": ("┌", "─", "┐", "│", "│", "└", "─", "┘"),
    "Heavy": ("┏", "━", "┓", "┃", "┃", "┗", "━", "┛"),
    "Double": ("╔", "═", "╗", "║", "║", "╚", "═", "╝"),
}
DEFAULT_FRAME = "None"


# Decorative background fills for blank (U+2800) cells.
STAR_TINY = "⠁⠂⠄⠈⠐⠠⡀⢀"      # single-dot specks
STAR_SMALL = "⠃⠘⠊⠒⠆⠰⠢⠡⣀⠉"  # 2-dot small stars
STAR_BIG = "⠿⠶⠽⠾⠫⡱⢋⠷"        # sparkles / little circles (Braille, aligned)
COSMIC_CHARS = "✦✧⋆∗·°◦∘⚬✫"     # real star/circle symbols (decorative)
BACKGROUNDS = ("None", "Stars", "Dots", "Cosmic")


def add_background(raw, mode, blank=BLANK_BRAILLE):
    """Fill blank cells with a decorative pattern (deterministic, no flicker):
    'Dots'   - every blank -> a faint dot (uniform texture; also fixes Braille
               drift since all cells become full 24px width).
    'Stars'  - sparse mix of Braille specks/sparkles/circles (stays aligned-ish,
               all glyphs are Braille).
    'Cosmic' - sparse real ✦ ◦ ° symbols (most star-like, but these aren't
               Braille so they can shift alignment a little)."""
    if mode == "None" or mode not in BACKGROUNDS:
        return raw
    rng = random.Random(0x5EED)
    out = []
    for line in raw.split("\n"):
        row = []
        for ch in line:
            if ch != blank:
                row.append(ch)
            elif mode == "Dots":
                row.append("⠁")
            elif mode == "Cosmic":
                row.append(rng.choice(COSMIC_CHARS) if rng.random() < 0.10 else ch)
            else:  # Stars: weighted — mostly empty, many tiny, some bigger
                r = rng.random()
                if r < 0.05:
                    row.append(rng.choice(STAR_BIG))
                elif r < 0.14:
                    row.append(rng.choice(STAR_SMALL))
                elif r < 0.30:
                    row.append(rng.choice(STAR_TINY))
                else:
                    row.append(ch)
        out.append("".join(row))
    return "\n".join(out)


def frame_art(raw, name, is_braille=True, pad=1):
    """Wrap the art in a decorative border, padded inside by `pad` blank cells.
    Braille art uses Braille border glyphs (same font/width so it aligns); other
    styles use the chosen box-drawing border. Blanks use U+2800 for Braille
    (non-collapsing) or a space for box frames inside [code]."""
    spec = FRAMES.get("Braille" if (is_braille and name != "None") else name)
    if not spec:
        return raw
    tl, t, tr, lft, rgt, bl, b, br = spec
    fill = BLANK_BRAILLE if is_braille else " "
    lines = raw.split("\n")
    w = max((len(ln) for ln in lines), default=1)
    lines = [ln + fill * (w - len(ln)) for ln in lines]
    if pad > 0:
        lines = [fill * pad + ln + fill * pad for ln in lines]
        blank_row = fill * (w + 2 * pad)
        lines = [blank_row] * pad + lines + [blank_row] * pad
        w += 2 * pad
    out = [tl + t * w + tr]
    out += [lft + ln + rgt for ln in lines]
    out.append(bl + b * w + br)
    return "\n".join(out)


# --- Steam destinations -----------------------------------------------------
# width      - recommended character width for that surface
# byte_limit - UTF-8 byte cap (0 = effectively unlimited)
# force_safe - Steam collapses runs of plain spaces here, so avoid them
# code       - wrap in [code]; inside it Steam keeps whitespace + monospaces
# title      - surface has a usable heading ([h1] for BBCode surfaces)
DESTINATIONS = {
    "Steam Chat": {
        "width": 50, "byte_limit": 2048, "force_safe": True, "code": False,
        "title": False,
        "note": "Desktop chat caps at 2048 bytes; glyphs are 3 bytes each.",
    },
    "Profile Comment": {
        "width": 40, "byte_limit": 1000, "force_safe": True, "code": False,
        "title": False,
        "note": "1000-byte cap; block/Braille glyphs are 3 bytes each (~330 max).",
    },
    "Custom Info Box": {
        "width": 45, "byte_limit": 8000, "force_safe": True, "code": False,
        "title": False,
        "note": "8000-byte showcase; no [code], collapses spaces — Braille "
                "blanks (U+2800) keep alignment. Has its own title field.",
    },
    "Review (BBCode)": {
        "width": 70, "byte_limit": 8000, "force_safe": False, "code": True,
        "title": True,
        "note": "8000-byte cap; [code] preserves spacing so blocks line up.",
    },
    "Group / Workshop": {
        "width": 80, "byte_limit": 8000, "force_safe": False, "code": True,
        "title": True,
        "note": "Descriptions support full BBCode and [code] (~8000 bytes).",
    },
    "Profile Summary": {
        "width": 55, "byte_limit": 0, "force_safe": True, "code": False,
        "title": False,
        "note": "About-me box. Collapses spaces; keep it compact.",
    },
    "Raw (file / no limit)": {
        "width": 100, "byte_limit": 0, "force_safe": False, "code": False,
        "title": False,
        "note": "Unrestricted output for saving or use outside Steam.",
    },
}
DEFAULT_DESTINATION = "Profile Comment"


def steam_byte_len(text):
    """Steam measures length in UTF-8 bytes and may store line breaks as
    CRLF, so count newlines as 2 bytes to stay safely under the cap."""
    return len(text.replace("\n", "\r\n").encode("utf-8"))


# --- Image -> text ----------------------------------------------------------

# Background removal is computed at this working resolution for speed; the
# resulting mask is scaled back up to the source size.
BG_WORK_SIZE = 200


def _background_mask(img, tolerance):
    """Flood-fill from the image border and return an 'L' mask the size of img:
    255 = foreground (subject, kept), 0 = edge-connected background color.
    tolerance is 0..1 of the max RGB color distance."""
    w, h = img.size
    scale = min(1.0, BG_WORK_SIZE / max(w, h))
    sw, sh = max(1, int(w * scale)), max(1, int(h * scale))
    small = img.convert("RGB").resize((sw, sh))
    px = small.load()

    corners = [px[0, 0], px[sw - 1, 0], px[0, sh - 1], px[sw - 1, sh - 1]]
    tol_sq = (tolerance * 441.673) ** 2  # 441.673 = sqrt(3)*255 = max distance

    def is_bg(c):
        for k in corners:
            dr, dg, db = c[0] - k[0], c[1] - k[1], c[2] - k[2]
            if dr * dr + dg * dg + db * db <= tol_sq:
                return True
        return False

    bg = bytearray(sw * sh)  # 0 = keep, 1 = background
    dq = deque()
    for x in range(sw):
        for y in (0, sh - 1):
            i = y * sw + x
            if not bg[i] and is_bg(px[x, y]):
                bg[i] = 1
                dq.append((x, y))
    for y in range(sh):
        for x in (0, sw - 1):
            i = y * sw + x
            if not bg[i] and is_bg(px[x, y]):
                bg[i] = 1
                dq.append((x, y))
    while dq:
        x, y = dq.popleft()
        for nx, ny in ((x - 1, y), (x + 1, y), (x, y - 1), (x, y + 1)):
            if 0 <= nx < sw and 0 <= ny < sh:
                i = ny * sw + nx
                if not bg[i] and is_bg(px[nx, ny]):
                    bg[i] = 1
                    dq.append((nx, ny))

    mask = Image.frombytes("L", (sw, sh), bytes(0 if b else 255 for b in bg))
    return mask.resize((w, h), Image.NEAREST)


def _strip_background(img, alpha, tolerance):
    """Clear the edge-connected background color to transparent."""
    return ImageChops.darker(alpha, _background_mask(img, tolerance))


def _split(img_rgba, remove_bg=False, tolerance=0.10):
    """Split an RGBA image into (grayscale, alpha), optionally clearing the
    edge-connected background color to transparent."""
    alpha = img_rgba.getchannel("A")
    if remove_bg:
        alpha = _strip_background(img_rgba, alpha, tolerance)
    return img_rgba.convert("L"), alpha


def _open_rgba(path):
    """Open an image as upright (EXIF-applied) RGBA."""
    return ImageOps.exif_transpose(Image.open(path)).convert("RGBA")


def _load(path, remove_bg=False, tolerance=0.10):
    """Return (grayscale, alpha) for an image file."""
    return _split(_open_rgba(path), remove_bg, tolerance)


def _prep(gray, alpha, size, detail, contrast, smooth=0.0):
    """Stretch contrast (more visible texture) and sharpen (more edge detail)
    so each cell carries more information without adding any characters.
    `smooth` (0..1) denoises before dithering: a median filter removes speckle,
    a light blur calms gradients, and it eases off the sharpening — this is what
    cuts the busy 'noise' in braille output (especially from compressed GIFs)."""
    if contrast:
        gray = ImageOps.autocontrast(gray, cutoff=1)
    gray = gray.resize(size)
    alpha = alpha.resize(size)
    if smooth > 0:
        gray = gray.filter(ImageFilter.MedianFilter(size=3))  # kill speckle
        if smooth > 0.5:
            gray = gray.filter(ImageFilter.GaussianBlur(radius=(smooth - 0.5) * 2))
        detail *= max(0.0, 1.0 - smooth)  # less sharpening as we denoise
    if detail > 0:
        gray = gray.filter(ImageFilter.UnsharpMask(
            radius=2, percent=int(detail * 250), threshold=2))
    return gray, alpha


# Signature font styles -> candidate Windows TTFs (first that loads wins,
# else the bundled mono font). Gives the signature a different look per style.
SIGNATURE_FONTS = {
    "Script": ["segoesc.ttf", "BRUSHSCI.TTF", "freescpt.ttf", "ITCKRIST.TTF"],
    "Handwriting": ["Inkfree.ttf", "segoepr.ttf", "comic.ttf"],
    "Elegant": ["Gabriola.ttf", "PALSCRI.TTF", "MTCORSVA.TTF"],
    "Bold": ["ariblk.ttf", "impact.ttf", "arialbd.ttf"],
    "Serif": ["georgiab.ttf", "timesbd.ttf", "georgia.ttf", "times.ttf"],
    "Mono": [None],  # use the bundled Cascadia Mono
}
DEFAULT_SIG_FONT = "Script"


def _signature_font(style, size):
    for name in SIGNATURE_FONTS.get(style, []):
        if name is None:
            break
        try:
            return ImageFont.truetype(name, size)
        except OSError:
            continue
    return _find_mono_font(size)


def _apply_signature(img_rgba, gray, alpha, sig, invert, tolerance):
    """Stamp the signature into the full-res grayscale image so it becomes part
    of the ASCII/braille art. `sig` = (text, size, x, y, rotation, font, behind).
    The stamp is painted in the glyph 'ink' value (dark normally, light when
    inverted) and marked opaque so background removal won't erase it. With
    `behind` it is composited only over the separated background region, so the
    foreground subject stays in front of it. Returns (gray, alpha)."""
    text, size, x, y, rotation, font_style, behind, sig_invert = sig
    text = (text or "").strip()
    if not text or size <= 0:
        return gray, alpha
    w, h = gray.size
    font_px = max(8, int(h * size))
    font = _signature_font(font_style, font_px)

    # Render the text to its own coverage stamp (255 where ink), then rotate.
    # Drawn at the font's natural weight (no stroke) — pick the 'Bold' font
    # style if you want bold.
    pad = 2
    bbox = ImageDraw.Draw(Image.new("L", (1, 1))).textbbox((0, 0), text, font=font)
    tw = max(1, bbox[2] - bbox[0]) + pad * 2
    th = max(1, bbox[3] - bbox[1]) + pad * 2
    stamp = Image.new("L", (tw, th), 0)
    ImageDraw.Draw(stamp).text((pad - bbox[0], pad - bbox[1]), text, font=font,
                               fill=255)
    if rotation:
        stamp = stamp.rotate(rotation, expand=True, resample=Image.BICUBIC)
    sw, sh = stamp.size
    px = int(round((w - sw) * x))
    py = int(round((h - sh) * y))
    coverage = stamp.point(lambda v: 255 if v > 64 else 0)  # binary ink mask

    if behind:
        # Keep the stamp only where the (separated) background is, so the
        # foreground subject occludes it.
        fg = _background_mask(img_rgba, tolerance)  # 255 = subject, 0 = background
        bg_region = fg.point(lambda v: 0 if v >= 128 else 255).crop(
            (px, py, px + sw, py + sh))
        coverage = ImageChops.darker(coverage, bg_region)

    # Normally the signature is drawn so it becomes dots (visible). 'Invert
    # text' flips it to the no-dot value, making the letters a cut-out instead.
    ink = 255 if (invert != sig_invert) else 0
    gray = gray.copy()
    gray.paste(Image.new("L", (sw, sh), ink), (px, py), coverage)
    alpha = alpha.copy()
    alpha.paste(Image.new("L", (sw, sh), 255), (px, py), coverage)
    return gray, alpha


def image_to_ascii(path, width, invert, ramp, blank, detail=0.0, contrast=True,
                   remove_bg=False, tolerance=0.10, aspect=None,
                   sig=None, stretch=1.0):
    """One glyph per cell from a dark->light ramp; transparent cells -> blank."""
    img = _open_rgba(path)
    gray, alpha = _split(img, remove_bg, tolerance)
    if sig:
        gray, alpha = _apply_signature(img, gray, alpha, sig, invert, tolerance)
    src_w, src_h = gray.size
    width = max(1, int(width))
    asp = aspect if aspect is not None else (src_h / src_w)
    height = max(1, int(width * asp * CELL_ASPECT * stretch))
    gray, alpha = _prep(gray, alpha, (width, height), detail, contrast)
    gp, ap = gray.getdata(), alpha.getdata()
    n = len(ramp)

    lines = []
    for row in range(height):
        chars = []
        for col in range(width):
            i = row * width + col
            if ap[i] < ALPHA_CUTOFF:
                chars.append(blank)
                continue
            value = gp[i]
            if invert:
                value = 255 - value
            idx = value * n // 256  # dark(0)->dense glyph, light(255)->lightest
            if idx >= n:
                idx = n - 1
            chars.append(ramp[idx])
        lines.append("".join(chars))
    return "\n".join(lines)


# Braille dot -> bit value, indexed [row 0..3][col 0..1].
BRAILLE_BITS = [
    [0x01, 0x08],
    [0x02, 0x10],
    [0x04, 0x20],
    [0x40, 0x80],
]
BRAILLE_BASE = 0x2800


def image_to_braille(path, width, invert, detail=0.0, contrast=True,
                     remove_bg=False, tolerance=0.10, aspect=None, sig=None,
                     stretch=1.0):
    """Braille art from an image file (see _braille_text)."""
    img = _open_rgba(path)
    gray, alpha = _split(img, remove_bg, tolerance)
    if sig:
        gray, alpha = _apply_signature(img, gray, alpha, sig, invert, tolerance)
    return _braille_text(gray, alpha, width, invert, detail, contrast, aspect,
                         stretch=stretch)


def _braille_text(gray, alpha, width, invert, detail=0.0, contrast=True,
                  aspect=None, smooth=0.0, edge_fade=0.0, stretch=1.0):
    """Each glyph packs a 2x4 dot grid (8x the detail of one ramp glyph),
    using Floyd-Steinberg dithering. Transparent pixels stay empty (no dots).
    `smooth` (0..1) denoises before dithering to reduce speckle.
    `edge_fade` (0..1) feathers dots out toward the edges so the art melts into
    Steam's dark background instead of showing a hard rectangular border.
    `stretch` (>1 taller) compensates for surfaces (like Steam's [code]) that
    pack rows tighter than the app preview, so the art isn't squashed wide."""
    src_w, src_h = gray.size
    cols = max(1, int(width))
    px_w = cols * 2
    asp = aspect if aspect is not None else (src_h / src_w)
    px_h = max(4, int(round(px_w * asp * stretch)))
    rows = max(1, round(px_h / 4))
    px_h = rows * 4
    gray, alpha = _prep(gray, alpha, (px_w, px_h), detail, contrast, smooth)

    gflat = list(gray.getdata())
    aflat = list(alpha.getdata())
    transparent = [[aflat[y * px_w + x] < ALPHA_CUTOFF for x in range(px_w)]
                   for y in range(px_h)]
    # Force transparent pixels white so they never become dots or bleed error.
    pix = [[255.0 if transparent[y][x] else float(gflat[y * px_w + x])
            for x in range(px_w)] for y in range(px_h)]

    # Edge fade: blend non-transparent pixels toward the "no dot" brightness
    # (255 normally, 0 when inverted) as they approach any edge, so dithering
    # thins the dots out to nothing and the art blends into the background.
    feather = edge_fade * min(px_w, px_h) / 2.0
    if feather > 0:
        no_dot = 0.0 if invert else 255.0
        for y in range(px_h):
            for x in range(px_w):
                if transparent[y][x]:
                    continue
                dist = min(x, y, px_w - 1 - x, px_h - 1 - y)
                m = dist / feather
                if m < 1.0:
                    pix[y][x] = pix[y][x] * m + no_dot * (1.0 - m)

    for y in range(px_h):
        for x in range(px_w):
            old = pix[y][x]
            new = 255.0 if old >= 128 else 0.0
            pix[y][x] = new
            err = old - new
            if x + 1 < px_w:
                pix[y][x + 1] += err * 7 / 16
            if y + 1 < px_h:
                if x - 1 >= 0:
                    pix[y + 1][x - 1] += err * 3 / 16
                pix[y + 1][x] += err * 5 / 16
                if x + 1 < px_w:
                    pix[y + 1][x + 1] += err * 1 / 16

    lines = []
    for cy in range(rows):
        chars = []
        for cx in range(cols):
            bits = 0
            for dy in range(4):
                for dx in range(2):
                    py, px_ = cy * 4 + dy, cx * 2 + dx
                    if transparent[py][px_]:
                        continue  # background: leave this dot empty
                    on = pix[py][px_] < 128  # dark = dot
                    if invert:
                        on = not on
                    if on:
                        bits |= BRAILLE_BITS[dy][dx]
            chars.append(chr(BRAILLE_BASE + bits))
        lines.append("".join(chars))
    return "\n".join(lines)


def convert(path, width, invert, steam_safe, style, detail=0.0, contrast=True,
            remove_bg=False, tolerance=0.10, aspect=None, sig=None, stretch=1.0):
    spec = STYLES[style]
    if spec["kind"] == "braille":
        return image_to_braille(path, width, invert, detail, contrast,
                                remove_bg, tolerance, aspect, sig, stretch)
    ramp = spec["safe_ramp"] if steam_safe else spec["ramp"]
    # On collapsing surfaces a plain-space background would vanish/misalign, so
    # use the non-collapsing braille blank; inside [code] a real space is fine.
    blank = BLANK_BRAILLE if steam_safe else " "
    return image_to_ascii(path, width, invert, ramp, blank, detail, contrast,
                          remove_bg, tolerance, aspect, sig, stretch)


# --- Panorama banner slicer -------------------------------------------------
def slice_banner(path, slots, out_dir, edge_fade=0.0, color=None, strength=0.0):
    """Slice an image into `slots` equal-width tiles for Steam's Artwork
    Showcase. Static -> PNG tiles; animated -> animated GIF tiles at NATIVE
    resolution (never downscaled). `color`+`strength` apply a colour-grade tint
    (e.g. redder); `edge_fade` (0..1) then feathers the banner's OUTER edges
    into black so the row melts into the dark showcase background while the
    seams between tiles stay intact. Returns the written paths."""
    src = Image.open(path)
    base = os.path.splitext(os.path.basename(path))[0]
    paths = []
    if getattr(src, "n_frames", 1) <= 1:  # static image -> PNG tiles
        img = ImageOps.exif_transpose(src).convert("RGBA")
        img = apply_color_filter(img, color, strength)
        if edge_fade > 0:
            img = _vignette(img, _edge_mask(img.size, edge_fade), (0, 0, 0))
        w, h = img.size
        tile_w = w // slots                    # EQUAL-width tiles (no drift)
        off = (w - tile_w * slots) // 2        # centre the <=slots-1 px trim
        for i in range(slots):
            x0 = off + i * tile_w
            dst = os.path.join(out_dir, f"{base}_panorama_{i + 1}.png")
            img.crop((x0, 0, x0 + tile_w, h)).save(dst)
            paths.append(dst)
        return paths
    # animated -> one animated GIF per tile (native resolution, no downscale)
    frames, durs = [], []
    for frame in ImageSequence.Iterator(src):
        frames.append(ImageOps.exif_transpose(frame.convert("RGB")))
        durs.append(frame.info.get("duration", 80))
    size = frames[0].size
    frames = [f if f.size == size else f.resize(size) for f in frames]
    if color and strength > 0:
        frames = [apply_color_filter(f, color, strength) for f in frames]
    if edge_fade > 0:
        m = _edge_mask(size, edge_fade)
        frames = [_vignette(f, m, (0, 0, 0)) for f in frames]
    w, h = size
    tile_w = w // slots                        # EQUAL-width tiles: identical
    off = (w - tile_w * slots) // 2            # aspect -> Steam scales them the
    for i in range(slots):                     # same, so no vertical drift
        x0 = off + i * tile_w
        tiles = [f.crop((x0, 0, x0 + tile_w, h)) for f in frames]
        dst = os.path.join(out_dir, f"{base}_panorama_{i + 1}.gif")
        _save_animated_gif(tiles, durs, dst, grayscale=False, max_bytes=None)
        paths.append(dst)
    return paths


def patch_long_image(path):
    """Apply the long-image upload trick from the Steam guide (id 2174159512):
    overwrite the file's final byte with 0x21 so Steam's uploader skips its
    dimension/size validation (and so accepts very wide/tall tiles or oversized
    GIFs). The byte is the GIF trailer / PNG IEND tail, which browsers render
    fine without, so the image still displays. Edits the file in place."""
    with open(path, "rb") as f:
        data = bytearray(f.read())
    if data:
        data[-1] = 0x21
        with open(path, "wb") as f:
            f.write(data)
    return path


# Main:side width ratios for the full-profile background trick. A regular
# Artwork Showcase shows a ~506px main beside a ~100px side; a Featured Artwork
# shows a wider ~630px main. Splitting the source at the main fraction keeps the
# two tiles seamless when placed next to each other at full profile height.
BACKGROUND_RATIOS = {
    "Regular (506 + 100)": 506 / 606,
    "Featured (630 + 100)": 630 / 730,
}
DEFAULT_BACKGROUND_RATIO = "Regular (506 + 100)"


def slice_background(path, out_dir, main_frac, patch=False, edge_fade=0.0,
                     color=None, strength=0.0):
    """Split one (typically tall) image into a wide Main tile and a narrow Side
    tile by `main_frac` of the width, for the full-profile background trick.
    Static -> PNG, animated -> GIF at NATIVE resolution (never downscaled).
    `color`+`strength` colour-grade the image; `edge_fade` (0..1) then feathers
    the outer edges into black (the Main|Side seam stays intact). Optionally
    applies the long-image patch. Returns [main, side]."""
    src = Image.open(path)
    base = os.path.splitext(os.path.basename(path))[0]
    animated = getattr(src, "n_frames", 1) > 1
    ext = "gif" if animated else "png"
    main_dst = os.path.join(out_dir, f"{base}_bg_main.{ext}")
    side_dst = os.path.join(out_dir, f"{base}_bg_side.{ext}")

    if not animated:
        img = ImageOps.exif_transpose(src).convert("RGBA")
        img = apply_color_filter(img, color, strength)
        if edge_fade > 0:
            img = _vignette(img, _edge_mask(img.size, edge_fade), (0, 0, 0))
        w, h = img.size
        cut = max(1, min(w - 1, round(w * main_frac)))
        img.crop((0, 0, cut, h)).save(main_dst)
        img.crop((cut, 0, w, h)).save(side_dst)
    else:
        frames, durs = [], []
        for frame in ImageSequence.Iterator(src):
            frames.append(ImageOps.exif_transpose(frame.convert("RGB")))
            durs.append(frame.info.get("duration", 80))
        size = frames[0].size
        frames = [f if f.size == size else f.resize(size) for f in frames]
        if color and strength > 0:
            frames = [apply_color_filter(f, color, strength) for f in frames]
        if edge_fade > 0:
            m = _edge_mask(size, edge_fade)
            frames = [_vignette(f, m, (0, 0, 0)) for f in frames]
        w, h = size
        cut = max(1, min(w - 1, round(w * main_frac)))
        _save_animated_gif([f.crop((0, 0, cut, h)) for f in frames], durs,
                           main_dst, grayscale=False, max_bytes=None)
        _save_animated_gif([f.crop((cut, 0, w, h)) for f in frames], durs,
                           side_dst, grayscale=False, max_bytes=None)

    paths = [main_dst, side_dst]
    if patch:
        for p in paths:
            patch_long_image(p)
    return paths


# --- Progress / loading bars ------------------------------------------------
# Each style is (filled_glyph, empty_glyph).
BAR_STYLES = {
    "Blocks █░": ("█", "░"),
    "Blocks ▰▱": ("▰", "▱"),
    "Squares ■□": ("■", "□"),
    "Circles ●○": ("●", "○"),
    "Bars ▮▯": ("▮", "▯"),
    "Brackets": ("=", "-"),
}
DEFAULT_BAR_STYLE = "Blocks ▰▱"


def progress_bar(label, percent, cells, style, show_pct=True):
    """Render one labelled progress bar, e.g. 'Level ▰▰▰▱▱ 60%'."""
    fill, empty = BAR_STYLES.get(style, BAR_STYLES[DEFAULT_BAR_STYLE])
    percent = max(0, min(100, percent))
    filled = round(cells * percent / 100)
    bar = fill * filled + empty * (cells - filled)
    if style == "Brackets":
        bar = "[" + bar + "]"
    parts = []
    if label:
        parts.append(f"{label}")
    parts.append(bar)
    if show_pct:
        parts.append(f"{percent}%")
    return " ".join(parts)


def progress_block(lines_text, cells, style, show_pct=True):
    """Turn multiline 'Label:percent' input into a block of progress bars."""
    out = []
    for raw in lines_text.splitlines():
        raw = raw.strip()
        if not raw:
            continue
        if ":" in raw:
            label, _, val = raw.rpartition(":")
        else:
            label, val = "", raw
        try:
            pct = int(float(val.strip().rstrip("%")))
        except ValueError:
            pct = 0
        out.append(progress_bar(label.strip(), pct, cells, style, show_pct))
    return "\n".join(out)


# --- Animated braille GIF ---------------------------------------------------
def _resource_path(rel):
    """Resolve a bundled data file both in dev and inside a PyInstaller exe."""
    base = getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(base, rel)


def _font_has_braille(font):
    """True if `font` actually draws Braille glyphs instead of the .notdef
    'tofu' box. Loading a font is not proof it can render the art: many
    "monospace" fonts (Consolas, Courier New, Lucida Console on Windows) omit
    the U+2800..U+28FF block entirely, so a Braille cell falls back to .notdef
    and the whole image comes out as identical hollow rectangles."""
    try:
        notdef = bytes(font.getmask(chr(0xE000)))  # private use -> always .notdef
        return bytes(font.getmask(chr(0x28FF))) != notdef
    except Exception:  # noqa: BLE001 - some font backends lack getmask
        return False


def _find_mono_font(size):
    """A monospace TTF that includes Braille glyphs, for rasterizing frames.
    Prefers the font bundled with the app, then known Braille-capable system
    fonts. A candidate is only accepted if it genuinely renders Braille (not
    tofu); otherwise the exported art would be a grid of empty boxes."""
    candidates = (
        _resource_path(os.path.join("assets", "CascadiaMono.ttf")),
        "CascadiaMono.ttf", "CascadiaCode.ttf",  # monospace + Braille
        "DejaVuSansMono.ttf",                     # genuine DejaVu has Braille
        "seguisym.ttf",                           # Segoe UI Symbol (last resort)
    )
    for name in candidates:
        try:
            font = ImageFont.truetype(name, size)
        except OSError:
            continue
        if _font_has_braille(font):
            return font
    return ImageFont.load_default()


def _steam_braille_font(size):
    """The font your browser/Steam actually shows Braille in on Windows:
    Segoe UI Symbol. Steam's CSS fonts (Consolas / Motiva Sans) have NO Braille
    glyphs, so the browser falls back to Segoe UI Symbol — its dots look
    different from the bundled font, which is why the preview didn't match the
    paste. It renders U+2800 as truly blank and Braille fixed-width. Used for
    the on-screen preview only; falls back to the bundled font off Windows."""
    try:
        font = ImageFont.truetype("seguisym.ttf", size)
        if _font_has_braille(font):
            return font
    except OSError:
        pass
    return _find_mono_font(size)


def register_bundled_font():
    """Register the bundled Cascadia Mono with the OS for this session so the
    Tk preview panes render Braille glyphs even when no suitable font is
    installed. Returns the Tk family name to use for monospace previews."""
    path = _resource_path(os.path.join("assets", "CascadiaMono.ttf"))
    if os.name == "nt" and os.path.exists(path):
        try:
            import ctypes
            FR_PRIVATE = 0x10
            ctypes.windll.gdi32.AddFontResourceExW(
                ctypes.c_wchar_p(path), FR_PRIVATE, 0)
            return "Cascadia Mono"
        except Exception:  # noqa: BLE001
            pass
    return "Consolas"


def _text_to_image(text, font, fg, bg, line_spacing=1.0):
    """Rasterize monospace text. line_spacing > 1 adds leading between rows;
    Steam adds line-height when it displays pasted art, so the preview uses a
    factor to match Steam's taller proportions, while baked GIF frames use 1.0
    (the Braille dots there ARE the image, no extra gap)."""
    lines = text.split("\n")
    asc, desc = font.getmetrics()
    line_h = int(round((asc + desc) * line_spacing))
    cell_w = font.getbbox("⣿")[2] or font.getbbox("M")[2]
    width = max((len(ln) for ln in lines), default=1) * cell_w
    height = len(lines) * line_h
    img = Image.new("RGB", (max(1, width), max(1, height)), bg)
    draw = ImageDraw.Draw(img)
    for i, ln in enumerate(lines):
        draw.text((0, i * line_h), ln, font=font, fill=fg)
    return img


# A fixed 256-level grayscale palette with black at index 0. Quantizing every
# braille frame to this SHARED palette (instead of a per-frame adaptive one)
# fixes a GIF bug where near-empty frames composited to white: with disposal=2
# the encoder restores untouched areas to the background index, and per-frame
# palettes made index 0 something other than black on sparse frames.
_GRAY_PALETTE = Image.new("P", (1, 1))
_GRAY_PALETTE.putpalette([v for i in range(256) for v in (i, i, i)])


# Steam rejects artwork uploads larger than 5 MB, so every exported GIF is kept
# under this. We shrink by dropping frames first (keeps resolution/sharpness),
# then downscaling only if frame-dropping isn't enough.
MAX_GIF_BYTES = 5 * 1024 * 1024


def _quantize_frames(frames, grayscale):
    """Map frames to a SHARED palette so disposal=2 restores a consistent
    background (index 0 = black for braille) — fixes white flashes."""
    if grayscale:
        return [f.convert("L").quantize(palette=_GRAY_PALETTE, dither=Image.NONE)
                for f in frames]
    # Derive the palette from ALL frames (a stacked thumbnail montage) so
    # colours that only appear in later frames survive. Using just frame[0]
    # makes later frames map onto the nearest frame-0 colour, which can make
    # distinct frames quantize identically and get merged away by the writer.
    thumbs = [f.convert("RGB").resize(
        (min(f.width, 96), min(f.height, 96)), Image.BILINEAR) for f in frames]
    tw = max(t.width for t in thumbs)
    montage = Image.new("RGB", (tw, sum(t.height for t in thumbs)))
    y = 0
    for t in thumbs:
        montage.paste(t, (0, y))
        y += t.height
    base = montage.quantize(colors=255, method=Image.MEDIANCUT)
    pf = []
    for f in frames:
        q = f.convert("RGB").quantize(palette=base, dither=Image.NONE)
        q.info.pop("transparency", None)  # avoid Pillow GIF writer crash
        pf.append(q)
    return pf


def _write_gif(frames, durations, path, grayscale):
    """Write one GIF using inter-frame delta encoding (optimize=True) to shrink
    the file without touching fps or resolution. disposal=1 (leave previous
    frame in place) lets unchanged pixels be skipped AND avoids the white-flash
    bug: with disposal=2 the background index restores, but disposal=1 never
    restores, so sparse/empty frames keep the prior black pixels."""
    pf = _quantize_frames(frames, grayscale)
    pf[0].save(path, save_all=True, append_images=pf[1:], duration=durations,
               loop=0, optimize=True, disposal=1)


def _save_animated_gif(frames, durations, path, grayscale=True,
                       max_bytes=MAX_GIF_BYTES):
    """Save an animated GIF at the HIGHEST quality that still fits max_bytes.
    If the native size already fits, it's kept as-is (best). Otherwise we
    binary-search the LARGEST scale that fits, so as much of the 5 MB budget as
    possible is used (minimal downscaling); frames are only thinned if even a
    tiny canvas overflows. max_bytes=None saves once (caller sized it)."""
    fr, du = list(frames), list(durations)
    _write_gif(fr, du, path, grayscale)
    if max_bytes is None or os.path.getsize(path) <= max_bytes:
        return  # native size already under budget = highest quality
    w0, h0 = fr[0].size

    def write_scaled(scale):
        sw, sh = max(1, int(w0 * scale)), max(1, int(h0 * scale))
        _write_gif([f.resize((sw, sh), Image.LANCZOS) for f in fr], du,
                   path, grayscale)
        return os.path.getsize(path)

    lo, hi, best = 0.1, 1.0, None
    for _ in range(7):  # find the largest scale whose file fits the budget
        mid = (lo + hi) / 2
        if write_scaled(mid) <= max_bytes:
            best, lo = mid, mid   # fits — try bigger
        else:
            hi = mid              # too big — go smaller
    if best is not None:
        if write_scaled(best) <= max_bytes:
            return
    # Even the smallest scale overflows (very long animation) — thin frames.
    sw, sh = max(1, int(w0 * 0.1)), max(1, int(h0 * 0.1))
    fr = [f.resize((sw, sh), Image.LANCZOS) for f in fr]
    while True:
        _write_gif(fr, du, path, grayscale)
        if os.path.getsize(path) <= max_bytes or len(fr) <= 6:
            return
        nf, nd = [], []
        for i in range(0, len(fr), 2):
            nf.append(fr[i])
            nd.append(du[i] + (du[i + 1] if i + 1 < len(du) else 0))
        fr, du = nf, nd


def braille_gif_frames(path, width, invert, detail, contrast, remove_bg,
                       tolerance, aspect, max_frames=60,
                       fg=(255, 255, 255), bg=(0, 0, 0), font_size=14,
                       smooth=0.0, edge_fade=0.0):
    """Render each frame of an animated image to a braille-art PIL image.
    Returns (frames, durations); all frames share frame[0]'s size."""
    src = Image.open(path)
    font = _find_mono_font(font_size)
    frames, durations = [], []
    for count, frame in enumerate(ImageSequence.Iterator(src)):
        if count >= max_frames:
            break
        rgba = ImageOps.exif_transpose(frame.convert("RGBA"))
        gray, alpha = _split(rgba, remove_bg, tolerance)
        art = _braille_text(gray, alpha, width, invert, detail, contrast,
                            aspect, smooth, edge_fade)
        frames.append(_text_to_image(art, font, fg, bg))
        durations.append(frame.info.get("duration", 100))
    if not frames:
        raise ValueError("No frames found in image.")
    size = frames[0].size
    frames = [f if f.size == size else f.resize(size) for f in frames]
    return frames, durations


def gif_to_braille_gif(path, out_path, width, invert, detail, contrast,
                       remove_bg, tolerance, aspect, max_frames=60,
                       fg=(255, 255, 255), bg=(0, 0, 0), font_size=14,
                       smooth=0.0, edge_fade=0.0):
    """Convert an animated image to braille art and save an animated GIF for
    Steam's Artwork Showcase. Returns (frame_count, out_path)."""
    frames, durations = braille_gif_frames(
        path, width, invert, detail, contrast, remove_bg, tolerance, aspect,
        max_frames, fg, bg, font_size, smooth, edge_fade)
    _save_animated_gif(frames, durations, out_path, grayscale=True)
    return len(frames), out_path


# Steam's "long image" Artwork Showcase trick: a wide middle artwork (Steam
# shows it ~506 px wide) sits beside a narrow side artwork (~100 px), both the
# same height, so they read as one image. Steam scales each piece to its slot
# width keeping the file's aspect ratio, so the two crops must be in an exact
# 506:100 width ratio for their displayed heights to match (else the seam drifts
# by a row). 506:100 reduces to 253:50, summing to 303.
SHOWCASE_BIG_FRAC = 506 / 606  # ≈ 0.835, used only for the preview guide line
SHOWCASE_BIG_UNITS, SHOWCASE_SIDE_UNITS, SHOWCASE_UNIT_SUM = 253, 50, 303


def showcase_boxes(size):
    """[("big", box), ("side", box)] full-height crops that together cover the
    ENTIRE width, split in the ~506:100 ratio (about 83% / 17%). The widths are
    native (no resampling) so braille dots stay crisp. We split the whole image
    rather than trimming to an exact 253:50 unit — trimming used to discard up
    to ~40% of the art off the right edge, which showed up as empty/white space
    in the recombined showcase. The near-exact ratio leaves at most sub-pixel
    seam drift over the height."""
    w, h = size
    bw = max(1, min(w - 1, round(w * SHOWCASE_BIG_UNITS / SHOWCASE_UNIT_SUM)))
    return [("big", (0, 0, bw, h)), ("side", (bw, 0, w, h))]


def orig_gif_frames(path, max_frames=60):
    """Original (un-braille) frames of an animated image as RGB, plus their
    durations. Used by the 'crop only' showcase mode, which keeps the source
    image's real pixels/colors instead of converting to braille."""
    src = Image.open(path)
    frames, durations = [], []
    for count, frame in enumerate(ImageSequence.Iterator(src)):
        if count >= max_frames:
            break
        frames.append(ImageOps.exif_transpose(frame.convert("RGB")))
        durations.append(frame.info.get("duration", 100))
    if not frames:
        raise ValueError("No frames found in image.")
    size = frames[0].size
    frames = [f if f.size == size else f.resize(size) for f in frames]
    return frames, durations


# Steam rejects very small artwork and shows an empty white slot, so the narrow
# side tile must be at least this wide. We upscale both tiles (integer factor,
# NEAREST so braille dots stay crisp) until the side reaches it.
MIN_SIDE_PX = 100


def _save_showcase_tiles(frames, durations, base, out_dir,
                         resample=Image.NEAREST, grayscale=True):
    """Slice each frame into the 1-big-1-side layout (~506:100 ratio, full
    width) and save 2 animated GIFs (…_showcase_big/side.gif). Tiles are
    upscaled so the narrow side piece is large enough for Steam to accept
    instead of showing a white/broken slot (NEAREST keeps braille dots crisp;
    pass LANCZOS for real-pixel frames). Returns the written paths."""
    w, h = frames[0].size
    side_w = next(b[2] - b[0] for n, b in showcase_boxes((w, h)) if n == "side")
    factor = max(1, -(-MIN_SIDE_PX // max(1, side_w)))  # ceil division
    if factor > 1:
        frames = [f.resize((w * factor, h * factor), resample) for f in frames]

    fr, du = frames, list(durations)
    big_dst = os.path.join(out_dir, f"{base}_showcase_big.gif")
    side_dst = os.path.join(out_dir, f"{base}_showcase_side.gif")
    # Shrink BOTH tiles together (full frames -> same height & 506:100 ratio)
    # until the larger 'big' tile fits 5 MB. Downscale first (keeps every frame
    # = FPS); only thin frames if the canvas is already small.
    for _ in range(24):
        big_box = next(b for n, b in showcase_boxes(fr[0].size) if n == "big")
        _save_animated_gif([f.crop(big_box) for f in fr], du,
                           big_dst, grayscale=grayscale, max_bytes=None)
        if os.path.getsize(big_dst) <= MAX_GIF_BYTES:
            break
        fw, fh = fr[0].size
        if min(fw, fh) > 150:
            fr = [f.resize((max(1, int(fw * 0.85)), max(1, int(fh * 0.85))),
                           Image.LANCZOS) for f in fr]
        elif len(fr) > 8:
            nf, nd = [], []
            for i in range(0, len(fr), 2):
                nf.append(fr[i])
                nd.append(du[i] + (du[i + 1] if i + 1 < len(du) else 0))
            fr, du = nf, nd
        else:
            break
    side_box = next(b for n, b in showcase_boxes(fr[0].size) if n == "side")
    _save_animated_gif([f.crop(side_box) for f in fr], du,
                       side_dst, grayscale=grayscale, max_bytes=None)
    return [big_dst, side_dst]


def gif_to_showcase_gifs(path, out_dir, width, invert, detail, contrast,
                         remove_bg, tolerance, aspect, max_frames=60,
                         fg=(255, 255, 255), bg=(0, 0, 0), font_size=14,
                         smooth=0.0, edge_fade=0.0):
    """Convert to braille, then slice into the 1-big-1-side showcase tiles.
    Returns (frame_count, [paths])."""
    frames, durations = braille_gif_frames(
        path, width, invert, detail, contrast, remove_bg, tolerance, aspect,
        max_frames, fg, bg, font_size, smooth, edge_fade)
    base = os.path.splitext(os.path.basename(path))[0]
    return len(frames), _save_showcase_tiles(frames, durations, base, out_dir)


def crop_to_showcase_gifs(path, out_dir, max_frames=60):
    """Slice the ORIGINAL animated image (no braille) into the 1-big-1-side
    showcase tiles, keeping its real pixels. Returns (frame_count, [paths])."""
    frames, durations = orig_gif_frames(path, max_frames)
    base = os.path.splitext(os.path.basename(path))[0]
    return len(frames), _save_showcase_tiles(frames, durations, base, out_dir,
                                             resample=Image.LANCZOS,
                                             grayscale=False)


def _edge_mask(size, frac):
    """L mask: 255 in the centre, fading to 0 within `frac` of the half-size of
    each edge. Built once and reused to vignette frames toward the background."""
    w, h = size
    mask = Image.new("L", (w, h), 255)
    feather = frac * min(w, h) / 2.0
    if feather <= 0:
        return mask
    px = mask.load()
    for y in range(h):
        dy = min(y, h - 1 - y)
        for x in range(w):
            dist = min(x, w - 1 - x, dy)
            if dist < feather:
                t = dist / feather                  # smoothstep -> seamless blend
                px[x, y] = int(t * t * (3 - 2 * t) * 255)
    return mask


def _vignette(img, mask, bg):
    return Image.composite(img.convert("RGB"),
                           Image.new("RGB", img.size, bg), mask)


def apply_color_filter(img, color, strength):
    """Grade `img` toward `color` (an (r,g,b) tuple) at `strength` (0..1) using a
    MULTIPLY tint blended over the original. Multiply keeps blacks black (so a
    dark background stays dark) while pushing the lit areas toward the colour —
    e.g. red makes a portrait warmer/bloodier without washing the backdrop.
    Preserves an alpha channel if present."""
    if not color or strength <= 0:
        return img
    alpha = img.split()[3] if img.mode == "RGBA" else None
    base = img.convert("RGB")
    tint = ImageChops.multiply(base, Image.new("RGB", base.size, tuple(color)))
    out = Image.blend(base, tint, min(1.0, strength))
    if alpha is not None:
        out = out.convert("RGBA")
        out.putalpha(alpha)
    return out


def morph_frames(path, width, invert, detail, contrast, remove_bg, tolerance,
                 aspect, smooth=0.0, edge_fade=0.0, fg=(255, 255, 255),
                 bg=(0, 0, 0), font_size=14, max_frames=60,
                 hold=8, fade=16, orig_hold=4, base_ms=80, fade_ms=80):
    """Frames that cross-fade the ORIGINAL image into its Braille version, hold
    on braille for `hold` frames, then fade back (and briefly hold the original
    so the loop breathes). The underlying animation keeps MOVING throughout.
    Transition speed is controlled by `fade_ms` (how long EACH fade frame shows)
    — not playback: the hold and original rest at `base_ms` regardless, so only
    the orig<->braille transition gets faster/slower. Background removal applies
    to the Braille phase only; edge fade to both. Returns (frames, durations)."""
    src = Image.open(path)
    font = _find_mono_font(font_size)
    origs, brs, durs = [], [], []
    for i, frame in enumerate(ImageSequence.Iterator(src)):
        if i >= max_frames:
            break
        rgba = ImageOps.exif_transpose(frame.convert("RGBA"))
        gray, alpha = _split(rgba, remove_bg, tolerance)  # braille: bg removed
        art = _braille_text(gray, alpha, width, invert, detail, contrast,
                            aspect, smooth, edge_fade)
        b = _text_to_image(art, font, fg, bg).convert("RGB")
        origs.append(rgba.convert("RGB").resize(b.size))  # original keeps bg
        brs.append(b)
        durs.append(frame.info.get("duration", 80))
    n = len(origs)
    if n == 0:
        raise ValueError("No frames found.")
    size = brs[0].size
    origs = [f if f.size == size else f.resize(size) for f in origs]
    if edge_fade > 0:  # fade the original's edges too
        m = _edge_mask(size, edge_fade)
        origs = [_vignette(o, m, bg) for o in origs]

    # Forward pass as (blend t, frame duration): brief original hold, fade in
    # (fade_ms per frame = transition speed), then hold on braille. The source
    # frame index advances every step so the animation keeps moving.
    fade = max(2, fade)
    fwd = ([(0.0, base_ms)] * max(0, orig_hold)
           + [(i / fade, fade_ms) for i in range(1, fade + 1)]
           + [(1.0, base_ms)] * max(0, hold))
    imgs, ds = [], []
    for k, (t, dur) in enumerate(fwd):
        idx = k % n
        imgs.append(Image.blend(origs[idx], brs[idx], t))
        ds.append(max(20, dur))
    # Boomerang: append the forward pass reversed (minus the two endpoints) so
    # it plays original->braille and then exactly back to the start — a seamless
    # loop with the source frames ping-ponging too.
    if len(imgs) > 2:
        imgs += imgs[-2:0:-1]
        ds += ds[-2:0:-1]
    return imgs, ds


# --- Terminal / hacker info box ---------------------------------------------
def terminal_box(art, fields, code=True):
    """Lay braille art beside a neofetch-style readout, wrapped in [code]."""
    art_lines = art.split("\n") if art else []
    art_w = max((len(ln) for ln in art_lines), default=0)
    info_lines = [f"{k}: {v}" for k, v in fields]

    rows = max(len(art_lines), len(info_lines))
    out = []
    gap = "  "
    for i in range(rows):
        left = art_lines[i] if i < len(art_lines) else ""
        left = left + BLANK_BRAILLE * (art_w - len(left))
        right = info_lines[i] if i < len(info_lines) else ""
        out.append((left + gap + right).rstrip() if not art_w else left + gap + right)
    body = "\n".join(out)
    return f"[code]\n{body}\n[/code]" if code else body


# Classic terminal phosphor colors for the image export (RGB).
TERM_COLORS = {
    "Green": (51, 255, 51),
    "Amber": (255, 176, 0),
    "Cyan": (0, 255, 255),
    "White": (220, 220, 220),
}
DEFAULT_TERM_COLOR = "Green"


def terminal_to_image(art, fields, color, bg=(8, 12, 8), font_size=18, pad=16):
    """Render the terminal box as a colored PNG (Steam text can't be colored,
    but an uploaded artwork image can). Returns a PIL image."""
    body = terminal_box(art, fields, code=False)
    font = _find_mono_font(font_size)
    inner = _text_to_image(body, font, color, bg)
    canvas = Image.new("RGB", (inner.width + pad * 2, inner.height + pad * 2), bg)
    canvas.paste(inner, (pad, pad))
    return canvas


TERMINAL_DEFAULT = """user@steam:~$ neofetch
OS: SteamOS 3.0 (Holo)
Host: GabenStation X
Kernel: 6.6.9-valve
Uptime: 1337 hours
Shell: bash 5.2
Resolution: 1920x1080
CPU: Ryzen 7 (16) @ 3.4GHz
GPU: Radeon RX 7800
Memory: 13337MiB / 32768MiB
Status: ONLINE"""

_TERM_OS = ["SteamOS 3.0 (Holo)", "Arch btw", "Windows 11 Pro", "Ubuntu 24.04",
            "Gentoo (compiling...)"]
_TERM_GPU = ["Radeon RX 7800", "RTX 4090", "GTX 1060 (still alive)",
             "Intel Arc A770", "RTX 5080"]
_TERM_STATUS = ["ONLINE", "AFK", "IN GAME", "DO NOT DISTURB", "TOUCHING GRASS"]


def random_terminal():
    return "\n".join([
        "user@steam:~$ neofetch",
        f"OS: {random.choice(_TERM_OS)}",
        "Host: GabenStation X",
        f"Kernel: 6.{random.randint(1, 9)}.{random.randint(0, 12)}-valve",
        f"Uptime: {random.randint(1, 9999)} hours",
        "Shell: bash 5.2",
        "Resolution: 1920x1080",
        f"CPU: Ryzen {random.choice('579')} ({random.choice((8, 12, 16))}) "
        f"@ {random.uniform(3.0, 5.0):.1f}GHz",
        f"GPU: {random.choice(_TERM_GPU)}",
        f"Memory: {random.randint(4, 30)}GiB / 32GiB",
        f"Status: {random.choice(_TERM_STATUS)}",
    ])


# --- Fancy text / name generator -------------------------------------------
def _alpha(upper, lower, digit=None, holes=None):
    holes = holes or {}

    def f(text):
        out = []
        for ch in text:
            if ch in holes:
                out.append(holes[ch])
            elif "A" <= ch <= "Z":
                out.append(chr(upper + ord(ch) - 65))
            elif "a" <= ch <= "z":
                out.append(chr(lower + ord(ch) - 97))
            elif digit is not None and "0" <= ch <= "9":
                out.append(chr(digit + ord(ch) - 48))
            else:
                out.append(ch)
        return "".join(out)
    return f


_CIRCLED_DIGITS = {"0": "⓪", **{str(d): chr(0x2460 + d - 1) for d in range(1, 10)}}

FONTS = {
    "Bold": _alpha(0x1D400, 0x1D41A, 0x1D7CE),
    "Italic": _alpha(0x1D434, 0x1D44E, holes={"h": "ℎ"}),
    "Bold Italic": _alpha(0x1D468, 0x1D482),
    "Sans": _alpha(0x1D5A0, 0x1D5BA, 0x1D7E2),
    "Sans Bold": _alpha(0x1D5D4, 0x1D5EE, 0x1D7EC),
    "Monospace": _alpha(0x1D670, 0x1D68A, 0x1D7F6),
    "Fraktur": _alpha(0x1D504, 0x1D51E, holes={
        "C": "ℭ", "H": "ℌ", "I": "ℑ", "R": "ℜ", "Z": "ℨ"}),
    "Double-struck": _alpha(0x1D538, 0x1D552, 0x1D7D8, holes={
        "C": "ℂ", "H": "ℍ", "N": "ℕ", "P": "ℙ",
        "Q": "ℚ", "R": "ℝ", "Z": "ℤ"}),
    "Circled": _alpha(0x24B6, 0x24D0, holes=_CIRCLED_DIGITS),
    "Fullwidth": lambda t: "".join(
        chr(ord(c) + 0xFEE0) if "!" <= c <= "~" else c for c in t),
}

# {n} is replaced by the (optionally font-styled) name.
DECORATIONS = [
    "✦ {n} ✦",
    "『{n}』",
    "꧁{n}꧂",
    "☠ {n} ☠",
    "⚔ {n} ⚔",
    "★彡{n}彡★",
    "「{n}」",
    "◄█ {n} █►",
    "✿ {n} ✿",
    "✵{n}✵",
]

ADJECTIVES = ["Shadow", "Toxic", "Silent", "Frost", "Dark", "Crimson", "Rapid",
              "Cyber", "Iron", "Phantom", "Savage", "Lunar", "Venom", "Rogue",
              "Mystic", "Brutal", "Neon", "Hyper", "Grim", "Stealth", "Vortex",
              "Chaos", "Solar", "Atomic", "Feral"]
NOUNS = ["Wolf", "Reaper", "Sniper", "Ghost", "Dragon", "Hunter", "Blade",
         "Storm", "Viper", "Knight", "Demon", "Raven", "Hawk", "Slayer",
         "Phoenix", "Titan", "Striker", "Fury", "Specter", "Warden", "Fang",
         "Hydra", "Cobra", "Saint", "Nomad"]


def random_base_name():
    name = random.choice(ADJECTIVES) + random.choice(NOUNS)
    if random.random() < 0.4:
        name += str(random.randint(1, 99))
    return name


def generate_names(base):
    """Return a list of (style_label, styled_name) variants for base text."""
    base = base.strip()
    if not base:
        base = random_base_name()
    results = [("Plain", base)]
    for label, fn in FONTS.items():
        results.append((label, fn(base)))
    # A few decorated combos using nice fonts.
    deco_fonts = ["Bold", "Sans Bold", "Fraktur"]
    for i, template in enumerate(DECORATIONS):
        fn = FONTS[deco_fonts[i % len(deco_fonts)]]
        results.append(("Decorated", template.format(n=fn(base))))
    return results


# --- How-to-upload guide ----------------------------------------------------
# The browser-console one-liners from the long-image showcase guide. Same
# upload page for both; the screenshot variant just appends file_type=5. Each
# is rendered as its own clickable, click-to-copy line ({cmd_art}/{cmd_ss}).
SHOWCASE_CONSOLE_CMD = (
    "$J('#image_width').val(1000).attr('id',''),"
    "$J('#image_height').val(1).attr('id','');")
SHOWCASE_CONSOLE_CMD_SCREENSHOT = (
    "$J('#image_width').val(1000).attr('id',''),"
    "$J('#image_height').val(1).attr('id',''),$J('[name=file_type]').val(5);")
# Console commands for the hexed.it long-image route (guide id 2174159512):
# point the artwork uploader at a Workshop item or a Guide item.
WORKSHOP_CONSOLE_CMD = (
    "$J('[name=consumer_app_id]').val(480);$J('[name=file_type]').val(0);")
GUIDE_CONSOLE_CMD = "$J('[name=file_type]').val(9);"
# token -> (tag name, command) used by the guide renderer.
GUIDE_CMD_TOKENS = {
    "{cmd_art}": ("code_art", SHOWCASE_CONSOLE_CMD),
    "{cmd_ss}": ("code_ss", SHOWCASE_CONSOLE_CMD_SCREENSHOT),
    "{cmd_ws}": ("code_ws", WORKSHOP_CONSOLE_CMD),
    "{cmd_guide}": ("code_guide", GUIDE_CONSOLE_CMD),
}

# Quick-open buttons shown at the top of the guide. /my/ redirects to whoever
# is logged in, so these open the right page for the user with no profile id.
GUIDE_LINKS = [
    ("Edit Showcases", "https://steamcommunity.com/my/edit/showcases"),
    ("Edit Summary/Name", "https://steamcommunity.com/my/edit/info"),
    ("Artwork Uploader", "https://steamcommunity.com/sharedfiles/edititem/767/3/"),
    ("Long-image Guide", "https://steamcommunity.com/sharedfiles/filedetails/?id=748624905"),
    ("Screenshot Guide", "https://steamcommunity.com/sharedfiles/filedetails/?id=693118839"),
    ("Hex Long-image Guide", "https://steamcommunity.com/sharedfiles/filedetails/?id=2174159512"),
    ("Formatting Help", "https://steamcommunity.com/comment/ForumTopic/formattinghelp"),
]
# Inline clickable links in body text: {{label|url}}
GUIDE_LINK_RE = re.compile(r"\{\{(.+?)\|(.+?)\}\}")

# (heading, body) sections rendered into the "How to Upload" tab. Body text is
# wrapped by the widget, so write it as flowing paragraphs / bullet lines.
GUIDE_SECTIONS = [
    ("Quick start",
     "1.  Open an image on the Image -> ASCII tab and pick a Style (Braille = "
     "most detail).\n"
     "2.  Choose where it's going in the 'Use for' box — it sets a safe width "
     "and byte limit automatically.\n"
     "3.  Click 'Copy to clipboard' for text art, or use a tool tab's Export "
     "button for image art.\n"
     "4.  Paste / upload it on Steam using the matching section below.\n"
     "The status bar shows the real Steam cost — block & braille glyphs are 3 "
     "bytes each, not 1."),

    ("Profile — Custom Info Box  (best for braille art)",
     "The Info Box is an 8000-byte showcase and is where braille art looks "
     "best. It does NOT use [code]; the app outputs raw braille whose blanks "
     "are U+2800 (a real glyph that Steam never collapses), so it stays aligned.\n"
     "1.  Open {{Edit → Showcases|https://steamcommunity.com/my/edit/showcases}} "
     "(needs Steam Level 10+).\n"
     "2.  Add a 'Custom Info Box', give it a Title.\n"
     "3.  Paste the copied art into the content field, then Save.\n"
     "Keep braille about 52 characters wide or less so it doesn't wrap in the "
     "box."),

    ("Chat, comments & profile summary  (plain text)",
     "These collapse runs of normal spaces, so keep 'Steam-safe spaces' and "
     "'Auto-fit' on (the app uses U+2800 blanks, which don't collapse).\n"
     "• Steam Chat — click the message box, Ctrl+V, Enter (~2048 bytes). "
     "Comments/chat use a non-monospace font, so braille can misalign there — "
     "the Info Box is more reliable.\n"
     "• Profile Comment — scroll to the Comments box on any profile, paste, "
     "Post Comment (1000-byte cap).\n"
     "• Profile Summary — {{Edit → Summary|https://steamcommunity.com/my/edit/info}} "
     "→ paste → Save."),

    ("[code] surfaces  (reviews, groups, guides)",
     "Inside a [code] block Steam keeps every space and uses a monospace font, "
     "so any style lines up. The app wraps output in [code] for these.\n"
     "• Review — a game's community page → Write a Review → paste into the "
     "body → Post.\n"
     "• Group / Workshop — a group's Edit page or your Workshop item → Edit → "
     "Description."),

    ("Fancy profile name  (Name Generator tab)",
     "The styled names are real Unicode letters, so they stick as your name.\n"
     "1.  Open {{Edit → Name|https://steamcommunity.com/my/edit/info}}.\n"
     "2.  Paste a generated name into Profile Name → Save.\n"
     "Steam shows ~32 characters; the tab flags variants that are too long."),

    ("Uploading image art  (Banner, Animated GIF, Terminal image)",
     "Steam can't color or animate pasted text, so these tabs make image files "
     "you upload as Artwork.\n"
     "1.  Upload: your profile → right-side 'Artwork' → Upload Artwork → choose "
     "the PNG/GIF → set Public → Save.\n"
     "2.  Show it: {{Edit → Showcases|https://steamcommunity.com/my/edit/showcases}} "
     "→ add an 'Artwork Showcase' → pick your upload.\n"
     "• Animated GIF — animates once uploaded; the exported GIF is kept under "
     "5 MB.\n"
     "• Terminal image — gives colored (green/amber) text a pasted box can't.\n"
     "Banner & 'Showcase split' tiles are very wide/narrow, so Steam's normal "
     "uploader rejects them — use the trick in the next section."),

    ("Long-image trick  (Banner & Showcase-split tiles)",
     "Based on two Steam guides: {{Long Images (artwork)|"
     "https://steamcommunity.com/sharedfiles/filedetails/?id=748624905}} and "
     "the often-faster {{Animated Screenshots|"
     "https://steamcommunity.com/sharedfiles/filedetails/?id=693118839}} route "
     "(screenshot showcase). A normal showcase shows a 506px middle next to a "
     "100px side (same height); the 'Showcase split' export uses that 506:100 "
     "ratio.\n"
     "Per tile:\n"
     "1.  Open {{the uploader|https://steamcommunity.com/sharedfiles/edititem/767/3/}} "
     "in Chrome or Firefox.\n"
     "2.  Click 'Choose File' and pick a tile (e.g. …_showcase_big.gif).\n"
     "3.  Open the dev console (Chrome Ctrl+Shift+J, Firefox Ctrl+Shift+K). In "
     "Firefox, type 'allow pasting' + Enter first.\n"
     "4.  Paste ONE line that matches your showcase type, then Enter "
     "(click a line to copy it):\n"
     "   • Artwork / Featured Artwork:\n"
     "{cmd_art}\n"
     "   • Screenshot showcase (adds file_type=5):\n"
     "{cmd_ss}\n"
     "5.  Add a title, tick 'I certify that I created this artwork', then "
     "'Save and Continue'. Repeat for the other tile.\n"
     "6.  On your profile add an Artwork Showcase and place the big piece in "
     "the middle and the side piece next to it.\n"
     "Note: in the picker the tile looks like a thin black line — that's normal "
     "and means the trick worked."),

    ("Long-image patch  (hex 0x21 method — Banner Slicer)",
     "An alternative to the console width/height trick, from the {{Hex "
     "Long-image Guide|https://steamcommunity.com/sharedfiles/filedetails/?id="
     "2174159512}}. It overwrites the file's last byte with 0x21 so Steam's "
     "uploader skips its size/dimension check — works for any wide/tall image "
     "or oversized GIF, regardless of frame count.\n"
     "The app can do the hex edit FOR you: on the Banner Slicer tab tick "
     "'Long-image patch (0x21)' before 'Slice & save'. The saved tiles are "
     "already patched, so you skip hexed.it entirely — just upload them.\n"
     "Then on {{the uploader|https://steamcommunity.com/sharedfiles/edititem/"
     "767/3/}} open the dev console and paste the line for your target:\n"
     "   • Workshop item (app 480):\n"
     "{cmd_ws}\n"
     "   • Guide item:\n"
     "{cmd_guide}\n"
     "Heads-up: as of mid-2026 some users report this hex method no longer "
     "works on every surface; if a patched upload is rejected, fall back to the "
     "console width/height trick in the section above."),

    ("Tips",
     "• Watch the byte counter, not character count — Steam measures UTF-8 "
     "bytes and stores line breaks as 2 bytes.\n"
     "• If art looks squished, change the Ratio or raise Width and let Auto-fit "
     "pull it back under the limit.\n"
     "• 'Remove background' + Tolerance isolates a subject from a flat backdrop.\n"
     "• The preview uses Steam's own braille font (Segoe UI Symbol) so it "
     "matches the paste; the desktop client renders most reliably."),
]


def center_block(raw, field, pad):
    """Center every line within `field` columns by left-padding with `pad`
    (U+2800 on space-collapsing surfaces, else a normal space). Trailing pad is
    dropped so the art stays a clean centered silhouette. Lines already as wide
    as the field are left untouched."""
    lines = raw.split("\n")
    field = max(field, max((len(l.rstrip(pad + " ")) for l in lines), default=0))
    out = []
    for line in lines:
        body = line.rstrip(pad + " ")
        left = max(0, (field - len(body)) // 2)
        out.append(pad * left + body)
    return "\n".join(out)


# --- Info-box decorations ---------------------------------------------------
# Ready-to-paste Unicode snippets for dressing up a Custom Info Box / summary.
# Everything here renders on Steam without [code]; multi-line entries use
# U+2800 (Braille blank) where a non-collapsing space is needed. Replace the
# word TITLE / TEXT after pasting. Each category is a list of (label, snippet).
DECORATIONS = {
    "Dividers": [
        ("Thin line", "────────────────────────"),
        ("Heavy line", "━━━━━━━━━━━━━━━━━━━━━━━━"),
        ("Double line", "════════════════════════"),
        ("Dashed", "╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌"),
        ("Dotted", "┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄"),
        ("Diamonds", "◆━━━━━━━━━◆━━━━━━━━━◆"),
        ("Stars", "✦  ✧  ✦  ✧  ✦  ✧  ✦  ✧  ✦"),
        ("Arrows", "➤➤➤➤➤➤➤➤➤➤➤➤➤➤➤➤➤➤➤➤"),
        ("Wave", "∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿"),
        ("Center flourish", "❖ ────────── ✦ ────────── ❖"),
    ],
    "Headers": [
        ("Bracketed", "▰▰▰▰▰▰▰▰  TITLE  ▰▰▰▰▰▰▰▰"),
        ("Star wrap", "✦ ✧ ✦  TITLE  ✦ ✧ ✦"),
        ("Arrow tag", "►  TITLE  ◄"),
        ("Bar", "█▓▒░  TITLE  ░▒▓█"),
        ("Diamond", "◇◆◇  TITLE  ◇◆◇"),
        ("Quote", "❝ TITLE ❞"),
        ("Tilde", "～•～•～ TITLE ～•～•～"),
        ("Heavy tag", "┏━━ TITLE ━━┓"),
    ],
    "Borders": [
        ("Rounded box", "╭─────────────╮\n│⠀⠀⠀TEXT⠀⠀⠀⠀⠀│\n╰─────────────╯"),
        ("Square box", "┌─────────────┐\n│⠀⠀⠀TEXT⠀⠀⠀⠀⠀│\n└─────────────┘"),
        ("Double box", "╔═════════════╗\n║⠀⠀⠀TEXT⠀⠀⠀⠀⠀║\n╚═════════════╝"),
        ("Heavy box", "┏━━━━━━━━━━━━━┓\n┃⠀⠀⠀TEXT⠀⠀⠀⠀⠀┃\n┗━━━━━━━━━━━━━┛"),
        ("Corners only", "┌            ┐\n⠀⠀⠀⠀TEXT\n└            ┘"),
        ("Star frame", "✦ ─────────── ✦\n⠀⠀⠀⠀⠀TEXT\n✦ ─────────── ✦"),
    ],
    "Bullets": [
        ("Diamond", "◆ "), ("Small diamond", "◈ "), ("Arrow", "➤ "),
        ("Triangle", "‣ "), ("Star", "★ "), ("Sparkle", "✦ "),
        ("Dot", "• "), ("Ring", "◦ "), ("Square", "▪ "),
        ("Chevron", "» "), ("Flower", "❀ "), ("Heart", "♥ "),
    ],
    "Kaomoji": [
        ("Shrug", "¯\\_(ツ)_/¯"), ("Happy", "(◕‿◕)"), ("Cool", "(⌐■_■)"),
        ("Wink", "(^_~)"), ("Love", "(♥ω♥)"), ("Table flip", "(╯°□°)╯︵ ┻━┻"),
        ("Bear", "ʕ•ᴥ•ʔ"), ("Cat", "(=^･ω･^=)"), ("Salute", "(￣^￣)ゞ"),
        ("Sleepy", "(￣o￣) zzZ"), ("Stars", "☆*:.｡.o(≧▽≦)o.｡.:*☆"),
    ],
    "Spacers (invisible)": [
        ("1 blank cell", "⠀"),
        ("Short indent (4)", "⠀⠀⠀⠀"),
        ("Long indent (8)", "⠀⠀⠀⠀⠀⠀⠀⠀"),
        ("Blank line", "⠀\n⠀"),
    ],
}
DEFAULT_DECOR_CATEGORY = "Dividers"


# --- Profile preview (read-only, no login) ----------------------------------
def _profile_xml_url(url):
    """Normalize a profile URL or bare vanity/id into its ?xml=1 endpoint."""
    url = (url or "").strip()
    if not url:
        return None
    if not url.startswith("http"):
        url = "https://steamcommunity.com/id/" + url
    return url.split("?")[0].rstrip("/") + "?xml=1"


def _http_get(url, timeout=10):
    """GET bytes. Verifies TLS; falls back to an unverified context only if the
    frozen build lacks a CA bundle (we only read PUBLIC data, so this is safe)."""
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return r.read()
    except urllib.error.URLError as exc:
        import ssl
        if not isinstance(getattr(exc, "reason", None), ssl.SSLError):
            raise
        ctx = ssl.create_default_context()
        ctx.check_hostname = False
        ctx.verify_mode = ssl.CERT_NONE
        with urllib.request.urlopen(req, timeout=timeout, context=ctx) as r:
            return r.read()


def fetch_profile(url, timeout=10):
    """Read PUBLIC profile data with NO login: persona name + avatar via the
    official ?xml=1 endpoint, plus a best-effort static background scraped from
    the page (animated webm backgrounds are skipped). Returns
    dict(name, avatar(RGBA|None), background(RGB|None)). Raises on failure."""
    xml_url = _profile_xml_url(url)
    if not xml_url:
        raise ValueError("Enter a profile URL or vanity name.")
    root = ET.fromstring(_http_get(xml_url, timeout))
    name = (root.findtext("steamID") or "Steam User").strip()
    avatar = None
    avatar_url = (root.findtext("avatarFull") or "").strip()
    if avatar_url:
        avatar = Image.open(BytesIO(_http_get(avatar_url, timeout))).convert("RGBA")
    background = None
    try:
        page = _http_get(xml_url[:-len("?xml=1")], timeout).decode("utf-8", "ignore")
        m = re.search(r"profile_background_image_content[^>]*background-image:"
                      r"\s*url\(\s*'?([^')\s]+\.(?:jpg|jpeg|png))", page)
        if m:
            background = Image.open(
                BytesIO(_http_get(m.group(1), timeout))).convert("RGB")
    except Exception:  # noqa: BLE001 - background is optional decoration
        background = None
    return {"name": name, "avatar": avatar, "background": background}


def render_profile_mock(name, avatar, background, main_img, side_img,
                        infobox, level=42, width=620):
    """Composite a Steam-style profile mockup (PIL RGB) from the supplied pieces
    so the user can see how their generated artwork/info box will look in place.
    Any piece may be None. The artwork row uses the ~506:100 main:side ratio."""
    H = 2000
    img = Image.new("RGB", (width, H), (0x17, 0x1a, 0x21))
    if background is not None:
        scaled = background.resize(
            (width, max(1, background.height * width // background.width)))
        band = scaled.crop((0, 0, width, min(scaled.height, 320)))
        img.paste(Image.blend(band, Image.new("RGB", band.size, (0, 0, 0)), 0.5),
                  (0, 0))
    draw = ImageDraw.Draw(img)
    f_name = _steam_braille_font(22)
    f_small = _steam_braille_font(12)
    f_mono = _steam_braille_font(13)
    pad = 16
    y = pad

    if avatar is not None:
        img.paste(avatar.convert("RGB").resize((64, 64)), (pad, y))
    name_x = pad + (80 if avatar is not None else 0)
    draw.text((name_x, y + 6), name or "Steam User", font=f_name,
              fill=(0xE8, 0xE8, 0xE8))
    draw.text((name_x, y + 36), f"Level  {level}", font=f_small,
              fill=(0x8F, 0x98, 0xA0))
    y += 64 + pad

    def fit(im, w):
        h = max(1, im.height * w // im.width)
        return im.convert("RGB").resize((w, h))

    if main_img is not None or side_img is not None:
        draw.text((pad, y), "ARTWORK SHOWCASE", font=f_small, fill=(0x6D, 0xCF, 0xF6))
        y += 20
        avail = width - 2 * pad
        side_w = max(1, 100 * avail // 606)
        gap = 6
        main_w = avail - side_w - gap
        row_h = 0
        if main_img is not None:
            mi = fit(main_img, main_w)
            img.paste(mi, (pad, y))
            row_h = max(row_h, mi.height)
        if side_img is not None:
            si = fit(side_img, side_w)
            img.paste(si, (pad + main_w + gap, y))
            row_h = max(row_h, si.height)
        y += row_h + pad

    if (infobox or "").strip():
        draw.text((pad, y), "INFO BOX", font=f_small, fill=(0x6D, 0xCF, 0xF6))
        y += 20
        lines = infobox.split("\n")
        lh = f_mono.getbbox("⣿")[3] + 3
        box_h = lh * len(lines) + 16
        draw.rectangle((pad, y, width - pad, y + box_h), fill=(0x16, 0x20, 0x2D))
        ty = y + 8
        for ln in lines:
            draw.text((pad + 10, ty), ln, font=f_mono, fill=(0xC6, 0xD4, 0xDE))
            ty += lh
        y += box_h + pad

    return img.crop((0, 0, width, min(H, y)))


# --- UI ---------------------------------------------------------------------
class App:
    def __init__(self, root):
        self.root = root
        self.path = None
        self.last_art = ""
        self.name_variants = []
        self.mono_family = register_bundled_font()

        root.title("ASCII Steam Art Studio")
        root.geometry("980x740")
        root.minsize(700, 520)

        nb = ttk.Notebook(root)
        nb.pack(fill="both", expand=True)
        tabs = {name: ttk.Frame(nb) for name in
                ("Image -> ASCII", "Name Generator", "Decorations",
                 "Banner Slicer", "Progress Bars", "Animated GIF",
                 "Terminal Box", "Profile Preview", "How to Upload")}
        for name, frame in tabs.items():
            nb.add(frame, text=name)

        self._build_converter(tabs["Image -> ASCII"])
        self._build_namegen(tabs["Name Generator"])
        self._build_decorations(tabs["Decorations"])
        self._build_banner(tabs["Banner Slicer"])
        self._build_progress(tabs["Progress Bars"])
        self._build_gif(tabs["Animated GIF"])
        self._build_terminal(tabs["Terminal Box"])
        self._build_profile_preview(tabs["Profile Preview"])
        self._build_guide(tabs["How to Upload"])

        if not DESTINATIONS[self.dest_var.get()]["title"]:
            self.title_entry.configure(state="disabled")
            self.title_label.configure(text="Title (n/a):")

    def _slider(self, parent, var, lo, hi, cmd, ewidth=4):
        """A Scale paired with an editable Entry so any value can be dragged OR
        typed. `var` is the IntVar the Scale drives; returns a frame to pack."""
        f = ttk.Frame(parent)
        ttk.Scale(f, from_=lo, to=hi, variable=var,
                  command=lambda _=None: cmd()).pack(
            side="left", fill="x", expand=True, padx=(4, 2))
        sv = tk.StringVar(value=str(int(var.get())))
        ent = ttk.Entry(f, width=ewidth, textvariable=sv)
        ent.pack(side="left")

        def commit(_=None):
            try:
                v = max(lo, min(hi, int(round(float(sv.get())))))
            except (ValueError, tk.TclError):
                v = int(var.get())
            var.set(v)
            sv.set(str(v))
            cmd()

        ent.bind("<Return>", commit)
        ent.bind("<FocusOut>", commit)
        var.trace_add("write", lambda *_: sv.set(str(int(var.get()))))
        return f

    # ---- converter tab --------------------------------------------------
    def _build_converter(self, parent):
        bar = ttk.Frame(parent, padding=8)
        bar.pack(side="top", fill="x")

        ttk.Button(bar, text="Open image…", command=self.choose_file).pack(side="left")

        ttk.Label(bar, text="Style:").pack(side="left", padx=(16, 4))
        self.style_var = tk.StringVar(value=DEFAULT_STYLE)
        style_box = ttk.Combobox(bar, textvariable=self.style_var, width=20,
                                 state="readonly", values=list(STYLES))
        style_box.pack(side="left")
        style_box.bind("<<ComboboxSelected>>", lambda _=None: self.render())

        ttk.Label(bar, text="Use for:").pack(side="left", padx=(16, 4))
        self.dest_var = tk.StringVar(value=DEFAULT_DESTINATION)
        dest_box = ttk.Combobox(bar, textvariable=self.dest_var, width=18,
                                state="readonly", values=list(DESTINATIONS))
        dest_box.pack(side="left")
        dest_box.bind("<<ComboboxSelected>>", lambda _=None: self._on_dest_change())

        ttk.Label(bar, text="Ratio:").pack(side="left", padx=(16, 4))
        self.ratio_var = tk.StringVar(value=DEFAULT_RATIO)
        ratio_box = ttk.Combobox(bar, textvariable=self.ratio_var, width=14,
                                 state="readonly", values=list(RATIOS))
        ratio_box.pack(side="left")
        ratio_box.bind("<<ComboboxSelected>>", lambda _=None: self.render())

        ttk.Label(bar, text="Frame:").pack(side="left", padx=(16, 4))
        self.frame_var = tk.StringVar(value=DEFAULT_FRAME)
        frame_box = ttk.Combobox(bar, textvariable=self.frame_var, width=8,
                                 state="readonly", values=list(FRAMES))
        frame_box.pack(side="left")
        frame_box.bind("<<ComboboxSelected>>", lambda _=None: self.render())

        ttk.Label(bar, text="Background:").pack(side="left", padx=(12, 4))
        self.bg_var = tk.StringVar(value="None")
        bg_box = ttk.Combobox(bar, textvariable=self.bg_var, width=7,
                              state="readonly", values=list(BACKGROUNDS))
        bg_box.pack(side="left")
        bg_box.bind("<<ComboboxSelected>>", lambda _=None: self.render())

        ttk.Button(bar, text="Copy to clipboard", command=self.copy).pack(side="right")

        bar2 = ttk.Frame(parent, padding=(8, 0, 8, 4))
        bar2.pack(side="top", fill="x")
        ttk.Label(bar2, text="Width:").pack(side="left")
        start_width = DESTINATIONS[DEFAULT_DESTINATION]["width"]
        self.width_var = tk.IntVar(value=start_width)
        self._slider(bar2, self.width_var, 20, 200, self._on_width_change).pack(
            side="left", fill="x", expand=True, padx=(0, 12))

        self.invert_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(bar2, text="Invert", variable=self.invert_var,
                        command=self.render).pack(side="left", padx=4)
        self.safe_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(bar2, text="Steam-safe spaces", variable=self.safe_var,
                        command=self.render).pack(side="left", padx=4)
        self.center_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(bar2, text="Center", variable=self.center_var,
                        command=self.render).pack(side="left", padx=4)

        self.autofit_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(bar2, text="Auto-fit ≤", variable=self.autofit_var,
                        command=self.render).pack(side="left", padx=(12, 2))
        self.limit_var = tk.StringVar(value=str(DESTINATIONS[DEFAULT_DESTINATION]["byte_limit"]))
        self.limit_var.trace_add("write", lambda *_: self.render())
        ttk.Entry(bar2, textvariable=self.limit_var, width=6).pack(side="left")
        ttk.Label(bar2, text="bytes").pack(side="left", padx=(2, 0))

        bar2b = ttk.Frame(parent, padding=(8, 0, 8, 4))
        bar2b.pack(side="top", fill="x")
        ttk.Label(bar2b, text="Detail:").pack(side="left")
        self.detail_var = tk.IntVar(value=60)
        self._slider(bar2b, self.detail_var, 0, 100, self.render).pack(
            side="left", fill="x", expand=True, padx=(0, 12))
        self.contrast_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(bar2b, text="Auto-contrast", variable=self.contrast_var,
                        command=self.render).pack(side="left", padx=4)

        bar2c = ttk.Frame(parent, padding=(8, 0, 8, 4))
        bar2c.pack(side="top", fill="x")
        self.removebg_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(bar2c, text="Remove background", variable=self.removebg_var,
                        command=self.render).pack(side="left")
        ttk.Label(bar2c, text="Tolerance:").pack(side="left", padx=(16, 4))
        self.tol_var = tk.IntVar(value=12)
        self._slider(bar2c, self.tol_var, 2, 60, self.render).pack(
            side="left", fill="x", expand=True, padx=(0, 12))

        bar2d = ttk.Frame(parent, padding=(8, 0, 8, 2))
        bar2d.pack(side="top", fill="x")
        ttk.Label(bar2d, text="Signature:").pack(side="left")
        self.sig_var = tk.StringVar(value="")
        self.sig_var.trace_add("write", lambda *_: self.render())
        ttk.Entry(bar2d, textvariable=self.sig_var, width=16).pack(side="left", padx=(4, 8))
        ttk.Label(bar2d, text="Font:").pack(side="left")
        self.sig_font = tk.StringVar(value=DEFAULT_SIG_FONT)
        fb = ttk.Combobox(bar2d, textvariable=self.sig_font, width=11,
                          state="readonly", values=list(SIGNATURE_FONTS))
        fb.pack(side="left", padx=(4, 8))
        fb.bind("<<ComboboxSelected>>", lambda _=None: self.render())
        ttk.Label(bar2d, text="Layer:").pack(side="left")
        self.sig_layer = tk.StringVar(value="In front")
        lb = ttk.Combobox(bar2d, textvariable=self.sig_layer, width=9,
                          state="readonly", values=["In front", "Behind"])
        lb.pack(side="left", padx=(4, 8))
        lb.bind("<<ComboboxSelected>>", lambda _=None: self.render())
        self.sig_invert = tk.BooleanVar(value=False)
        ttk.Checkbutton(bar2d, text="Invert text", variable=self.sig_invert,
                        command=self.render).pack(side="left", padx=4)

        bar2e = ttk.Frame(parent, padding=(8, 0, 8, 6))
        bar2e.pack(side="top", fill="x")
        ttk.Label(bar2e, text="Size").pack(side="left")
        self.sig_size = tk.IntVar(value=14)
        self._slider(bar2e, self.sig_size, 0, 60, self.render).pack(side="left", fill="x", expand=True, padx=(2, 8))
        ttk.Label(bar2e, text="X").pack(side="left")
        self.sig_x = tk.IntVar(value=50)
        self._slider(bar2e, self.sig_x, 0, 100, self.render).pack(side="left", fill="x", expand=True, padx=(2, 8))
        ttk.Label(bar2e, text="Y").pack(side="left")
        self.sig_y = tk.IntVar(value=88)
        self._slider(bar2e, self.sig_y, 0, 100, self.render).pack(side="left", fill="x", expand=True, padx=(2, 8))
        ttk.Label(bar2e, text="Rotate").pack(side="left")
        self.sig_rot = tk.IntVar(value=0)
        self._slider(bar2e, self.sig_rot, 0, 359, self.render).pack(side="left", fill="x", expand=True, padx=(2, 0))

        bar2f = ttk.Frame(parent, padding=(8, 0, 8, 6))
        bar2f.pack(side="top", fill="x")
        ttk.Label(bar2f, text="Crop lines  Top").pack(side="left")
        self.crop_top = tk.IntVar(value=0)
        self._slider(bar2f, self.crop_top, 0, 60, self.render, ewidth=3).pack(
            side="left", fill="x", expand=True, padx=(2, 8))
        ttk.Label(bar2f, text="Bottom").pack(side="left")
        self.crop_bottom = tk.IntVar(value=0)
        self._slider(bar2f, self.crop_bottom, 0, 60, self.render, ewidth=3).pack(
            side="left", fill="x", expand=True, padx=(2, 0))

        bar3 = ttk.Frame(parent, padding=(8, 0, 8, 8))
        bar3.pack(side="top", fill="x")
        self.title_label = ttk.Label(bar3, text="Title:")
        self.title_label.pack(side="left")
        self.title_var = tk.StringVar(value="")
        self.title_var.trace_add("write", lambda *_: self.render())
        self.title_entry = ttk.Entry(bar3, textvariable=self.title_var)
        self.title_entry.pack(side="left", fill="x", expand=True, padx=(4, 0))

        # Preview in a real Text widget so it renders through the OS text engine
        # exactly like a browser/Steam textbox (same glyph fallback: Braille ->
        # Segoe UI Symbol). This is true WYSIWYG — what you see here is what
        # Steam shows, including any glyph-width quirks.
        frame = ttk.Frame(parent, padding=(8, 0, 8, 8))
        frame.pack(side="top", fill="both", expand=True)
        self._preview_font = tkfont.Font(family="Consolas", size=11)
        self.preview = tk.Text(frame, wrap="none", bg=STEAM_BG, fg=STEAM_FG,
                               font=self._preview_font, borderwidth=0,
                               padx=10, pady=10, insertbackground=STEAM_FG)
        yscroll = ttk.Scrollbar(frame, orient="vertical", command=self.preview.yview)
        xscroll = ttk.Scrollbar(frame, orient="horizontal", command=self.preview.xview)
        self.preview.configure(yscrollcommand=yscroll.set, xscrollcommand=xscroll.set)
        self.preview.grid(row=0, column=0, sticky="nsew")
        yscroll.grid(row=0, column=1, sticky="ns")
        xscroll.grid(row=1, column=0, sticky="ew")
        frame.rowconfigure(0, weight=1)
        frame.columnconfigure(0, weight=1)
        self.preview.bind(
            "<Shift-MouseWheel>",
            lambda e: self.preview.xview_scroll(int(-e.delta / 120), "units"))
        self.preview.insert("1.0", "Open an image…")
        self.preview.configure(state="disabled")

        self.status = ttk.Label(parent, anchor="w", padding=(10, 4))
        self.status.pack(side="bottom", fill="x")
        self.status.configure(text="No image loaded.")

    # ---- name generator tab --------------------------------------------
    def _build_namegen(self, parent):
        top = ttk.Frame(parent, padding=8)
        top.pack(side="top", fill="x")
        ttk.Label(top, text="Your name/text:").pack(side="left")
        self.name_input = tk.StringVar(value="")
        entry = ttk.Entry(top, textvariable=self.name_input)
        entry.pack(side="left", fill="x", expand=True, padx=(4, 8))
        entry.bind("<Return>", lambda _=None: self.gen_names())
        ttk.Button(top, text="Generate", command=self.gen_names).pack(side="left")
        ttk.Button(top, text="Random", command=self.random_name).pack(side="left", padx=(4, 0))

        mid = ttk.Frame(parent, padding=(8, 0, 8, 8))
        mid.pack(side="top", fill="both", expand=True)
        fancy = tkfont.Font(family="Segoe UI", size=14)
        self.name_list = tk.Listbox(mid, bg=STEAM_BG, fg=STEAM_FG, font=fancy,
                                    selectbackground=STEAM_ACCENT, borderwidth=0,
                                    activestyle="none")
        nscroll = ttk.Scrollbar(mid, orient="vertical", command=self.name_list.yview)
        self.name_list.configure(yscrollcommand=nscroll.set)
        self.name_list.pack(side="left", fill="both", expand=True)
        nscroll.pack(side="left", fill="y")
        self.name_list.bind("<Double-Button-1>", lambda _=None: self.copy_name())
        self.name_list.bind("<<ListboxSelect>>", lambda _=None: self._on_name_select())

        bottom = ttk.Frame(parent, padding=(8, 0, 8, 8))
        bottom.pack(side="bottom", fill="x")
        ttk.Button(bottom, text="Copy selected", command=self.copy_name).pack(side="left")
        self.name_status = ttk.Label(bottom, anchor="w", padding=(10, 0))
        self.name_status.pack(side="left", fill="x", expand=True)
        self.name_status.configure(
            text="Type a name and Generate, or hit Random. Double-click a result to copy.")

    # ---- converter actions ---------------------------------------------
    def choose_file(self):
        path = filedialog.askopenfilename(
            title="Choose an image",
            filetypes=[("Images", "*.png *.jpg *.jpeg *.bmp *.gif *.webp *.tiff"),
                       ("All files", "*.*")])
        if path:
            self.path = path
            self.render()

    def _on_width_change(self):
        if self.path:
            self.render()

    def _on_dest_change(self):
        profile = DESTINATIONS[self.dest_var.get()]
        self.width_var.set(profile["width"])
        if profile["force_safe"]:
            self.safe_var.set(True)
        self.limit_var.set(str(profile["byte_limit"]) if profile["byte_limit"] else "")
        state = "normal" if profile["title"] else "disabled"
        self.title_entry.configure(state=state)
        self.title_label.configure(text="Title:" if profile["title"] else "Title (n/a):")
        self.render()

    def _build_art(self, profile, steam_safe, width):
        """Return (wrapped, raw): wrapped has [code]/title for pasting; raw is
        just the art grid (what Steam actually displays) for the preview."""
        sig = (self.sig_var.get(), self.sig_size.get() / 100.0,
               self.sig_x.get() / 100.0, self.sig_y.get() / 100.0,
               self.sig_rot.get(), self.sig_font.get(),
               self.sig_layer.get() == "Behind", self.sig_invert.get())
        raw = convert(self.path, width, self.invert_var.get(),
                      steam_safe, self.style_var.get(),
                      self.detail_var.get() / 100.0, self.contrast_var.get(),
                      self.removebg_var.get(), self.tol_var.get() / 100.0,
                      RATIOS[self.ratio_var.get()], sig)
        # Crop whole text lines off the top/bottom (e.g. trim empty margins).
        # Clamp so over-cropping never wraps to a negative slice index (which
        # made the crop behave erratically and look un-undoable); always keep
        # at least one line.
        ct, cb = self.crop_top.get(), self.crop_bottom.get()
        if ct or cb:
            lines = raw.split("\n")
            n = len(lines)
            ct = max(0, min(ct, n - 1))
            cb = max(0, min(cb, n - 1 - ct))
            raw = "\n".join(lines[ct:n - cb])
        is_braille = STYLES[self.style_var.get()]["kind"] == "braille"
        if is_braille:
            raw = add_background(raw, self.bg_var.get())
        raw = frame_art(raw, self.frame_var.get(), is_braille)
        if self.center_var.get():
            raw = center_block(raw, width,
                               "⠀" if (steam_safe or is_braille) else " ")
        art = raw
        if profile["code"]:
            art = "[code]\n" + art + "\n[/code]"
        title = self.title_var.get().strip()
        if title and profile["title"]:
            heading = f"[h1]{title}[/h1]\n" if profile["code"] else f"{title}\n"
            art = heading + art
        return art, raw

    def _parse_limit(self):
        try:
            return max(0, int(self.limit_var.get().strip()))
        except (ValueError, AttributeError):
            return 0

    def render(self):
        if not self.path:
            return
        profile = DESTINATIONS[self.dest_var.get()]
        steam_safe = self.safe_var.get() or profile["force_safe"]
        desired = self.width_var.get()
        limit = self._parse_limit()

        try:
            if self.autofit_var.get() and limit:
                art, raw, used_w, fitted = self._autofit(profile, steam_safe, desired, limit)
            else:
                art, raw = self._build_art(profile, steam_safe, desired)
                used_w, fitted = desired, False
        except Exception as exc:  # noqa: BLE001 - surface load/convert errors
            messagebox.showerror("Conversion failed", str(exc))
            return

        self.last_art = art
        self._show_preview(raw)

        lines = art.count("\n") + 1
        bytes_ = steam_byte_len(art)
        info = f"{lines} lines  |  {bytes_} Steam bytes"
        if fitted:
            info += f"  |  auto-fit width {used_w} (under {limit}-byte limit)"
        elif limit and bytes_ >= limit:
            info = (f"⚠ {bytes_} bytes is over the {limit}-byte limit. "
                    f"Enable Auto-fit or lower the width.")
        else:
            info += f"  |  {profile['note']}"
        self.status.configure(text=info)

    def _autofit(self, profile, steam_safe, desired, limit):
        """Largest width whose output stays strictly under the byte limit.
        Steam requires '< limit', so we target limit-1 and measure with CRLF."""
        target = limit - 1
        lo, hi = 4, max(4, desired)
        best = None
        while lo <= hi:
            mid = (lo + hi) // 2
            art, raw = self._build_art(profile, steam_safe, mid)
            if steam_byte_len(art) <= target:
                best = (art, raw, mid)
                lo = mid + 1
            else:
                hi = mid - 1
        if best is None:  # even the minimum width overflows
            art, raw = self._build_art(profile, steam_safe, 4)
            return art, raw, 4, False
        art, raw, used_w = best
        return art, raw, used_w, used_w < desired

    def _show_preview(self, raw):
        """Show the art in the Text widget via the OS text engine — same glyph
        rendering/fallback Steam uses, so it's true WYSIWYG. Braille -> Segoe UI
        Symbol (Steam's fallback); Block/ASCII -> Consolas (Steam's [code])."""
        family = ("Segoe UI Symbol"
                  if STYLES[self.style_var.get()]["kind"] == "braille"
                  else "Consolas")
        self._preview_font.configure(family=family)
        self.preview.configure(state="normal")
        self.preview.delete("1.0", "end")
        self.preview.insert("1.0", raw if (raw and raw.strip()) else "(no preview)")
        self.preview.configure(state="disabled")

    def copy(self):
        if not self.last_art:
            return
        self.root.clipboard_clear()
        self.root.clipboard_append(self.last_art)
        self.status.configure(text="Copied to clipboard. Paste into Steam.")

    # ---- name actions ---------------------------------------------------
    def gen_names(self):
        self.name_variants = generate_names(self.name_input.get())
        if not self.name_input.get().strip():
            # Random was effectively used; show the base that was picked.
            self.name_input.set(self.name_variants[0][1])
        self.name_list.delete(0, "end")
        for _label, styled in self.name_variants:
            self.name_list.insert("end", styled)
        self.name_status.configure(
            text=f"{len(self.name_variants)} variants. Select one to see its byte cost.")

    def random_name(self):
        self.name_input.set(random_base_name())
        self.gen_names()

    def _on_name_select(self):
        sel = self.name_list.curselection()
        if not sel:
            return
        styled = self.name_variants[sel[0]][1]
        bytes_ = len(styled.encode("utf-8"))
        warn = "  ⚠ likely too long for a Steam name (~32 char display limit)" if len(styled) > 32 else ""
        self.name_status.configure(
            text=f"{len(styled)} chars / {bytes_} bytes{warn}")

    def copy_name(self):
        sel = self.name_list.curselection()
        if not sel:
            return
        styled = self.name_variants[sel[0]][1]
        self.root.clipboard_clear()
        self.root.clipboard_append(styled)
        self.name_status.configure(text=f"Copied: {styled}")

    # ---- decorations tab -----------------------------------------------
    def _build_decorations(self, parent):
        top = ttk.Frame(parent, padding=8)
        top.pack(side="top", fill="x")
        ttk.Label(top, text="Category:").pack(side="left")
        self.decor_cat = tk.StringVar(value=DEFAULT_DECOR_CATEGORY)
        cat = ttk.Combobox(top, textvariable=self.decor_cat, width=20,
                           state="readonly", values=list(DECORATIONS))
        cat.pack(side="left", padx=(4, 16))
        cat.bind("<<ComboboxSelected>>", lambda _=None: self._decor_fill())
        ttk.Button(top, text="Copy", command=self.decor_copy).pack(side="right")

        ttk.Label(parent, padding=(8, 0), wraplength=900, justify="left",
                  text="Copy-paste decorations for a Custom Info Box or profile "
                       "summary — no [code] needed. Multi-line pieces use U+2800 "
                       "blanks so Steam keeps them aligned. Replace TITLE / TEXT "
                       "after pasting. Double-click an item to copy it.").pack(
            side="top", fill="x")

        body = ttk.Frame(parent, padding=8)
        body.pack(side="top", fill="both", expand=True)
        self.decor_list = tk.Listbox(body, height=12, exportselection=False,
                                     font=tkfont.Font(family=self.mono_family,
                                                      size=11))
        self.decor_list.pack(side="left", fill="both", expand=True)
        ds = ttk.Scrollbar(body, orient="vertical",
                           command=self.decor_list.yview)
        ds.pack(side="left", fill="y")
        self.decor_list.configure(yscrollcommand=ds.set)
        self.decor_list.bind("<Double-Button-1>", lambda _=None: self.decor_copy())
        self.decor_list.bind("<<ListboxSelect>>", lambda _=None: self._decor_show())

        prev = ttk.Frame(parent, padding=(8, 0, 8, 8))
        prev.pack(side="top", fill="x")
        self.decor_preview = tk.Text(prev, height=4, wrap="none", bg=STEAM_BG,
                                     fg=STEAM_FG, borderwidth=0, padx=10, pady=6,
                                     font=tkfont.Font(
                                         family="Segoe UI Symbol", size=13))
        self.decor_preview.pack(side="top", fill="x")
        self.decor_status = ttk.Label(parent, anchor="w", padding=(10, 4))
        self.decor_status.pack(side="bottom", fill="x")
        self._decor_fill()

    def _decor_fill(self):
        self.decor_list.delete(0, "end")
        for label, _ in DECORATIONS[self.decor_cat.get()]:
            self.decor_list.insert("end", label)
        self.decor_list.selection_set(0)
        self._decor_show()

    def _decor_show(self):
        items = DECORATIONS[self.decor_cat.get()]
        sel = self.decor_list.curselection()
        if not sel:
            return
        snippet = items[sel[0]][1]
        self.decor_preview.configure(state="normal")
        self.decor_preview.delete("1.0", "end")
        self.decor_preview.insert("1.0", snippet)
        self.decor_preview.configure(state="disabled")

    def decor_copy(self):
        items = DECORATIONS[self.decor_cat.get()]
        sel = self.decor_list.curselection()
        if not sel:
            return
        label, snippet = items[sel[0]]
        self.root.clipboard_clear()
        self.root.clipboard_append(snippet)
        self.decor_status.configure(text=f"Copied '{label}' to clipboard.")

    # ---- banner slicer tab ---------------------------------------------
    def _build_banner(self, parent):
        top = ttk.Frame(parent, padding=8)
        top.pack(side="top", fill="x")
        ttk.Button(top, text="Open image / GIF…",
                   command=self.banner_choose).pack(side="left")
        ttk.Label(top, text="Mode:").pack(side="left", padx=(16, 4))
        self.banner_mode = tk.StringVar(value="Equal slots")
        mode_box = ttk.Combobox(top, textvariable=self.banner_mode, width=20,
                                state="readonly",
                                values=["Equal slots", "Background (Main+Side)"])
        mode_box.pack(side="left")
        mode_box.bind("<<ComboboxSelected>>", lambda _=None: self._banner_mode_change())
        self.banner_slot_lbl = ttk.Label(top, text="Slots:")
        self.banner_slot_lbl.pack(side="left", padx=(16, 4))
        self.banner_slots = tk.IntVar(value=5)
        self.banner_slot_spin = ttk.Spinbox(top, from_=2, to=10, width=4,
                                            textvariable=self.banner_slots,
                                            command=self.banner_preview)
        self.banner_slot_spin.pack(side="left")
        self.banner_bgratio = tk.StringVar(value=DEFAULT_BACKGROUND_RATIO)
        self.banner_bg_box = ttk.Combobox(top, textvariable=self.banner_bgratio,
                                         width=18, state="readonly",
                                         values=list(BACKGROUND_RATIOS))
        self.banner_bg_box.bind("<<ComboboxSelected>>",
                                lambda _=None: self.banner_preview())
        self.banner_patch = tk.BooleanVar(value=False)
        ttk.Checkbutton(top, text="Long-image patch (0x21)",
                        variable=self.banner_patch).pack(side="left", padx=(16, 0))
        ttk.Button(top, text="Slice & save…",
                   command=self.banner_save).pack(side="left", padx=(16, 0))

        row2 = ttk.Frame(parent, padding=(8, 0, 8, 4))
        row2.pack(side="top", fill="x")
        ttk.Label(row2, text="Edge fade:").pack(side="left")
        self.banner_edge = tk.IntVar(value=0)
        self._slider(row2, self.banner_edge, 0, 100, self.banner_preview).pack(
            side="left", fill="x", expand=True, padx=(4, 12))
        ttk.Label(row2, text="Color filter:").pack(side="left")
        self.banner_color = (220, 20, 20)            # default red, off until >0%
        self.banner_color_btn = tk.Button(row2, text="  ", width=3,
                                          bg="#dc1414", relief="groove",
                                          command=self._banner_pick_color)
        self.banner_color_btn.pack(side="left", padx=(4, 4))
        self.banner_tint = tk.IntVar(value=0)
        self._slider(row2, self.banner_tint, 0, 100, self.banner_preview).pack(
            side="left", fill="x", expand=True, padx=(0, 0))

        ttk.Label(parent, padding=(8, 0), wraplength=900, justify="left",
                  text="Equal slots: cut a wide image into N vertical tiles for "
                       "a seamless Artwork Showcase banner. Background (Main+Side): "
                       "cut a tall image into a wide Main tile + narrow Side tile "
                       "for the full-profile background trick. Animated GIFs slice "
                       "frame-by-frame; tick the long-image patch to upload "
                       "directly.").pack(side="top", fill="x")

        self.banner_canvas = tk.Label(parent, bg="#000000")  # black = shows blend
        self.banner_canvas.pack(side="top", fill="both", expand=True,
                                padx=8, pady=8)
        self.banner_status = ttk.Label(parent, anchor="w", padding=(10, 4))
        self.banner_status.pack(side="bottom", fill="x")
        self.banner_status.configure(text="Open a wide image to begin.")
        self.banner_path = None
        self._banner_preview_img = None

    def banner_choose(self):
        path = filedialog.askopenfilename(
            title="Choose a wide image or GIF",
            filetypes=[("Images & GIFs",
                        "*.png *.jpg *.jpeg *.bmp *.webp *.gif *.apng"),
                       ("All files", "*.*")])
        if path:
            self.banner_path = path
            self.banner_preview()

    def _banner_pick_color(self):
        rgb, hx = colorchooser.askcolor(
            color="#%02x%02x%02x" % self.banner_color,
            title="Choose color filter")
        if rgb:
            self.banner_color = tuple(int(c) for c in rgb)
            self.banner_color_btn.configure(bg=hx)
            self.banner_preview()

    def _banner_mode_change(self):
        background = self.banner_mode.get().startswith("Background")
        if background:
            self.banner_slot_lbl.configure(text="Ratio:")
            self.banner_slot_spin.pack_forget()
            self.banner_bg_box.pack(side="left", after=self.banner_slot_lbl)
        else:
            self.banner_bg_box.pack_forget()
            self.banner_slot_lbl.configure(text="Slots:")
            self.banner_slot_spin.pack(side="left", after=self.banner_slot_lbl)
        self.banner_preview()

    def banner_preview(self):
        if not self.banner_path:
            return
        src = Image.open(self.banner_path)
        animated = getattr(src, "n_frames", 1) > 1
        img = ImageOps.exif_transpose(src).convert("RGB")
        background = self.banner_mode.get().startswith("Background")
        # Scale to fit the preview area while keeping aspect.
        max_w = max(400, self.banner_canvas.winfo_width() - 20)
        scale = min(1.0, max_w / img.width)
        disp = img.resize((max(1, int(img.width * scale)),
                           max(1, int(img.height * scale))))
        tint = self.banner_tint.get() / 100.0
        if tint > 0:  # show the colour grade in the preview
            disp = apply_color_filter(disp, self.banner_color, tint)
        ef = self.banner_edge.get() / 100.0
        if ef > 0:  # show the fade-to-black blend in the preview (WYSIWYG)
            disp = _vignette(disp, _edge_mask(disp.size, ef), (0, 0, 0))
        draw = ImageDraw.Draw(disp)
        kind = "animated GIFs" if animated else "PNGs"
        frames = f", {src.n_frames} frames each" if animated else ""
        if background:
            frac = BACKGROUND_RATIOS[self.banner_bgratio.get()]
            x = int(disp.width * frac)
            draw.line((x, 0, x, disp.height), fill=(102, 192, 244), width=2)
            mw = int(img.width * frac)
            self.banner_status.configure(
                text=f"Main {mw}x{img.height}px + Side {img.width - mw}x"
                     f"{img.height}px{frames}. Saves 2 {kind} "
                     f"(_bg_main, _bg_side).")
        else:
            slots = self.banner_slots.get()
            for i in range(1, slots):
                x = disp.width * i // slots
                draw.line((x, 0, x, disp.height), fill=(102, 192, 244), width=2)
            self.banner_status.configure(
                text=f"{slots} tiles, each ~{img.width // slots}x{img.height}px"
                     f"{frames}. Click 'Slice & save' to export {kind}.")
        self._banner_preview_img = self._to_tk(disp)
        self.banner_canvas.configure(image=self._banner_preview_img)

    def banner_save(self):
        if not self.banner_path:
            return
        out_dir = filedialog.askdirectory(title="Choose output folder")
        if not out_dir:
            return
        patch = self.banner_patch.get()
        ef = self.banner_edge.get() / 100.0
        tint = self.banner_tint.get() / 100.0
        col = self.banner_color
        if self.banner_mode.get().startswith("Background"):
            frac = BACKGROUND_RATIOS[self.banner_bgratio.get()]
            paths = slice_background(self.banner_path, out_dir, frac, patch, ef,
                                     col, tint)
        else:
            paths = slice_banner(self.banner_path, self.banner_slots.get(),
                                 out_dir, ef, col, tint)
            if patch:
                for p in paths:
                    patch_long_image(p)
        patched = " (long-image patched — upload directly)" if patch else ""
        self.banner_status.configure(
            text=f"Saved {len(paths)} tiles to {out_dir} "
                 f"({os.path.basename(paths[0])} … {os.path.basename(paths[-1])})"
                 f"{patched}.")

    # ---- progress bars tab ---------------------------------------------
    def _build_progress(self, parent):
        top = ttk.Frame(parent, padding=8)
        top.pack(side="top", fill="x")
        ttk.Label(top, text="Style:").pack(side="left")
        self.bar_style = tk.StringVar(value=DEFAULT_BAR_STYLE)
        ttk.Combobox(top, textvariable=self.bar_style, width=14, state="readonly",
                     values=list(BAR_STYLES)).pack(side="left", padx=(4, 16))
        self.bar_style.trace_add("write", lambda *_: self.progress_render())
        ttk.Label(top, text="Length:").pack(side="left")
        self.bar_cells = tk.IntVar(value=12)
        self._slider(top, self.bar_cells, 4, 30, self.progress_render,
                     ewidth=3).pack(side="left", fill="x", expand=True, padx=4)
        self.bar_pct_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(top, text="Show %", variable=self.bar_pct_var,
                        command=self.progress_render).pack(side="left", padx=4)
        ttk.Button(top, text="Copy", command=self.progress_copy).pack(side="right")

        ttk.Label(parent, padding=(8, 0), justify="left",
                  text="One bar per line as  Label:percent  (e.g.  Level:75)").pack(
            side="top", fill="x")
        mid = ttk.Frame(parent, padding=8)
        mid.pack(side="top", fill="both", expand=True)
        mono = tkfont.Font(family=self.mono_family, size=12)
        self.bar_input = tk.Text(mid, height=8, wrap="none", font=mono,
                                 bg="#2a3f5a", fg=STEAM_FG, insertbackground=STEAM_FG)
        self.bar_input.pack(side="top", fill="x")
        self.bar_input.insert("1.0", "Gaming:90\nSleep:30\nMotivation:60\nBattery:75")
        self.bar_input.bind("<KeyRelease>", lambda _=None: self.progress_render())
        self.bar_output = tk.Text(mid, wrap="none", font=mono, bg=STEAM_BG,
                                  fg=STEAM_FG, state="disabled")
        self.bar_output.pack(side="top", fill="both", expand=True, pady=(8, 0))

        self.bar_status = ttk.Label(parent, anchor="w", padding=(10, 4))
        self.bar_status.pack(side="bottom", fill="x")
        self._last_bars = ""
        self.progress_render()

    def progress_render(self):
        text = self.bar_input.get("1.0", "end")
        out = progress_block(text, self.bar_cells.get(), self.bar_style.get(),
                             self.bar_pct_var.get())
        self._last_bars = out
        self.bar_output.configure(state="normal")
        self.bar_output.delete("1.0", "end")
        self.bar_output.insert("1.0", out)
        self.bar_output.configure(state="disabled")
        self.bar_status.configure(
            text=f"{steam_byte_len(out)} Steam bytes  |  paste into chat, "
                 f"comment, or [code] info box.")

    def progress_copy(self):
        if self._last_bars:
            self.root.clipboard_clear()
            self.root.clipboard_append(self._last_bars)
            self.bar_status.configure(text="Copied progress bars to clipboard.")

    # ---- animated GIF tab ----------------------------------------------
    def _build_gif(self, parent):
        top = ttk.Frame(parent, padding=8)
        top.pack(side="top", fill="x")
        ttk.Button(top, text="Open GIF…", command=self.gif_choose).pack(side="left")
        ttk.Label(top, text="Width:").pack(side="left", padx=(16, 4))
        self.gif_width = tk.IntVar(value=60)
        self._slider(top, self.gif_width, 20, 120, self._gif_schedule).pack(
            side="left", fill="x", expand=True, padx=(0, 12))
        self.gif_invert = tk.BooleanVar(value=False)
        ttk.Checkbutton(top, text="Invert", variable=self.gif_invert,
                        command=self._gif_schedule).pack(side="left")
        self.gif_removebg = tk.BooleanVar(value=False)
        ttk.Checkbutton(top, text="Remove bg", variable=self.gif_removebg,
                        command=self._gif_schedule).pack(side="left", padx=4)
        ttk.Label(top, text="Mode:").pack(side="left", padx=(12, 4))
        self.gif_mode = tk.StringVar(value="Braille")
        mode_box = ttk.Combobox(top, textvariable=self.gif_mode, width=9,
                                state="readonly",
                                values=["Braille", "Original", "Morph"])
        mode_box.pack(side="left")
        mode_box.bind("<<ComboboxSelected>>", lambda _=None: self.gif_preview())
        ttk.Button(top, text="Export GIF…",
                   command=self.gif_export).pack(side="right")

        topc = ttk.Frame(parent, padding=(8, 0, 8, 0))
        topc.pack(side="top", fill="x")
        ttk.Label(topc, text="Speed (morph=transition):").pack(side="left")
        self.gif_speed = tk.IntVar(value=100)
        self._slider(topc, self.gif_speed, 25, 300, self._gif_schedule).pack(
            side="left", fill="x", expand=True, padx=(4, 12))
        ttk.Label(topc, text="Braille hold:").pack(side="left")
        self.gif_hold = tk.IntVar(value=8)
        self._slider(topc, self.gif_hold, 0, 40, self._gif_schedule, ewidth=3).pack(
            side="left", fill="x", expand=True, padx=(4, 0))

        topd = ttk.Frame(parent, padding=(8, 0, 8, 0))
        topd.pack(side="top", fill="x")
        ttk.Label(topd, text="Smooth (denoise):").pack(side="left")
        self.gif_smooth = tk.IntVar(value=35)
        self._slider(topd, self.gif_smooth, 0, 100, self._gif_schedule).pack(
            side="left", fill="x", expand=True, padx=(4, 12))
        ttk.Label(topd, text="BG strength:").pack(side="left")
        self.gif_tol = tk.IntVar(value=12)
        self._slider(topd, self.gif_tol, 2, 60, self._gif_schedule).pack(
            side="left", fill="x", expand=True, padx=(4, 0))

        tope = ttk.Frame(parent, padding=(8, 0, 8, 0))
        tope.pack(side="top", fill="x")
        ttk.Label(tope, text="Edge fade (blend into background):").pack(side="left")
        self.gif_edge = tk.IntVar(value=0)
        self._slider(tope, self.gif_edge, 0, 100, self._gif_schedule).pack(
            side="left", fill="x", expand=True, padx=(4, 0))

        top2 = ttk.Frame(parent, padding=(8, 0, 8, 4))
        top2.pack(side="top", fill="x")
        self.gif_split_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(top2, text="Showcase split preview (1 big + 1 side)",
                        variable=self.gif_split_var,
                        command=self.gif_preview).pack(side="left")
        ttk.Label(top2, text="Max size:").pack(side="left", padx=(16, 4))
        self.gif_budget = tk.StringVar(value="5 MB")
        ttk.Combobox(top2, textvariable=self.gif_budget, width=6,
                     state="readonly",
                     values=["5 MB", "8 MB", "10 MB", "15 MB"]).pack(side="left")
        ttk.Button(top2, text="Export showcase tiles…",
                   command=self.gif_export_showcase).pack(side="right")

        ttk.Label(parent, padding=(8, 0), wraplength=920, justify="left",
                  text="Mode: Braille = dot art, Original = real frames, Morph = "
                       "fades original↔braille as it plays (frame 1..n). Speed "
                       "sets playback rate. 'Max size' caps the exported GIF "
                       "(it auto-scales to fit). 'Export GIF' saves the previewed "
                       "mode; 'Export showcase tiles' splits into a wide middle + "
                       "narrow side (~506:100) for the long-image trick.").pack(
                           side="top", fill="x")
        self.gif_canvas = tk.Label(parent, bg=STEAM_BG)
        self.gif_canvas.pack(side="top", fill="both", expand=True, padx=8, pady=8)
        self.gif_status = ttk.Label(parent, anchor="w", padding=(10, 8))
        self.gif_status.pack(side="bottom", fill="x")
        self.gif_status.configure(text="Open an animated GIF to begin.")
        self.gif_path = None
        self._gif_pending = None   # debounce timer id
        self._gif_anim = None      # animation timer id
        self._gif_photos = []
        self._gif_durs = []
        self._gif_idx = 0

    def _gif_schedule(self):
        """Debounce preview regeneration so slider drags don't lag."""
        if self._gif_pending:
            self.root.after_cancel(self._gif_pending)
        self._gif_pending = self.root.after(350, self.gif_preview)

    def _gif_mode_frames(self, mode, max_frames=40):
        """(frames, durations) for the selected mode, applying current settings.
        Durations are scaled by the Speed slider (higher % = faster)."""
        w, inv = self.gif_width.get(), self.gif_invert.get()
        rmbg, tol = self.gif_removebg.get(), self.gif_tol.get() / 100.0
        sm, ef = self.gif_smooth.get() / 100.0, self.gif_edge.get() / 100.0
        speed = max(25, self.gif_speed.get())
        if mode == "Morph":
            # Speed = transition speed only: it sets how long EACH fade frame
            # shows (higher % = shorter = faster morph). The fade keeps a fixed,
            # smooth frame count and the braille/original holds stay at base_ms,
            # so the rest of the playback rate is unaffected.
            fade_ms = max(20, round(80 * 100 / speed))
            return morph_frames(self.gif_path, w, inv, 0.4, True, rmbg, tol,
                                None, sm, ef, max_frames=max_frames,
                                hold=self.gif_hold.get(), fade=16,
                                base_ms=80, fade_ms=fade_ms)
        if mode == "Original":
            frames, durs = orig_gif_frames(self.gif_path, max_frames)
            if ef > 0:
                m = _edge_mask(frames[0].size, ef)
                frames = [_vignette(f, m, (0, 0, 0)) for f in frames]
        else:  # Braille
            frames, durs = braille_gif_frames(
                self.gif_path, w, inv, 0.4, True, rmbg, tol, None, max_frames,
                smooth=sm, edge_fade=ef)
        # For Braille/Original, Speed is the playback rate (scales durations).
        durs = [max(20, int(d * 100 / speed)) for d in durs]
        return frames, durs

    def gif_choose(self):
        path = filedialog.askopenfilename(
            title="Choose an animated GIF",
            filetypes=[("Animated images", "*.gif *.webp *.apng *.png"),
                       ("All files", "*.*")])
        if path:
            self.gif_path = path
            self.gif_preview()

    def gif_preview(self):
        self._gif_pending = None
        if not self.gif_path:
            return
        if self._gif_anim:
            self.root.after_cancel(self._gif_anim)
            self._gif_anim = None
        self.gif_status.configure(text="Rendering preview…")
        self.root.update_idletasks()
        mode = self.gif_mode.get()
        try:
            frames, durs = self._gif_mode_frames(mode, max_frames=40)
        except Exception as exc:  # noqa: BLE001
            self.gif_status.configure(text=f"Preview failed: {exc}")
            return
        maxw = max(400, self.gif_canvas.winfo_width() - 20)
        maxh = max(200, self.gif_canvas.winfo_height() - 20)
        scale = min(1.0, maxw / frames[0].width, maxh / frames[0].height)
        rw = max(1, int(frames[0].width * scale))
        rh = max(1, int(frames[0].height * scale))
        split = self.gif_split_var.get()
        self._gif_photos = [
            self._to_tk(self._gif_overlay(f.resize((rw, rh)), split))
            for f in frames]
        self._gif_durs = durs
        self._gif_idx = 0
        extra = "  |  blue line = big | side split" if split else ""
        self.gif_status.configure(
            text=f"{len(frames)} frames — {mode} mode.{extra} Export to save.")
        self._gif_play()

    def _gif_overlay(self, frame, split):
        """Draw the showcase-split guide line (506:100) onto a preview frame."""
        if not split:
            return frame
        frame = frame.convert("RGB")
        draw = ImageDraw.Draw(frame)
        w, h = frame.size
        bw = max(1, min(w - 1, int(round(w * SHOWCASE_BIG_FRAC))))
        draw.line((bw, 0, bw, h), fill=(102, 192, 244), width=2)  # big | side
        return frame

    def _gif_play(self):
        if not self._gif_photos:
            return
        self.gif_canvas.configure(image=self._gif_photos[self._gif_idx])
        dur = self._gif_durs[self._gif_idx] if self._gif_idx < len(self._gif_durs) else 100
        self._gif_idx = (self._gif_idx + 1) % len(self._gif_photos)
        self._gif_anim = self.root.after(max(40, dur), self._gif_play)

    def gif_export(self):
        if not self.gif_path:
            self.gif_status.configure(text="Open a GIF first.")
            return
        mode = self.gif_mode.get()
        out = filedialog.asksaveasfilename(
            title=f"Save {mode} GIF", defaultextension=".gif",
            initialfile=f"{mode.lower()}.gif", filetypes=[("GIF", "*.gif")])
        if not out:
            return
        self.gif_status.configure(text="Rendering frames…")
        self.root.update_idletasks()
        budget = int(self.gif_budget.get().split()[0]) * 1024 * 1024
        try:
            frames, durs = self._gif_mode_frames(mode, max_frames=60)
            _save_animated_gif(frames, durs, out, grayscale=(mode == "Braille"),
                               max_bytes=budget)
        except Exception as exc:  # noqa: BLE001
            import traceback
            messagebox.showerror("Export failed",
                                 f"{type(exc).__name__}: {exc}\n\n"
                                 + traceback.format_exc())
            self.gif_status.configure(text="Export failed.")
            return
        mb = os.path.getsize(out) / (1024 * 1024)
        self.gif_status.configure(
            text=f"Saved {len(frames)}-frame {mode} GIF ({mb:.2f} MB) to {out}. "
                 f"Upload it as profile artwork.")

    def gif_export_showcase(self):
        if not self.gif_path:
            self.gif_status.configure(text="Open a GIF first.")
            return
        mode = self.gif_mode.get()
        out_dir = filedialog.askdirectory(
            title="Choose a folder for the 2 showcase tiles")
        if not out_dir:
            return
        self.gif_status.configure(text="Slicing frames…")
        self.root.update_idletasks()
        try:
            frames, durs = self._gif_mode_frames(mode, max_frames=60)
            base = os.path.splitext(os.path.basename(self.gif_path))[0]
            resample = Image.NEAREST if mode == "Braille" else Image.LANCZOS
            paths = _save_showcase_tiles(frames, durs, base, out_dir,
                                         resample=resample,
                                         grayscale=(mode == "Braille"))
            n = len(frames)
        except Exception as exc:  # noqa: BLE001
            messagebox.showerror("Export failed", str(exc))
            self.gif_status.configure(text="Export failed.")
            return
        self.gif_status.configure(
            text=f"Saved {len(paths)} tiles ({n} frames each) to {out_dir}. In "
                 f"the Artwork Showcase put '…_big' in the wide middle slot and "
                 f"'…_side' in the narrow side slot.")

    # ---- terminal box tab ----------------------------------------------
    def _build_terminal(self, parent):
        top = ttk.Frame(parent, padding=8)
        top.pack(side="top", fill="x")
        ttk.Button(top, text="Open image (optional)…",
                   command=self.term_choose).pack(side="left")
        ttk.Label(top, text="Art width:").pack(side="left", padx=(16, 4))
        self.term_width = tk.IntVar(value=18)
        self._slider(top, self.term_width, 0, 40, self.term_render,
                     ewidth=3).pack(side="left", fill="x", expand=True)
        ttk.Button(top, text="Randomize", command=self.term_random).pack(side="left", padx=4)
        ttk.Button(top, text="Copy text", command=self.term_copy).pack(side="right")
        ttk.Button(top, text="Export image…",
                   command=self.term_export_image).pack(side="right", padx=(0, 6))
        self.term_color = tk.StringVar(value=DEFAULT_TERM_COLOR)
        ttk.Combobox(top, textvariable=self.term_color, width=8, state="readonly",
                     values=list(TERM_COLORS)).pack(side="right")
        ttk.Label(top, text="Image color:").pack(side="right", padx=(0, 4))

        ttk.Label(parent, padding=(8, 0), wraplength=920, justify="left",
                  text="Readout fields, one per line as  Key:Value.  'Copy text' "
                       "pastes into a Custom Info Box; 'Export image' saves a "
                       "colored PNG (green/amber/…) to upload as artwork, since "
                       "Steam can't color pasted text.").pack(side="top", fill="x")
        mid = ttk.Frame(parent, padding=8)
        mid.pack(side="top", fill="both", expand=True)
        mono = tkfont.Font(family=self.mono_family, size=11)
        self.term_fields = tk.Text(mid, height=8, wrap="none", font=mono,
                                   bg="#2a3f5a", fg=STEAM_FG, insertbackground=STEAM_FG)
        self.term_fields.pack(side="top", fill="x")
        self.term_fields.insert("1.0", TERMINAL_DEFAULT)
        self.term_fields.bind("<KeyRelease>", lambda _=None: self.term_render())
        self.term_out = tk.Text(mid, wrap="none", font=mono, bg=STEAM_BG,
                                fg=STEAM_FG, state="disabled")
        self.term_out.pack(side="top", fill="both", expand=True, pady=(8, 0))
        self.term_status = ttk.Label(parent, anchor="w", padding=(10, 4))
        self.term_status.pack(side="bottom", fill="x")
        self.term_path = None
        self._last_term = ""
        self.term_render()

    def term_choose(self):
        path = filedialog.askopenfilename(
            title="Choose an image for the logo",
            filetypes=[("Images", "*.png *.jpg *.jpeg *.bmp *.webp"),
                       ("All files", "*.*")])
        if path:
            self.term_path = path
            self.term_render()

    def term_random(self):
        self.term_fields.delete("1.0", "end")
        self.term_fields.insert("1.0", random_terminal())
        self.term_render()

    def _term_data(self):
        """Parse the field lines and (optionally) the braille logo art."""
        fields = []
        for line in self.term_fields.get("1.0", "end").splitlines():
            if ":" in line:
                k, _, v = line.partition(":")
                fields.append((k.strip(), v.strip()))
        art = ""
        w = self.term_width.get()
        if self.term_path and w > 0:
            try:
                art = image_to_braille(self.term_path, w, False, 0.4, True,
                                       True, 0.12, None)
            except Exception:  # noqa: BLE001
                art = ""
        return fields, art

    def term_render(self):
        fields, art = self._term_data()
        out = terminal_box(art, fields, code=True)
        self._last_term = out
        self.term_out.configure(state="normal")
        self.term_out.delete("1.0", "end")
        self.term_out.insert("1.0", out)
        self.term_out.configure(state="disabled")
        self.term_status.configure(
            text=f"{steam_byte_len(out)} Steam bytes (Info Box limit 8000). "
                 f"Paste into a Custom Info Box showcase.")

    def term_copy(self):
        if self._last_term:
            self.root.clipboard_clear()
            self.root.clipboard_append(self._last_term)
            self.term_status.configure(text="Copied terminal box to clipboard.")

    def term_export_image(self):
        out = filedialog.asksaveasfilename(
            title="Save terminal image", defaultextension=".png",
            initialfile="terminal.png", filetypes=[("PNG", "*.png")])
        if not out:
            return
        fields, art = self._term_data()
        color = TERM_COLORS[self.term_color.get()]
        try:
            terminal_to_image(art, fields, color).save(out)
        except Exception as exc:  # noqa: BLE001
            messagebox.showerror("Export failed", str(exc))
            return
        self.term_status.configure(
            text=f"Saved {self.term_color.get()} terminal image to {out}. "
                 f"Upload it as profile artwork.")

    # ---- profile preview tab -------------------------------------------
    def _build_profile_preview(self, parent):
        self._pp_name = "Steam User"
        self._pp_avatar = None
        self._pp_bg = None
        self._pp_main_path = None
        self._pp_side_path = None
        self._pp_photo = None

        r1 = ttk.Frame(parent, padding=(8, 8, 8, 2))
        r1.pack(side="top", fill="x")
        ttk.Label(r1, text="Profile URL:").pack(side="left")
        self.pp_url = tk.StringVar(value="")
        ttk.Entry(r1, textvariable=self.pp_url).pack(
            side="left", fill="x", expand=True, padx=(4, 6))
        ttk.Button(r1, text="Fetch (avatar/name/bg)",
                   command=self.pp_fetch).pack(side="left")
        ttk.Button(r1, text="Open real profile",
                   command=lambda: self._open_url(self.pp_url.get().strip())
                   ).pack(side="left", padx=(6, 0))

        r2 = ttk.Frame(parent, padding=(8, 0, 8, 2))
        r2.pack(side="top", fill="x")
        ttk.Button(r2, text="Main tile…",
                   command=lambda: self._pp_pick("main")).pack(side="left")
        self.pp_main_lbl = ttk.Label(r2, text="(none)", width=22, anchor="w")
        self.pp_main_lbl.pack(side="left", padx=(4, 12))
        ttk.Button(r2, text="Side tile…",
                   command=lambda: self._pp_pick("side")).pack(side="left")
        self.pp_side_lbl = ttk.Label(r2, text="(none)", width=22, anchor="w")
        self.pp_side_lbl.pack(side="left", padx=(4, 12))
        ttk.Button(r2, text="Render preview",
                   command=self.pp_render).pack(side="right")

        r3 = ttk.Frame(parent, padding=(8, 0, 8, 4))
        r3.pack(side="top", fill="x")
        ttk.Label(r3, text="Info box art:").pack(side="left", anchor="n")
        self.pp_info = tk.Text(r3, height=4, wrap="none", bg="#2a3f5a",
                               fg=STEAM_FG, insertbackground=STEAM_FG,
                               font=tkfont.Font(family="Segoe UI Symbol", size=11))
        self.pp_info.pack(side="left", fill="x", expand=True, padx=(4, 6))
        ttk.Button(r3, text="Use converter art",
                   command=self.pp_use_converter).pack(side="left", anchor="n")

        ttk.Label(parent, padding=(8, 0), wraplength=920, justify="left",
                  text="Mockup of how your generated art sits on a Steam profile. "
                       "Fetch pulls your PUBLIC avatar/name/background (no login). "
                       "Pick exported showcase tiles and paste/Use info-box art, "
                       "then Render. This is a layout preview, not the live page."
                  ).pack(side="top", fill="x")

        wrap = ttk.Frame(parent, padding=8)
        wrap.pack(side="top", fill="both", expand=True)
        self.pp_canvas = tk.Canvas(wrap, bg=STEAM_BG, highlightthickness=0)
        ppscroll = ttk.Scrollbar(wrap, orient="vertical",
                                 command=self.pp_canvas.yview)
        self.pp_canvas.configure(yscrollcommand=ppscroll.set)
        self.pp_canvas.grid(row=0, column=0, sticky="nsew")
        ppscroll.grid(row=0, column=1, sticky="ns")
        wrap.rowconfigure(0, weight=1)
        wrap.columnconfigure(0, weight=1)

        self.pp_status = ttk.Label(parent, anchor="w", padding=(10, 4))
        self.pp_status.pack(side="bottom", fill="x")
        self.pp_status.configure(
            text="Paste a profile URL and Fetch, or just pick tiles and Render.")

    def _pp_pick(self, which):
        path = filedialog.askopenfilename(
            title=f"Choose the {which} tile",
            filetypes=[("Images & GIFs", "*.png *.gif *.jpg *.jpeg *.webp *.bmp"),
                       ("All files", "*.*")])
        if not path:
            return
        if which == "main":
            self._pp_main_path = path
            self.pp_main_lbl.configure(text=os.path.basename(path))
        else:
            self._pp_side_path = path
            self.pp_side_lbl.configure(text=os.path.basename(path))

    def pp_use_converter(self):
        art = (self.last_art or "").replace("[code]\n", "").replace("\n[/code]", "")
        self.pp_info.delete("1.0", "end")
        self.pp_info.insert("1.0", art)
        self.pp_status.configure(text="Loaded the latest converter art into the info box.")

    def pp_fetch(self):
        self.pp_status.configure(text="Fetching public profile data…")
        self.root.update_idletasks()
        try:
            data = fetch_profile(self.pp_url.get())
        except Exception as exc:  # noqa: BLE001 - surface network/parse errors
            self.pp_status.configure(text=f"Fetch failed: {exc}")
            return
        self._pp_name = data["name"]
        self._pp_avatar = data["avatar"]
        self._pp_bg = data["background"]
        bg = "background ✓" if self._pp_bg is not None else "no static background"
        self.pp_status.configure(
            text=f"Fetched '{self._pp_name}' ({bg}). Pick tiles / info box and Render.")
        self.pp_render()

    def pp_render(self):
        main_img = side_img = None
        try:
            if self._pp_main_path:
                main_img = Image.open(self._pp_main_path)
            if self._pp_side_path:
                side_img = Image.open(self._pp_side_path)
            mock = render_profile_mock(
                self._pp_name, self._pp_avatar, self._pp_bg,
                main_img, side_img, self.pp_info.get("1.0", "end").rstrip("\n"))
        except Exception as exc:  # noqa: BLE001
            self.pp_status.configure(text=f"Render failed: {exc}")
            return
        self._pp_photo = self._to_tk(mock)
        self.pp_canvas.delete("all")
        self.pp_canvas.create_image(0, 0, anchor="nw", image=self._pp_photo)
        self.pp_canvas.configure(scrollregion=(0, 0, mock.width, mock.height))
        self.pp_status.configure(
            text=f"Rendered mockup ({mock.width}x{mock.height}). Scroll to see it all.")

    # ---- how-to-upload guide tab ---------------------------------------
    def _build_guide(self, parent):
        # Quick-open buttons: jump straight to the right Steam page in a browser.
        links = ttk.Frame(parent, padding=(10, 8, 10, 4))
        links.pack(side="top", fill="x")
        ttk.Label(links, text="Open in browser:").pack(side="left", padx=(0, 6))
        for label, url in GUIDE_LINKS:
            ttk.Button(links, text=label, width=16,
                       command=lambda u=url: self._open_url(u)).pack(
                side="left", padx=2)

        frame = ttk.Frame(parent, padding=(8, 4, 8, 0))
        frame.pack(side="top", fill="both", expand=True)
        body = tkfont.Font(family="Segoe UI", size=11)
        head = tkfont.Font(family="Segoe UI", size=13, weight="bold")
        code = tkfont.Font(family=self.mono_family, size=10)
        text = tk.Text(frame, wrap="word", bg=STEAM_BG, fg=STEAM_FG,
                       font=body, borderwidth=0, padx=16, pady=12,
                       cursor="arrow", spacing1=2, spacing3=4)
        self.guide_text = text
        yscroll = ttk.Scrollbar(frame, orient="vertical", command=text.yview)
        text.configure(yscrollcommand=yscroll.set)
        text.grid(row=0, column=0, sticky="nsew")
        yscroll.grid(row=0, column=1, sticky="ns")
        frame.rowconfigure(0, weight=1)
        frame.columnconfigure(0, weight=1)

        text.tag_configure("h", font=head, foreground=STEAM_ACCENT,
                           spacing1=14, spacing3=6)
        text.tag_configure("link", font=body, foreground=STEAM_ACCENT,
                           underline=True)
        self._guide_link_n = 0
        # One clickable, click-to-copy line per console command.
        for tag, cmd in GUIDE_CMD_TOKENS.values():
            text.tag_configure(tag, font=code, foreground="#a4d977",
                               background="#0e1620", lmargin1=24, lmargin2=24,
                               spacing1=6, spacing3=6)
            text.tag_bind(tag, "<Button-1>",
                          lambda _=None, c=cmd: self._guide_copy_cmd(c))
            text.tag_bind(tag, "<Enter>",
                          lambda _=None: text.configure(cursor="hand2"))
            text.tag_bind(tag, "<Leave>",
                          lambda _=None: text.configure(cursor="arrow"))

        text.insert("end", "Getting your art onto Steam\n", "h")
        for heading, paragraph in GUIDE_SECTIONS:
            text.insert("end", heading + "\n", "h")
            self._insert_guide_body(text, paragraph)
            text.insert("end", "\n")
        text.configure(state="disabled")  # read-only, still scroll/selectable

        self.guide_status = ttk.Label(parent, anchor="w", padding=(18, 4))
        self.guide_status.pack(side="bottom", fill="x")
        self.guide_status.configure(
            text="Tip: click a blue link to open it, or a green command to copy it.")

    def _insert_guide_body(self, text, paragraph):
        """Insert body text, rendering {cmd_*} commands as click-to-copy lines
        and {{label|url}} as clickable links."""
        i = 0
        while i < len(paragraph):
            cmd_tok, cmd_pos = None, len(paragraph)
            for cand in GUIDE_CMD_TOKENS:
                p = paragraph.find(cand, i)
                if p != -1 and p < cmd_pos:
                    cmd_tok, cmd_pos = cand, p
            link = GUIDE_LINK_RE.search(paragraph, i)
            link_pos = link.start() if link else len(paragraph)

            if cmd_tok is None and link is None:
                text.insert("end", paragraph[i:])
                return
            if link_pos < cmd_pos:  # render a link first
                text.insert("end", paragraph[i:link_pos])
                self._insert_guide_link(text, link.group(1), link.group(2))
                i = link.end()
            else:  # render a command line first
                text.insert("end", paragraph[i:cmd_pos])
                tag, cmd = GUIDE_CMD_TOKENS[cmd_tok]
                text.insert("end", cmd, tag)
                i = cmd_pos + len(cmd_tok)

    def _insert_guide_link(self, text, label, url):
        tag = f"link{self._guide_link_n}"
        self._guide_link_n += 1
        text.tag_configure(tag, foreground=STEAM_ACCENT, underline=True)
        text.tag_bind(tag, "<Button-1>", lambda _=None, u=url: self._open_url(u))
        text.tag_bind(tag, "<Enter>", lambda _=None: text.configure(cursor="hand2"))
        text.tag_bind(tag, "<Leave>", lambda _=None: text.configure(cursor="arrow"))
        text.insert("end", label, tag)

    def _open_url(self, url):
        webbrowser.open(url)
        self.guide_status.configure(text=f"Opened in browser: {url}")

    def _guide_copy_cmd(self, cmd):
        self.root.clipboard_clear()
        self.root.clipboard_append(cmd)
        which = "screenshot" if "file_type" in cmd else "artwork"
        self.guide_status.configure(
            text=f"Copied the {which} console command to clipboard.")

    # ---- helpers --------------------------------------------------------
    def _to_tk(self, pil_img):
        """PhotoImage from a PIL image without requiring ImageTk (PNG via PPM)."""
        from io import BytesIO
        buf = BytesIO()
        pil_img.convert("RGB").save(buf, format="png")
        return tk.PhotoImage(data=buf.getvalue())


def main():
    root = tk.Tk()
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
