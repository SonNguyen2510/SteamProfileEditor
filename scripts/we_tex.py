"""Minimal Wallpaper Engine .tex decoder (enough for rgba8888 + LZ4 mipmaps and
sprite sheets). Returns the full texture image and, if the .tex-json defines a
spritesheet sequence, the list of individual frame images."""
import os
import json
import struct
import lz4.block
from PIL import Image


def _read_cstr(b, p):
    e = b.index(0, p)
    return b[p:e].decode("ascii", "replace"), e + 1


def decode_tex(path):
    b = open(path, "rb").read()
    magic1, p = _read_cstr(b, 0)          # TEXV0005
    magic2, p = _read_cstr(b, p)          # TEXI0001

    def ri():
        nonlocal p
        v = struct.unpack_from("<i", b, p)[0]
        p += 4
        return v

    fmt, flags = ri(), ri()
    tex_w, tex_h = ri(), ri()
    img_w, img_h = ri(), ri()
    ri()                                   # unk
    cont, p = _read_cstr(b, p)            # TEXB0003
    image_count = ri()
    if cont.endswith("0003"):
        ri()                               # FreeImageFormat (unused here)
    mip_count = ri()
    # first (largest) mipmap
    mw, mh = ri(), ri()
    is_lz4 = ri()
    decomp_size = ri()
    n = ri()
    raw = b[p:p + n]
    if is_lz4:
        raw = lz4.block.decompress(raw, uncompressed_size=decomp_size)
    img = Image.frombytes("RGBA", (mw, mh), raw)
    # WE stores textures with padding to power-of-two; crop to real image size.
    img = img.crop((0, 0, img_w, img_h))
    return img


def decode_sprites(path):
    """Return list of frame images per the sidecar .tex-json spritesheet."""
    sheet = decode_tex(path)
    meta_path = path + "-json"
    if not os.path.exists(meta_path):
        return [sheet]
    meta = json.load(open(meta_path, encoding="utf-8"))
    seqs = meta.get("spritesheetsequences")
    if not seqs:
        return [sheet]
    seq = seqs[0]
    fw, fh = seq["width"], seq["height"]
    frames = int(seq["frames"])
    cols = max(1, round(sheet.width / fw))
    out = []
    for i in range(frames):
        cx, cy = i % cols, i // cols
        x0 = int(round(cx * fw))
        y0 = int(round(cy * fh))
        out.append(sheet.crop((x0, y0, int(round(x0 + fw)), int(round(y0 + fh)))))
    return out


if __name__ == "__main__":
    import sys
    src = sys.argv[1]
    frames = decode_sprites(src)
    print(f"{src}: {len(frames)} frames, frame size {frames[0].size}")
    # save a montage to eyeball
    cols = 6
    rows = (len(frames) + cols - 1) // cols
    fw, fh = frames[0].size
    montage = Image.new("RGBA", (cols * fw, rows * fh), (30, 30, 30, 255))
    for i, fr in enumerate(frames):
        montage.paste(fr, ((i % cols) * fw, (i // cols) * fh), fr)
    montage.convert("RGB").save(os.path.join(os.path.dirname(__file__),
                                             "_leaf_montage.png"))
    frames[0].convert("RGB").save(os.path.join(os.path.dirname(__file__),
                                               "_leaf0.png"))
    print("saved _leaf_montage.png and _leaf0.png")
