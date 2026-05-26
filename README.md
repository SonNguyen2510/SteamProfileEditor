# ASCII Steam Art Studio

A Windows desktop app (tkinter) for making **Steam-profile-compatible art**: it
converts images into ASCII / Unicode-braille art, slices banners and showcase
backgrounds, builds animated GIFs, generates fancy names, and more — all sized
to Steam's real byte limits and rendered the way Steam actually displays them.

## Features

- **Image → ASCII / Braille** — multiple styles, dithering, auto-contrast,
  background removal, output-ratio control, and per-destination byte limits
  (Chat, Comment, Custom Info Box, Review, etc.) with auto-fit so output never
  exceeds the cap. A live preview uses the same font Steam falls back to
  (Segoe UI Symbol), so it's true WYSIWYG.
- **Banner Slicer** — cut a wide image into equal tiles for an Artwork
  Showcase, or split a tall image into a Main + Side profile background. Edge
  fade-to-black, color-grade filter, native-resolution animated-GIF tiles, and
  the long-image upload patch. Tiles are cut to identical dimensions so they
  never drift a pixel against their neighbours.
- **Animated GIF** — braille, original, or a morph that fades between them,
  with a configurable size budget and showcase-split export.
- **Decorations** — copy-paste Unicode dividers, headers, borders, bullets, and
  kaomoji for Info Boxes.
- **Profile Preview** — composites your generated tiles / info-box art onto a
  Steam-style mockup, optionally pulling your public avatar/name/background
  (read-only, no login).
- **Name Generator**, **Progress Bars**, **Terminal Box**, and an in-app
  **How to Upload** guide.

## Run from source

```bash
pip install pillow
python ascii_steam.py
```

## Build the standalone .exe

```bash
pip install pyinstaller
python -m PyInstaller ASCIISteamArt.spec --noconfirm
# output: dist/ASCIISteamArt.exe
```

The bundled `assets/CascadiaMono.ttf` provides braille glyphs so the art renders
correctly even on systems without a braille-capable monospace font.

## Wallpaper Engine helper scripts (`scripts/`)

`scripts/we_tex.py` decodes Wallpaper Engine `.tex` textures (LZ4 / RGBA8888 +
sprite sheets) and `scripts/render_wallpaper.py` reproduces a WE "scene" wallpaper
(static background + procedural falling-leaves and bokeh particles) as a
seamless animated GIF, with an interactive crop window.

> These scripts operate on Wallpaper Engine assets and a workshop item that are
> **not** included in this repository (they are third-party copyrighted
> content). You must supply your own, and update the asset paths at the top of
> the scripts to point at your local Wallpaper Engine install.

## Notes

- "Steam bytes" are counted as UTF-8 with CRLF line breaks; braille/block glyphs
  are 3 bytes each.
- Long/oversized artwork uploads use a documented community trick (overwriting
  the file's final byte) to bypass Steam's dimension/size checks.

## License

See [LICENSE](LICENSE).
