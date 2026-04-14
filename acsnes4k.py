#!/usr/bin/env python3
"""
AC's SNES Emu 0.2 — Vibe Mode 🐱🔥
GUI: Tkinter (ZMZ/ZSNES inspired)
Core: mewsnes 0.2 (Cython Pre-baked / Pure Python Tile Viewer Fallback)

Honest ROM Tile Viewer + Graphics Explorer.
- Real SNES 2bpp/4bpp/8bpp planar decoding
- Palette cycling, offset jumping, export to PPM
- Scroll with keys, wheel, PgUp/PgDn
"""

import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog
import os
import time

# ---------------------------------------------------------------------------
# Core import (Cython preferred, Python fallback)
# ---------------------------------------------------------------------------
try:
    import mewsnes
    CoreClass = mewsnes.MeWSNESCore
    CORE_TYPE = "mewsnes 0.2 [Cython Pre-baked Native]"
except ImportError:
    CORE_TYPE = "mewsnes 0.2 [Python Graphics Viewer Fallback]"

    # ------- Palettes (16 colors each; 8bpp will tile these 16x) -------
    PALETTES = {
        "Greyscale": [(i * 17, i * 17, i * 17) for i in range(16)],
        "SNES Default": [
            (0, 0, 0), (0, 0, 85), (0, 85, 0), (0, 85, 85),
            (85, 0, 0), (85, 0, 85), (85, 85, 0), (170, 170, 170),
            (85, 85, 85), (0, 0, 255), (0, 255, 0), (0, 255, 255),
            (255, 0, 0), (255, 0, 255), (255, 255, 0), (255, 255, 255),
        ],
        "NES-ish": [
            (0, 0, 0), (60, 60, 60), (120, 120, 120), (200, 200, 200),
            (20, 40, 120), (60, 90, 200), (120, 160, 255), (200, 220, 255),
            (120, 20, 20), (200, 60, 60), (255, 120, 120), (255, 200, 200),
            (40, 120, 40), (90, 200, 90), (160, 255, 160), (240, 255, 240),
        ],
        "Neon Cat": [
            (0, 0, 0), (10, 10, 20), (20, 5, 40), (40, 0, 80),
            (74, 163, 255), (120, 200, 255), (0, 220, 255), (0, 255, 200),
            (255, 0, 170), (255, 80, 200), (255, 160, 220), (255, 220, 240),
            (255, 255, 100), (180, 255, 60), (80, 255, 120), (255, 255, 255),
        ],
    }

    class MeWSNESCore:
        """Pure Python fallback — an honest SNES graphics explorer."""

        def __init__(self):
            self.memory = bytearray(0x20000)   # 128KB Work RAM (stub)
            self.vram = bytearray(0x10000)     # 64KB VRAM (stub)
            self.rom = bytearray()
            self.rom_info = {}
            self.running = False
            self.cycles = 0
            self.frame = 0
            self.scroll_offset = 0
            self.input_regs = [0xFF, 0xFF, 0xFF, 0xFF]

            # Tile rendering config
            self.bpp = 4                       # 2, 4, or 8
            self.palette_name = "SNES Default"
            self.palette_names = list(PALETTES.keys())

            # Framebuffer dims (SNES native)
            self.fb_w = 256
            self.fb_h = 224

            self._blank_pattern = self._generate_test_pattern()

        # ---------------- Test pattern (pre-ROM boot screen) -------------
        def _generate_test_pattern(self):
            pixels = bytearray(self.fb_w * self.fb_h * 3)
            bars = [
                (255, 255, 255), (255, 255, 0), (0, 255, 255), (0, 255, 0),
                (255, 0, 255), (255, 0, 0), (0, 0, 255), (0, 0, 0),
            ]
            idx = 0
            for y in range(self.fb_h):
                for x in range(self.fb_w):
                    if y < 160:
                        r, g, b = bars[x // 32]
                    elif y < 180:
                        r = g = b = x
                    else:
                        r = g = b = 0
                    pixels[idx] = r; pixels[idx + 1] = g; pixels[idx + 2] = b
                    idx += 3
            return pixels

        # ---------------- ROM loading + header parse ---------------------
        def load_rom(self, filepath):
            try:
                with open(filepath, "rb") as f:
                    f.seek(0, os.SEEK_END)
                    size = f.tell()
                    f.seek(0)
                    if size % 1024 == 512:
                        f.read(512)
                        self.rom = bytearray(f.read())
                    else:
                        self.rom = bytearray(f.read())

                def get_title(offset):
                    if len(self.rom) >= offset + 21:
                        raw = self.rom[offset:offset + 21]
                        return "".join(chr(b) if 32 <= b <= 126 else ' ' for b in raw).strip()
                    return ""

                title_hi = get_title(0xFFC0)
                title_lo = get_title(0x7FC0)
                score_hi = sum(1 for c in title_hi if c.isalnum())
                score_lo = sum(1 for c in title_lo if c.isalnum())

                if score_hi > score_lo and score_hi > 2:
                    title, mapping = title_hi, "HiROM"
                elif score_lo > 2:
                    title, mapping = title_lo, "LoROM"
                else:
                    title, mapping = "UNKNOWN ROM", "Unknown"

                self.rom_info = {
                    "title": title,
                    "mapping": mapping,
                    "rom_size": len(self.rom) // 1024,
                }

                # Mock RAM seed
                for i in range(min(len(self.rom), len(self.memory))):
                    self.memory[i] = self.rom[i]

                self.scroll_offset = 0
                return True
            except Exception as e:
                print(f"ROM Load Error: {e}")
                return False

        # ---------------- Controls / scroll ------------------------------
        def step(self):
            if not self.running or not self.rom:
                return
            self.cycles += 1364 * 262
            self.frame += 1

            page = 1024
            if not (self.input_regs[0] & (1 << 4)):   # UP
                self.scroll_offset = max(0, self.scroll_offset - page)
            if not (self.input_regs[0] & (1 << 5)):   # DOWN
                self.scroll_offset = min(max(0, len(self.rom) - page), self.scroll_offset + page)

        def cycle_bpp(self):
            self.bpp = {2: 4, 4: 8, 8: 2}[self.bpp]

        def cycle_palette(self):
            i = self.palette_names.index(self.palette_name)
            self.palette_name = self.palette_names[(i + 1) % len(self.palette_names)]

        def scroll_by(self, delta):
            if not self.rom:
                return
            max_off = max(0, len(self.rom) - 1024)
            self.scroll_offset = max(0, min(max_off, self.scroll_offset + delta))

        def jump_to(self, offset):
            if not self.rom:
                return
            max_off = max(0, len(self.rom) - 1024)
            self.scroll_offset = max(0, min(max_off, offset))

        # ---------------- Tile decoders ----------------------------------
        def _decode_tile_2bpp(self, rom, base, palette, pixels, px, py):
            rom_len = len(rom)
            for y in range(8):
                b1 = rom[(base + y * 2) % rom_len]
                b2 = rom[(base + y * 2 + 1) % rom_len]
                row_idx = ((py + y) * self.fb_w + px) * 3
                for x in range(8):
                    bit = 7 - x
                    c = ((b1 >> bit) & 1) | (((b2 >> bit) & 1) << 1)
                    r, g, b = palette[c]
                    i = row_idx + x * 3
                    pixels[i] = r; pixels[i + 1] = g; pixels[i + 2] = b

        def _decode_tile_4bpp(self, rom, base, palette, pixels, px, py):
            rom_len = len(rom)
            for y in range(8):
                b1 = rom[(base + y * 2) % rom_len]
                b2 = rom[(base + y * 2 + 1) % rom_len]
                b3 = rom[(base + y * 2 + 16) % rom_len]
                b4 = rom[(base + y * 2 + 17) % rom_len]
                row_idx = ((py + y) * self.fb_w + px) * 3
                for x in range(8):
                    bit = 7 - x
                    c = (((b1 >> bit) & 1)
                         | (((b2 >> bit) & 1) << 1)
                         | (((b3 >> bit) & 1) << 2)
                         | (((b4 >> bit) & 1) << 3))
                    r, g, b = palette[c]
                    i = row_idx + x * 3
                    pixels[i] = r; pixels[i + 1] = g; pixels[i + 2] = b

        def _decode_tile_8bpp(self, rom, base, palette, pixels, px, py):
            # 8bpp = 64 bytes/tile, 8 bitplanes. We mod index into 16-color palette.
            rom_len = len(rom)
            for y in range(8):
                planes = [
                    rom[(base + y * 2 + off) % rom_len]
                    for off in (0, 1, 16, 17, 32, 33, 48, 49)
                ]
                row_idx = ((py + y) * self.fb_w + px) * 3
                for x in range(8):
                    bit = 7 - x
                    c = 0
                    for p_i, pb in enumerate(planes):
                        c |= ((pb >> bit) & 1) << p_i
                    r, g, b = palette[c & 0x0F]
                    i = row_idx + x * 3
                    pixels[i] = r; pixels[i + 1] = g; pixels[i + 2] = b

        # ---------------- Framebuffer render -----------------------------
        def get_frame_buffer(self):
            if not self.rom:
                return self._blank_pattern

            pixels = bytearray(self.fb_w * self.fb_h * 3)
            palette = PALETTES[self.palette_name]
            bytes_per_tile = {2: 16, 4: 32, 8: 64}[self.bpp]
            decoder = {
                2: self._decode_tile_2bpp,
                4: self._decode_tile_4bpp,
                8: self._decode_tile_8bpp,
            }[self.bpp]

            cols = self.fb_w // 8   # 32
            rows = self.fb_h // 8   # 28

            for ty in range(rows):
                for tx in range(cols):
                    base = self.scroll_offset + (ty * cols + tx) * bytes_per_tile
                    if base >= len(self.rom):
                        continue
                    decoder(self.rom, base, palette, pixels, tx * 8, ty * 8)
            return pixels

        # ---------------- Input ------------------------------------------
        def press_key(self, player, key_idx):
            self.input_regs[player] &= ~(1 << key_idx)

        def release_key(self, player, key_idx):
            self.input_regs[player] |= (1 << key_idx)

    CoreClass = MeWSNESCore


# ---------------------------------------------------------------------------
# GUI — ZMZ/ZSNES flavored
# ---------------------------------------------------------------------------
class ACsSNESEmu(tk.Tk):
    BTN_B = 0; BTN_Y = 1; BTN_SELECT = 2; BTN_START = 3
    BTN_UP = 4; BTN_DOWN = 5; BTN_LEFT = 6; BTN_RIGHT = 7
    BTN_A = 8; BTN_X = 9; BTN_L = 10; BTN_R = 11

    KEY_MAP = {
        'z': BTN_B, 'x': BTN_A, 'a': BTN_Y, 's': BTN_X,
        'c': BTN_L, 'v': BTN_R,
        'Return': BTN_START, 'Shift_R': BTN_SELECT,
        'Up': BTN_UP, 'Down': BTN_DOWN, 'Left': BTN_LEFT, 'Right': BTN_RIGHT,
    }

    ZOOM = 3
    FB_W = 256
    FB_H = 224

    def __init__(self):
        super().__init__()
        self.title("AC's SNES Emu 0.2 — Vibe Mode")
        w = self.FB_W * self.ZOOM + 40
        h = self.FB_H * self.ZOOM + 120
        self.geometry(f"{w}x{h}")
        self.resizable(False, False)
        self.configure(bg="#000000")

        self.core = CoreClass()
        self.rom_loaded = False
        self.is_running = False
        self.fps = 0
        self.last_time = time.time()
        self.frame_count = 0

        self.img = tk.PhotoImage(width=self.FB_W, height=self.FB_H)
        self.zoomed_img = None

        self._build_gui()
        self.bind("<KeyPress>", self._key_down)
        self.bind("<KeyRelease>", self._key_up)
        self.bind("<MouseWheel>", self._on_wheel)        # Win/Mac
        self.bind("<Button-4>", lambda e: self._scroll_delta(-256))  # Linux up
        self.bind("<Button-5>", lambda e: self._scroll_delta(256))   # Linux down
        self.bind("<Prior>", lambda e: self._scroll_delta(-1024))    # PgUp
        self.bind("<Next>", lambda e: self._scroll_delta(1024))      # PgDn
        self.bind("<Shift-Prior>", lambda e: self._scroll_delta(-16384))
        self.bind("<Shift-Next>", lambda e: self._scroll_delta(16384))
        self.bind("<Home>", lambda e: self._jump_to_offset(0))
        self.bind("<End>", lambda e: self._jump_to_offset(max(0, len(self.core.rom) - 1024)))
        self.bind("<Control-g>", lambda e: self._prompt_jump())
        self.bind("<p>", lambda e: self._cycle_palette())
        self.bind("<P>", lambda e: self._cycle_palette())
        self.bind("<b>", lambda e: self._cycle_bpp())
        self.bind("<B>", lambda e: self._cycle_bpp())

    # --------------------------- GUI building -----------------------------
    def _build_gui(self):
        menubar = tk.Menu(self, bg="#0000AA", fg="#000000",
                          activebackground="#0000FF", activeforeground="#000000", relief='flat')

        file_menu = tk.Menu(menubar, tearoff=0, bg="#0000AA", fg="#000000")
        file_menu.add_command(label="Load ROM...        (Ctrl+O)", command=self._load_rom)
        file_menu.add_command(label="Export Frame (PPM)...", command=self._export_ppm)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.quit)
        menubar.add_cascade(label="File", menu=file_menu)
        self.bind("<Control-o>", lambda e: self._load_rom())

        view_menu = tk.Menu(menubar, tearoff=0, bg="#0000AA", fg="#000000")
        view_menu.add_command(label="Cycle BPP          (B)", command=self._cycle_bpp)
        view_menu.add_command(label="Cycle Palette      (P)", command=self._cycle_palette)
        view_menu.add_separator()
        view_menu.add_command(label="Jump to Offset... (Ctrl+G)", command=self._prompt_jump)
        menubar.add_cascade(label="View", menu=view_menu)

        help_menu = tk.Menu(menubar, tearoff=0, bg="#0000AA", fg="#000000")
        help_menu.add_command(label="Controls",
                              command=lambda: messagebox.showinfo(
                                  "Controls",
                                  "Scroll: Wheel / Arrows / PgUp / PgDn\n"
                                  "Shift+PgUp/PgDn: jump 16KB\n"
                                  "Home / End: start / end of ROM\n"
                                  "Ctrl+G: jump to hex offset\n"
                                  "B: cycle BPP (2/4/8)\n"
                                  "P: cycle palette\n"
                                  "Ctrl+O: load ROM"))
        menubar.add_cascade(label="Help", menu=help_menu)

        self.config(menu=menubar)

        # ---- Toolbar ----
        toolbar = tk.Frame(self, bg="#000000", height=30)
        toolbar.pack(fill='x', side='top')

        btn_style = {
            "bg": "#0000AA", "fg": "#000000",
            "font": ("Courier", 10, "bold"),
            "relief": 'raised', "bd": 2,
            "activebackground": "#0000FF", "activeforeground": "#000000",
        }

        tk.Button(toolbar, text="LOAD", command=self._load_rom, **btn_style).pack(side='left', padx=2, pady=2)
        tk.Button(toolbar, text="RUN", command=self._run_emu, **btn_style).pack(side='left', padx=2, pady=2)
        tk.Button(toolbar, text="PAUSE", command=self._pause_emu, **btn_style).pack(side='left', padx=2, pady=2)
        tk.Button(toolbar, text="RESET", command=self._reset_emu, **btn_style).pack(side='left', padx=2, pady=2)
        tk.Button(toolbar, text="BPP", command=self._cycle_bpp, **btn_style).pack(side='left', padx=2, pady=2)
        tk.Button(toolbar, text="PAL", command=self._cycle_palette, **btn_style).pack(side='left', padx=2, pady=2)
        tk.Button(toolbar, text="GOTO", command=self._prompt_jump, **btn_style).pack(side='left', padx=2, pady=2)

        self.status_label = tk.Label(toolbar, text="No ROM Loaded",
                                     bg="#000000", fg="#0000AA", font=("Courier", 10))
        self.status_label.pack(side='right', padx=10)

        # ---- Canvas ----
        display_frame = tk.Frame(self, bg="#000000")
        display_frame.pack(expand=True, fill='both', padx=10, pady=5)

        cw = self.FB_W * self.ZOOM
        ch = self.FB_H * self.ZOOM
        self.canvas = tk.Canvas(display_frame, width=cw, height=ch, bg="#000000",
                                highlightthickness=2, highlightbackground="#0000AA")
        self.canvas.pack(expand=True)

        self.canvas_img_id = self.canvas.create_image(cw // 2, ch // 2, image=None)
        self.canvas_bg_id = self.canvas.create_rectangle(5, 5, 470, 70,
                                                         fill="#000000", outline="#00FF00", width=2)
        self.canvas_text_id = self.canvas.create_text(
            15, 13, anchor="nw",
            text="No ROM loaded — hit LOAD to start cookin' 🐱",
            fill="#00FF00", font=("Courier", 13, "bold"))

        # ---- Status bar ----
        status_bar = tk.Frame(self, bg="#000000")
        status_bar.pack(fill='x', side='bottom')

        self.core_label = tk.Label(status_bar, text=f"Core: {CORE_TYPE}",
                                   bg="#000000", fg="#0000AA", font=("Courier", 9))
        self.core_label.pack(side='left', padx=5)

        self.fps_label = tk.Label(status_bar, text="FPS: 0",
                                  bg="#000000", fg="#0000AA", font=("Courier", 9))
        self.fps_label.pack(side='right', padx=5)

        self._render_frame()

    # --------------------------- Actions ----------------------------------
    def _load_rom(self):
        filepath = filedialog.askopenfilename(
            title="Select SNES ROM",
            filetypes=[("SNES ROMs", "*.sfc *.smc"), ("All Files", "*.*")])
        if not filepath:
            return
        self.is_running = False
        if self.core.load_rom(filepath):
            self.rom_loaded = True
            title = self.core.rom_info.get('title', 'Unknown')
            size = self.core.rom_info.get('rom_size', 0)
            mapping = self.core.rom_info.get('mapping', '?')
            self.status_label.config(text=f"{title} ({size}KB, {mapping})")
            self._render_frame()
        else:
            messagebox.showerror("Error", "Failed to load ROM.")

    def _run_emu(self):
        if not self.rom_loaded:
            messagebox.showwarning("Warning", "Please load a ROM first!")
            return
        self.is_running = True
        self.core.running = True
        self.last_time = time.time()
        self.frame_count = 0
        self._emulation_loop()

    def _pause_emu(self):
        self.is_running = False
        self.core.running = False

    def _reset_emu(self):
        self._pause_emu()
        if self.rom_loaded:
            self.core.frame = 0
            self.core.scroll_offset = 0
            self._render_frame()

    def _cycle_bpp(self):
        if hasattr(self.core, 'cycle_bpp'):
            self.core.cycle_bpp()
            self._render_frame()

    def _cycle_palette(self):
        if hasattr(self.core, 'cycle_palette'):
            self.core.cycle_palette()
            self._render_frame()

    def _scroll_delta(self, delta):
        if hasattr(self.core, 'scroll_by'):
            self.core.scroll_by(delta)
            self._render_frame()

    def _on_wheel(self, event):
        # Windows/Mac: event.delta is +-120 per notch
        step = -256 if event.delta > 0 else 256
        self._scroll_delta(step)

    def _jump_to_offset(self, off):
        if hasattr(self.core, 'jump_to'):
            self.core.jump_to(off)
            self._render_frame()

    def _prompt_jump(self):
        if not self.rom_loaded:
            return
        ans = simpledialog.askstring("Jump to Offset",
                                     "Hex offset (e.g. 0x10000 or 10000):",
                                     parent=self)
        if not ans:
            return
        try:
            ans = ans.strip().lower().replace('0x', '')
            off = int(ans, 16)
            self._jump_to_offset(off)
        except ValueError:
            messagebox.showerror("Bad offset", f"Couldn't parse: {ans}")

    def _export_ppm(self):
        if not self.rom_loaded:
            messagebox.showwarning("Warning", "Load a ROM first.")
            return
        path = filedialog.asksaveasfilename(
            title="Export frame as PPM",
            defaultextension=".ppm",
            filetypes=[("PPM image", "*.ppm")])
        if not path:
            return
        pixels = self.core.get_frame_buffer()
        try:
            with open(path, "wb") as f:
                f.write(f"P6\n{self.FB_W} {self.FB_H}\n255\n".encode())
                f.write(pixels)
            messagebox.showinfo("Exported", f"Saved frame to:\n{path}")
        except Exception as e:
            messagebox.showerror("Export failed", str(e))

    # --------------------------- Emulation loop ---------------------------
    def _emulation_loop(self):
        if not self.is_running:
            return
        self.core.step()
        self._render_frame()

        self.frame_count += 1
        now = time.time()
        elapsed = now - self.last_time
        if elapsed >= 1.0:
            self.fps = self.frame_count / elapsed
            self.fps_label.config(text=f"FPS: {int(self.fps)}")
            self.frame_count = 0
            self.last_time = now

        self.after(16, self._emulation_loop)

    # --------------------------- Render -----------------------------------
    def _render_frame(self):
        pixels = self.core.get_frame_buffer()
        header = f"P6 {self.FB_W} {self.FB_H} 255 ".encode()
        self.img.configure(data=header + pixels)
        self.zoomed_img = self.img.zoom(self.ZOOM, self.ZOOM)
        self.canvas.itemconfig(self.canvas_img_id, image=self.zoomed_img)

        if self.rom_loaded:
            title = self.core.rom_info.get('title', 'Unknown')
            bpp = getattr(self.core, 'bpp', 4)
            pal = getattr(self.core, 'palette_name', '?')
            off = self.core.scroll_offset
            rom_kb = self.core.rom_info.get('rom_size', 0)
            bytes_per_tile = {2: 16, 4: 32, 8: 64}.get(bpp, 32)
            tiles_per_screen = (self.FB_W // 8) * (self.FB_H // 8)
            end_off = off + tiles_per_screen * bytes_per_tile
            osd = (f"{title}  [{rom_kb}KB]\n"
                   f"OFFSET 0x{off:06X} -> 0x{end_off:06X}\n"
                   f"FMT {bpp}bpp   PAL {pal}")
            self.canvas.itemconfig(self.canvas_text_id, text=osd)
        # keep text on top
        self.canvas.tag_raise(self.canvas_bg_id)
        self.canvas.tag_raise(self.canvas_text_id)

    # --------------------------- Input ------------------------------------
    def _key_down(self, event):
        if event.keysym in self.KEY_MAP:
            self.core.press_key(0, self.KEY_MAP[event.keysym])

    def _key_up(self, event):
        if event.keysym in self.KEY_MAP:
            self.core.release_key(0, self.KEY_MAP[event.keysym])


if __name__ == "__main__":
    app = ACsSNESEmu()
    app.mainloop()
