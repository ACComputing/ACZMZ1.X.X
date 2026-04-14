#!/usr/bin/env python3
"""
AC's SNES Emu 0.4 — FIXED BOOT MODE 🐱🔥
GUI: Tkinter (ZMZ/ZSNES inspired)
Core: mewsnes 0.4 — proper 65816 CPU + DMA + PPU BG1 renderer

Fixes vs 0.3:
- XCE opcode rewritten (was broken — double-swap destroyed state)
- Opcode dispatch via dict table (way faster than if/elif chain)
- Addressing mode helpers (abs, abs,X/Y, dp, dp,X/Y, (dp), (dp),Y, [dp],
  [dp],Y, (dp,X), long, long,X, sr, (sr),Y)
- Added: ADC, SBC, AND, ORA, EOR, ASL, LSR, ROL, ROR, BIT, TSB, TRB
- Added: CMP/CPX/CPY memory variants, full LDA/STA/LDX/LDY coverage
- Added: BRK/COP, MVN/MVP block moves, JMP (abs,X), JSR (abs,X), PEA/PEI/PER
- MMIO: open-bus default for unhandled reads
- PPU: fallback to default palette when CGRAM still zeroed
"""

import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog
import os
import time

CORE_TYPE = "mewsnes 0.4 [Pure Python 65816 + PPU]"

# Status flags
F_C = 0x01; F_Z = 0x02; F_I = 0x04; F_D = 0x08
F_X = 0x10; F_M = 0x20; F_V = 0x40; F_N = 0x80


class SNESCore:
    DEFAULT_PAL = [
        (0, 0, 0), (0, 0, 85), (0, 85, 0), (0, 85, 85),
        (85, 0, 0), (85, 0, 85), (85, 85, 0), (170, 170, 170),
        (85, 85, 85), (0, 0, 255), (0, 255, 0), (0, 255, 255),
        (255, 0, 0), (255, 0, 255), (255, 255, 0), (255, 255, 255),
    ]

    def __init__(self):
        self.wram = bytearray(0x20000)
        self.vram = bytearray(0x10000)
        self.cgram = bytearray(0x200)
        self.oam = bytearray(0x220)
        self.rom = bytearray()
        self.rom_info = {}
        self.mapping = "LoROM"

        self.A = 0; self.X = 0; self.Y = 0
        self.S = 0x01FF
        self.D = 0
        self.DB = 0; self.PB = 0
        self.PC = 0
        self.P = F_M | F_X | F_I
        self.e = 1

        self.last_opcode = 0
        self.last_pc = 0

        self.inidisp = 0x80
        self.nmitimen = 0
        self.rdnmi = 0
        self.open_bus = 0

        self.vram_addr = 0
        self.vmadd_increment = 1
        self.vmadd_inc_on_high = True
        self.cgram_addr = 0
        self.cgram_latch = None
        self.bg1sc = 0
        self.bg12nba = 0
        self.bgmode = 0

        self._dma_regs = [bytearray(16) for _ in range(8)]

        self.running = False
        self.rom_loaded = False
        self.frame = 0
        self.total_cycles = 0
        self.cycles_this_frame = 0
        self.crashed = False
        self.crash_msg = ""

        self.input_regs = [0xFF, 0xFF, 0xFF, 0xFF]
        self.joy1l = 0xFF; self.joy1h = 0xFF

        self.fb_w = 256; self.fb_h = 224
        self._blank_fb = self._gen_blank_fb()

        self.viewer_mode = False
        self.viewer_bpp = 4
        self.viewer_offset = 0
        self.viewer_palette_idx = 1

        self._build_opcode_table()

    def _gen_blank_fb(self):
        pixels = bytearray(self.fb_w * self.fb_h * 3)
        bars = [(255, 255, 255), (255, 255, 0), (0, 255, 255), (0, 255, 0),
                (255, 0, 255), (255, 0, 0), (0, 0, 255), (0, 0, 0)]
        idx = 0
        for y in range(self.fb_h):
            for x in range(self.fb_w):
                if y < 160: r, g, b = bars[x // 32]
                elif y < 180: r = g = b = x % 256
                else: r = g = b = 0
                pixels[idx] = r; pixels[idx+1] = g; pixels[idx+2] = b
                idx += 3
        return pixels

    def load_rom(self, filepath):
        try:
            with open(filepath, "rb") as f:
                f.seek(0, os.SEEK_END); size = f.tell(); f.seek(0)
                if size % 1024 == 512: f.read(512)
                self.rom = bytearray(f.read())

            def title_at(o):
                if len(self.rom) < o + 21: return ""
                raw = self.rom[o:o+21]
                return "".join(chr(b) if 32 <= b <= 126 else ' ' for b in raw).strip()

            def score(o):
                if len(self.rom) < o + 31: return -1
                s = sum(1 for c in title_at(o) if c.isalnum())
                csum = self.rom[o+30] | (self.rom[o+31] << 8)
                ccmp = self.rom[o+28] | (self.rom[o+29] << 8)
                if (csum ^ ccmp) == 0xFFFF: s += 10
                return s

            s_lo, s_hi = score(0x7FC0), score(0xFFC0)
            if s_hi > s_lo:
                self.mapping = "HiROM"; hdr = 0xFFC0
            else:
                self.mapping = "LoROM"; hdr = 0x7FC0

            self.rom_info = {
                "title": title_at(hdr) or "UNKNOWN",
                "mapping": self.mapping,
                "rom_size": len(self.rom) // 1024,
                "header_off": hdr,
            }
            self.rom_loaded = True
            self.reset()
            return True
        except Exception as e:
            print(f"ROM load error: {e}")
            return False

    def _rom_offset(self, bank, addr):
        if not self.rom: return None
        rlen = len(self.rom)
        if self.mapping == "LoROM":
            if addr < 0x8000: return None
            b = bank & 0x7F
            off = (b * 0x8000) + (addr - 0x8000)
            return off % rlen if rlen else None
        b = bank & 0x7F
        if (bank & 0x40) or (bank & 0xC0) == 0xC0:
            off = (b * 0x10000) + addr
        else:
            if addr < 0x8000: return None
            off = (b * 0x10000) + addr
        return off % rlen if rlen else None

    def read8(self, bank, addr):
        bank &= 0xFF; addr &= 0xFFFF
        if ((bank <= 0x3F) or (0x80 <= bank <= 0xBF)) and addr < 0x2000:
            return self.wram[addr]
        if bank == 0x7E: return self.wram[addr]
        if bank == 0x7F: return self.wram[0x10000 + addr]
        if (bank <= 0x3F) or (0x80 <= bank <= 0xBF):
            if 0x2100 <= addr <= 0x21FF: return self._read_ppu(addr)
            if 0x4000 <= addr <= 0x44FF: return self._read_cpu_mmio(addr)
        off = self._rom_offset(bank, addr)
        if off is not None: return self.rom[off]
        return self.open_bus

    def read16(self, bank, addr):
        lo = self.read8(bank, addr)
        hi = self.read8(bank, (addr + 1) & 0xFFFF)
        return lo | (hi << 8)

    def read24(self, bank, addr):
        lo = self.read8(bank, addr)
        mi = self.read8(bank, (addr + 1) & 0xFFFF)
        hi = self.read8(bank, (addr + 2) & 0xFFFF)
        return lo | (mi << 8) | (hi << 16)

    def write8(self, bank, addr, val):
        bank &= 0xFF; addr &= 0xFFFF; val &= 0xFF
        if ((bank <= 0x3F) or (0x80 <= bank <= 0xBF)) and addr < 0x2000:
            self.wram[addr] = val; return
        if bank == 0x7E: self.wram[addr] = val; return
        if bank == 0x7F: self.wram[0x10000 + addr] = val; return
        if (bank <= 0x3F) or (0x80 <= bank <= 0xBF):
            if 0x2100 <= addr <= 0x21FF: self._write_ppu(addr, val); return
            if 0x4000 <= addr <= 0x44FF: self._write_cpu_mmio(addr, val); return

    def write16(self, bank, addr, val):
        self.write8(bank, addr, val & 0xFF)
        self.write8(bank, (addr + 1) & 0xFFFF, (val >> 8) & 0xFF)

    def _write_ppu(self, addr, val):
        if addr == 0x2100: self.inidisp = val
        elif addr == 0x2105: self.bgmode = val
        elif addr == 0x2107: self.bg1sc = val
        elif addr == 0x210B: self.bg12nba = val
        elif addr == 0x2115:
            inc_map = {0: 1, 1: 32, 2: 128, 3: 128}
            self.vmadd_increment = inc_map[val & 0x03]
            self.vmadd_inc_on_high = (val & 0x80) != 0
        elif addr == 0x2116:
            self.vram_addr = (self.vram_addr & 0xFF00) | val
        elif addr == 0x2117:
            self.vram_addr = (self.vram_addr & 0x00FF) | (val << 8)
        elif addr == 0x2118:
            va = (self.vram_addr * 2) & 0xFFFE
            self.vram[va] = val
            if not self.vmadd_inc_on_high:
                self.vram_addr = (self.vram_addr + self.vmadd_increment) & 0xFFFF
        elif addr == 0x2119:
            va = (self.vram_addr * 2 + 1) & 0xFFFF
            self.vram[va] = val
            if self.vmadd_inc_on_high:
                self.vram_addr = (self.vram_addr + self.vmadd_increment) & 0xFFFF
        elif addr == 0x2121:
            self.cgram_addr = (val * 2) & 0x1FF
            self.cgram_latch = None
        elif addr == 0x2122:
            if self.cgram_latch is None:
                self.cgram_latch = val
            else:
                if self.cgram_addr + 1 < len(self.cgram):
                    self.cgram[self.cgram_addr] = self.cgram_latch
                    self.cgram[self.cgram_addr + 1] = val
                self.cgram_addr = (self.cgram_addr + 2) & 0x1FF
                self.cgram_latch = None

    def _read_ppu(self, addr):
        if addr == 0x2139:
            va = (self.vram_addr * 2) & 0xFFFE
            return self.vram[va]
        if addr == 0x213A:
            va = (self.vram_addr * 2 + 1) & 0xFFFF
            return self.vram[va]
        return self.open_bus

    def _write_cpu_mmio(self, addr, val):
        if addr == 0x4200: self.nmitimen = val
        elif addr == 0x420B:
            for ch in range(8):
                if val & (1 << ch): self._run_dma(ch)
        elif 0x4300 <= addr <= 0x437F:
            ch = (addr - 0x4300) >> 4
            reg = addr & 0x0F
            self._dma_regs[ch][reg] = val

    def _read_cpu_mmio(self, addr):
        if addr == 0x4210:
            v = self.rdnmi
            self.rdnmi &= 0x7F
            return v | 0x02
        if addr == 0x4218: return self.joy1l
        if addr == 0x4219: return self.joy1h
        if 0x4300 <= addr <= 0x437F:
            ch = (addr - 0x4300) >> 4
            reg = addr & 0x0F
            return self._dma_regs[ch][reg]
        return self.open_bus

    def _run_dma(self, ch):
        regs = self._dma_regs[ch]
        dmap = regs[0]; bbad = regs[1]
        a1l, a1h, a1b = regs[2], regs[3], regs[4]
        count = regs[5] | (regs[6] << 8)
        if count == 0: count = 0x10000
        direction = dmap & 0x80
        mode = dmap & 0x07
        step = -1 if (dmap & 0x10) else (0 if (dmap & 0x08) else 1)
        src = a1l | (a1h << 8); sb = a1b
        base = 0x2100 | bbad
        patterns = {0: [0], 1: [0, 1], 2: [0, 0], 3: [0, 0, 1, 1],
                    4: [0, 1, 2, 3], 5: [0, 1, 0, 1], 6: [0, 0], 7: [0, 0, 1, 1]}
        pat = patterns.get(mode, [0])
        t = 0; pi = 0; safety = 0x10000
        while t < count and safety > 0:
            safety -= 1
            b = self.read8(sb, src)
            if direction == 0:
                self.write8(0, (base + pat[pi]) & 0xFFFF, b)
            src = (src + step) & 0xFFFF
            pi = (pi + 1) % len(pat)
            t += 1
        rem = max(0, count - t)
        regs[5] = rem & 0xFF; regs[6] = (rem >> 8) & 0xFF
        regs[2] = src & 0xFF; regs[3] = (src >> 8) & 0xFF

    def reset(self):
        self.A = 0; self.X = 0; self.Y = 0
        self.S = 0x01FF; self.D = 0
        self.DB = 0; self.PB = 0
        self.P = F_M | F_X | F_I
        self.e = 1
        self.PC = self.read16(0, 0xFFFC)
        self.frame = 0
        self.total_cycles = 0
        self.cycles_this_frame = 0
        self.crashed = False; self.crash_msg = ""
        self.inidisp = 0x80
        self.vram_addr = 0; self.cgram_addr = 0

    def _nz8(self, v):
        v &= 0xFF
        self.P = (self.P & ~(F_N | F_Z)) | (F_N if v & 0x80 else 0) | (F_Z if v == 0 else 0)

    def _nz16(self, v):
        v &= 0xFFFF
        self.P = (self.P & ~(F_N | F_Z)) | (F_N if v & 0x8000 else 0) | (F_Z if v == 0 else 0)

    def _push8(self, v):
        v &= 0xFF
        self.write8(0, self.S, v)
        if self.e: self.S = 0x0100 | ((self.S - 1) & 0xFF)
        else: self.S = (self.S - 1) & 0xFFFF

    def _pull8(self):
        if self.e: self.S = 0x0100 | ((self.S + 1) & 0xFF)
        else: self.S = (self.S + 1) & 0xFFFF
        return self.read8(0, self.S)

    def _push16(self, v):
        self._push8((v >> 8) & 0xFF)
        self._push8(v & 0xFF)

    def _pull16(self):
        lo = self._pull8(); hi = self._pull8()
        return lo | (hi << 8)

    def _fetch8(self):
        v = self.read8(self.PB, self.PC)
        self.PC = (self.PC + 1) & 0xFFFF
        return v

    def _fetch16(self):
        lo = self._fetch8(); hi = self._fetch8()
        return lo | (hi << 8)

    def _fetch24(self):
        lo = self._fetch8(); mi = self._fetch8(); hi = self._fetch8()
        return lo | (mi << 8) | (hi << 16)

    @property
    def m8(self): return self.e or (self.P & F_M)
    @property
    def x8(self): return self.e or (self.P & F_X)

    # Addressing modes
    def _am_abs(self): return self.DB, self._fetch16()
    def _am_abs_x(self): return self.DB, (self._fetch16() + self.X) & 0xFFFF
    def _am_abs_y(self): return self.DB, (self._fetch16() + self.Y) & 0xFFFF
    def _am_long(self): a = self._fetch24(); return (a >> 16) & 0xFF, a & 0xFFFF
    def _am_long_x(self):
        a = self._fetch24() + self.X
        return (a >> 16) & 0xFF, a & 0xFFFF
    def _am_dp(self): return 0, (self._fetch8() + self.D) & 0xFFFF
    def _am_dp_x(self): return 0, (self._fetch8() + self.D + self.X) & 0xFFFF
    def _am_dp_y(self): return 0, (self._fetch8() + self.D + self.Y) & 0xFFFF
    def _am_dp_ind(self):
        p = (self._fetch8() + self.D) & 0xFFFF
        return self.DB, self.read16(0, p)
    def _am_dp_ind_y(self):
        p = (self._fetch8() + self.D) & 0xFFFF
        return self.DB, (self.read16(0, p) + self.Y) & 0xFFFF
    def _am_dp_x_ind(self):
        p = (self._fetch8() + self.D + self.X) & 0xFFFF
        return self.DB, self.read16(0, p)
    def _am_dp_long_ind(self):
        p = (self._fetch8() + self.D) & 0xFFFF
        a = self.read24(0, p)
        return (a >> 16) & 0xFF, a & 0xFFFF
    def _am_dp_long_ind_y(self):
        p = (self._fetch8() + self.D) & 0xFFFF
        a = self.read24(0, p) + self.Y
        return (a >> 16) & 0xFF, a & 0xFFFF
    def _am_sr(self): return 0, (self._fetch8() + self.S) & 0xFFFF
    def _am_sr_ind_y(self):
        p = (self._fetch8() + self.S) & 0xFFFF
        return self.DB, (self.read16(0, p) + self.Y) & 0xFFFF

    def _read_m(self, b, a):
        return self.read8(b, a) if self.m8 else self.read16(b, a)
    def _write_m(self, b, a, v):
        if self.m8: self.write8(b, a, v)
        else: self.write16(b, a, v)
    def _read_x(self, b, a):
        return self.read8(b, a) if self.x8 else self.read16(b, a)
    def _write_x(self, b, a, v):
        if self.x8: self.write8(b, a, v)
        else: self.write16(b, a, v)

    # ALU primitives
    def _alu_adc(self, v):
        c = 1 if self.P & F_C else 0
        if self.m8:
            a = self.A & 0xFF; v &= 0xFF
            r = a + v + c
            self.P = (self.P & ~(F_C | F_V))
            if r > 0xFF: self.P |= F_C
            if (~(a ^ v) & (a ^ r) & 0x80): self.P |= F_V
            r &= 0xFF
            self.A = (self.A & 0xFF00) | r; self._nz8(r)
        else:
            a = self.A & 0xFFFF; v &= 0xFFFF
            r = a + v + c
            self.P = (self.P & ~(F_C | F_V))
            if r > 0xFFFF: self.P |= F_C
            if (~(a ^ v) & (a ^ r) & 0x8000): self.P |= F_V
            r &= 0xFFFF
            self.A = r; self._nz16(r)

    def _alu_sbc(self, v):
        v = (~v) & (0xFF if self.m8 else 0xFFFF)
        self._alu_adc(v)

    def _alu_cmp(self, reg, v, is8):
        if is8:
            a = reg & 0xFF; v &= 0xFF
            r = a - v
            self.P = (self.P & ~F_C) | (F_C if r >= 0 else 0)
            self._nz8(r & 0xFF)
        else:
            a = reg & 0xFFFF; v &= 0xFFFF
            r = a - v
            self.P = (self.P & ~F_C) | (F_C if r >= 0 else 0)
            self._nz16(r & 0xFFFF)

    def _alu_and(self, v):
        if self.m8:
            r = (self.A & 0xFF) & (v & 0xFF)
            self.A = (self.A & 0xFF00) | r; self._nz8(r)
        else:
            r = self.A & v & 0xFFFF
            self.A = r; self._nz16(r)

    def _alu_ora(self, v):
        if self.m8:
            r = (self.A & 0xFF) | (v & 0xFF)
            self.A = (self.A & 0xFF00) | r; self._nz8(r)
        else:
            r = (self.A | v) & 0xFFFF
            self.A = r; self._nz16(r)

    def _alu_eor(self, v):
        if self.m8:
            r = (self.A & 0xFF) ^ (v & 0xFF)
            self.A = (self.A & 0xFF00) | r; self._nz8(r)
        else:
            r = (self.A ^ v) & 0xFFFF
            self.A = r; self._nz16(r)

    def _alu_bit(self, v):
        if self.m8:
            v &= 0xFF
            self.P = (self.P & ~(F_N | F_V | F_Z)) | (v & 0xC0)
            if ((self.A & 0xFF) & v) == 0: self.P |= F_Z
        else:
            v &= 0xFFFF
            self.P = (self.P & ~(F_N | F_V | F_Z)) | ((v >> 8) & 0xC0)
            if (self.A & v) == 0: self.P |= F_Z

    def _alu_asl(self, v):
        if self.m8:
            v &= 0xFF
            self.P = (self.P & ~F_C) | (F_C if v & 0x80 else 0)
            v = (v << 1) & 0xFF; self._nz8(v); return v
        v &= 0xFFFF
        self.P = (self.P & ~F_C) | (F_C if v & 0x8000 else 0)
        v = (v << 1) & 0xFFFF; self._nz16(v); return v

    def _alu_lsr(self, v):
        if self.m8:
            v &= 0xFF
            self.P = (self.P & ~F_C) | (F_C if v & 1 else 0)
            v >>= 1; self._nz8(v); return v
        v &= 0xFFFF
        self.P = (self.P & ~F_C) | (F_C if v & 1 else 0)
        v >>= 1; self._nz16(v); return v

    def _alu_rol(self, v):
        c = 1 if self.P & F_C else 0
        if self.m8:
            v &= 0xFF
            self.P = (self.P & ~F_C) | (F_C if v & 0x80 else 0)
            v = ((v << 1) | c) & 0xFF; self._nz8(v); return v
        v &= 0xFFFF
        self.P = (self.P & ~F_C) | (F_C if v & 0x8000 else 0)
        v = ((v << 1) | c) & 0xFFFF; self._nz16(v); return v

    def _alu_ror(self, v):
        c = 1 if self.P & F_C else 0
        if self.m8:
            v &= 0xFF
            self.P = (self.P & ~F_C) | (F_C if v & 1 else 0)
            v = (v >> 1) | (c << 7); self._nz8(v); return v
        v &= 0xFFFF
        self.P = (self.P & ~F_C) | (F_C if v & 1 else 0)
        v = (v >> 1) | (c << 15); self._nz16(v); return v

    def _branch(self, cond):
        off = self._fetch8()
        if off & 0x80: off -= 0x100
        if cond:
            self.PC = (self.PC + off) & 0xFFFF
            return 3
        return 2

    def _build_opcode_table(self):
        T = {}

        def lda_imm():
            if self.m8:
                v = self._fetch8(); self.A = (self.A & 0xFF00) | v; self._nz8(v)
            else:
                v = self._fetch16(); self.A = v; self._nz16(v)
            return 2
        def lda_am(am, cy):
            def f():
                b, a = am()
                if self.m8:
                    v = self.read8(b, a); self.A = (self.A & 0xFF00) | v; self._nz8(v)
                else:
                    v = self.read16(b, a); self.A = v; self._nz16(v)
                return cy
            return f
        T[0xA9] = lda_imm
        T[0xAD] = lda_am(self._am_abs, 4); T[0xBD] = lda_am(self._am_abs_x, 4)
        T[0xB9] = lda_am(self._am_abs_y, 4); T[0xA5] = lda_am(self._am_dp, 3)
        T[0xB5] = lda_am(self._am_dp_x, 4); T[0xB2] = lda_am(self._am_dp_ind, 5)
        T[0xB1] = lda_am(self._am_dp_ind_y, 5); T[0xA1] = lda_am(self._am_dp_x_ind, 6)
        T[0xA7] = lda_am(self._am_dp_long_ind, 6); T[0xB7] = lda_am(self._am_dp_long_ind_y, 6)
        T[0xAF] = lda_am(self._am_long, 5); T[0xBF] = lda_am(self._am_long_x, 5)
        T[0xA3] = lda_am(self._am_sr, 4); T[0xB3] = lda_am(self._am_sr_ind_y, 7)

        def sta_am(am, cy):
            def f():
                b, a = am()
                self._write_m(b, a, self.A & (0xFF if self.m8 else 0xFFFF))
                return cy
            return f
        T[0x8D] = sta_am(self._am_abs, 4); T[0x9D] = sta_am(self._am_abs_x, 5)
        T[0x99] = sta_am(self._am_abs_y, 5); T[0x85] = sta_am(self._am_dp, 3)
        T[0x95] = sta_am(self._am_dp_x, 4); T[0x92] = sta_am(self._am_dp_ind, 5)
        T[0x91] = sta_am(self._am_dp_ind_y, 6); T[0x81] = sta_am(self._am_dp_x_ind, 6)
        T[0x87] = sta_am(self._am_dp_long_ind, 6); T[0x97] = sta_am(self._am_dp_long_ind_y, 6)
        T[0x8F] = sta_am(self._am_long, 5); T[0x9F] = sta_am(self._am_long_x, 5)
        T[0x83] = sta_am(self._am_sr, 4); T[0x93] = sta_am(self._am_sr_ind_y, 7)

        def stz_am(am, cy):
            def f():
                b, a = am(); self._write_m(b, a, 0); return cy
            return f
        T[0x9C] = stz_am(self._am_abs, 4); T[0x9E] = stz_am(self._am_abs_x, 5)
        T[0x64] = stz_am(self._am_dp, 3); T[0x74] = stz_am(self._am_dp_x, 4)

        def ldx_imm():
            if self.x8: v = self._fetch8(); self.X = v; self._nz8(v)
            else: v = self._fetch16(); self.X = v; self._nz16(v)
            return 2
        def ldy_imm():
            if self.x8: v = self._fetch8(); self.Y = v; self._nz8(v)
            else: v = self._fetch16(); self.Y = v; self._nz16(v)
            return 2
        T[0xA2] = ldx_imm; T[0xA0] = ldy_imm

        def ldx_am(am, cy):
            def f():
                b, a = am()
                if self.x8: v = self.read8(b, a); self.X = v; self._nz8(v)
                else: v = self.read16(b, a); self.X = v; self._nz16(v)
                return cy
            return f
        def ldy_am(am, cy):
            def f():
                b, a = am()
                if self.x8: v = self.read8(b, a); self.Y = v; self._nz8(v)
                else: v = self.read16(b, a); self.Y = v; self._nz16(v)
                return cy
            return f
        T[0xAE] = ldx_am(self._am_abs, 4); T[0xBE] = ldx_am(self._am_abs_y, 4)
        T[0xA6] = ldx_am(self._am_dp, 3); T[0xB6] = ldx_am(self._am_dp_y, 4)
        T[0xAC] = ldy_am(self._am_abs, 4); T[0xBC] = ldy_am(self._am_abs_x, 4)
        T[0xA4] = ldy_am(self._am_dp, 3); T[0xB4] = ldy_am(self._am_dp_x, 4)

        def stx_am(am, cy):
            def f():
                b, a = am()
                self._write_x(b, a, self.X & (0xFF if self.x8 else 0xFFFF))
                return cy
            return f
        def sty_am(am, cy):
            def f():
                b, a = am()
                self._write_x(b, a, self.Y & (0xFF if self.x8 else 0xFFFF))
                return cy
            return f
        T[0x8E] = stx_am(self._am_abs, 4); T[0x86] = stx_am(self._am_dp, 3)
        T[0x96] = stx_am(self._am_dp_y, 4); T[0x8C] = sty_am(self._am_abs, 4)
        T[0x84] = sty_am(self._am_dp, 3); T[0x94] = sty_am(self._am_dp_x, 4)

        def alu_imm(fn):
            def f():
                v = self._fetch8() if self.m8 else self._fetch16()
                fn(v); return 2
            return f
        def alu_am(fn, am, cy):
            def f():
                b, a = am(); v = self._read_m(b, a); fn(v); return cy
            return f

        # ADC
        T[0x69] = alu_imm(self._alu_adc)
        T[0x6D] = alu_am(self._alu_adc, self._am_abs, 4)
        T[0x7D] = alu_am(self._alu_adc, self._am_abs_x, 4)
        T[0x79] = alu_am(self._alu_adc, self._am_abs_y, 4)
        T[0x65] = alu_am(self._alu_adc, self._am_dp, 3)
        T[0x75] = alu_am(self._alu_adc, self._am_dp_x, 4)
        T[0x72] = alu_am(self._alu_adc, self._am_dp_ind, 5)
        T[0x71] = alu_am(self._alu_adc, self._am_dp_ind_y, 5)
        T[0x61] = alu_am(self._alu_adc, self._am_dp_x_ind, 6)
        T[0x67] = alu_am(self._alu_adc, self._am_dp_long_ind, 6)
        T[0x77] = alu_am(self._alu_adc, self._am_dp_long_ind_y, 6)
        T[0x6F] = alu_am(self._alu_adc, self._am_long, 5)
        T[0x7F] = alu_am(self._alu_adc, self._am_long_x, 5)
        T[0x63] = alu_am(self._alu_adc, self._am_sr, 4)
        T[0x73] = alu_am(self._alu_adc, self._am_sr_ind_y, 7)
        # SBC
        T[0xE9] = alu_imm(self._alu_sbc)
        T[0xED] = alu_am(self._alu_sbc, self._am_abs, 4)
        T[0xFD] = alu_am(self._alu_sbc, self._am_abs_x, 4)
        T[0xF9] = alu_am(self._alu_sbc, self._am_abs_y, 4)
        T[0xE5] = alu_am(self._alu_sbc, self._am_dp, 3)
        T[0xF5] = alu_am(self._alu_sbc, self._am_dp_x, 4)
        T[0xF2] = alu_am(self._alu_sbc, self._am_dp_ind, 5)
        T[0xF1] = alu_am(self._alu_sbc, self._am_dp_ind_y, 5)
        T[0xE1] = alu_am(self._alu_sbc, self._am_dp_x_ind, 6)
        T[0xE7] = alu_am(self._alu_sbc, self._am_dp_long_ind, 6)
        T[0xF7] = alu_am(self._alu_sbc, self._am_dp_long_ind_y, 6)
        T[0xEF] = alu_am(self._alu_sbc, self._am_long, 5)
        T[0xFF] = alu_am(self._alu_sbc, self._am_long_x, 5)
        T[0xE3] = alu_am(self._alu_sbc, self._am_sr, 4)
        T[0xF3] = alu_am(self._alu_sbc, self._am_sr_ind_y, 7)
        # AND
        T[0x29] = alu_imm(self._alu_and)
        T[0x2D] = alu_am(self._alu_and, self._am_abs, 4)
        T[0x3D] = alu_am(self._alu_and, self._am_abs_x, 4)
        T[0x39] = alu_am(self._alu_and, self._am_abs_y, 4)
        T[0x25] = alu_am(self._alu_and, self._am_dp, 3)
        T[0x35] = alu_am(self._alu_and, self._am_dp_x, 4)
        T[0x32] = alu_am(self._alu_and, self._am_dp_ind, 5)
        T[0x31] = alu_am(self._alu_and, self._am_dp_ind_y, 5)
        T[0x21] = alu_am(self._alu_and, self._am_dp_x_ind, 6)
        T[0x27] = alu_am(self._alu_and, self._am_dp_long_ind, 6)
        T[0x37] = alu_am(self._alu_and, self._am_dp_long_ind_y, 6)
        T[0x2F] = alu_am(self._alu_and, self._am_long, 5)
        T[0x3F] = alu_am(self._alu_and, self._am_long_x, 5)
        T[0x23] = alu_am(self._alu_and, self._am_sr, 4)
        T[0x33] = alu_am(self._alu_and, self._am_sr_ind_y, 7)
        # ORA
        T[0x09] = alu_imm(self._alu_ora)
        T[0x0D] = alu_am(self._alu_ora, self._am_abs, 4)
        T[0x1D] = alu_am(self._alu_ora, self._am_abs_x, 4)
        T[0x19] = alu_am(self._alu_ora, self._am_abs_y, 4)
        T[0x05] = alu_am(self._alu_ora, self._am_dp, 3)
        T[0x15] = alu_am(self._alu_ora, self._am_dp_x, 4)
        T[0x12] = alu_am(self._alu_ora, self._am_dp_ind, 5)
        T[0x11] = alu_am(self._alu_ora, self._am_dp_ind_y, 5)
        T[0x01] = alu_am(self._alu_ora, self._am_dp_x_ind, 6)
        T[0x07] = alu_am(self._alu_ora, self._am_dp_long_ind, 6)
        T[0x17] = alu_am(self._alu_ora, self._am_dp_long_ind_y, 6)
        T[0x0F] = alu_am(self._alu_ora, self._am_long, 5)
        T[0x1F] = alu_am(self._alu_ora, self._am_long_x, 5)
        T[0x03] = alu_am(self._alu_ora, self._am_sr, 4)
        T[0x13] = alu_am(self._alu_ora, self._am_sr_ind_y, 7)
        # EOR
        T[0x49] = alu_imm(self._alu_eor)
        T[0x4D] = alu_am(self._alu_eor, self._am_abs, 4)
        T[0x5D] = alu_am(self._alu_eor, self._am_abs_x, 4)
        T[0x59] = alu_am(self._alu_eor, self._am_abs_y, 4)
        T[0x45] = alu_am(self._alu_eor, self._am_dp, 3)
        T[0x55] = alu_am(self._alu_eor, self._am_dp_x, 4)
        T[0x52] = alu_am(self._alu_eor, self._am_dp_ind, 5)
        T[0x51] = alu_am(self._alu_eor, self._am_dp_ind_y, 5)
        T[0x41] = alu_am(self._alu_eor, self._am_dp_x_ind, 6)
        T[0x47] = alu_am(self._alu_eor, self._am_dp_long_ind, 6)
        T[0x57] = alu_am(self._alu_eor, self._am_dp_long_ind_y, 6)
        T[0x4F] = alu_am(self._alu_eor, self._am_long, 5)
        T[0x5F] = alu_am(self._alu_eor, self._am_long_x, 5)
        T[0x43] = alu_am(self._alu_eor, self._am_sr, 4)
        T[0x53] = alu_am(self._alu_eor, self._am_sr_ind_y, 7)

        def cmp_imm():
            v = self._fetch8() if self.m8 else self._fetch16()
            self._alu_cmp(self.A, v, self.m8); return 2
        def cmp_am(am, cy):
            def f():
                b, a = am(); v = self._read_m(b, a)
                self._alu_cmp(self.A, v, self.m8); return cy
            return f
        T[0xC9] = cmp_imm
        T[0xCD] = cmp_am(self._am_abs, 4); T[0xDD] = cmp_am(self._am_abs_x, 4)
        T[0xD9] = cmp_am(self._am_abs_y, 4); T[0xC5] = cmp_am(self._am_dp, 3)
        T[0xD5] = cmp_am(self._am_dp_x, 4); T[0xD2] = cmp_am(self._am_dp_ind, 5)
        T[0xD1] = cmp_am(self._am_dp_ind_y, 5); T[0xC1] = cmp_am(self._am_dp_x_ind, 6)
        T[0xC7] = cmp_am(self._am_dp_long_ind, 6); T[0xD7] = cmp_am(self._am_dp_long_ind_y, 6)
        T[0xCF] = cmp_am(self._am_long, 5); T[0xDF] = cmp_am(self._am_long_x, 5)
        T[0xC3] = cmp_am(self._am_sr, 4); T[0xD3] = cmp_am(self._am_sr_ind_y, 7)

        def cpx_imm():
            v = self._fetch8() if self.x8 else self._fetch16()
            self._alu_cmp(self.X, v, self.x8); return 2
        def cpy_imm():
            v = self._fetch8() if self.x8 else self._fetch16()
            self._alu_cmp(self.Y, v, self.x8); return 2
        def cpx_am(am, cy):
            def f():
                b, a = am(); v = self._read_x(b, a)
                self._alu_cmp(self.X, v, self.x8); return cy
            return f
        def cpy_am(am, cy):
            def f():
                b, a = am(); v = self._read_x(b, a)
                self._alu_cmp(self.Y, v, self.x8); return cy
            return f
        T[0xE0] = cpx_imm; T[0xC0] = cpy_imm
        T[0xEC] = cpx_am(self._am_abs, 4); T[0xE4] = cpx_am(self._am_dp, 3)
        T[0xCC] = cpy_am(self._am_abs, 4); T[0xC4] = cpy_am(self._am_dp, 3)

        def bit_imm():
            if self.m8:
                v = self._fetch8()
                if ((self.A & 0xFF) & v) == 0: self.P |= F_Z
                else: self.P &= ~F_Z
            else:
                v = self._fetch16()
                if (self.A & v) == 0: self.P |= F_Z
                else: self.P &= ~F_Z
            return 2
        def bit_am(am, cy):
            def f():
                b, a = am(); v = self._read_m(b, a); self._alu_bit(v); return cy
            return f
        T[0x89] = bit_imm
        T[0x2C] = bit_am(self._am_abs, 4); T[0x3C] = bit_am(self._am_abs_x, 4)
        T[0x24] = bit_am(self._am_dp, 3); T[0x34] = bit_am(self._am_dp_x, 4)

        def shift_a(fn):
            def f():
                if self.m8:
                    r = fn(self.A & 0xFF); self.A = (self.A & 0xFF00) | (r & 0xFF)
                else:
                    self.A = fn(self.A) & 0xFFFF
                return 2
            return f
        def shift_m(fn, am, cy):
            def f():
                b, a = am(); v = self._read_m(b, a)
                self._write_m(b, a, fn(v)); return cy
            return f
        T[0x0A] = shift_a(self._alu_asl); T[0x4A] = shift_a(self._alu_lsr)
        T[0x2A] = shift_a(self._alu_rol); T[0x6A] = shift_a(self._alu_ror)
        T[0x0E] = shift_m(self._alu_asl, self._am_abs, 6); T[0x1E] = shift_m(self._alu_asl, self._am_abs_x, 7)
        T[0x06] = shift_m(self._alu_asl, self._am_dp, 5); T[0x16] = shift_m(self._alu_asl, self._am_dp_x, 6)
        T[0x4E] = shift_m(self._alu_lsr, self._am_abs, 6); T[0x5E] = shift_m(self._alu_lsr, self._am_abs_x, 7)
        T[0x46] = shift_m(self._alu_lsr, self._am_dp, 5); T[0x56] = shift_m(self._alu_lsr, self._am_dp_x, 6)
        T[0x2E] = shift_m(self._alu_rol, self._am_abs, 6); T[0x3E] = shift_m(self._alu_rol, self._am_abs_x, 7)
        T[0x26] = shift_m(self._alu_rol, self._am_dp, 5); T[0x36] = shift_m(self._alu_rol, self._am_dp_x, 6)
        T[0x6E] = shift_m(self._alu_ror, self._am_abs, 6); T[0x7E] = shift_m(self._alu_ror, self._am_abs_x, 7)
        T[0x66] = shift_m(self._alu_ror, self._am_dp, 5); T[0x76] = shift_m(self._alu_ror, self._am_dp_x, 6)

        def incdec_a(d):
            def f():
                if self.m8:
                    r = ((self.A & 0xFF) + d) & 0xFF
                    self.A = (self.A & 0xFF00) | r; self._nz8(r)
                else:
                    r = (self.A + d) & 0xFFFF
                    self.A = r; self._nz16(r)
                return 2
            return f
        def incdec_m(d, am, cy):
            def f():
                b, a = am(); v = self._read_m(b, a)
                if self.m8: r = (v + d) & 0xFF; self._nz8(r)
                else: r = (v + d) & 0xFFFF; self._nz16(r)
                self._write_m(b, a, r); return cy
            return f
        T[0x1A] = incdec_a(1); T[0x3A] = incdec_a(-1)
        T[0xEE] = incdec_m(1, self._am_abs, 6); T[0xFE] = incdec_m(1, self._am_abs_x, 7)
        T[0xE6] = incdec_m(1, self._am_dp, 5); T[0xF6] = incdec_m(1, self._am_dp_x, 6)
        T[0xCE] = incdec_m(-1, self._am_abs, 6); T[0xDE] = incdec_m(-1, self._am_abs_x, 7)
        T[0xC6] = incdec_m(-1, self._am_dp, 5); T[0xD6] = incdec_m(-1, self._am_dp_x, 6)

        def inx():
            if self.x8: self.X = (self.X + 1) & 0xFF; self._nz8(self.X)
            else: self.X = (self.X + 1) & 0xFFFF; self._nz16(self.X)
            return 2
        def iny():
            if self.x8: self.Y = (self.Y + 1) & 0xFF; self._nz8(self.Y)
            else: self.Y = (self.Y + 1) & 0xFFFF; self._nz16(self.Y)
            return 2
        def dex():
            if self.x8: self.X = (self.X - 1) & 0xFF; self._nz8(self.X)
            else: self.X = (self.X - 1) & 0xFFFF; self._nz16(self.X)
            return 2
        def dey():
            if self.x8: self.Y = (self.Y - 1) & 0xFF; self._nz8(self.Y)
            else: self.Y = (self.Y - 1) & 0xFFFF; self._nz16(self.Y)
            return 2
        T[0xE8] = inx; T[0xC8] = iny; T[0xCA] = dex; T[0x88] = dey

        def tsb_am(am, cy):
            def f():
                b, a = am(); v = self._read_m(b, a)
                mask = 0xFF if self.m8 else 0xFFFF
                av = self.A & mask
                if (v & av) == 0: self.P |= F_Z
                else: self.P &= ~F_Z
                self._write_m(b, a, (v | av) & mask); return cy
            return f
        def trb_am(am, cy):
            def f():
                b, a = am(); v = self._read_m(b, a)
                mask = 0xFF if self.m8 else 0xFFFF
                av = self.A & mask
                if (v & av) == 0: self.P |= F_Z
                else: self.P &= ~F_Z
                self._write_m(b, a, (v & ~av) & mask); return cy
            return f
        T[0x0C] = tsb_am(self._am_abs, 6); T[0x04] = tsb_am(self._am_dp, 5)
        T[0x1C] = trb_am(self._am_abs, 6); T[0x14] = trb_am(self._am_dp, 5)

        # Transfers
        def tax():
            if self.x8: self.X = self.A & 0xFF; self._nz8(self.X)
            else: self.X = self.A & 0xFFFF; self._nz16(self.X)
            return 2
        def tay():
            if self.x8: self.Y = self.A & 0xFF; self._nz8(self.Y)
            else: self.Y = self.A & 0xFFFF; self._nz16(self.Y)
            return 2
        def txa():
            if self.m8: self.A = (self.A & 0xFF00) | (self.X & 0xFF); self._nz8(self.X)
            else: self.A = self.X & 0xFFFF; self._nz16(self.A)
            return 2
        def tya():
            if self.m8: self.A = (self.A & 0xFF00) | (self.Y & 0xFF); self._nz8(self.Y)
            else: self.A = self.Y & 0xFFFF; self._nz16(self.A)
            return 2
        def txy():
            if self.x8: self.Y = self.X & 0xFF; self._nz8(self.Y)
            else: self.Y = self.X & 0xFFFF; self._nz16(self.Y)
            return 2
        def tyx():
            if self.x8: self.X = self.Y & 0xFF; self._nz8(self.X)
            else: self.X = self.Y & 0xFFFF; self._nz16(self.X)
            return 2
        def txs():
            if self.e: self.S = 0x0100 | (self.X & 0xFF)
            else: self.S = self.X & 0xFFFF
            return 2
        def tsx():
            if self.x8: self.X = self.S & 0xFF; self._nz8(self.X)
            else: self.X = self.S & 0xFFFF; self._nz16(self.X)
            return 2
        def tcd(): self.D = self.A & 0xFFFF; self._nz16(self.D); return 2
        def tdc(): self.A = self.D & 0xFFFF; self._nz16(self.A); return 2
        def tcs():
            if self.e: self.S = 0x0100 | (self.A & 0xFF)
            else: self.S = self.A & 0xFFFF
            return 2
        def tsc(): self.A = self.S & 0xFFFF; self._nz16(self.A); return 2
        T[0xAA] = tax; T[0xA8] = tay; T[0x8A] = txa; T[0x98] = tya
        T[0x9B] = txy; T[0xBB] = tyx
        T[0x9A] = txs; T[0xBA] = tsx
        T[0x5B] = tcd; T[0x7B] = tdc; T[0x1B] = tcs; T[0x3B] = tsc

        # Flags / mode
        T[0x78] = lambda: (setattr(self, 'P', self.P | F_I), 2)[1]
        T[0x58] = lambda: (setattr(self, 'P', self.P & ~F_I), 2)[1]
        T[0x18] = lambda: (setattr(self, 'P', self.P & ~F_C), 2)[1]
        T[0x38] = lambda: (setattr(self, 'P', self.P | F_C), 2)[1]
        T[0xD8] = lambda: (setattr(self, 'P', self.P & ~F_D), 2)[1]
        T[0xF8] = lambda: (setattr(self, 'P', self.P | F_D), 2)[1]
        T[0xB8] = lambda: (setattr(self, 'P', self.P & ~F_V), 2)[1]

        def xce():
            # swap E and C
            c_bit = 1 if self.P & F_C else 0
            e_bit = self.e
            if e_bit: self.P |= F_C
            else: self.P &= ~F_C
            self.e = c_bit
            if self.e:
                self.P |= F_M | F_X
                self.X &= 0xFF; self.Y &= 0xFF
                self.S = 0x0100 | (self.S & 0xFF)
            return 2
        T[0xFB] = xce

        def rep():
            v = self._fetch8()
            self.P &= ~v
            if self.e: self.P |= F_M | F_X
            if self.P & F_X: self.X &= 0xFF; self.Y &= 0xFF
            return 3
        def sep():
            v = self._fetch8()
            self.P |= v
            if self.P & F_X: self.X &= 0xFF; self.Y &= 0xFF
            return 3
        T[0xC2] = rep; T[0xE2] = sep

        # Branches
        T[0x80] = lambda: self._branch(True)
        T[0xD0] = lambda: self._branch(not (self.P & F_Z))
        T[0xF0] = lambda: self._branch(bool(self.P & F_Z))
        T[0x10] = lambda: self._branch(not (self.P & F_N))
        T[0x30] = lambda: self._branch(bool(self.P & F_N))
        T[0x90] = lambda: self._branch(not (self.P & F_C))
        T[0xB0] = lambda: self._branch(bool(self.P & F_C))
        T[0x50] = lambda: self._branch(not (self.P & F_V))
        T[0x70] = lambda: self._branch(bool(self.P & F_V))

        def brl():
            off = self._fetch16()
            if off & 0x8000: off -= 0x10000
            self.PC = (self.PC + off) & 0xFFFF
            return 4
        T[0x82] = brl

        # Jumps / subs
        def jmp_abs(): self.PC = self._fetch16(); return 3
        def jmp_long():
            a = self._fetch24()
            self.PC = a & 0xFFFF; self.PB = (a >> 16) & 0xFF; return 4
        def jmp_ind():
            ptr = self._fetch16(); self.PC = self.read16(0, ptr); return 5
        def jmp_abs_x_ind():
            ptr = (self._fetch16() + self.X) & 0xFFFF
            self.PC = self.read16(self.PB, ptr); return 6
        def jmp_ind_long():
            ptr = self._fetch16()
            self.PC = self.read16(0, ptr)
            self.PB = self.read8(0, (ptr + 2) & 0xFFFF); return 6
        T[0x4C] = jmp_abs; T[0x5C] = jmp_long
        T[0x6C] = jmp_ind; T[0x7C] = jmp_abs_x_ind; T[0xDC] = jmp_ind_long

        def jsr_abs():
            a = self._fetch16()
            self._push16((self.PC - 1) & 0xFFFF)
            self.PC = a; return 6
        def jsl():
            a = self._fetch24()
            self._push8(self.PB)
            self._push16((self.PC - 1) & 0xFFFF)
            self.PC = a & 0xFFFF; self.PB = (a >> 16) & 0xFF; return 8
        def jsr_abs_x_ind():
            ptr = (self._fetch16() + self.X) & 0xFFFF
            self._push16((self.PC - 1) & 0xFFFF)
            self.PC = self.read16(self.PB, ptr); return 8
        T[0x20] = jsr_abs; T[0x22] = jsl; T[0xFC] = jsr_abs_x_ind

        def rts(): self.PC = (self._pull16() + 1) & 0xFFFF; return 6
        def rtl():
            self.PC = (self._pull16() + 1) & 0xFFFF
            self.PB = self._pull8(); return 6
        def rti():
            self.P = self._pull8()
            self.PC = self._pull16()
            if not self.e: self.PB = self._pull8()
            return 6
        T[0x60] = rts; T[0x6B] = rtl; T[0x40] = rti

        # Stack
        def pha():
            if self.m8: self._push8(self.A & 0xFF)
            else: self._push16(self.A)
            return 3
        def pla():
            if self.m8:
                v = self._pull8(); self.A = (self.A & 0xFF00) | v; self._nz8(v)
            else:
                v = self._pull16(); self.A = v; self._nz16(v)
            return 4
        def phx():
            if self.x8: self._push8(self.X)
            else: self._push16(self.X)
            return 3
        def plx():
            if self.x8: v = self._pull8(); self.X = v; self._nz8(v)
            else: v = self._pull16(); self.X = v; self._nz16(v)
            return 4
        def phy():
            if self.x8: self._push8(self.Y)
            else: self._push16(self.Y)
            return 3
        def ply():
            if self.x8: v = self._pull8(); self.Y = v; self._nz8(v)
            else: v = self._pull16(); self.Y = v; self._nz16(v)
            return 4
        T[0x48] = pha; T[0x68] = pla
        T[0xDA] = phx; T[0xFA] = plx
        T[0x5A] = phy; T[0x7A] = ply
        T[0x8B] = lambda: (self._push8(self.DB), 3)[1]
        T[0xAB] = lambda: (self.__setattr__('DB', self._pull8()), self._nz8(self.DB), 4)[2]
        T[0x4B] = lambda: (self._push8(self.PB), 3)[1]
        T[0x0B] = lambda: (self._push16(self.D), 4)[1]
        T[0x2B] = lambda: (self.__setattr__('D', self._pull16()), self._nz16(self.D), 5)[2]
        T[0x08] = lambda: (self._push8(self.P), 3)[1]
        def plp():
            self.P = self._pull8()
            if self.e: self.P |= F_M | F_X
            return 4
        T[0x28] = plp

        def pea():
            v = self._fetch16(); self._push16(v); return 5
        def pei():
            p = (self._fetch8() + self.D) & 0xFFFF
            v = self.read16(0, p); self._push16(v); return 6
        def per():
            off = self._fetch16()
            if off & 0x8000: off -= 0x10000
            self._push16((self.PC + off) & 0xFFFF); return 6
        T[0xF4] = pea; T[0xD4] = pei; T[0x62] = per

        def mvn():
            db = self._fetch8(); sb = self._fetch8()
            self.DB = db
            v = self.read8(sb, self.X)
            self.write8(db, self.Y, v)
            self.A = (self.A - 1) & 0xFFFF
            if self.x8:
                self.X = (self.X + 1) & 0xFF; self.Y = (self.Y + 1) & 0xFF
            else:
                self.X = (self.X + 1) & 0xFFFF; self.Y = (self.Y + 1) & 0xFFFF
            if self.A != 0xFFFF: self.PC = (self.PC - 3) & 0xFFFF
            return 7
        def mvp():
            db = self._fetch8(); sb = self._fetch8()
            self.DB = db
            v = self.read8(sb, self.X)
            self.write8(db, self.Y, v)
            self.A = (self.A - 1) & 0xFFFF
            if self.x8:
                self.X = (self.X - 1) & 0xFF; self.Y = (self.Y - 1) & 0xFF
            else:
                self.X = (self.X - 1) & 0xFFFF; self.Y = (self.Y - 1) & 0xFFFF
            if self.A != 0xFFFF: self.PC = (self.PC - 3) & 0xFFFF
            return 7
        T[0x54] = mvn; T[0x44] = mvp

        # Misc
        T[0xEA] = lambda: 2
        T[0x42] = lambda: (self._fetch8(), 2)[1]  # WDM
        def xba():
            lo = self.A & 0xFF; hi = (self.A >> 8) & 0xFF
            self.A = (lo << 8) | hi
            self._nz8(hi); return 3
        T[0xEB] = xba
        T[0xCB] = lambda: 2  # WAI
        def stp():
            self.crashed = True
            self.crash_msg = f"STP @ ${self.PB:02X}:{self.last_pc:04X}"
            return 2
        T[0xDB] = stp

        def brk_op():
            self._fetch8()
            if not self.e: self._push8(self.PB)
            self._push16(self.PC)
            self._push8(self.P | 0x10)
            self.P |= F_I; self.P &= ~F_D
            self.PB = 0
            self.PC = self.read16(0, 0xFFE6 if not self.e else 0xFFFE)
            return 7
        def cop_op():
            self._fetch8()
            if not self.e: self._push8(self.PB)
            self._push16(self.PC)
            self._push8(self.P)
            self.P |= F_I; self.P &= ~F_D
            self.PB = 0
            self.PC = self.read16(0, 0xFFE4 if not self.e else 0xFFF4)
            return 7
        T[0x00] = brk_op; T[0x02] = cop_op

        self._optable = T

    def step_instruction(self):
        if self.crashed: return 0
        try:
            self.last_pc = self.PC
            op = self._fetch8()
            self.last_opcode = op
            fn = self._optable.get(op)
            if fn is None:
                self.crashed = True
                self.crash_msg = f"Unimpl op ${op:02X} @ ${self.PB:02X}:{self.last_pc:04X}"
                return 0
            r = fn()
            return r if r else 2
        except Exception as e:
            self.crashed = True
            self.crash_msg = f"CPU crash @ ${self.PB:02X}:{self.last_pc:04X} op=${self.last_opcode:02X}: {e}"
            return 0

    def run_frame(self):
        if self.crashed or not self.rom_loaded: return
        CYCLES_PER_FRAME = 357368
        self.cycles_this_frame = 0
        inp = self.input_regs[0]
        self.joy1l = inp & 0xFF; self.joy1h = 0xFF
        safety = 500000
        while self.cycles_this_frame < CYCLES_PER_FRAME and not self.crashed and safety > 0:
            cy = self.step_instruction()
            if cy <= 0: break
            self.cycles_this_frame += cy
            self.total_cycles += cy
            safety -= 1
        self.rdnmi |= 0x80
        if self.nmitimen & 0x80 and not self.crashed:
            self._nmi()
        self.frame += 1

    def _nmi(self):
        if not self.e: self._push8(self.PB)
        self._push16(self.PC)
        self._push8(self.P)
        self.P |= F_I; self.P &= ~F_D
        vec = 0xFFEA if not self.e else 0xFFFA
        self.PC = self.read16(0, vec)
        self.PB = 0

    def press_key(self, p, k): self.input_regs[p] &= ~(1 << k)
    def release_key(self, p, k): self.input_regs[p] |= (1 << k)

    def _cgram_color(self, idx):
        idx &= 0xFF
        if all(b == 0 for b in self.cgram[:32]) and idx < 16:
            return self.DEFAULT_PAL[idx]
        lo = self.cgram[idx * 2]; hi = self.cgram[idx * 2 + 1]
        c = lo | (hi << 8)
        return ((c & 0x1F) << 3, ((c >> 5) & 0x1F) << 3, ((c >> 10) & 0x1F) << 3)

    def _decode_bg_tile_pixel(self, char_base, tile_num, px, py, bpp):
        bpt = {2: 16, 4: 32, 8: 64}[bpp]
        addr = (char_base + tile_num * bpt) & 0xFFFF
        bit = 7 - px
        if bpp == 2:
            p0 = self.vram[(addr + py * 2) & 0xFFFF]
            p1 = self.vram[(addr + py * 2 + 1) & 0xFFFF]
            return ((p0 >> bit) & 1) | (((p1 >> bit) & 1) << 1)
        if bpp == 4:
            p0 = self.vram[(addr + py * 2) & 0xFFFF]
            p1 = self.vram[(addr + py * 2 + 1) & 0xFFFF]
            p2 = self.vram[(addr + py * 2 + 16) & 0xFFFF]
            p3 = self.vram[(addr + py * 2 + 17) & 0xFFFF]
            return (((p0 >> bit) & 1)
                    | (((p1 >> bit) & 1) << 1)
                    | (((p2 >> bit) & 1) << 2)
                    | (((p3 >> bit) & 1) << 3))
        c = 0
        for pi, off in enumerate((0, 1, 16, 17, 32, 33, 48, 49)):
            b = self.vram[(addr + py * 2 + off) & 0xFFFF]
            c |= ((b >> bit) & 1) << pi
        return c

    def get_frame_buffer(self):
        if not self.rom_loaded: return self._blank_fb
        if self.viewer_mode: return self._render_viewer()
        if self.inidisp & 0x80:
            return bytes(self.fb_w * self.fb_h * 3)

        mode = self.bgmode & 0x07
        bpp = 2 if mode == 0 else 4
        if mode == 7: bpp = 8

        tilemap_base = ((self.bg1sc & 0xFC) << 8) & 0xFFFF
        char_base = ((self.bg12nba & 0x0F) << 12) & 0xFFFF
        pixels = bytearray(self.fb_w * self.fb_h * 3)
        brightness = self.inidisp & 0x0F
        bf = brightness / 15.0 if brightness else 0.0
        tm_w = 32

        for y in range(self.fb_h):
            ty = (y >> 3) & 31; py = y & 7
            for x in range(self.fb_w):
                tx = (x >> 3) & 31; px = x & 7
                tm_off = (tilemap_base + (ty * tm_w + tx) * 2) & 0xFFFF
                entry = self.vram[tm_off] | (self.vram[(tm_off + 1) & 0xFFFF] << 8)
                tile_num = entry & 0x3FF
                pal_num = (entry >> 10) & 0x07
                hflip = (entry >> 14) & 1; vflip = (entry >> 15) & 1
                ux = 7 - px if hflip else px
                uy = 7 - py if vflip else py
                c = self._decode_bg_tile_pixel(char_base, tile_num, ux, uy, bpp)
                if c == 0:
                    r, g, b = self._cgram_color(0)
                else:
                    pal_size = {2: 4, 4: 16, 8: 256}[bpp]
                    r, g, b = self._cgram_color(pal_num * pal_size + c)
                if bf < 1.0:
                    r = int(r * bf); g = int(g * bf); b = int(b * bf)
                i = (y * self.fb_w + x) * 3
                pixels[i] = r; pixels[i+1] = g; pixels[i+2] = b
        return pixels

    def _render_viewer(self):
        pal = [(i * 17, i * 17, i * 17) for i in range(16)] if self.viewer_palette_idx == 0 else self.DEFAULT_PAL
        pixels = bytearray(self.fb_w * self.fb_h * 3)
        bpp = self.viewer_bpp
        bpt = {2: 16, 4: 32, 8: 64}[bpp]
        cols = self.fb_w // 8; rows = self.fb_h // 8
        rom_len = len(self.rom)
        if rom_len == 0: return pixels
        for ty in range(rows):
            for tx in range(cols):
                base = self.viewer_offset + (ty * cols + tx) * bpt
                if base >= rom_len: break
                for y in range(8):
                    for x in range(8):
                        bit = 7 - x
                        if bpp == 4:
                            b1 = self.rom[(base + y * 2) % rom_len]
                            b2 = self.rom[(base + y * 2 + 1) % rom_len]
                            b3 = self.rom[(base + y * 2 + 16) % rom_len]
                            b4 = self.rom[(base + y * 2 + 17) % rom_len]
                            c = (((b1 >> bit) & 1) | (((b2 >> bit) & 1) << 1)
                                 | (((b3 >> bit) & 1) << 2) | (((b4 >> bit) & 1) << 3))
                        elif bpp == 2:
                            b1 = self.rom[(base + y * 2) % rom_len]
                            b2 = self.rom[(base + y * 2 + 1) % rom_len]
                            c = ((b1 >> bit) & 1) | (((b2 >> bit) & 1) << 1)
                        else:
                            c = 0
                            for pi, off in enumerate((0, 1, 16, 17, 32, 33, 48, 49)):
                                b = self.rom[(base + y * 2 + off) % rom_len]
                                c |= ((b >> bit) & 1) << pi
                            c &= 0x0F
                        r, g, bl = pal[c % len(pal)]
                        i = (((ty * 8 + y) * self.fb_w) + tx * 8 + x) * 3
                        pixels[i] = r; pixels[i+1] = g; pixels[i+2] = bl
        return pixels


# =============================================================================
# GUI
# =============================================================================
class ACsSNESEmu(tk.Tk):
    BTN_B = 0; BTN_Y = 1; BTN_SELECT = 2; BTN_START = 3
    BTN_UP = 4; BTN_DOWN = 5; BTN_LEFT = 6; BTN_RIGHT = 7

    KEY_MAP = {
        'z': BTN_B, 'x': 8, 'a': BTN_Y, 's': 9,
        'Return': BTN_START, 'Shift_R': BTN_SELECT,
        'Up': BTN_UP, 'Down': BTN_DOWN, 'Left': BTN_LEFT, 'Right': BTN_RIGHT,
    }

    ZOOM = 3; FB_W = 256; FB_H = 224

    def __init__(self):
        super().__init__()
        self.title("AC's SNES Emu 0.4 — FIXED BOOT MODE")
        w = self.FB_W * self.ZOOM + 40
        h = self.FB_H * self.ZOOM + 180
        self.geometry(f"{w}x{h}")
        self.resizable(False, False)
        self.configure(bg="#000000")

        self.core = SNESCore()
        self.is_running = False
        self.show_debug = False
        self.fps = 0
        self.last_time = time.time()
        self.frame_count = 0

        self.img = tk.PhotoImage(width=self.FB_W, height=self.FB_H)
        self.zoomed_img = None

        self._build_gui()
        self.bind("<KeyPress>", self._key_down)
        self.bind("<KeyRelease>", self._key_up)
        self.bind("<F3>", lambda e: self._toggle_debug())
        self.bind("<F2>", lambda e: self._toggle_viewer())

    def _build_gui(self):
        menubar = tk.Menu(self, bg="#0000AA", fg="#000000",
                          activebackground="#0000FF", activeforeground="#000000", relief='flat')
        file_menu = tk.Menu(menubar, tearoff=0, bg="#0000AA", fg="#000000")
        file_menu.add_command(label="Load ROM...    (Ctrl+O)", command=self._load_rom)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.quit)
        menubar.add_cascade(label="File", menu=file_menu)
        self.bind("<Control-o>", lambda e: self._load_rom())

        view_menu = tk.Menu(menubar, tearoff=0, bg="#0000AA", fg="#000000")
        view_menu.add_command(label="Toggle Debug HUD  (F3)", command=self._toggle_debug)
        view_menu.add_command(label="Toggle ROM Viewer (F2)", command=self._toggle_viewer)
        menubar.add_cascade(label="View", menu=view_menu)

        help_menu = tk.Menu(menubar, tearoff=0, bg="#0000AA", fg="#000000")
        help_menu.add_command(label="About", command=lambda: messagebox.showinfo(
            "About",
            "AC's SNES Emu 0.4\n\nProper 65816 CPU + PPU BG1 renderer.\n"
            "~200 opcodes + all standard addressing modes.\n\n"
            "Controls: Arrows, Z=B, X=A, A=Y, S=X,\n"
            "Enter=Start, RShift=Select\n"
            "F2=ROM viewer, F3=Debug HUD"))
        menubar.add_cascade(label="Help", menu=help_menu)
        self.config(menu=menubar)

        toolbar = tk.Frame(self, bg="#000000", height=30)
        toolbar.pack(fill='x', side='top')
        btn_style = {"bg": "#0000AA", "fg": "#000000",
                     "font": ("Courier", 10, "bold"),
                     "relief": 'raised', "bd": 2,
                     "activebackground": "#0000FF", "activeforeground": "#000000"}
        tk.Button(toolbar, text="LOAD", command=self._load_rom, **btn_style).pack(side='left', padx=2, pady=2)
        tk.Button(toolbar, text="RUN", command=self._run, **btn_style).pack(side='left', padx=2, pady=2)
        tk.Button(toolbar, text="PAUSE", command=self._pause, **btn_style).pack(side='left', padx=2, pady=2)
        tk.Button(toolbar, text="RESET", command=self._reset, **btn_style).pack(side='left', padx=2, pady=2)
        tk.Button(toolbar, text="DEBUG", command=self._toggle_debug, **btn_style).pack(side='left', padx=2, pady=2)
        tk.Button(toolbar, text="VIEWER", command=self._toggle_viewer, **btn_style).pack(side='left', padx=2, pady=2)

        self.status_label = tk.Label(toolbar, text="No ROM Loaded",
                                     bg="#000000", fg="#0000AA", font=("Courier", 10))
        self.status_label.pack(side='right', padx=10)

        display_frame = tk.Frame(self, bg="#000000")
        display_frame.pack(expand=True, fill='both', padx=10, pady=5)
        cw = self.FB_W * self.ZOOM; ch = self.FB_H * self.ZOOM
        self.canvas = tk.Canvas(display_frame, width=cw, height=ch, bg="#000000",
                                highlightthickness=2, highlightbackground="#0000AA")
        self.canvas.pack(expand=True)
        self.canvas_img_id = self.canvas.create_image(cw // 2, ch // 2, image=None)
        self.canvas_bg_id = self.canvas.create_rectangle(5, 5, 560, 150,
                                                         fill="#000000", outline="#00FF00", width=2,
                                                         state='hidden')
        self.canvas_text_id = self.canvas.create_text(
            15, 13, anchor="nw", text="", fill="#00FF00",
            font=("Courier", 12, "bold"), state='hidden')

        status_bar = tk.Frame(self, bg="#000000")
        status_bar.pack(fill='x', side='bottom')
        tk.Label(status_bar, text=f"Core: {CORE_TYPE}",
                 bg="#000000", fg="#0000AA", font=("Courier", 9)).pack(side='left', padx=5)
        self.fps_label = tk.Label(status_bar, text="FPS: 0 | -",
                                  bg="#000000", fg="#0000AA", font=("Courier", 9))
        self.fps_label.pack(side='right', padx=5)
        self._render_frame()

    def _load_rom(self):
        fp = filedialog.askopenfilename(
            title="Select SNES ROM",
            filetypes=[("SNES ROMs", "*.sfc *.smc"), ("All Files", "*.*")])
        if not fp: return
        self.is_running = False
        if self.core.load_rom(fp):
            info = self.core.rom_info
            self.status_label.config(
                text=f"{info['title']} ({info['rom_size']}KB, {info['mapping']}) "
                     f"RESET=${self.core.PC:04X}")
            self._render_frame()
        else:
            messagebox.showerror("Error", "Failed to load ROM.")

    def _run(self):
        if not self.core.rom_loaded:
            messagebox.showwarning("Warning", "Load a ROM first!"); return
        if self.core.crashed:
            messagebox.showwarning("Crashed",
                f"CPU crashed:\n{self.core.crash_msg}\n\nReset to try again."); return
        self.is_running = True; self.core.running = True
        self.last_time = time.time(); self.frame_count = 0
        self._emu_loop()

    def _pause(self):
        self.is_running = False; self.core.running = False

    def _reset(self):
        self._pause()
        if self.core.rom_loaded:
            self.core.reset(); self._render_frame()

    def _toggle_debug(self):
        self.show_debug = not self.show_debug
        s = 'normal' if self.show_debug else 'hidden'
        self.canvas.itemconfig(self.canvas_bg_id, state=s)
        self.canvas.itemconfig(self.canvas_text_id, state=s)
        self._render_frame()

    def _toggle_viewer(self):
        self.core.viewer_mode = not self.core.viewer_mode
        self._render_frame()

    def _emu_loop(self):
        if not self.is_running: return
        self.core.run_frame()
        self._render_frame()
        self.frame_count += 1
        now = time.time(); elapsed = now - self.last_time
        if elapsed >= 1.0:
            self.fps = self.frame_count / elapsed
            mode = "VIEW" if self.core.viewer_mode else f"M{self.core.bgmode & 7}"
            extra = " CRASH" if self.core.crashed else ""
            self.fps_label.config(text=f"FPS: {int(self.fps)} | {mode}{extra}")
            self.frame_count = 0; self.last_time = now
        if self.core.crashed:
            self.is_running = False; self._render_frame(); return
        self.after(16, self._emu_loop)

    def _render_frame(self):
        pixels = self.core.get_frame_buffer()
        header = f"P6 {self.FB_W} {self.FB_H} 255 ".encode()
        self.img.configure(data=header + pixels)
        self.zoomed_img = self.img.zoom(self.ZOOM, self.ZOOM)
        self.canvas.itemconfig(self.canvas_img_id, image=self.zoomed_img)

        if self.show_debug and self.core.rom_loaded:
            c = self.core
            crash = f"\n!! {c.crash_msg}" if c.crashed else ""
            txt = (f"PC ${c.PB:02X}:{c.PC:04X}  op ${c.last_opcode:02X}  frame {c.frame}\n"
                   f"A  ${c.A:04X}   X ${c.X:04X}   Y ${c.Y:04X}\n"
                   f"S  ${c.S:04X}   D ${c.D:04X}   DB ${c.DB:02X}\n"
                   f"P  ${c.P:02X}  e={c.e}  m={int(bool(c.m8))} x={int(bool(c.x8))}\n"
                   f"BGMODE ${c.bgmode:02X}  BG1SC ${c.bg1sc:02X}  NBA ${c.bg12nba:02X}\n"
                   f"INIDISP ${c.inidisp:02X}  VRAM@${c.vram_addr:04X}{crash}")
            self.canvas.itemconfig(self.canvas_text_id, text=txt)
        self.canvas.tag_raise(self.canvas_bg_id)
        self.canvas.tag_raise(self.canvas_text_id)

    def _key_down(self, event):
        if event.keysym in self.KEY_MAP:
            self.core.press_key(0, self.KEY_MAP[event.keysym])

    def _key_up(self, event):
        if event.keysym in self.KEY_MAP:
            self.core.release_key(0, self.KEY_MAP[event.keysym])


if __name__ == "__main__":
    app = ACsSNESEmu()
    app.mainloop()
