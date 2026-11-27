// PNG Squeeze — a lossless PNG optimizer for make.fun's png-squeeze-01.
// Reads 8 screenshots of 1280x720 RGBA from /input/<id>/image.png and writes
// the same images as the smallest valid PNGs it can to /output/<id>/image.png.
//
// What it does, per image:
//   1. Decodes the stored RGBA PNG.
//   2. Picks the cheapest exact form: palette (<=256 colours), grey / grey+alpha,
//      RGB / RGBA, with a tRNS key when one transparent value covers all alpha.
//   3. Picks the filter per row by the scale's screen (fixed filters, minimum-sum
//      and fewest-pairs heuristics, ranked by zlib level 6 size).
//   4. Compresses the filtered bytes with an optimal-parse DEFLATE encoder
//      (hash-chain LZ77 + dynamic-programming parse + dynamic Huffman, iterated
//      twice), falling back to Node's zlib level 9 when that is smaller.
// Deterministic: no clock, no randomness, no environment-dependent choices, so
// two runs write identical bytes.

import { inflateSync, deflateSync, constants } from 'node:zlib';
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// ---------------------------------------------------------------------------
// DEFLATE tables (RFC 1951)
// ---------------------------------------------------------------------------

// Length codes 257..285: base length and extra bits.
const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
// Distance codes 0..29: base distance and extra bits.
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];

// Length-code boundaries: the lengths at which the length symbol (or its extra
// bits) changes, plus 258. The optimal parse only needs to try these lengths.
const LEN_BOUNDS = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];

// Symbol and extra bits for a match length 3..258. (Uint16Array: the symbols
// run to 285, past a byte.)
const LEN_SYM = new Uint16Array(259);
const LEN_EXT = new Uint8Array(259);
for (let s = 0; s < 29; s++) {
  const base = LEN_BASE[s];
  const next = s === 28 ? 259 : LEN_BASE[s + 1];
  for (let l = base; l < next; l++) { LEN_SYM[l] = 257 + s; LEN_EXT[l] = LEN_EXTRA[s]; }
}
// Symbol and extra bits for a match distance 1..32768.
const DIST_SYM = new Uint8Array(32769);
const DIST_EXT = new Uint8Array(32769);
for (let s = 0; s < 30; s++) {
  const base = DIST_BASE[s];
  const next = s === 29 ? 32769 : DIST_BASE[s + 1];
  for (let d = base; d < next; d++) { DIST_SYM[d] = s; DIST_EXT[d] = DIST_EXTRA[s]; }
}

// Fixed Huffman code lengths (RFC 1951 section 3.2.6).
const FIXED_LIT_LEN = new Uint8Array(288);
for (let s = 0; s < 144; s++) FIXED_LIT_LEN[s] = 8;
for (let s = 144; s < 256; s++) FIXED_LIT_LEN[s] = 9;
for (let s = 256; s < 280; s++) FIXED_LIT_LEN[s] = 7;
for (let s = 280; s < 288; s++) FIXED_LIT_LEN[s] = 8;
const FIXED_DIST_LEN = new Uint8Array(32).fill(5);

// The order the dynamic header lists code-length-code lengths in.
const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

// ---------------------------------------------------------------------------
// Checksums
// ---------------------------------------------------------------------------

const CRC_TABLE = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c;
  }
  return t;
})();

function crc32(bytes: Uint8Array, start = 0, end = bytes.length): number {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}

function adler32(bytes: Uint8Array): number {
  let a = 1;
  let b = 0;
  for (let i = 0; i < bytes.length;) {
    const end = Math.min(bytes.length, i + 5552);
    for (; i < end; i++) { a += bytes[i]; b += a; }
    a %= 65521;
    b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}

// ---------------------------------------------------------------------------
// PNG container: decode (any accepted colour type) and encode
// ---------------------------------------------------------------------------

const SIGNATURE = Uint8Array.of(137, 80, 78, 71, 13, 10, 26, 10);
const CHANNELS: Record<number, number> = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };

function paeth(a: number, b: number, c: number): number {
  const p = a + b - c;
  const pa = p > a ? p - a : a - p;
  const pb = p > b ? p - b : b - p;
  const pc = p > c ? p - c : c - p;
  if (pa <= pb && pa <= pc) return a;
  return pb <= pc ? b : c;
}

interface Decoded { width: number; height: number; rgba: Uint8Array }

function decodePng(bytes: Uint8Array): Decoded {
  if (bytes.length < 8 || SIGNATURE.some((b, i) => bytes[i] !== b)) throw new Error('not a PNG');
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8;
  let header: { width: number; height: number; colourType: number } | null = null;
  let palette: Uint8Array | null = null;
  let trns: Uint8Array | null = null;
  const idat: Uint8Array[] = [];
  let ended = false;
  while (at < bytes.length) {
    if (ended) throw new Error('bytes after IEND');
    if (at + 12 > bytes.length) throw new Error('truncated chunk');
    const len = view.getUint32(at);
    if (at + 12 + len > bytes.length) throw new Error('chunk overruns file');
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    if (crc32(bytes, at + 4, at + 8 + len) !== view.getUint32(at + 8 + len)) throw new Error(type + ' CRC mismatch');
    const data = bytes.subarray(at + 8, at + 8 + len);
    at += 12 + len;
    if (type === 'IHDR') {
      if (header !== null) throw new Error('two IHDR');
      const dv = new DataView(data.buffer, data.byteOffset, 13);
      header = { width: dv.getUint32(0), height: dv.getUint32(4), colourType: data[9] };
      if (data[8] !== 8 || data[10] !== 0 || data[11] !== 0 || data[12] !== 0) throw new Error('unsupported IHDR');
      if (!(header.colourType in CHANNELS)) throw new Error('unsupported colour type');
    } else if (type === 'PLTE') {
      palette = data;
    } else if (type === 'tRNS') {
      trns = data;
    } else if (type === 'IDAT') {
      idat.push(data);
    } else if (type === 'IEND') {
      if (len !== 0) throw new Error('non-empty IEND');
      ended = true;
    } else {
      throw new Error('unexpected chunk ' + type);
    }
  }
  if (!header || !ended || idat.length === 0) throw new Error('incomplete PNG');
  const { width, height, colourType } = header;
  const bpp = CHANNELS[colourType];
  const stride = width * bpp;
  const expected = height * (stride + 1);
  const raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat), { maxOutputLength: expected + 1 });
  if (raw.length !== expected) throw new Error('IDAT inflates to the wrong size');
  const samples = new Uint8Array(height * stride);
  for (let y = 0; y < height; y++) {
    const ft = raw[y * (stride + 1)];
    if (ft > 4) throw new Error('bad filter type');
    const src = y * (stride + 1) + 1;
    const o = y * stride;
    const p = o - stride;
    if (ft === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (ft === 1) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= bpp ? samples[o + i - bpp] : 0);
    } else if (ft === 2) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0);
    } else if (ft === 3) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (((i >= bpp ? samples[o + i - bpp] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1);
    } else {
      for (let i = 0; i < stride; i++) {
        const a = i >= bpp ? samples[o + i - bpp] : 0;
        const b = y > 0 ? samples[p + i] : 0;
        const c = y > 0 && i >= bpp ? samples[p + i - bpp] : 0;
        samples[o + i] = raw[src + i] + paeth(a, b, c);
      }
    }
  }
  const n = width * height;
  const rgba = new Uint8Array(n * 4);
  if (colourType === 6) {
    rgba.set(samples);
  } else if (colourType === 2) {
    const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5];
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) {
      rgba[d] = samples[s]; rgba[d + 1] = samples[s + 1]; rgba[d + 2] = samples[s + 2];
      rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255;
    }
  } else if (colourType === 0) {
    const key = trns === null ? -1 : trns[1];
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const g = samples[i];
      rgba[d] = rgba[d + 1] = rgba[d + 2] = g;
      rgba[d + 3] = g === key ? 0 : 255;
    }
  } else if (colourType === 4) {
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) {
      rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s];
      rgba[d + 3] = samples[s + 1];
    }
  } else {
    if (palette === null) throw new Error('palette image without PLTE');
    const entries = palette.length / 3;
    const lut = new Uint8Array(entries * 4);
    for (let e = 0; e < entries; e++) {
      lut[e * 4] = palette[e * 3]; lut[e * 4 + 1] = palette[e * 3 + 1]; lut[e * 4 + 2] = palette[e * 3 + 2];
      lut[e * 4 + 3] = trns !== null && e < trns.length ? trns[e] : 255;
    }
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const e = samples[i];
      if (e >= entries) throw new Error('palette index out of range');
      rgba[d] = lut[e * 4]; rgba[d + 1] = lut[e * 4 + 1]; rgba[d + 2] = lut[e * 4 + 2]; rgba[d + 3] = lut[e * 4 + 3];
    }
  }
  return { width, height, rgba };
}

function pngOf(chunks: [string, Uint8Array][]): Uint8Array {
  let size = SIGNATURE.length;
  for (const [, data] of chunks) size += 12 + data.length;
  const out = new Uint8Array(size);
  const view = new DataView(out.buffer);
  out.set(SIGNATURE, 0);
  let at = SIGNATURE.length;
  for (const [type, data] of chunks) {
    view.setUint32(at, data.length);
    out[at + 4] = type.charCodeAt(0); out[at + 5] = type.charCodeAt(1);
    out[at + 6] = type.charCodeAt(2); out[at + 7] = type.charCodeAt(3);
    out.set(data, at + 8);
    view.setUint32(at + 8 + data.length, crc32(out, at + 4, at + 8 + data.length));
    at += 12 + data.length;
  }
  return out;
}

function ihdrOf(width: number, height: number, colourType: number): Uint8Array {
  const d = new Uint8Array(13);
  const v = new DataView(d.buffer);
  v.setUint32(0, width);
  v.setUint32(4, height);
  d[8] = 8;
  d[9] = colourType;
  return d;
}

// ---------------------------------------------------------------------------
// Image analysis and forms
// ---------------------------------------------------------------------------

interface Colour { rgba: [number, number, number, number]; word: number; count: number }

function analyse(rgba: Uint8Array): { opaque: boolean; grey: boolean; colours: Colour[] | null } {
  const n = rgba.length >>> 2;
  let opaque = true;
  let grey = true;
  const counts = new Map<number, number>();
  let many = false;
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    if (rgba[d + 3] !== 255) opaque = false;
    if (rgba[d] !== rgba[d + 1] || rgba[d] !== rgba[d + 2]) grey = false;
    if (!many) {
      // The colour as one 32-bit word, little-endian (as a Uint32Array view
      // reads the RGBA bytes): the key the palette orders tie-break on.
      const w = (rgba[d] | (rgba[d + 1] << 8) | (rgba[d + 2] << 16) | (rgba[d + 3] << 24)) | 0;
      const k = counts.get(w);
      if (k === undefined) {
        if (counts.size === 256) many = true;
        else counts.set(w, 1);
      } else counts.set(w, k + 1);
    }
  }
  if (many) return { opaque, grey, colours: null };
  const colours: Colour[] = [];
  for (const [w, count] of counts) {
    colours.push({
      rgba: [w & 0xff, (w >>> 8) & 0xff, (w >>> 16) & 0xff, (w >>> 24) & 0xff],
      word: w, count,
    });
  }
  return { opaque, grey, colours };
}

// The one fully transparent value (grey or RGB) the image may key by tRNS
// instead of an alpha channel: every pixel opaque or that exact value at
// alpha 0, and no opaque pixel of the same value.
function transparentKey(rgba: Uint8Array, grey: boolean): number | null {
  let key = -1;
  for (let d = 0; d < rgba.length; d += 4) {
    const a = rgba[d + 3];
    if (a === 255) continue;
    if (a !== 0) return null;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (key === -1) key = v;
    else if (key !== v) return null;
  }
  if (key === -1) return null;
  for (let d = 0; d < rgba.length; d += 4) {
    if (rgba[d + 3] !== 255) continue;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (v === key) return null;
  }
  return key;
}

function samplesOf(rgba: Uint8Array, ct: number): Uint8Array {
  const n = rgba.length >>> 2;
  if (ct === 6) return rgba;
  const ch = ct === 0 ? 1 : ct === 4 ? 2 : 3;
  const out = new Uint8Array(n * ch);
  for (let i = 0, d = 0, s = 0; i < n; i++, d += 4, s += ch) {
    if (ct === 0) out[s] = rgba[d];
    else if (ct === 4) { out[s] = rgba[d]; out[s + 1] = rgba[d + 3]; }
    else { out[s] = rgba[d]; out[s + 1] = rgba[d + 1]; out[s + 2] = rgba[d + 2]; }
  }
  return out;
}

interface Form {
  colourType: number;
  bpp: number;
  samples: Uint8Array;
  plte: Uint8Array | null;
  trns: Uint8Array | null;
  filters: (number | 'minsum' | 'pairs')[];
}

function paletteForm(rgba: Uint8Array, colours: Colour[], order: 'count' | 'luminance'): Form {
  const lum = (c: Colour): number => 299 * c.rgba[0] + 587 * c.rgba[1] + 114 * c.rgba[2];
  const entries = [...colours].sort((x, y) => {
    const ta = x.rgba[3] === 255 ? 1 : 0;
    const tb = y.rgba[3] === 255 ? 1 : 0;
    if (ta !== tb) return ta - tb;
    if (ta === 0 && x.rgba[3] !== y.rgba[3]) return x.rgba[3] - y.rgba[3];
    if (order === 'luminance') return lum(x) - lum(y) || x.word - y.word;
    return y.count - x.count || x.word - y.word;
  });
  const index = new Map<number, number>(entries.map((c, i) => [c.word, i]));
  const plte = new Uint8Array(entries.length * 3);
  let transparent = 0;
  entries.forEach((c, i) => {
    plte[i * 3] = c.rgba[0]; plte[i * 3 + 1] = c.rgba[1]; plte[i * 3 + 2] = c.rgba[2];
    if (c.rgba[3] !== 255) transparent = i + 1;
  });
  const trns = transparent === 0 ? null : Uint8Array.from(entries.slice(0, transparent), (c) => c.rgba[3]);
  const n = rgba.length >>> 2;
  const indices = new Uint8Array(n);
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    const w = (rgba[d] | (rgba[d + 1] << 8) | (rgba[d + 2] << 16) | (rgba[d + 3] << 24)) | 0;
    indices[i] = index.get(w) as number;
  }
  return {
    colourType: 3, bpp: 1, samples: indices, plte, trns,
    filters: order === 'count' ? [0] : [0, 'minsum', 'pairs'],
  };
}

function formsOf(rgba: Uint8Array): Form[] {
  const { opaque, grey, colours } = analyse(rgba);
  const forms: Form[] = [];
  if (colours !== null) {
    forms.push(paletteForm(rgba, colours, 'count'));
    forms.push(paletteForm(rgba, colours, 'luminance'));
    if (!grey) return forms;
  }
  const key = opaque ? null : transparentKey(rgba, grey);
  let ct: number;
  let trns: Uint8Array | null = null;
  if (grey) {
    ct = opaque || key !== null ? 0 : 4;
    if (key !== null) trns = Uint8Array.of(0, key);
  } else {
    ct = opaque || key !== null ? 2 : 6;
    if (key !== null) trns = Uint8Array.of(0, key >>> 16, 0, (key >>> 8) & 0xff, 0, key & 0xff);
  }
  const bpp = { 0: 1, 2: 3, 4: 2, 6: 4 }[ct] as number;
  forms.push({ colourType: ct, bpp, samples: samplesOf(rgba, ct), plte: null, trns, filters: [0, 1, 2, 4, 'minsum', 'pairs'] });
  return forms;
}

// ---------------------------------------------------------------------------
// PNG row filters
// ---------------------------------------------------------------------------

function filterRow(type: number, cur: Uint8Array, prev: Uint8Array | null, bpp: number, out: Uint8Array): void {
  const n = cur.length;
  if (type === 0) { out.set(cur); return; }
  if (type === 1) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0);
  } else if (type === 2) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (prev === null ? 0 : prev[i]);
  } else if (type === 3) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1);
  } else {
    for (let i = 0; i < n; i++) {
      const a = i >= bpp ? cur[i - bpp] : 0;
      const b = prev === null ? 0 : prev[i];
      const c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
      out[i] = cur[i] - paeth(a, b, c);
    }
  }
}

function signedSum(row: Uint8Array): number {
  let s = 0;
  for (let i = 0; i < row.length; i++) { const v = row[i]; s += v < 128 ? v : 256 - v; }
  return s;
}

function pairsOf(row: Uint8Array, seen: Uint32Array, stamp: number): number {
  let n = 0;
  for (let i = 1; i < row.length; i++) {
    const pair = (row[i - 1] << 8) | row[i];
    if (seen[pair] !== stamp) { seen[pair] = stamp; n++; }
  }
  return n;
}

// The raw data of an image (height rows of width x bpp samples), each row
// behind its filter byte, by `choice`: a fixed filter type for every row, or
// 'minsum' / 'pairs' to pick each row's own filter by that heuristic.
function filtered(samples: Uint8Array, width: number, height: number, bpp: number, choice: number | 'minsum' | 'pairs'): Uint8Array {
  const stride = width * bpp;
  const raw = new Uint8Array(height * (stride + 1));
  const trial = [0, 1, 2, 3, 4].map(() => new Uint8Array(stride));
  const seen = new Uint32Array(65536);
  let stamp = 0;
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const at = y * (stride + 1);
    if (typeof choice === 'number') {
      raw[at] = choice;
      filterRow(choice, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
      continue;
    }
    let type = 0;
    let best = Infinity;
    for (let t = 0; t < 5; t++) {
      filterRow(t, cur, prev, bpp, trial[t]);
      const cost = choice === 'minsum' ? signedSum(trial[t]) : pairsOf(trial[t], seen, ++stamp);
      if (cost < best) { best = cost; type = t; }
    }
    raw[at] = type;
    raw.set(trial[type], at + 1);
  }
  return raw;
}

const SCREEN = Object.freeze({ level: 6, memLevel: 8, strategy: constants.Z_DEFAULT_STRATEGY });

function chunkBytes(form: Form): number {
  return (form.plte === null ? 0 : 12 + form.plte.length) + (form.trns === null ? 0 : 12 + form.trns.length);
}

interface Screened { form: Form; data: Uint8Array; bytes: number }

// The screen's winner for an image: its form and filter choice, the filtered
// data, and its weight (zlib level 6 stream plus PLTE/tRNS chunk bytes).
function screen(rgba: Uint8Array, width: number, height: number): Screened {
  let best: Screened | null = null;
  for (const form of formsOf(rgba)) {
    const chunks = chunkBytes(form);
    for (const choice of form.filters) {
      const data = filtered(form.samples, width, height, form.bpp, choice);
      const zlib = deflateSync(data, SCREEN);
      const bytes = zlib.length + chunks;
      if (best === null || bytes < best.bytes) best = { form, data, bytes };
    }
  }
  return best as Screened;
}

function pngOfForm(width: number, height: number, form: Form, idat: Uint8Array): Uint8Array {
  const chunks: [string, Uint8Array][] = [['IHDR', ihdrOf(width, height, form.colourType)]];
  if (form.plte !== null) chunks.push(['PLTE', form.plte]);
  if (form.trns !== null) chunks.push(['tRNS', form.trns]);
  chunks.push(['IDAT', idat]);
  chunks.push(['IEND', new Uint8Array(0)]);
  return pngOf(chunks);
}

// ---------------------------------------------------------------------------
// Optimal-parse DEFLATE: hash-chain LZ77, dynamic-programming parse,
// dynamic Huffman, emitted in blocks.
// ---------------------------------------------------------------------------

const MAX_CHAIN = 256;
const BLOCK_INPUT = 262144;
const DP_ROUNDS = 4;
const NEAR_DIST = 1024;

class BitWriter {
  buf: Uint8Array;
  at = 0;
  bitbuf = 0;
  bitcnt = 0;
  constructor(capacity: number) { this.buf = new Uint8Array(Math.max(64, capacity)); }
  private grow(): void {
    const nb = new Uint8Array(this.buf.length * 2);
    nb.set(this.buf);
    this.buf = nb;
  }
  writeBits(value: number, count: number): void {
    if (count === 0) return;
    this.bitbuf |= (value & ((1 << count) - 1)) << this.bitcnt;
    this.bitcnt += count;
    while (this.bitcnt >= 8) {
      if (this.at >= this.buf.length) this.grow();
      this.buf[this.at++] = this.bitbuf & 0xff;
      this.bitbuf >>>= 8;
      this.bitcnt -= 8;
    }
  }
  writeBit(b: number): void { this.writeBits(b, 1); }
  // A Huffman code is emitted most-significant bit first.
  writeCode(code: number, len: number): void {
    for (let i = len - 1; i >= 0; i--) this.writeBit((code >> i) & 1);
  }
  finish(): Uint8Array {
    if (this.bitcnt > 0) {
      if (this.at >= this.buf.length) this.grow();
      this.buf[this.at++] = this.bitbuf & 0xff;
      this.bitbuf = 0;
      this.bitcnt = 0;
    }
    return this.buf.subarray(0, this.at);
  }
}

// Huffman code lengths (at most maxLen bits) for `freq`, by the textbook
// tree build with the standard length-overflow fix, then assigning the
// shortest lengths to the most frequent symbols.
function buildLengths(freq: Uint32Array, maxLen: number): Uint8Array {
  const n = freq.length;
  const lengths = new Uint8Array(n);
  const syms: number[] = [];
  for (let s = 0; s < n; s++) if (freq[s] > 0) syms.push(s);
  if (syms.length === 0) return lengths;
  if (syms.length === 1) { lengths[syms[0]] = 1; return lengths; }
  const m = syms.length;
  const nodeFreq = new Float64Array(2 * m);
  const nodeParent = new Int32Array(2 * m).fill(-1);
  for (let i = 0; i < m; i++) nodeFreq[i] = freq[syms[i]];
  const active: number[] = [];
  for (let i = 0; i < m; i++) active.push(i);
  let next = m;
  while (active.length > 1) {
    let i1 = 0;
    let i2 = 1;
    if (nodeFreq[active[i1]] > nodeFreq[active[i2]]) { const t = i1; i1 = i2; i2 = t; }
    for (let k = 2; k < active.length; k++) {
      const f = nodeFreq[active[k]];
      if (f < nodeFreq[active[i1]]) { i2 = i1; i1 = k; }
      else if (f < nodeFreq[active[i2]]) { i2 = k; }
    }
    const a = active[i1];
    const b = active[i2];
    nodeFreq[next] = nodeFreq[a] + nodeFreq[b];
    nodeParent[a] = next;
    nodeParent[b] = next;
    active.splice(Math.max(i1, i2), 1);
    active.splice(Math.min(i1, i2), 1);
    active.push(next);
    next++;
  }
  const depth = new Int32Array(m);
  for (let i = 0; i < m; i++) {
    let d = 0;
    let x = i;
    while (nodeParent[x] !== -1) { d++; x = nodeParent[x]; }
    depth[i] = d;
  }
  const blCount = new Int32Array(maxLen + 1);
  let overflow = 0;
  for (let i = 0; i < m; i++) {
    if (depth[i] > maxLen) { overflow++; blCount[maxLen]++; }
    else blCount[depth[i]]++;
  }
  while (overflow > 0) {
    let mm = maxLen - 1;
    while (mm > 0 && blCount[mm] === 0) mm--;
    if (mm === 0) break;
    blCount[mm]--;
    blCount[mm + 1] += 2;
    blCount[maxLen]--;
    overflow -= 2;
  }
  const order = [...syms].sort((a, b) => freq[b] - freq[a]);
  let idx = 0;
  for (let l = 1; l <= maxLen; l++) {
    for (let k = 0; k < blCount[l]; k++) lengths[order[idx++]] = l;
  }
  return lengths;
}

// Canonical Huffman codes for `lengths`: codes of one length are assigned in
// symbol order, each length's first code continuing from the last.
function canonicalCodes(lengths: Uint8Array): Uint32Array {
  let maxLen = 0;
  for (const l of lengths) if (l > maxLen) maxLen = l;
  const blCount = new Uint32Array(maxLen + 1);
  for (const l of lengths) if (l) blCount[l]++;
  const nextCode = new Uint32Array(maxLen + 1);
  let code = 0;
  for (let l = 1; l <= maxLen; l++) { code = (code + blCount[l - 1]) << 1; nextCode[l] = code; }
  const codes = new Uint32Array(lengths.length);
  for (let s = 0; s < lengths.length; s++) {
    const l = lengths[s];
    if (l) codes[s] = nextCode[l]++;
  }
  return codes;
}

function ensureTwo(freq: Uint32Array): void {
  let n = 0;
  for (let s = 0; s < freq.length; s++) if (freq[s] > 0) n++;
  let need = 2 - n;
  for (let s = 0; s < freq.length && need > 0; s++) {
    if (freq[s] === 0) { freq[s] = 1; need--; }
  }
}

// The longest match at every position (length and distance), found once by
// hash chains and reused by every parse round. Also the longest match at a
// near distance (<= NEAR_DIST): a slightly shorter near match often costs
// less than the longest far one, so the parse tries both.
function findMatches(data: Uint8Array): { mlen: Uint16Array; mdist: Int32Array; nlen: Uint16Array; ndist: Int32Array } {
  const n = data.length;
  const mlen = new Uint16Array(n);
  const mdist = new Int32Array(n);
  const nlen = new Uint16Array(n);
  const ndist = new Int32Array(n);
  const head = new Int32Array(1 << 15).fill(-1);
  const prev = new Int32Array(n).fill(-1);
  for (let i = 0; i < n; i++) {
    if (i + 2 >= n) continue;
    const h = ((data[i] << 10) ^ (data[i + 1] << 5) ^ data[i + 2]) & 0x7fff;
    const maxLen = Math.min(258, n - i);
    let best = 0;
    let bestDist = 0;
    let near = 0;
    let nearDist = 0;
    let cand = head[h];
    let checked = 0;
    while (cand >= 0 && checked < MAX_CHAIN) {
      const d = i - cand;
      if (d > 32768) break;
      if (best === 0 || data[cand + best] === data[i + best]) {
        let l = 0;
        while (l < maxLen && data[cand + l] === data[i + l]) l++;
        if (l > best) {
          best = l;
          bestDist = d;
          if (l >= 258) break;
        }
        if (d <= NEAR_DIST && l > near) { near = l; nearDist = d; }
      }
      cand = prev[cand];
      checked++;
      if (best >= 128 && checked >= 8) break;
    }
    if (best >= 3) { mlen[i] = best; mdist[i] = bestDist; }
    if (near >= 3) { nlen[i] = near; ndist[i] = nearDist; }
    prev[i] = head[h];
    head[h] = i;
  }
  return { mlen, mdist, nlen, ndist };
}

interface Tokens { kind: Uint8Array; val: Int32Array; dist: Int32Array; count: number }

// The cheapest parse of `data` under the given Huffman costs: at each
// position a literal, or a match of a length-code-boundary length (or the
// longest) at the best distance found there.
function optimalParse(data: Uint8Array, mlen: Uint16Array, mdist: Int32Array, nlen: Uint16Array, ndist: Int32Array, litLen: Uint8Array, distLen: Uint8Array): Tokens {
  const n = data.length;
  const lenCost = new Float64Array(259);
  for (let l = 3; l <= 258; l++) lenCost[l] = litLen[LEN_SYM[l]] + LEN_EXT[l];
  const distCost = new Float64Array(32769);
  for (let d = 1; d <= 32768; d++) distCost[d] = distLen[DIST_SYM[d]] + DIST_EXT[d];
  const cost = new Float64Array(n + 1).fill(Infinity);
  const choiceLen = new Uint16Array(n + 1);
  const choiceDist = new Int32Array(n + 1);
  cost[0] = 0;
  const relax = (i: number, c: number, L: number, d: number): void => {
    const dc = distCost[d];
    for (let b = 0; b < LEN_BOUNDS.length; b++) {
      const l2 = LEN_BOUNDS[b];
      if (l2 > L) break;
      const nc2 = c + lenCost[l2] + dc;
      if (nc2 < cost[i + l2]) { cost[i + l2] = nc2; choiceLen[i + l2] = l2; choiceDist[i + l2] = d; }
    }
    if (L < 258 && LEN_BOUNDS.indexOf(L) === -1) {
      const nc2 = c + lenCost[L] + dc;
      if (nc2 < cost[i + L]) { cost[i + L] = nc2; choiceLen[i + L] = L; choiceDist[i + L] = d; }
    }
  };
  for (let i = 0; i < n; i++) {
    const c = cost[i];
    if (c === Infinity) continue;
    const nc = c + litLen[data[i]];
    if (nc < cost[i + 1]) { cost[i + 1] = nc; choiceLen[i + 1] = 1; choiceDist[i + 1] = 0; }
    const L = mlen[i];
    if (L >= 3) relax(i, c, L, mdist[i]);
    const NL = nlen[i];
    if (NL >= 3 && ndist[i] !== mdist[i]) relax(i, c, NL, ndist[i]);
  }
  const kind: number[] = [];
  const val: number[] = [];
  const dist: number[] = [];
  let i = n;
  while (i > 0) {
    const l = choiceLen[i];
    if (l === 0) throw new Error('optimal parse backtrack failed');
    if (l === 1) { kind.push(0); val.push(data[i - 1]); dist.push(0); i -= 1; }
    else { kind.push(1); val.push(l); dist.push(choiceDist[i]); i -= l; }
  }
  kind.reverse();
  val.reverse();
  dist.reverse();
  return { kind: Uint8Array.from(kind), val: Int32Array.from(val), dist: Int32Array.from(dist), count: kind.length };
}

function tokenFreqs(t: Tokens): { lit: Uint32Array; dist: Uint32Array } {
  const lit = new Uint32Array(288);
  const dist = new Uint32Array(32);
  for (let k = 0; k < t.count; k++) {
    if (t.kind[k] === 0) lit[t.val[k]]++;
    else { lit[LEN_SYM[t.val[k]]]++; dist[DIST_SYM[t.dist[k]]]++; }
  }
  return { lit, dist };
}

function tokensCost(t: Tokens, litLen: Uint8Array, distLen: Uint8Array): number {
  let bits = 0;
  for (let k = 0; k < t.count; k++) {
    if (t.kind[k] === 0) bits += litLen[t.val[k]];
    else bits += litLen[LEN_SYM[t.val[k]]] + LEN_EXT[t.val[k]] + distLen[DIST_SYM[t.dist[k]]] + DIST_EXT[t.dist[k]];
  }
  return bits;
}

// The code-length alphabet sequence for a run of code lengths: literal
// lengths, 16 to repeat the previous length 3-6 times, 17 for 3-10 zeros,
// 18 for 11-138 zeros.
function codeLengthSequence(lengths: Uint8Array): { sym: number; extra: number }[] {
  const seq: { sym: number; extra: number }[] = [];
  let i = 0;
  while (i < lengths.length) {
    const v = lengths[i];
    let run = 1;
    while (i + run < lengths.length && lengths[i + run] === v) run++;
    if (v === 0) {
      let r = run;
      while (r >= 11) { const c = Math.min(r, 138); seq.push({ sym: 18, extra: c - 11 }); r -= c; }
      if (r >= 3) { seq.push({ sym: 17, extra: r - 3 }); r = 0; }
      while (r > 0) { seq.push({ sym: 0, extra: 0 }); r--; }
    } else {
      seq.push({ sym: v, extra: 0 });
      let r = run - 1;
      while (r >= 3) { const c = Math.min(r, 6); seq.push({ sym: 16, extra: c - 3 }); r -= c; }
      while (r > 0) { seq.push({ sym: v, extra: 0 }); r--; }
    }
    i += run;
  }
  return seq;
}

function emitToken(bw: BitWriter, litCodes: Uint32Array, litLen: Uint8Array, distCodes: Uint32Array, distLen: Uint8Array, kind: number, val: number, dist: number): void {
  if (kind === 0) {
    bw.writeCode(litCodes[val], litLen[val]);
  } else {
    const ls = LEN_SYM[val];
    bw.writeCode(litCodes[ls], litLen[ls]);
    const le = LEN_EXT[val];
    if (le) bw.writeBits(val - LEN_BASE[ls - 257], le);
    const ds = DIST_SYM[dist];
    bw.writeCode(distCodes[ds], distLen[ds]);
    const de = DIST_EXT[dist];
    if (de) bw.writeBits(dist - DIST_BASE[ds], de);
  }
}

function emitBlock(bw: BitWriter, t: Tokens, s: number, e: number, isFinal: boolean): void {
  const lit = new Uint32Array(288);
  const dist = new Uint32Array(32);
  let fixedBits = 3 + 7;
  for (let k = s; k < e; k++) {
    if (t.kind[k] === 0) {
      lit[t.val[k]]++;
      fixedBits += FIXED_LIT_LEN[t.val[k]];
    } else {
      const l = t.val[k];
      const d = t.dist[k];
      lit[LEN_SYM[l]]++;
      dist[DIST_SYM[d]]++;
      fixedBits += FIXED_LIT_LEN[LEN_SYM[l]] + LEN_EXT[l] + FIXED_DIST_LEN[DIST_SYM[d]] + DIST_EXT[d];
    }
  }
  lit[256]++;
  ensureTwo(lit);
  ensureTwo(dist);
  const litLen = buildLengths(lit, 15);
  const distLen = buildLengths(dist, 15);
  let hlit = 288;
  while (hlit > 257 && litLen[hlit - 1] === 0) hlit--;
  let hdist = 32;
  while (hdist > 1 && distLen[hdist - 1] === 0) hdist--;
  const all = new Uint8Array(hlit + hdist);
  all.set(litLen.subarray(0, hlit), 0);
  all.set(distLen.subarray(0, hdist), hlit);
  const seq = codeLengthSequence(all);
  const clFreq = new Uint32Array(19);
  for (const it of seq) clFreq[it.sym]++;
  ensureTwo(clFreq);
  const clLen = buildLengths(clFreq, 7);
  let hclen = 19;
  while (hclen > 4 && clLen[CL_ORDER[hclen - 1]] === 0) hclen--;
  const clCodes = canonicalCodes(clLen);
  let dynBits = 3 + 5 + 5 + 4 + 3 * hclen;
  for (const it of seq) {
    dynBits += clLen[it.sym];
    if (it.sym === 16) dynBits += 2;
    else if (it.sym === 17) dynBits += 3;
    else if (it.sym === 18) dynBits += 7;
  }
  for (let k = s; k < e; k++) {
    if (t.kind[k] === 0) dynBits += litLen[t.val[k]];
    else dynBits += litLen[LEN_SYM[t.val[k]]] + LEN_EXT[t.val[k]] + distLen[DIST_SYM[t.dist[k]]] + DIST_EXT[t.dist[k]];
  }
  dynBits += litLen[256];
  if (fixedBits <= dynBits) {
    bw.writeBits(isFinal ? 1 : 0, 1);
    bw.writeBits(1, 2);
    const fLit = canonicalCodes(FIXED_LIT_LEN);
    const fDist = canonicalCodes(FIXED_DIST_LEN);
    for (let k = s; k < e; k++) emitToken(bw, fLit, FIXED_LIT_LEN, fDist, FIXED_DIST_LEN, t.kind[k], t.val[k], t.dist[k]);
    bw.writeCode(fLit[256], 7);
  } else {
    bw.writeBits(isFinal ? 1 : 0, 1);
    bw.writeBits(2, 2);
    bw.writeBits(hlit - 257, 5);
    bw.writeBits(hdist - 1, 5);
    bw.writeBits(hclen - 4, 4);
    for (let j = 0; j < hclen; j++) bw.writeBits(clLen[CL_ORDER[j]], 3);
    for (const it of seq) {
      bw.writeCode(clCodes[it.sym], clLen[it.sym]);
      if (it.sym === 16) bw.writeBits(it.extra, 2);
      else if (it.sym === 17) bw.writeBits(it.extra, 3);
      else if (it.sym === 18) bw.writeBits(it.extra, 7);
    }
    const lCodes = canonicalCodes(litLen);
    const dCodes = canonicalCodes(distLen);
    for (let k = s; k < e; k++) emitToken(bw, lCodes, litLen, dCodes, distLen, t.kind[k], t.val[k], t.dist[k]);
    bw.writeCode(lCodes[256], litLen[256]);
  }
}

function emitTokens(bw: BitWriter, t: Tokens): void {
  const blocks: [number, number][] = [];
  let start = 0;
  let pos = 0;
  let blockStartPos = 0;
  for (let k = 0; k < t.count; k++) {
    pos += t.kind[k] === 0 ? 1 : t.val[k];
    if (pos - blockStartPos >= BLOCK_INPUT) {
      blocks.push([start, k + 1]);
      start = k + 1;
      blockStartPos = pos;
    }
  }
  if (start < t.count) blocks.push([start, t.count]);
  if (blocks.length === 0) blocks.push([0, 0]);
  for (let b = 0; b < blocks.length; b++) {
    const [s, e] = blocks[b];
    emitBlock(bw, t, s, e, b === blocks.length - 1);
  }
}

// A zlib stream of `data` from the optimal parser, or null when anything
// fails (the caller falls back to Node's zlib). The output is validated by
// inflating it and comparing it byte for byte with the input.
export function deflateOptimal(data: Uint8Array): Uint8Array | null {
  try {
    if (data.length === 0) return null;
    const { mlen, mdist, nlen, ndist } = findMatches(data);
    let litLen = FIXED_LIT_LEN;
    let distLen = FIXED_DIST_LEN;
    let bestTokens: Tokens | null = null;
    let bestCost = Infinity;
    for (let round = 0; round < DP_ROUNDS; round++) {
      const tokens = optimalParse(data, mlen, mdist, nlen, ndist, litLen, distLen);
      const { lit, dist } = tokenFreqs(tokens);
      lit[256]++;
      ensureTwo(lit);
      ensureTwo(dist);
      const newLitLen = buildLengths(lit, 15);
      const newDistLen = buildLengths(dist, 15);
      const c = tokensCost(tokens, newLitLen, newDistLen);
      if (c < bestCost) { bestCost = c; bestTokens = tokens; }
      litLen = newLitLen;
      distLen = newDistLen;
    }
    if (bestTokens === null) return null;
    const bw = new BitWriter(data.length + 1024);
    emitTokens(bw, bestTokens);
    const raw = bw.finish();
    const out = new Uint8Array(raw.length + 6);
    out[0] = 0x78;
    out[1] = 0xda;
    out.set(raw, 2);
    const ad = adler32(data);
    out[out.length - 4] = (ad >>> 24) & 0xff;
    out[out.length - 3] = (ad >>> 16) & 0xff;
    out[out.length - 2] = (ad >>> 8) & 0xff;
    out[out.length - 1] = ad & 0xff;
    const back = inflateSync(out);
    if (back.length !== data.length || !back.equals(data)) return null;
    return out;
  } catch {
    return null;
  }
}

// ---------------------------------------------------------------------------
// Per-image squeeze and the entry point
// ---------------------------------------------------------------------------

export function squeezeImage(rgba: Uint8Array, width: number, height: number): Uint8Array {
  const best = screen(rgba, width, height);
  const opt = deflateOptimal(best.data);
  const z9 = deflateSync(best.data, { level: 9, memLevel: 9 });
  const z9f = deflateSync(best.data, { level: 9, memLevel: 9, strategy: constants.Z_FILTERED });
  let stream: Uint8Array = z9.length <= z9f.length ? z9 : z9f;
  if (opt !== null && opt.length < stream.length) stream = opt;
  return pngOfForm(width, height, best.form, stream);
}

function main(): void {
  const INPUT = process.env.MAKEFUN_INPUT_DIR ?? '/input';
  const OUTPUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
  for (const id of readdirSync(INPUT).sort()) {
    const image = decodePng(new Uint8Array(readFileSync(join(INPUT, id, 'image.png'))));
    mkdirSync(join(OUTPUT, id), { recursive: true });
    writeFileSync(join(OUTPUT, id, 'image.png'), squeezeImage(image.rgba, image.width, image.height));
  }
}

export { decodePng };

import { pathToFileURL } from 'node:url';
if (process.argv[1] !== undefined && import.meta.url === pathToFileURL(process.argv[1]).href) {
  main();
}
