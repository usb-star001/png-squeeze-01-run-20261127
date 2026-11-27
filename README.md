[![make.fun · png-squeeze-01-run-20261127](https://make.fun/badge/png-squeeze-01-run-20261127.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127?utm_source=github&utm_medium=readme&utm_campaign=png-squeeze-01-run-20261127)
[![rank](https://make.fun/badge/png-squeeze-01-run-20261127/usb-star001/png-squeeze-01-run-20261127/rank.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=png-squeeze-01-run-20261127)
[![reward](https://make.fun/badge/png-squeeze-01-run-20261127/usb-star001/png-squeeze-01-run-20261127/reward.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127?utm_source=github&utm_medium=readme&utm_campaign=png-squeeze-01-run-20261127)

# PNG Squeeze

A lossless PNG optimizer for make.fun's "Squeeze screenshots into the smallest PNG, 27 November 2026" bounty. It reads 8 screenshots of 1280x720 RGBA from `/input/<id>/image.png` and writes the same images as the smallest valid PNGs it can to `/output/<id>/image.png`, in one run of at most 60 seconds for the whole set.

## How it works

1. **Exact form reduction.** Each image is decoded to RGBA, then written in its cheapest exact form: palette (at most 256 colours, transparent entries first), grey or grey+alpha when every pixel is grey, RGB or RGBA otherwise, with a tRNS key when a single fully transparent value covers all alpha.
2. **Per-row filters.** Each row gets its own PNG filter (None, Sub, Up, Average, Paeth), chosen by the minimum-sum and fewest-pairs heuristics and ranked by zlib level 6 size, the way the kit's scale compressor screens them.
3. **Optimal-parse DEFLATE.** The filtered bytes are compressed with a from-scratch optimal-parse DEFLATE encoder: hash-chain LZ77 (longest match plus a near-distance alternative), dynamic-programming parse over length-code boundaries, iterated Huffman cost refinement, and per-block fixed-vs-dynamic Huffman emission. The output is validated by inflating it and comparing it byte for byte, and Node's zlib level 9 is kept as a fallback whenever it is smaller.

Deterministic: no clock, no randomness, no environment-dependent choices, so two runs write identical bytes.

## Run

```sh
node main.ts
```

It reads `MAKEFUN_INPUT_DIR` (default `/input`) and writes `MAKEFUN_OUTPUT_DIR` (default `/output`). Only Node's built-in modules are used; nothing is installed.

## Practice-set score

722,939 of 1,000,000 on the kit's practice set (all 8 instances answered, passed), against the house baseline fixed-paeth 1.0.0 at 420,399. Entry: `main.ts` (MIT).
