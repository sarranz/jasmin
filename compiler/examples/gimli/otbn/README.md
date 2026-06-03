# Gimli for OTBN

Two implementations of the [Gimli](https://gimli.cr.yp.to/) permutation for
OTBN:

- **`gimli.jazz`** -- scalar, using only the base (RISC-V) instruction set of
  the ISA (no wide `BN.*`). OTBN's base core is a 32-bit RISC-V (RV32I-like)
  machine, so this is essentially the RISC-V implementation
  (`../risc-v/gimli.jazz`): the 12-word state lives in a `u32[12]` array
  accessed with `lw`/`sw`, and the round logic uses
  `add`/`xor`/`and`/`or`/shift. OTBN has no rotate, so the column rotations are
  built from two shifts and an `or`.

- **`gimliv.jazz`** -- vectorized, using the wide big-number vector
  instructions, after the x86-64 SSE version (`../x86-64/gimliv.jinc`). Each of
  the three Gimli rows is kept in the low four u32 lanes of a 256-bit WDR.
  Per-lane shifts/rotates use `BN.SHV.8S`, the SP-box mixing uses
  `BN.AND/OR/XOR`, and the small/big column swaps (the SSE `VPSHUFD`) use
  `BN.TRN`. `BN.SHV` and `BN.TRN` are PQC-mode instructions, so the simulator
  must run with `--pqc`.

## Compile

```sh
../../../jasminc -arch otbn gimli.jazz  -o gimli.s
../../../jasminc -arch otbn gimliv.jazz -o gimliv.s
```

Or just check they assemble with the real toolchain:

```sh
../../../scripts/check-otbn gimli.jazz
../../../scripts/check-otbn gimliv.jazz
```

## Functional test

`test.sh` compiles each implementation, links it with a small driver, runs it
on the ACC/OTBN standalone simulator, and compares the result of one
permutation of the canonical Gimli test input against an independent reference
(`gen.py`).

```sh
sh test.sh
```

It needs `python3` and the ACC toolchain env vars `$ACC_AS`, `$ACC_LD`,
`$ACC_SIM`. Build artifacts land in `build/` (git-ignored).

Files:

- `gimli.jazz`  -- scalar (base RISC-V ISA) implementation.
- `gimliv.jazz` -- vectorized (wide PQC vector ISA) implementation.
- `gen.py`  -- reference Gimli; emits the drivers and `build/expected.txt`.
- `check.py` -- compares the simulator's DMEM dump to the expected vector.
- `test.sh` -- runs the whole pipeline for both implementations.
