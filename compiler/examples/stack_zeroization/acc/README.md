# Stack zeroization for ACC: simulator harness

Functional test for the three ACC stack zeroization strategies (`loop`,
`unrolled`, and the unverified `loophw`) at both supported clear steps
(`u32` and `u256`), per `plan_ACC_SZ.md` (repo root), Phase 1.6.

`sz.jazz` defines six export functions, `sz_<strategy>_<width>(reg u32
secret) -> reg u32`, one per (strategy, width) pair. Each fills its own
64-byte stack frame with a value derived from `secret`, reads every word of
the frame back into a running sum (so the compiler cannot dead-code-
eliminate the stores -- the read-back is what keeps the frame "used"), and
returns the sum. No `#[stackzerosize=...]` annotation is set on any
function, so the clear step is whatever the stack allocator's default
alignment (`lfd_align`) picks for the frame. Confirmed by a real compile:
this is driven by the frame's *actual access widths*, not its *declared*
element type -- a `stack u256[2]` array touched only through `:u32`-sized
accesses gets a plain 4-byte-aligned, `sw`-based frame just like a `stack
u32[16]` would. The three u256 functions below therefore each perform two
"anchor" writes of a zeroed `reg u256` (from `#set0_256()`) at natural
u256 width before doing their actual `secret`-dependent bookkeeping through
`:u32`-sized sub-accesses on the same array; this alone is enough to make
the stack allocator infer 32-byte alignment and hence the `u256` (`bn.sd`)
clear step. See the comment at the top of `sz.jazz` and
`notes_ACC_SZ_asm.md` (repo root) for the parallel finding in the opposite
direction (`stackzero_step_above_align.jazz`: you also cannot force a
*stricter* alignment than the access pattern needs via `#[stackalign=...]`).

`test.sh` runs each function on the ACC simulator with a small driver that:

- sets the stack pointer to a fixed value with room for the frame and 32
  bytes of untouched memory on each side;
- fills 12 callee-saved registers (x8, x9, x18..x27) and 16 words of memory
  around the frame with distinct sentinel values;
- calls the function with a fixed secret argument, then halts.

`check.py` then verifies, from the simulator's `--dump-dmem` and
`--dump-regs` output, that: the whole frame reads back as zero (the
zeroization code ran), the neighbor sentinel words are untouched (it did
not overrun), every callee-saved register and the stack pointer still hold
their sentinel/entry value (the epilogue did not clobber them), and the
returned checksum matches an independently computed expectation.

This is the only execution-level check the unverified `loophw` strategy
gets in this plan (Part 2's proofs admit that branch): if a `loophw` run
stops early, look at the simulator's reported error (loop count 0, a bad
data address, or loop-stack misuse are the likely causes, per
`plan_ACC_SZ.md` Section 1.4's "Hardware loop" bullet).

## Compile

```sh
../../../jasminc -arch acc sz.jazz -o sz.s
```

Or just check it assembles with the real toolchain:

```sh
../../../scripts/check-acc sz.jazz
```

## Functional test

```sh
sh test.sh
```

It needs `python3` and the ACC toolchain env vars `$ACC_AS`, `$ACC_LD`,
`$ACC_SIM`. Build artifacts land in `build/` (git-ignored, see the repo
root `.gitignore`).

Files:

- `sz.jazz`  -- the six functions under test.
- `gen.py`   -- writes each function's driver and its expected-value file.
- `check.py` -- checks one function's simulator dump against expectations.
- `test.sh`  -- runs the whole pipeline for all six functions.

## Verification status

Confirmed end to end by a real run (2026-09-23): `sh test.sh` compiles
`sz.jazz`, assembles/links all six drivers with the real ACC toolchain, runs
each on the standalone simulator, and all six `check.py` checks pass,
including both `loophw` functions (the only execution-level check the
hardware loop strategy gets in this plan). Notes from that run:

- `stk_max` (`S` in `gen.py`) is confirmed 64 bytes for all six functions,
  from the real `li x6, 64` prologue instruction.
- The initial version of `sz.jazz`'s u256 functions used only
  `:u32`-sized array accesses; a real compile showed this produces a plain
  4-byte-aligned, `sw`-based frame (the declared array type alone does not
  drive the clear step -- see the paragraph above). Fixed by adding two
  natural-width "anchor" writes per function; all three u256 functions now
  correctly emit `bn.xor`/`bn.sd`-based zeroization code.
- `check.py`'s `parse_regs` (a permissive regex, since
  `../../gimli/acc/check.py` does not parse `--dump-regs` at all) works
  correctly against the real format, which is line-oriented:
  ` xN  = 0xHHHHHHHH` (plus ` ERR_BITS`/` INSN_CNT`/` STOP_PC` lines at the
  top, which `parse_regs` correctly ignores).
- Running the ACC toolchain in this environment requires
  `pavona.pavona/.venv/bin` ahead of this repo's own Python virtualenv on
  `PATH`: `acc_ld.py`'s `#!/usr/bin/env python3` shebang otherwise resolves
  to a `python3` that lacks the `mako` package it needs (this affects
  `../../gimli/acc/test.sh` identically; it is an environment-setup detail
  unrelated to this harness).
