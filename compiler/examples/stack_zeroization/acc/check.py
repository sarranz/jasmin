#!/usr/bin/env python3
"""Check one sz_<strategy>_<width> simulator run for the ACC stack
zeroization harness (plan_ACC_SZ.md, Phase 1.6).

Usage: check.py <build-dir> <fn>

Reads <build-dir>/expected_<fn>.txt, <build-dir>/dmem_<fn>.bin (the ACC
simulator's --dump-dmem output) and <build-dir>/regs_<fn>.txt (its
--dump-regs output), and checks:
  1. every word of the S-byte frame just below the SP top is validity=1,
     value=0 (the compiler's appended zeroization code ran);
  2. the 16 neighbor words (8 just below the frame, 8 just above the SP
     top) still hold the memory sentinel (the zeroization code did not
     overrun);
  3. x2 is still the SP top and every callee-saved register still holds
     its sentinel (the epilogue did not clobber anything it should not
     have);
  4. x10 holds the expected return value.

Prints a table and exits non-zero on any mismatch.

VERIFIED BY A REAL RUN (2026-09-23): the actual --dump-regs format is
line-oriented, e.g. " x10 = 0x23456780" (also " ERR_BITS = 0x...",
" INSN_CNT = 0x...", " STOP_PC = 0x..." at the top, which parse_regs()
below ignores since they don't match "x<digits>"). parse_regs()'s
permissive regex handles this format correctly; all six sz_* functions
pass end to end on the standalone simulator, including both loophw
functions (the only execution-level check the hardware loop strategy
gets).
"""
import re
import sys

NEIGHBOR_WORDS = 8   # words checked on each side of the frame (fixed by the
                      # plan at 32 bytes = 8 words, independent of S).


def read_expected(path):
    vals = {}
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            key, val = line.split(None, 1)
            vals[key] = val
    return {
        "secret": int(vals["secret"], 16),
        "ret": int(vals["return"], 16),
        "S": int(vals["S"]),
        "top": int(vals["top"], 16),
        "mem_sentinel": int(vals["mem_sentinel"], 16),
        "callee": {
            int(k[1:]): int(v, 16)
            for k, v in vals.items()
            if k.startswith("x")
        },
    }


def read_dmem(path):
    with open(path, "rb") as f:
        return f.read()


def dmem_word(raw, addr):
    """5 bytes per 32-bit word: 1 validity byte then 4 little-endian data
    bytes (plan_ACC_SZ.md Section 1.4's "Simulator" bullet); word index is
    the byte address divided by 4, as in compiler/examples/gimli/acc/
    check.py's word_at()."""
    i = addr // 4
    rec = raw[i * 5:i * 5 + 5]
    valid = rec[0]
    data = rec[1] | (rec[2] << 8) | (rec[3] << 16) | (rec[4] << 24)
    return data, valid


def parse_regs(path):
    """UNVERIFIED, see module docstring. Accepts any occurrence of 'x<N>'
    (case-insensitive) followed by an optional '='/':' and a hex value
    (with or without a '0x' prefix), anywhere in the file; the last
    occurrence for a given register wins, in case the dump lists register
    state more than once (e.g. an initial and a final snapshot)."""
    regs = {}
    pat = re.compile(
        r"\bx(\d{1,2})\b\s*[:=]?\s*(?:0x)?([0-9a-fA-F]{1,8})\b",
        re.IGNORECASE)
    with open(path) as f:
        for line in f:
            for m in pat.finditer(line):
                regs[int(m.group(1))] = int(m.group(2), 16)
    return regs


def main():
    workdir = sys.argv[1]
    fn = sys.argv[2]

    exp = read_expected("%s/expected_%s.txt" % (workdir, fn))
    raw = read_dmem("%s/dmem_%s.bin" % (workdir, fn))
    regs = parse_regs("%s/regs_%s.txt" % (workdir, fn))

    ok = [True]

    def check(label, cond, detail):
        ok[0] = ok[0] and cond
        print("%-40s %-8s %s" % (label, "OK" if cond else "MISMATCH", detail))

    print("[%s]" % fn)
    print("secret=0x%08x expected return=0x%08x S=%d" %
          (exp["secret"], exp["ret"], exp["S"]))
    print()

    # 1. every word of the frame reads back as zero.
    frame_base = exp["top"] - exp["S"]
    frame_words = exp["S"] // 4
    for k in range(frame_words):
        addr = frame_base + 4 * k
        data, valid = dmem_word(raw, addr)
        check("frame[0x%x]" % addr, valid == 1 and data == 0,
              "valid=%d data=0x%08x (want valid=1 data=0)" % (valid, data))

    # 2. the 8 neighbor words below the frame and the 8 above the SP top
    # still hold the memory sentinel.
    below_base = frame_base - 32
    above_base = exp["top"]
    for label, base in (("below", below_base), ("above", above_base)):
        for k in range(NEIGHBOR_WORDS):
            addr = base + 4 * k
            data, valid = dmem_word(raw, addr)
            check("%s[0x%x]" % (label, addr), data == exp["mem_sentinel"],
                  "data=0x%08x (want 0x%08x)" % (data, exp["mem_sentinel"]))

    # 3. SP and every callee-saved register.
    x2 = regs.get(2)
    check("x2 (SP)", x2 == exp["top"],
          "got %s want 0x%x" %
          ("0x%08x" % x2 if x2 is not None else "not found", exp["top"]))
    for r in sorted(exp["callee"]):
        want = exp["callee"][r]
        got = regs.get(r)
        check("x%d (callee-saved)" % r, got == want,
              "got %s want 0x%08x" %
              ("0x%08x" % got if got is not None else "not found", want))

    # 4. return value.
    x10 = regs.get(10)
    check("x10 (return value)", x10 == exp["ret"],
          "got %s want 0x%08x" %
          ("0x%08x" % x10 if x10 is not None else "not found", exp["ret"]))

    print()
    if ok[0]:
        print("RESULT: PASS -- %s" % fn)
    else:
        print("RESULT: FAIL -- %s" % fn)
    sys.exit(0 if ok[0] else 1)


if __name__ == "__main__":
    main()
