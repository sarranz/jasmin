#!/usr/bin/env python3
"""Generate the ACC test drivers and expected-value files for the stack
zeroization simulator harness (plan_ACC_SZ.md, Phase 1.6).

For each of the six sz_<strategy>_<width> functions in sz.jazz, writes
driver_<fn>.s (a standalone RV32-style assembly file that sets up sentinel
register/memory values, calls the function, and halts) and
expected_<fn>.txt (the secret passed in, the expected return value, and
the sentinel/geometry constants check.py needs).

Usage: gen.py <build-dir>

VERIFIED BY A REAL COMPILE (2026-09-23): S below is stk_max in bytes,
confirmed as 64 for all six sz_* functions via the real `li x6, 64`
prologue instruction in the compiled sz.s.
"""
import sys

TOP = 0x4000               # SP entry value: 32-byte aligned, well inside DMEM.
S = 64                      # stk_max in bytes, confirmed by a real compile.
MEM_SENTINEL = 0xA5A5A5A5   # neighbor-word sentinel value.
CALLEE_SAVED = [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

STRATEGIES = ["loop", "unrolled", "loophw"]
WIDTHS = ["u32", "u256"]
FUNCTIONS = [
    "sz_%s_%s" % (strat, width) for width in WIDTHS for strat in STRATEGIES
]

BASE_SECRET = 0x12345678


def reg_sentinel(r):
    """A distinct, easily-recognisable sentinel per callee-saved register."""
    return 0xCEE00000 | r


def expected_return(secret):
    """Mirrors sz.jazz's body: 16 words all holding `secret`, summed back
    with ordinary 32-bit wraparound. All six functions share this exact
    read/write/sum shape -- only the array's declared element type and the
    #[stackzero=...] annotation differ, so one formula covers all six."""
    return (secret * 16) & 0xFFFFFFFF


def emit_driver(path, fn, secret):
    below_base = TOP - S - 32
    above_base = TOP

    lines = [
        "\t.section .text.start",
        "\t.globl _start",
        "_start:",
        "\t# SP top: 32-byte aligned, S=%d bytes of frame below it, 32" % S,
        "\t# bytes of neighbor sentinels on each side, all inside DMEM.",
        "\tli   x2, 0x%x" % TOP,
        "",
        "\t# Distinct sentinels in every callee-saved register except x2",
        "\t# (already the SP set above).",
    ]
    for r in CALLEE_SAVED:
        lines.append("\tli   x%d, 0x%08x" % (r, reg_sentinel(r)))

    lines += [
        "",
        "\t# Sentinel word in the 8 words just below the frame.",
        "\tli   x11, 0x%08x" % MEM_SENTINEL,
        "\tli   x12, 0x%x" % below_base,
    ]
    for k in range(8):
        lines.append("\tsw   x11, %d(x12)" % (4 * k))

    lines += [
        "",
        "\t# Sentinel word in the 8 words just above the frame.",
        "\tli   x12, 0x%x" % above_base,
    ]
    for k in range(8):
        lines.append("\tsw   x11, %d(x12)" % (4 * k))

    lines += [
        "",
        "\t# Call the function under test, then halt.",
        "\tli   x10, 0x%08x" % secret,
        "\tjal  x1, %s" % fn,
        "\tecall",
        "",
    ]
    with open(path, "w") as f:
        f.write("\n".join(lines))


def main():
    workdir = sys.argv[1]
    for idx, fn in enumerate(FUNCTIONS):
        secret = (BASE_SECRET + idx) & 0xFFFFFFFF
        ret = expected_return(secret)

        emit_driver("%s/driver_%s.s" % (workdir, fn), fn, secret)

        with open("%s/expected_%s.txt" % (workdir, fn), "w") as f:
            f.write("secret          0x%08x\n" % secret)
            f.write("return          0x%08x\n" % ret)
            f.write("S               %d\n" % S)
            f.write("top             0x%x\n" % TOP)
            f.write("mem_sentinel    0x%08x\n" % MEM_SENTINEL)
            for r in CALLEE_SAVED:
                f.write("x%-3d            0x%08x\n" % (r, reg_sentinel(r)))

        print("%-18s secret=0x%08x expected return=0x%08x" %
              (fn, secret, ret))


if __name__ == "__main__":
    main()
