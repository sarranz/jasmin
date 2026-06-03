#!/usr/bin/env python3
"""Generate the OTBN test drivers for gimli/gimliv and the expected vector.

A reference Gimli (transcribed from the canonical gimli.c reference code) is
used purely as an independent oracle to check the Jasmin/OTBN implementations.

Usage: gen.py <build-dir>
Writes <build-dir>/driver.s (scalar), <build-dir>/driver_v.s (vectorized) and
<build-dir>/expected.txt.
"""
import sys

MASK = 0xffffffff

def rol(x, n):
    return ((x << n) | (x >> (32 - n))) & MASK

def gimli(state):
    s = list(state)
    for rnd in range(24, 0, -1):            # rounds 24, 23, ..., 1
        for col in range(4):
            x = rol(s[col], 24)
            y = rol(s[col + 4], 9)
            z = s[col + 8]
            s[col + 8] = (x ^ ((z << 1) & MASK) ^ ((y & z) << 2)) & MASK
            s[col + 4] = (y ^ x ^ ((x | z) << 1)) & MASK
            s[col]     = (z ^ y ^ ((x & y) << 3)) & MASK
        if (rnd & 3) == 0:                  # small swap
            s[0], s[1] = s[1], s[0]
            s[2], s[3] = s[3], s[2]
        if (rnd & 3) == 2:                  # big swap
            s[0], s[2] = s[2], s[0]
            s[1], s[3] = s[3], s[1]
        if (rnd & 3) == 0:                  # add round constant
            s[0] = (s[0] ^ (0x9e377900 | rnd)) & MASK
    return s

# Canonical Gimli test input: x[i] = i^3 + i*0x9e3779b9  (mod 2^32)
inp = [(i * i * i + i * 0x9e3779b9) & MASK for i in range(12)]
out = gimli(inp)

workdir = sys.argv[1]


def emit_driver(path, callee, words):
    """A driver: `words` go at the start of .data (DMEM VMA 0), the entry is
    forced to PC 0 via .text.start, we load the absolute DMEM address of the
    state (Harvard machine -> absolute %hi/%lo, not pc-relative la), call the
    permutation, then ecall to halt."""
    lines = [
        "\t.section .data",
        "\t.balign 32",
        "\t.globl gimli_state",
        "gimli_state:",
    ]
    lines += ["\t.word 0x%08x" % w for w in words]
    lines += [
        "",
        "\t.section .text.start",
        "\t.globl _start",
        "_start:",
        "\tlui  x10, %hi(gimli_state)",
        "\taddi x10, x10, %lo(gimli_state)",
        "\tjal  x1, " + callee,
        "\tecall",
        "",
    ]
    with open(path, "w") as f:
        f.write("\n".join(lines))


# Scalar gimli: the 12 state words laid out contiguously.
emit_driver(workdir + "/driver.s", "gimli", inp)

# Vectorized gimliv: three 256-bit slots, each holding four u32 columns in the
# low 128 bits and four zero padding words in the high 128 bits.
words_v = (inp[0:4] + [0, 0, 0, 0]
           + inp[4:8] + [0, 0, 0, 0]
           + inp[8:12] + [0, 0, 0, 0])
emit_driver(workdir + "/driver_v.s", "gimliv", words_v)

with open(workdir + "/expected.txt", "w") as f:
    for w in out:
        f.write("%08x\n" % w)

print("input:   ", " ".join("%08x" % w for w in inp))
print("expected:", " ".join("%08x" % w for w in out))
