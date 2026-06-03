#!/usr/bin/env python3
"""Compare 12 DMEM words from an ACC sim dump against expected.txt.

The DMEM dump format is 5 bytes per word: 1 validity byte + 4 little-endian
data bytes.

Usage: check.py <build-dir> <dmem-file> <indices> [label]
  <indices> is a comma-separated list of the 12 DMEM word indices that hold the
  output state (contiguous 0..11 for the scalar layout, or the padded slots
  0,1,2,3,8,9,10,11,16,17,18,19 for the vectorized layout).
"""
import sys

workdir = sys.argv[1]
dmem_file = sys.argv[2]
indices = [int(t) for t in sys.argv[3].split(",")]
label = sys.argv[4] if len(sys.argv) > 4 else dmem_file

assert len(indices) == 12, "expected 12 word indices"

with open(dmem_file, "rb") as f:
    raw = f.read()

def word_at(i):
    rec = raw[i * 5:i * 5 + 5]
    valid = rec[0]
    data = rec[1] | (rec[2] << 8) | (rec[3] << 16) | (rec[4] << 24)
    return data, valid

expected = []
with open(workdir + "/expected.txt") as f:
    for line in f:
        line = line.strip()
        if line:
            expected.append(int(line, 16))

ok = True
print("[%s]" % label)
print("idx  expected   got        valid  match")
for k in range(12):
    i = indices[k]
    w, v = word_at(i)
    e = expected[k]
    m = (w == e) and (v != 0)
    ok = ok and m
    print("%2d   %08x   %08x   %d      %s" % (i, e, w, v, "OK" if m else "MISMATCH"))

print()
if ok:
    print("RESULT: PASS -- %s matches the reference Gimli vector." % label)
    sys.exit(0)
else:
    print("RESULT: FAIL -- %s" % label)
    sys.exit(1)
