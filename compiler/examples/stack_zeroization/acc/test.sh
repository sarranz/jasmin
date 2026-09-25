#!/bin/sh
# Functional test for the ACC stack zeroization simulator harness
# (plan_ACC_SZ.md, Phase 1.6).
#
# Compiles sz.jazz once, then for each of its six sz_<strategy>_<width>
# functions: assembles and links a small driver against it with the real
# ACC toolchain, runs it on the standalone simulator, and checks the DMEM
# and register dumps against an independently computed expectation.
#
# Unlike ../../gimli/acc/test.sh (two independent runs), this loop keeps
# going after a failure at any one function's assemble/link/simulate step
# instead of aborting the whole script, so a single failing case does not
# hide the results of the other five -- useful since the plan calls out
# that the loophw runs are the only execution-level check the hardware
# loop strategy gets and may need inspecting individually.
#
# Requires python3 and the ACC toolchain env vars: $ACC_AS, $ACC_LD,
# $ACC_SIM.

HERE=$(dirname "$0")
JC="$HERE/../../../jasminc"
BUILD="$HERE/build"
mkdir -p "$BUILD" || exit 1
SIMPATH="$(dirname "$ACC_SIM"):$(dirname "$ACC_AS")"

# Generate the six drivers and their expected-value files.
python3 "$HERE/gen.py" "$BUILD" || exit 1

# Compile sz.jazz once; every driver links against the same object.
"$JC" -arch acc "$HERE/sz.jazz" -o "$BUILD/sz.s" || exit 1
"$ACC_AS" -o "$BUILD/sz.o" "$BUILD/sz.s" || exit 1

FAIL=0
for fn in sz_loop_u32 sz_unrolled_u32 sz_loophw_u32 \
          sz_loop_u256 sz_unrolled_u256 sz_loophw_u256; do
  echo
  echo "=== $fn ==="

  if ! "$ACC_AS" -o "$BUILD/driver_$fn.o" "$BUILD/driver_$fn.s"; then
    echo "RESULT: FAIL -- $fn (assemble)"
    FAIL=1
    continue
  fi

  if ! "$ACC_LD" -o "$BUILD/run_$fn.elf" "$BUILD/driver_$fn.o" "$BUILD/sz.o"; then
    echo "RESULT: FAIL -- $fn (link)"
    FAIL=1
    continue
  fi

  if ! PYTHONPATH="$SIMPATH" "$ACC_SIM" "$BUILD/run_$fn.elf" \
       --dump-dmem "$BUILD/dmem_$fn.bin" --dump-regs "$BUILD/regs_$fn.txt"; then
    echo "RESULT: FAIL -- $fn (simulator stopped early; check its error" \
         "bits above -- loop count 0, a bad data address, or loop-stack" \
         "misuse are the likely causes for the loophw functions)"
    FAIL=1
    continue
  fi

  if ! python3 "$HERE/check.py" "$BUILD" "$fn"; then
    FAIL=1
  fi
done

echo
if [ "$FAIL" = 0 ]; then
  echo "All ACC stack zeroization simulator tests passed."
  exit 0
else
  echo "ACC stack zeroization simulator tests FAILED."
  exit 1
fi
