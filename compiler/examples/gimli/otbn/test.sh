#!/bin/sh
# Functional test for the OTBN gimli implementations (scalar + vectorized).
#
# For each: compiles the .jazz, assembles and links it with a small driver
# against the real ACC/OTBN toolchain, runs it on the standalone simulator, and
# checks the result against an independent reference Gimli.
#
# Requires python3 and the ACC toolchain env vars: $ACC_AS, $ACC_LD, $ACC_SIM.
set -e

HERE=$(dirname "$0")
JC="$HERE/../../../jasminc"
BUILD="$HERE/build"
mkdir -p "$BUILD"
SIMPATH="$(dirname "$ACC_SIM"):$(dirname "$ACC_AS")"

# Generate the drivers (input state + entry point) and the expected vector.
python3 "$HERE/gen.py" "$BUILD"

# --- scalar gimli (base RISC-V ISA) ------------------------------------------
# The driver's .text.start section forces the entry to PC 0; multiple objects
# are fine. The 12 state words are laid out contiguously at DMEM 0.
"$JC" -arch otbn "$HERE/gimli.jazz" -o "$BUILD/gimli.s"
"$ACC_AS" -o "$BUILD/gimli.o"  "$BUILD/gimli.s"
"$ACC_AS" -o "$BUILD/driver.o" "$BUILD/driver.s"
"$ACC_LD" -o "$BUILD/run.elf" "$BUILD/driver.o" "$BUILD/gimli.o"
PYTHONPATH="$SIMPATH" "$ACC_SIM" "$BUILD/run.elf" \
  --dump-dmem "$BUILD/dmem.bin" --dump-regs "$BUILD/regs.txt"
python3 "$HERE/check.py" "$BUILD" "$BUILD/dmem.bin" \
  0,1,2,3,4,5,6,7,8,9,10,11 gimli

# --- vectorized gimliv (wide PQC vector ISA) ---------------------------------
# State is three 256-bit slots; the 12 output words are the low four lanes of
# each slot (DMEM words 0-3, 8-11, 16-19). BN.SHV / BN.TRN are PQC-mode
# instructions, so the simulator must run with --pqc.
"$JC" -arch otbn "$HERE/gimliv.jazz" -o "$BUILD/gimliv.s"
"$ACC_AS" -o "$BUILD/gimliv.o"   "$BUILD/gimliv.s"
"$ACC_AS" -o "$BUILD/driver_v.o" "$BUILD/driver_v.s"
"$ACC_LD" -o "$BUILD/run_v.elf" "$BUILD/driver_v.o" "$BUILD/gimliv.o"
PYTHONPATH="$SIMPATH" "$ACC_SIM" "$BUILD/run_v.elf" --pqc 1 \
  --dump-dmem "$BUILD/dmem_v.bin" --dump-regs "$BUILD/regs_v.txt"
python3 "$HERE/check.py" "$BUILD" "$BUILD/dmem_v.bin" \
  0,1,2,3,8,9,10,11,16,17,18,19 gimliv

echo
echo "All OTBN gimli tests passed."
