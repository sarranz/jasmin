set -u

JASMIN2ROCQ=$1

proofs=${JASMIN_PROOFS_DIR:-}
if [ -z "$proofs" ]; then
  d=$PWD
  while [ ! -f "$d/proofs/_CoqProject" ]; do
    if [ "$d" = / ]; then
      echo "Could not locate Jasmin proofs/ directory; set JASMIN_PROOFS_DIR." >&2
      exit 2
    fi
    d=$(dirname "$d")
  done
  proofs=$d/proofs
fi

ROCQ="rocq c -R $proofs/lang Jasmin -R $proofs/compiler Jasmin \
  -R $proofs/arch Jasmin -R $proofs/3rdparty Jasmin -R $proofs/ssrmisc Jasmin \
  -R $proofs/printing Printing -q -w -all"

FAILURES=$(mktemp)
export JASMIN2ROCQ ROCQ FAILURES

list_tests() {
  dirs=$(find ../../examples ../success -type d -name "$2"
         find ../success -type d -name common)
  for dir in $(echo "$dirs" | sort); do
    for f in "$dir"/*.jazz; do
      if [ -e "$f" ]; then echo "$1 $f"; fi
    done
  done
}

tests=$(mktemp)
{
  list_tests x86-64 x86-64
  list_tests arm-m4 arm-m4
  list_tests riscv risc-v
} > "$tests"

xargs -n 2 -P "${JOBS:-8}" sh "$(dirname "$0")/check-one.sh" < "$tests"
rc=$?

checked=$(wc -l < "$tests")
failed=$(wc -l < "$FAILURES")
rm -f "$tests" "$FAILURES"
echo "$checked tests, $failed failures"
[ "$failed" -eq 0 ] && [ "$rc" -eq 0 ]
