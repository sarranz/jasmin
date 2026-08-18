set -u

arch=$1
file=$2
name=$(printf 'p_%s_%s' "$arch" "$file" | tr -c 'a-zA-Z0-9' '_')
tmp=$(mktemp -d)
err=""
if ! "$JASMIN2ROCQ" --arch "$arch" -o "$tmp/test.v" "$file" "$name" \
    > "$tmp/log" 2>&1; then
  err="extraction failed"
elif ! $ROCQ "$tmp/test.v" > "$tmp/log" 2>&1; then
  err="rocq failed"
fi
status=0
if [ -n "$err" ]; then
  printf 'File %s (%s): %s\n%s\n' "$file" "$arch" "$err" "$(cat "$tmp/log")"
  echo "$file ($arch)" >> "$FAILURES"
  status=1
fi
rm -rf "$tmp"
exit $status
