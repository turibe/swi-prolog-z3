#!/usr/bin/env bash
# Times Z3 on the same 9x9 Latin square with three encodings of the values: integers 1..9, an
# enumeration sort and 4-bit bit-vectors. Each must print sat; the integer one is far slower.
#
#     examples/smt2/latin_squares.sh [TimeoutSeconds]      (default 60)
#
# Needs the z3 command line on the PATH.

set -u
limit=${1:-60}
dir=$(cd "$(dirname "$0")" && pwd)
command -v z3 > /dev/null || { echo "z3 is not on the PATH" >&2; exit 2; }
z3 --version

for encoding in int enum bv; do
  file="$dir/latin_square_$encoding.smt2"
  start=$(date +%s.%N 2>/dev/null || date +%s)
  result=$(z3 -T:"$limit" "$file")
  end=$(date +%s.%N 2>/dev/null || date +%s)
  printf '%-5s %-8s %6.2f s\n' "$encoding" "$result" "$(echo "$end - $start" | bc)"
done
