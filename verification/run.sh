#!/usr/bin/env bash
# Run both verification scripts and compare with the recorded output.
set -euo pipefail
cd "$(dirname "$0")"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

echo "== Python =="
python3 python/abgv52_certs.py --out "$tmp/python-certs.json"

echo
echo "== GAP (needs HAP) =="
gap -q -b gap/abgv52_verify.g > "$tmp/gap-output.txt"
cat "$tmp/gap-output.txt"

echo
echo "== compare with recorded output =="
if diff -q expected/python-certs.json "$tmp/python-certs.json" >/dev/null; then
    echo "python: output identical to expected/python-certs.json"
else
    echo "python: DIFFERS from expected/python-certs.json"
    exit 1
fi
if diff -q expected/gap-output.txt "$tmp/gap-output.txt" >/dev/null; then
    echo "gap:    output identical to expected/gap-output.txt"
else
    echo "gap:    DIFFERS from expected/gap-output.txt"
    exit 1
fi

echo
echo "== GAP, p = 5 =="
sed 's/^p := 3;;/p := 5;;/' gap/abgv52_verify.g > "$tmp/p5.g"
gap -q -b "$tmp/p5.g" > "$tmp/gap-output-p5.txt"
tail -4 "$tmp/gap-output-p5.txt"
if diff -q expected/gap-output-p5.txt "$tmp/gap-output-p5.txt" >/dev/null; then
    echo "gap p5: output identical to expected/gap-output-p5.txt"
else
    echo "gap p5: DIFFERS from expected/gap-output-p5.txt"
    exit 1
fi
echo
echo "all outputs match."
