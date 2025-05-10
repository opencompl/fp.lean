#!/usr/bin/env bash
set -e
set -o xtrace

TOPLEVEL="$(git rev-parse --show-toplevel)"

cd "$TOPLEVEL"
shellcheck test/ci/compare-floatx-fplean.sh
make -C test/against-floatx all
./test/against-floatx/test.out > "$TOPLEVEL/golden-floatx.csv"
lake exec fp-lean e5m2 > "$TOPLEVEL/golden-fplean.csv"
test/ci/compare-against-golden.py "$TOPLEVEL/golden-floatx.csv" "$TOPLEVEL/golden-fplean.csv"

