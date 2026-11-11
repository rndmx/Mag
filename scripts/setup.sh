#!/bin/sh
# Sparse dependency setup for Windows: Stacks has filenames too long for a full checkout.
# Usage: scripts/setup.sh <module> ...   (Stacks modules whose import closure to check out)
set -e
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
pkg=.lake/packages
mkdir -p "$pkg"
rev=$(grep -E '^rev' lakefile.toml | head -1 | cut -d'"' -f2)

if [ ! -d "$pkg/Stacks/.git" ]; then
  git init -q "$pkg/Stacks"
  git -C "$pkg/Stacks" config core.longpaths true
  git -C "$pkg/Stacks" config core.sparseCheckout true
  git -C "$pkg/Stacks" remote add origin https://github.com/AxiomMath/Stacks
  git -C "$pkg/Stacks" fetch -q --depth 1 origin "$rev"
fi
python -I scripts/closure.py "$pkg/Stacks" "$rev" "$@" > "$pkg/Stacks/.git/info/sparse-checkout"
git -C "$pkg/Stacks" checkout -q "$rev"
wc -l "$pkg/Stacks/.git/info/sparse-checkout"

mlrev=$(git -C "$pkg/Stacks" show HEAD:lake-manifest.json | python -I -c "import json,sys;print([p['rev'] for p in json.load(sys.stdin)['packages'] if p['name']=='mathlib'][0])")
if [ ! -d "$pkg/mathlib/.git" ]; then
  git init -q "$pkg/mathlib"
  git -C "$pkg/mathlib" config core.longpaths true
  git -C "$pkg/mathlib" remote add origin https://github.com/leanprover-community/mathlib4
  git -C "$pkg/mathlib" fetch -q --depth 1 origin "$mlrev"
  git -C "$pkg/mathlib" checkout -q "$mlrev"
fi
git -C "$pkg/Stacks" show HEAD:lean-toolchain > lean-toolchain
