#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."/no-zeros

echo "==> lake update"
lake update

echo "==> lake build (conservative)"
export LEAN_EXTRA_ARGS="-j2 -M 4096"
lake build

echo "==> lake build +rh.Proof.AxiomsCheck (printing axioms)"
lake build +rh.Proof.AxiomsCheck

echo "Done. See printed axioms from #print axioms statements in rh/Proof/AxiomsCheck.lean"

