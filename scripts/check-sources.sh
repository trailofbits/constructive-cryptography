#!/usr/bin/env bash
# Fails if the sources declare an axiom, evaluate natively, bind compiled code, or raise a
# resource limit. `sorry` and `admit` are caught by `lake build --wfail`.
set -euo pipefail

cd "$(dirname "$0")/.."

status=0

check() {
  local what=$1 pattern=$2
  local hits
  hits=$(grep -rnE "$pattern" src || true)
  if [[ -n $hits ]]; then
    echo "$hits"
    echo "error: $what"
    status=1
  fi
}

check "axiom declarations" '^[[:space:]]*((private|protected)[[:space:]]+)?axiom[[:space:]]'
check "native evaluation" 'native_decide|bv_decide|decide \+native|Lean\.ofReduceBool'
check "compiled code bindings" '@\[(implemented_by|extern)'
check "resource limits" 'maxHeartbeats|maxRecDepth|synthInstance\.maxSize'

if [[ $status -eq 0 ]]; then
  echo "sources: no axiom declarations, native evaluation, code bindings or limit overrides"
fi
exit $status
