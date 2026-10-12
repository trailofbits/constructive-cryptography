#!/usr/bin/env bash
# A quick first check, before anything is built: fails if the sources declare an axiom, evaluate
# natively, bind compiled code, switch off a kernel or `sorry` check, or raise a resource limit.
# Comments and docstrings are matched too. `scripts/check-axioms.sh` is the complete audit.
set -euo pipefail

cd "$(dirname "$0")/.."

status=0

check() {
  local what=$1 pattern=$2
  local hits code=0
  hits=$(grep -rnE "$pattern" src) || code=$?
  if [[ $code -gt 1 ]]; then
    echo "error: grep failed while checking for $what"
    exit 2
  fi
  if [[ -n $hits ]]; then
    echo "$hits"
    echo "error: $what"
    status=1
  fi
}

modifiers='((private|protected|public|noncomputable|unsafe|partial|nonrec|meta)[[:space:]]+)*'
attributes='(@\[[^]]*[]][[:space:]]*)*'
check "axiom declarations" "(^|-/|[]])[[:space:]]*${attributes}${modifiers}axiom[[:space:]]"
check "native evaluation" \
  'native_decide|bv_decide|[+]native|native[[:space:]]*:=|reduceBool|reduceNat|trustCompiler'
check "compiled code bindings" \
  'implemented_by|csimp|(@\[|attribute[[:space:]]*\[|,)[[:space:]]*extern'
check "kernel or sorry checks switched off" \
  'debug\.skipKernelTC|warn\.sorry|addDeclCore|addDeclWithoutChecking|doCheck'
check "resource limits" 'maxHeartbeats|maxRecDepth|synthInstance\.max'

if [[ $status -eq 0 ]]; then
  echo "sources: no axioms, native evaluation, code bindings, disabled checks or limit overrides"
fi
exit $status
