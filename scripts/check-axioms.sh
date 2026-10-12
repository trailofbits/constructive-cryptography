#!/usr/bin/env bash
# Runs every file under `src/Tests` that prints axioms and fails if an audited endpoint depends
# on an axiom other than `propext`, `Classical.choice` and `Quot.sound` (`sorryAx` included).
# Expects the library to be built (`lake build`).
set -euo pipefail

cd "$(dirname "$0")/.."

allowed='^(propext|Classical\.choice|Quot\.sound)$'
status=0
total=0

files=()
while IFS= read -r file; do
  files+=("$file")
done < <(grep -rl '#print axioms' src/Tests | sort)
if [[ ${#files[@]} -eq 0 ]]; then
  echo "error: no axiom audits found under src/Tests"
  exit 1
fi

for file in "${files[@]}"; do
  if ! output=$(lake env lean "$file" 2>&1); then
    echo "$output"
    echo "error: $file does not compile"
    status=1
    continue
  fi
  # A message may wrap over several lines; join them before matching.
  joined=$(tr '\n' ' ' <<<"$output")
  audited=$(grep -oE "depends on axioms|does not depend on any axioms" <<<"$joined" \
    | wc -l | tr -d ' ' || true)
  total=$((total + audited))
  outside=$(grep -oE "depends on axioms: \[[^]]*\]" <<<"$joined" \
    | sed -E 's/.*\[//; s/\]$//' | tr ',' '\n' | tr -d ' ' | grep -vE "$allowed" | sort -u || true)
  if [[ -n $outside ]]; then
    echo "error: $file: axioms outside the envelope: $(tr '\n' ' ' <<<"$outside")"
    status=1
  fi
  echo "$file: $audited endpoints"
done

echo "axioms: $total endpoints in ${#files[@]} files"
exit $status
