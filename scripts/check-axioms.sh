#!/usr/bin/env bash
# Audits every declaration of every module under `src` and fails if one depends on an axiom other
# than `propext`, `Classical.choice` and `Quot.sound` (`sorryAx` included). The exemptions are
# listed in `scripts/AxiomAudit.lean`. Expects the library to be built (`lake build`).
set -euo pipefail

cd "$(dirname "$0")/.."

modules=()
while IFS= read -r file; do
  module=${file#src/}
  module=${module%.lean}
  modules+=("${module//\//.}")
done < <(find src -name '*.lean' | sort)

lake env lean --run scripts/AxiomAudit.lean "${modules[@]}"
