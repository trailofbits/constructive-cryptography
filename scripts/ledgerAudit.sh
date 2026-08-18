#!/usr/bin/env bash
# Two gates, both derived from LEDGER.md on every run — never from memory.
#
#  1. Carrier ledger: every def/abbrev/structure/instance in RandomSystems/System/
#     and RandomSystems/Converter/ must appear (by name) in LEDGER.md.
#     Fails listing unclassified names.  See LEDGER.md header for the rule.
#  2. Provenance fence (MR11-DEFERRED): no MR16-track file may import a module
#     listed under `FENCED:` in LEDGER.md.  Fenced -> fenced is permitted.
#     See LEDGER.md "PROVENANCE FENCE (MR11-DEFERRED)" for the rule.
set -euo pipefail
cd "$(dirname "$0")/.."

# ---------------------------------------------------------------- check 1
missing=0
names=$(for f in RandomSystems/System/*.lean RandomSystems/Converter/*.lean; do
  grep -hoE "^(noncomputable |@\[[^]]*\] )*(def|abbrev|structure|instance) [A-Za-z_][A-Za-z0-9_'.]*" "$f" 2>/dev/null
done | sed -E 's/^(noncomputable |@\[[^]]*\] )*//' | awk '{print $2}' | sort -u)
for n in $names; do
  if ! grep -qw -- "$n" LEDGER.md; then
    echo "UNCLASSIFIED: $n"
    missing=1
  fi
done
if [ "$missing" -eq 1 ]; then
  echo "ledgerAudit: FAIL — classify the names above in LEDGER.md" >&2
  exit 1
fi
echo "ledgerAudit: OK ($(echo "$names" | wc -l | tr -d ' ') names classified)"

# ---------------------------------------------------------------- check 2
fenced=$(grep -E '^FENCED: ' LEDGER.md | sed -E 's/^FENCED: +//' | sed -E 's/[[:space:]]+$//' | sort -u)
if [ -z "$fenced" ]; then
  echo "fenceAudit: FAIL — LEDGER.md lists no FENCED: modules" >&2
  exit 1
fi
is_fenced() { printf '%s\n' "$fenced" | grep -qxF -- "$1"; }

breaches=0
checked=0
while IFS= read -r file; do
  rel=${file#./}
  self=$(printf '%s' "${rel%.lean}" | tr '/' '.')
  if is_fenced "$self"; then continue; fi   # fenced -> fenced is permitted
  checked=$((checked + 1))
  while IFS= read -r imported; do
    if is_fenced "$imported"; then
      echo "FENCE BREACH: $rel imports the fenced module $imported"
      breaches=$((breaches + 1))
    fi
  done < <(grep -E '^import +[A-Za-z_]' "$file" | awk '{print $2}')
done < <(find . -name '*.lean' -not -path './.lake/*' | sort)

if [ "$breaches" -ne 0 ]; then
  echo "fenceAudit: FAIL — $breaches MR16-track import(s) of a fenced module." >&2
  echo "  The discipline is MR16-only until the MR11 reconciliation task." >&2
  echo "  Either drop the import, or add the importing module to LEDGER.md's" >&2
  echo "  FENCED: list in the same commit.  See LEDGER.md PROVENANCE FENCE." >&2
  exit 1
fi
# ---------------------------------------------------------------- check 3
# Tripwire: refuted designs must never re-enter as code.
if grep -rnE "def (relayExcept|attachFullyAt|botToken)" --include="*.lean" RandomSystems/ AbstractCryptography/ ConstructiveCryptography/ 2>/dev/null; then
  echo "primitiveAudit: FAIL — a refuted design name re-entered as a definition." >&2
  exit 1
fi
echo "primitiveAudit: OK (refuted designs absent)"
# ---------------------------------------------------------------- check 4
# Root aggregator: `lake build` globs exclude RandomSystems.lean, so a
# cross-lane clash (duplicate declaration) can hide behind a green build.
if ! lake env lean RandomSystems.lean >/dev/null 2>&1; then
  echo "rootAudit: FAIL — RandomSystems.lean does not elaborate (cross-lane clash?)" >&2
  exit 1
fi
echo "rootAudit: OK (root aggregator elaborates)"
echo "fenceAudit: OK ($(printf '%s\n' "$fenced" | wc -l | tr -d ' ') modules fenced, $checked MR16-track files clean)"
