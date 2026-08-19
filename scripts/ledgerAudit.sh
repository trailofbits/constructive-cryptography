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
# ---------------------------------------------------------------- check 5
# Registry tripwires (2026-08-18, stretch-assessment B2/B6 — both previously
# ungated):
#  (a) `IsNonexpandingPar` must never be INSTANTIATED at the RS carrier `Phi`:
#      the PRIMITIVE REGISTRY records it as not obtainable (spike G6.f), and an
#      instance would silently unlock `epsilonRelaxation_parCompatible` with
#      unsound content.  The `D.Behaviour` instance (Metric/Behaviour.lean) is
#      legitimate and does not match.  Hypothesis use `[IsNonexpandingPar Φ]`
#      over a variable carrier is fine.
#  (b) `converterMonoidAt` is the registry's metric-facing Σ; its generator set
#      carries `IsNonexpandingSMul ↥converterMonoidAt Phi` and every leg-(c)/(d)
#      receipt.  Widening it silently changes what the landed receipts mean, so
#      the definition block is pinned by hash; a legitimate re-ruling updates the
#      hash here AND the registry entry in the same commit.
#      RE-RULED 2026-08-19 (Marc, approved): the block family
#      `{π | ∃ Q, π = block Q}` is widened to CR18 Definition 3.10's domain
#      filters `{π | ∃ P hP, π = filterPhi P hP}` at any prefix-closed
#      predicate — `block Q` and `filterQueries q` are both instances, and the
#      nonexpansion receipt the widening owes is
#      `filterPhi_mem_nonexpandingConverters` (`System/Absorb.lean`).  Pin
#      recomputed in the same commit; the previous pin was
#      dca1e2e8643141c0379a9ee44e3ae2e03566dd0a666ca6665a95cee2d350475e.
if grep -rnE "^(noncomputable )?instance[^:]*:[[:space:]]*(RandomSystems\.)?IsNonexpandingPar[[:space:]]+(RandomSystems\.)?Phi" --include="*.lean" RandomSystems/ AbstractCryptography/ ConstructiveCryptography/ Applications/ 2>/dev/null; then
  echo "registryAudit: FAIL — IsNonexpandingPar instantiated at Phi (registry: not obtainable, spike G6.f)" >&2
  exit 1
fi
pin_expect="fd0d3a826fbd4cd2450a8fc4c6ffc6ec32a0c3cddbe5faafc652dbe2c95614f8"
pin_actual=$(awk '/^def converterMonoidAt : Submonoid/{f=1} f{print} f&&/^$/{exit}' RandomSystems/System/AttachEngineFully.lean | shasum -a 256 | awk '{print $1}')
if [ "$pin_actual" != "$pin_expect" ]; then
  echo "registryAudit: FAIL — converterMonoidAt definition changed (metric-facing Σ pin)." >&2
  echo "  It carries the IsNonexpandingSMul instance and the leg-(c)/(d) receipts;" >&2
  echo "  add a NEW submonoid instead of widening it (LEDGER PRIMITIVE REGISTRY)," >&2
  echo "  or update the pin + registry entry together if Marc re-ruled" >&2
  echo "  (as on 2026-08-19 for the domain-filter generator family)." >&2
  exit 1
fi
echo "registryAudit: OK (IsNonexpandingPar uninstantiated at Phi; converterMonoidAt pinned)"
# ---------------------------------------------------------------- check 6
# Opt-in citation gate.  A file whose header (first 40 lines) carries the
# literal marker PAPER-FAITHFUL declares that its statements are the printed
# source's statements, so inside it **a numbered source result may not be
# cited without its printed page**: any top-level `theorem` whose doc-comment
# names a `Definition/Theorem/Lemma/Example/Corollary/Remark/Proposition N`
# or an `eq. (N)` must also name the page — `printed p. 3153`,
# `printed pp. 121–122`, `preprint p. 12` (both `-` and `–` are used).
#
# SCOPE RULING (2026-08-19).  The gate deliberately does NOT demand a citation
# of every theorem.  Every technique module is a chain of internal bookkeeping
# lemmas (`weight_enhance`, `nonNeg_adjoin`, `dom_blockReplies`) that state
# nothing any paper states; requiring a page on those would manufacture false
# attributions, which is the exact drift the LEDGER charter's trap list bars
# ("cite paper + printed page, never bare numbers").  What the charter forbids
# is a BARE NUMBER, and that is what this gate catches.  Measured on the tree
# at the time of writing: the every-theorem reading would have flagged 45 of
# `Technique/ConditionalEquivalence.lean`'s 50 theorems; this reading flags
# the citations that were genuinely missing a page, and they were fixed.
#
# Purely grep-level — no Lean elaboration — and green on an unmarked tree, so
# marking a file is the whole opt-in.
marked=0
uncited=0
while IFS= read -r file; do
  header=$(head -n 40 "$file")
  case "$header" in
    *PAPER-FAITHFUL*) ;;
    *) continue ;;
  esac
  marked=$((marked + 1))
  offenders=$(awk '
    BEGIN { inblk = 0; isdoc = 0; doctext = "" }
    {
      if (inblk) {
        if (isdoc) doctext = doctext " " $0
        if ($0 ~ /-\//) { inblk = 0 }
        next
      }
      if ($0 ~ /^\/-/) {
        inblk = 1
        isdoc = ($0 ~ /^\/--/)
        if (isdoc) doctext = $0
        if ($0 ~ /-\/[[:space:]]*$/) { inblk = 0 }
        next
      }
      if ($0 ~ /^(@\[[^]]*\][[:space:]]*)*(nonrec[[:space:]]+)?theorem[[:space:]]/) {
        cites = (doctext ~ /(Definition|Theorem|Lemma|Example|Corollary|Remark|Proposition)[[:space:]]+[0-9]/) ||
                (doctext ~ /eq\.[[:space:]]*\([0-9]/)
        if (cites &&
            doctext !~ /[Pp]rinted[[:space:]]+pp?\.[[:space:]]*[0-9]/ &&
            doctext !~ /[Pp]reprint[[:space:]]+pp?\.[[:space:]]*[0-9]/)
          printf "  %s:%d: %s\n", FILENAME, NR, $0
        doctext = ""
        next
      }
      if ($0 ~ /^[[:space:]]*$/) { doctext = ""; next }
      if ($0 ~ /^(@\[|open |omit |noncomputable|attribute )/) next
      doctext = ""
    }' "$file")
  if [ -n "$offenders" ]; then
    printf '%s\n' "$offenders"
    uncited=$((uncited + 1))
  fi
done < <(find . -name '*.lean' -not -path './.lake/*' | sort)

if [ "$uncited" -ne 0 ]; then
  echo "citationAudit: FAIL — the theorems above are in a PAPER-FAITHFUL file" >&2
  echo "  and cite a NUMBERED source result with no page.  The rule: in a file" >&2
  echo "  whose header is marked PAPER-FAITHFUL, a doc-comment that names a" >&2
  echo "  Definition/Theorem/Lemma/eq. (N) must also name the printed page —" >&2
  echo "  'printed p. 3153', 'printed pp. 121–122', 'preprint p. 12'." >&2
  echo "  Either add the page, refer to the landed declaration instead of the" >&2
  echo "  bare number, or drop the marker from the file header." >&2
  exit 1
fi
echo "citationAudit: OK ($marked file(s) marked PAPER-FAITHFUL, every numbered citation paged)"
