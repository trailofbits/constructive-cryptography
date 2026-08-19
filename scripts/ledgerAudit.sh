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
#      `{π | ∃ Q, π = block Q}` is widened to CR18 §3.4.3's domain filters
#      (unnumbered prose, printed p. 62 — Definition 3.10 is ONLY the `[q]`
#      notation) `{π | ∃ P hP, π = filterPhi P hP}` at any prefix-closed
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
# Opt-in citation gate.  REBUILT 2026-08-19 after the adversarial audit of
# aeb685f demonstrated six bypasses of the first version, every one of which it
# reported as OK (docstring with several citations but a single page; a citation
# with a WRONG page; `lemma`; `protected theorem`; a blank line between the
# doc-comment and the declaration; and every `def`/`instance`).
#
# THE CHARTER RULE THIS IMPLEMENTS is LEDGER.md:1842, cross-source trap 4:
#   "Definition- and equation-number collisions across papers. ...
#    **Never cite by bare number across papers** — every AC docstring must
#    carry paper + page."
# A file whose header (first 40 lines) carries the literal marker
# PAPER-FAITHFUL declares that its statements are the printed source's
# statements, and opts every declaration in it into that rule.
#
# WHAT IS CHECKED, per doc-comment attached to a top-level declaration of ANY
# kind (`theorem`, `lemma`, `def`, `instance`, `abbrev`, `structure`, `class`,
# `inductive`, `example`, `opaque`, `axiom`, with any combination of `@[...]`,
# `private`, `protected`, `scoped`, `local`, `nonrec`, `noncomputable`,
# `unsafe`, `partial` in front, and with blank lines allowed between the
# doc-comment and the declaration):
#
#   * count the DISTINCT numbered citations it makes — `Definition 2.25`,
#     `Theorem 4.17`, `Lemma 2`, `Remark 2.24`, `eq. (4.39)`, `fn. 6`,
#     `footnote 9`, singular or plural;
#   * count the printed-page references it carries — `printed p. 3153`,
#     `printed pp. 121-122`, `preprint p. 12` (both `-` and `–` occur);
#   * FAIL unless pages >= distinct citations.  One page for three citations
#     is bypass 1 and is now a failure: a page must be bound to each number.
#   * a doc-comment that NAMES a source (CR18, Maurer13b, MauRen16, MPR07,
#     Lanzenberger, LiuMau20, Cachin/Renner, Jost, …) but cites no numbered
#     result is NOT exempt — it must still carry one page.  Under the first
#     version, deleting the numbered attribution made the gate go quiet, which
#     rewarded exactly the wrong edit (one of aeb685f's sixteen "fixes"
#     deleted "Lanzenberger Definition 2.17" instead of paging it).
#
# WHAT IS NOT CHECKED — stated so nobody reads more into a green run:
#   * whether a page is CORRECT.  No script can know that; five of the pages
#     this gate certified green on 2026-08-19 were wrong by one (Lanzenberger
#     Definition 2.25 is on printed p. 18, not 17).  In place of a check the
#     gate PRINTS the certified surface: the number of paged citations per
#     marked file.  That count is the size of the claim a green run is making,
#     and it is there so a reviewer can spot-check it against the rendered
#     pages.  A rising count is new attribution surface to verify by eye.
#   * whether the page belongs to the citation nearest it, rather than to some
#     other citation in the same doc-comment.
#   * module/section doc-comments (`/-! ... -/`).  The marked file's own header
#     carries the paper+page banner; only declaration doc-comments are gated.
#
# SCOPE RULING (2026-08-19, unchanged from the first version).  The gate does
# NOT demand a citation of every declaration.  A technique module is mostly
# internal bookkeeping (`weight_enhance`, `nonNeg_adjoin`, `dom_blockReplies`)
# that states nothing any paper states; demanding a page there would
# manufacture false attributions.  What the charter forbids is a BARE NUMBER,
# and that is what this gate catches.
#
# Purely grep-level — no Lean elaboration — and green on an unmarked tree, so
# marking a file is the whole opt-in.
marked=0
uncited=0
certified=0
report=""
while IFS= read -r file; do
  header=$(head -n 40 "$file")
  case "$header" in
    *PAPER-FAITHFUL*) ;;
    *) continue ;;
  esac
  marked=$((marked + 1))
  out=$(awk '
    function norm(k) { gsub(/[[:space:]]+/, " ", k); return k }
    function harvest(txt, seen, re,    rest, key, n) {
      n = 0; rest = txt
      while (match(rest, re)) {
        key = norm(substr(rest, RSTART, RLENGTH))
        if (!(key in seen)) { seen[key] = 1; n++ }
        rest = substr(rest, RSTART + RLENGTH)
      }
      return n
    }
    function check(txt, lno, decl,    seen, ncit, npg, rest, need, list, k) {
      delete seen
      ncit  = harvest(txt, seen, RESULT)
      ncit += harvest(txt, seen, EQN)
      ncit += harvest(txt, seen, FN)
      npg = 0; rest = txt
      while (match(rest, PAGE)) { npg++; rest = substr(rest, RSTART + RLENGTH) }
      need = ncit
      if (need == 0 && txt ~ SOURCE) need = 1
      if (need == 0) return
      if (npg >= need) { PAGED += npg; return }
      list = ""
      for (k in seen) list = (list == "" ? k : list "; " k)
      if (list == "") list = "a source, with no numbered result"
      printf "  %s:%d: %s\n", FILENAME, lno, decl
      printf "      cites %d [%s]; carries %d printed page(s)\n", need, list, npg
      BAD += 1
    }
    BEGIN {
      RESULT = "(Definition|Definitions|Theorem|Theorems|Lemma|Lemmas|Example|Examples|Corollary|Corollaries|Remark|Remarks|Proposition|Propositions|Notation|Exercise)[[:space:]]+[0-9]+([.][0-9]+)*"
      EQN    = "eq[.][[:space:]]*[(][0-9]+([.][0-9]+)*[)]"
      FN     = "(fn[.]|footnote)[[:space:]]*[0-9]+"
      PAGE   = "[Pp](rinted|reprint)[[:space:]]+pp?[.][[:space:]]*[0-9]+"
      SOURCE = "CR18|Maurer[0-9]|MauRen[0-9]|MPR07|MaPiRe[0-9]|Lanzenberger|LiuMau[0-9]|Cachin|Renner|Jost"
      DECL   = "^(@\\[[^]]*\\][[:space:]]*)*(private[[:space:]]+|protected[[:space:]]+|scoped[[:space:]]+|local[[:space:]]+|nonrec[[:space:]]+|noncomputable[[:space:]]+|unsafe[[:space:]]+|partial[[:space:]]+)*(theorem|lemma|def|instance|abbrev|structure|class|inductive|example|opaque|axiom)([[:space:]]|:|$)"
      SKIP   = "^([[:space:]]*$|[[:space:]]*--|@\\[|open |omit |attribute |set_option |universe |variable |local |scoped |section|namespace)"
      inblk = 0; isdoc = 0; doc = ""; have = 0; dline = 0; BAD = 0; PAGED = 0
    }
    {
      if (inblk) {
        if (isdoc) doc = doc " " $0
        if ($0 ~ /-\//) { inblk = 0; if (isdoc) have = 1 }
        next
      }
      if ($0 ~ /^[[:space:]]*\/--/) {
        inblk = 1; isdoc = 1; doc = $0; dline = NR
        if ($0 ~ /-\/[[:space:]]*$/) { inblk = 0; have = 1 }
        next
      }
      if ($0 ~ /^[[:space:]]*\/-/) {
        inblk = 1; isdoc = 0; have = 0; doc = ""
        if ($0 ~ /-\/[[:space:]]*$/) inblk = 0
        next
      }
      if ($0 ~ DECL) {
        if (have) check(doc, NR, $0)
        have = 0; doc = ""
        next
      }
      if ($0 ~ SKIP) next
      have = 0; doc = ""
    }
    END { printf "@@ %d %d\n", BAD, PAGED }' "$file")
  tally=$(printf '%s\n' "$out" | grep '^@@ ' | tail -n 1 || true)
  offenders=$(printf '%s\n' "$out" | grep -v '^@@ ' || true)
  nbad=$(printf '%s' "$tally" | awk '{print $2}')
  npaged=$(printf '%s' "$tally" | awk '{print $3}')
  certified=$((certified + npaged))
  report="${report}  ${file#./}: ${npaged} paged citation(s) certified"$'\n'
  if [ "$nbad" -ne 0 ]; then
    printf '%s\n' "$offenders"
    uncited=$((uncited + 1))
  fi
done < <(find . -name '*.lean' -not -path './.lake/*' | sort)

if [ "$uncited" -ne 0 ]; then
  echo "citationAudit: FAIL — the declarations above are in a PAPER-FAITHFUL file" >&2
  echo "  and cite a NUMBERED source result without a printed page for it." >&2
  echo "  The rule (LEDGER.md:1842): every AC docstring must carry paper + page," >&2
  echo "  so in a PAPER-FAITHFUL file a doc-comment needs at least as many page" >&2
  echo "  references — 'printed p. 3153', 'printed pp. 121-122', 'preprint" >&2
  echo "  p. 12' — as it makes distinct numbered citations, and a doc-comment" >&2
  echo "  that names a source at all needs at least one." >&2
  echo "  Either page each citation, refer to the landed declaration instead of" >&2
  echo "  the bare number, or drop the marker from the file header.  Deleting" >&2
  echo "  the attribution is NOT a fix." >&2
  exit 1
fi
echo "citationAudit: OK ($marked file(s) marked PAPER-FAITHFUL, $certified paged citation(s) certified PRESENT — not correct; verify pages on the rendered page)"
printf '%s' "$report"
