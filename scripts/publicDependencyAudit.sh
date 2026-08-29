#!/usr/bin/env bash
# Enforce the public dependency order and the selection of one ambient
# query-indexed random-system model.
set -euo pipefail

cd "$(dirname "$0")/.."

audit_tmp=$(mktemp -d)
trap 'rm -rf "$audit_tmp"' EXIT

module_file() {
  printf '%s.lean\n' "${1//./\/}"
}

dependency_closure() {
  root=$1
  output=$2
  queue="$audit_tmp/queue"
  : > "$output"
  printf '%s\n' "$root" > "$queue"
  index=1
  while :; do
    module=$(sed -n "${index}p" "$queue")
    if [ -z "$module" ]; then
      break
    fi
    index=$((index + 1))
    if grep -qxF -- "$module" "$output"; then
      continue
    fi
    printf '%s\n' "$module" >> "$output"
    file=$(module_file "$module")
    if [ ! -f "$file" ]; then
      continue
    fi
    awk '/^import[[:space:]]+/ {
      for (i = 2; i <= NF; i++) if ($i != "all") print $i
    }' "$file" >> "$queue"
  done
  sort -u -o "$output" "$output"
}

reject_prefixes() {
  label=$1
  closure=$2
  shift 2
  failed=0
  while IFS= read -r module; do
    for prefix in "$@"; do
      case "$module" in
        "$prefix"|"$prefix".*)
          echo "PUBLIC DEPENDENCY BREACH: $label reaches $module" >&2
          failed=1
          ;;
      esac
    done
  done < "$closure"
  if [ "$failed" -ne 0 ]; then
    exit 1
  fi
}

retired_modules=(
  AbstractCryptography.Algebra
  AbstractCryptography.MR11
  AbstractCryptography.Metric
  AbstractCryptography.Refinement
  AbstractCryptography.Specification.Basic
  AbstractCryptography.Specification.ChoiceSetting
  AbstractCryptography.Specification.ConstructorClass
  AbstractCryptography.Specification.CostBounded
  AbstractCryptography.Specification.Filtered
  AbstractCryptography.Specification.Interfaces
  AbstractCryptography.Specification.Outbound
  AbstractCryptography.Specification.Parallel
  AbstractCryptography.Specification.Parameterized
  AbstractCryptography.Specification.TwoParty
  ConstructiveCryptography.Generalizations
  ConstructiveCryptography.Multiparty.GameMetric
  RandomSystems.Converter.Attachment
  RandomSystems.Converter.Cascade
  RandomSystems.Converter.CascadeLaw
  RandomSystems.Converter.CascadeRealization
  RandomSystems.Converter.CombineRealization
  RandomSystems.Converter.Converter
  RandomSystems.Converter.ConverterImpl
  RandomSystems.Converter.Sigma
  RandomSystems.Game
  RandomSystems.Interface
  RandomSystems.Notation
  RandomSystems.System
)

retired_paths=(
  AbstractCryptography/Algebra
  AbstractCryptography/MR11.lean
  AbstractCryptography/MR11
  AbstractCryptography/Metric
  AbstractCryptography/Refinement
  AbstractCryptography/Specification/Basic.lean
  AbstractCryptography/Specification/ChoiceSetting.lean
  AbstractCryptography/Specification/ConstructorClass.lean
  AbstractCryptography/Specification/CostBounded.lean
  AbstractCryptography/Specification/Filtered.lean
  AbstractCryptography/Specification/Interfaces.lean
  AbstractCryptography/Specification/Outbound.lean
  AbstractCryptography/Specification/Parallel.lean
  AbstractCryptography/Specification/Parameterized.lean
  AbstractCryptography/Specification/Relaxation.lean
  AbstractCryptography/Specification/TwoParty.lean
  ConstructiveCryptography/Generalizations
  ConstructiveCryptography/Multiparty/GameMetric.lean
  Applications/Frost/ConstructionEps.lean
  AbstractCryptographyContextRestrictedTests.lean
  AbstractCryptographyIndexedRelaxationTests.lean
  ConstructiveCryptographyDemo.lean
  ConstructiveCryptographyDemoSupport.lean
  RandomSystems/Converter/Attachment.lean
  RandomSystems/Converter/Cascade.lean
  RandomSystems/Converter/CascadeLaw.lean
  RandomSystems/Converter/CascadeRealization.lean
  RandomSystems/Converter/CombineRealization.lean
  RandomSystems/Converter/Converter.lean
  RandomSystems/Converter/ConverterImpl.lean
  RandomSystems/Converter/Sigma.lean
  RandomSystems/Game
  RandomSystems/Interface
  RandomSystems/Notation.lean
  RandomSystems/PartialFunction.lean
  RandomSystems/System
  RandomSystems/Technique/BlindWinning.lean
  RandomSystems/Technique/BlindWinning
  RandomSystems/Technique/Completeness.lean
  RandomSystems/Technique/ConditionalEquivalence.lean
  RandomSystems/Technique/DataProcessing.lean
  RandomSystems/Technique/Switching.lean
  RandomSystems/Technique/TotalHCoefficient.lean
)

for path in "${retired_paths[@]}"; do
  if [ -e "$path" ]; then
    echo "RETIRED MODEL BREACH: $path is present in the production tree" >&2
    exit 1
  fi
done

dependency_closure AbstractCryptography "$audit_tmp/abstract"
reject_prefixes AbstractCryptography "$audit_tmp/abstract" \
  "${retired_modules[@]}" RandomSystems RandomSystemsCC \
  ConstructiveCryptography Applications

dependency_closure ConstructiveCryptography "$audit_tmp/constructive"
reject_prefixes ConstructiveCryptography "$audit_tmp/constructive" \
  "${retired_modules[@]}" RandomSystems RandomSystemsCC Applications

dependency_closure RandomSystems "$audit_tmp/random-systems"
reject_prefixes RandomSystems "$audit_tmp/random-systems" \
  RandomSystems.Converter RandomSystemsCC AbstractCryptography \
  ConstructiveCryptography Applications

dependency_closure RandomSystems.Converter "$audit_tmp/converter"
reject_prefixes RandomSystems.Converter "$audit_tmp/converter" \
  RandomSystemsCC AbstractCryptography ConstructiveCryptography Applications \
  "${retired_modules[@]}"

dependency_closure RandomSystemsCC "$audit_tmp/random-systems-cc"
reject_prefixes RandomSystemsCC "$audit_tmp/random-systems-cc" \
  ConstructiveCryptography Applications "${retired_modules[@]}"

dependency_closure Applications.CBCMAC "$audit_tmp/cbc"
reject_prefixes Applications.CBCMAC "$audit_tmp/cbc" \
  "${retired_modules[@]}"

instance_sites=$(find AbstractCryptography ConstructiveCryptography RandomSystems \
    RandomSystemsCC Applications -name '*.lean' -print0 | sort -z |
  xargs -0 awk '
    FNR == 1 { in_instance = 0; reported = 0 }
    /^[[:space:]]*(noncomputable[[:space:]]+)?instance([[:space:]]|$)/ {
      in_instance = 1
      reported = 0
      start = FNR
    }
    in_instance && /ResourceAlgebra/ && !reported {
      print FILENAME ":" start
      reported = 1
    }
    in_instance && (/[:][=]/ || /where[[:space:]]*$/) { in_instance = 0 }
    in_instance && FNR - start > 20 { in_instance = 0 }
  ')

instance_count=$(printf '%s\n' "$instance_sites" | sed '/^$/d' | wc -l | tr -d ' ')
case "$instance_sites" in
  RandomSystemsCC/ResourceAlgebra.lean:*) ;;
  *)
    echo "AMBIENT MODEL BREACH: expected the sole ResourceAlgebra instance in RandomSystemsCC/ResourceAlgebra.lean" >&2
    printf '%s\n' "$instance_sites" >&2
    exit 1
    ;;
esac
if [ "$instance_count" -ne 1 ]; then
  echo "AMBIENT MODEL BREACH: found $instance_count ResourceAlgebra instances" >&2
  printf '%s\n' "$instance_sites" >&2
  exit 1
fi

if rg -n 'BraidedCategory|SymmetricMonoidalCategory' \
    RandomSystems/Converter AbstractCryptography/Categorical >/dev/null; then
  echo "PARALLEL STRUCTURE BREACH: the selected theory must remain ordered, not symmetric" >&2
  exit 1
fi

if rg -n \
    'ConstructiveCryptography\.CCAlgebra|AbstractCryptography\.Par\.par|AbstractCryptography\.HasReduction\.Red|RandomSystems\.CR18|PFunPDS|PFunDDS' \
    Rendering/CCWidget.lean >/dev/null; then
  echo "RENDERER BREACH: the theory-free widget names a retired semantic surface" >&2
  exit 1
fi

if rg -n '^#print axioms' \
    RandomSystems/Converter/Interface.lean \
    RandomSystems/Converter/DDS.lean \
    RandomSystems/Converter/DDC.lean \
    RandomSystems/Converter/Filter.lean >/dev/null; then
  echo "SOURCE HYGIENE BREACH: move axiom inspection to the verification gate" >&2
  exit 1
fi

echo "publicDependencyAudit: OK (dependency order and sole ambient ResourceAlgebra instance)"
