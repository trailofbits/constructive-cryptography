#!/usr/bin/env bash
# List added definition heads and probability-construction sites in Lean changes for a reuse
# review. The match is lexical: the report lists candidates, not semantic duplicates.
set -euo pipefail

if [[ ${1:-} == --help ]]; then
  printf 'Usage: scripts/review-reuse.sh [base-commit]\n'
  printf 'Reviews tracked Lean changes from the base (default HEAD), plus untracked Lean files.\n'
  exit 0
fi
if [[ $# -gt 1 ]]; then
  printf 'Usage: scripts/review-reuse.sh [base-commit]\n' >&2
  exit 2
fi
cd "$(git rev-parse --show-toplevel)"
review_base=$(git rev-parse --verify --end-of-options "${1:-HEAD}^{commit}")

review_sites() {
  awk -v source_file="${1:-}" '
    BEGIN {
      declaration = "^[[:space:]]*(@\\[[^]]*\\][[:space:]]*)*"
      declaration = declaration "((private|protected|public|noncomputable|unsafe|partial|nonrec"
      declaration = declaration "|meta)"
      declaration = declaration "[[:space:]]+)*"
      declaration = declaration "(def|abbrev|system|converter|interface|structure|class)"
      declaration = declaration "[[:space:]]"
      construction = "((TypedSystem|Resource)\\.sample|Distribution\\.(uniform|prod|pi|fTransform)"
      construction = construction "|ProbDist\\.(map|bind|jointLaw)|prodProbDist)([^[:alnum:]_]|$)"
      construction = construction "|←\\$|𝒰\\["
    }
    function inspect(text, line) {
      if (source_file !~ /\.lean$/) return
      if (text ~ declaration)
        printf "%s:%d: definition: %s\n", source_file, line, text
      else if (text ~ construction)
        printf "%s:%d: law or sampling: %s\n", source_file, line, text
    }
    mode == "file" { inspect($0, NR); next }
    /^\+\+\+ b\// { source_file = substr($0, 7); next }
    /^@@ / {
      split($3, range, ",")
      next_line = substr(range[1], 2) + 0
      next
    }
    /^\+/ { inspect(substr($0, 2), next_line); next_line++; next }
    /^ / { next_line++ }
  ' mode="${2:-diff}"
}

printf 'Reuse review candidates: inspect ownership, existing declarations and sampling scope.\n'
git -c core.quotepath=false diff --no-ext-diff --no-color --unified=0 "$review_base" -- '*.lean' |
  review_sites
while IFS= read -r -d '' review_file; do
  [[ $review_file == *.lean ]] || continue
  review_sites "$review_file" file < "$review_file"
done < <(git ls-files --others --exclude-standard -z -- '*.lean')
