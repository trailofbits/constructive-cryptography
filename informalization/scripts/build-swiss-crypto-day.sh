#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "$0")/.." && pwd)"
cbc_root="${INFORMALIZATION_CBC_ROOT:-"$project_root/../../cbc-mac-cc"}"

write_reload_stamp() {
  local directory="$1"
  mkdir -p "$directory"
  printf '%s-%s-%s\n' "$(date +%s)" "$$" "$RANDOM" > \
    "$directory/.informalization-build-stamp"
}

build_informalization() {
  cd "$project_root"

  # This gate re-elaborates the live declaration and rejects an incomplete
  # proof before any reader artifact is refreshed.
  lake exe cbcIntegrationTests

  lake exe informalize \
    "$cbc_root/CBCMAC/Main.lean" \
    CBCMAC.cbc_randomness_expander \
    "--lake-root=$cbc_root" \
    --semantic-json=preview/cbc-mac.semantic.json \
    --json=preview/cbc-mac.document.json \
    --html=preview/cbc-mac.html \
    --profile=random-systems-cbc

  write_reload_stamp "$project_root/preview"
}

build_slides() {
  cd "$project_root/slides"
  lake exe swiss-crypto-day
  write_reload_stamp "$project_root/slides/_draft_talk"
}

case "${1:-}" in
  "")
    build_informalization
    build_slides
    ;;
  --informalization-only)
    build_informalization
    ;;
  --slides-only)
    build_slides
    ;;
  --help|-h)
    printf '%s\n' \
      "Usage: $0 [--informalization-only|--slides-only]" \
      "With no option, regenerate the live CBC informalization and then the deck."
    ;;
  *)
    printf 'Unknown option: %s\n' "$1" >&2
    exit 2
    ;;
esac
