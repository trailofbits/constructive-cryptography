#!/usr/bin/env bash
set -uo pipefail

project_root="$(cd "$(dirname "$0")/.." && pwd)"
cbc_root="${INFORMALIZATION_CBC_ROOT:-"$project_root/.lake/packages/cbc-mac-cc"}"
abstract_crypto_root="${INFORMALIZATION_ABSTRACT_CRYPTO_ROOT:-"$project_root/.."}"
interval="${INFORMALIZATION_WATCH_INTERVAL:-1}"
serve=false
port=8766

usage() {
  printf '%s\n' \
    "Usage: $0 [--serve] [--port PORT]" \
    "Watch the live CBC proof, abstract-crypto, the informalizer, and the Verso deck." \
    "Successful rebuilds reload localhost readers automatically."
}

while (($# > 0)); do
  case "$1" in
    --serve)
      serve=true
      shift
      ;;
    --port)
      if (($# < 2)); then
        printf '%s\n' "--port requires a value" >&2
        exit 2
      fi
      port="$2"
      shift 2
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      printf 'Unknown option: %s\n' "$1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

fingerprint() {
  find "$@" \
    \( -name .lake -o -name .git -o -name Scratch -o -name _draft_talk \) -prune -o \
    -type f -print 2>/dev/null |
    while IFS= read -r path; do
      stat -f '%N|%m|%z' "$path" 2>/dev/null || true
    done |
    LC_ALL=C sort |
    shasum |
    cut -d ' ' -f 1
}

core_fingerprint() {
  fingerprint \
    "$project_root/Informalization" \
    "$project_root/LanguageDesign" \
    "$project_root/LeanTeX" \
    "$project_root/web" \
    "$project_root/Informalization.lean" \
    "$project_root/LanguageDesign.lean" \
    "$project_root/lakefile.lean" \
    "$project_root/lean-toolchain" \
    "$cbc_root/CBCMAC" \
    "$cbc_root/lakefile.lean" \
    "$cbc_root/lean-toolchain" \
    "$abstract_crypto_root/ConstructiveCryptography" \
    "$abstract_crypto_root/RandomSystems" \
    "$abstract_crypto_root/RandomSystemsCC" \
    "$abstract_crypto_root/Probability" \
    "$abstract_crypto_root/lakefile.lean" \
    "$abstract_crypto_root/lean-toolchain"
}

slide_fingerprint() {
  fingerprint \
    "$project_root/slides/DraftTalk.lean" \
    "$project_root/slides/MainDraftTalk.lean" \
    "$project_root/slides/static" \
    "$project_root/slides/tikz" \
    "$project_root/slides/lakefile.lean" \
    "$project_root/slides/lean-toolchain"
}

run_build() {
  local stage="$1"
  shift
  printf '[informalization-watch] rebuilding %s\n' "$stage"
  if "$project_root/scripts/build-swiss-crypto-day.sh" "$@"; then
    printf '[informalization-watch] %s is current\n' "$stage"
  else
    printf '[informalization-watch] %s failed; retaining the last valid output\n' \
      "$stage" >&2
  fi
}

server_pid=""
stop_server() {
  if [[ -n "$server_pid" ]]; then kill "$server_pid" 2>/dev/null || true; fi
}
trap stop_server EXIT INT TERM

if [[ "$serve" == true ]]; then
  mkdir -p "$project_root/slides/_draft_talk"
  if command -v lsof >/dev/null &&
      lsof -nP -iTCP:"$port" -sTCP:LISTEN >/dev/null 2>&1; then
    printf '[informalization-watch] using the existing server on http://127.0.0.1:%s\n' \
      "$port"
  else
    (
      cd "$project_root/slides/_draft_talk"
      python3 -m http.server "$port" --bind 127.0.0.1
    ) &
    server_pid="$!"
    printf '[informalization-watch] serving http://127.0.0.1:%s\n' "$port"
  fi
fi

core_state="$(core_fingerprint)"
slide_state="$(slide_fingerprint)"
run_build "informalization and deck"

printf '[informalization-watch] watching for changes\n'
while true; do
  sleep "$interval"
  next_core_state="$(core_fingerprint)"
  next_slide_state="$(slide_fingerprint)"

  if [[ "$next_core_state" != "$core_state" ]]; then
    core_state="$next_core_state"
    slide_state="$next_slide_state"
    run_build "informalization and deck"
  elif [[ "$next_slide_state" != "$slide_state" ]]; then
    slide_state="$next_slide_state"
    run_build "deck" --slides-only
  fi
done
