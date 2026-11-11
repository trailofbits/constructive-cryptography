#!/usr/bin/env bash
# Exercise the public entry point against small core-only fixture packages.
set -euo pipefail
repo=$(cd "$(dirname "$0")/.." && pwd)
fixture=$(mktemp -d)
trap 'code=$?; if [[ $code == 0 ]]; then rm -rf "$fixture"; else echo "fixture: $fixture"; fi' EXIT
mkdir -p "$fixture/src/Fixture"
cp "$repo/lean-toolchain" "$fixture/lean-toolchain"
cat > "$fixture/lakefile.lean" <<'LEAN'
import Lake
open Lake DSL
package fixture where
  srcDir := "src"
  buildDir := (get_config? focusedBuildDir).getD ".lake/build"
lean_lib Fixture
LEAN
cat > "$fixture/lake-manifest.json" <<'JSON'
{"version":"1.3.0","packagesDir":".lake/packages","name":"fixture","lakeDir":".lake","packages":[]}
JSON
cat > "$fixture/src/Fixture/Owner.lean" <<'LEAN'
module
@[expose] public section
def answer : Nat := 7
LEAN
cat > "$fixture/src/Fixture/Consumer.lean" <<'LEAN'
module
public import Fixture.Owner
example : answer = 7 := rfl
LEAN
check() {
  "$repo/scripts/check-focused.sh" --project "$fixture" --owner Fixture.Owner \
    --consumer Fixture.Consumer --output "$fixture/$1"
}
default_path() {
  local paths
  paths=$(cd "$fixture" && lake env printenv LEAN_PATH)
  [[ "$paths" == *"$fixture/.lake/build/lib/lean"* ]]
  [[ "$paths" != *"/positive/build/"* && "$paths" != *"/missing/build/"* ]]
}
reject() {
  if check "$1"; then
    echo "error: $1 control unexpectedly passed" >&2
    exit 1
  fi
  default_path
  python3 - "$fixture/$1/manifest.json" "$2" <<'PY'
import json, sys
from pathlib import Path
record = json.loads(Path(sys.argv[1]).read_text())
assert record["status"] == "failed"
assert sys.argv[2] in record["error"], record
PY
}
check positive
default_path
# Seed a valid ordinary artifact, then break its source. Isolated checking must reject it.
(cd "$fixture" && lake build Fixture.Consumer)
printf '\nexample : False := True.intro\n' >> "$fixture/src/Fixture/Owner.lean"
reject stale 'command failed'
grep -q 'error: src/Fixture/Owner.lean:.*Type mismatch' "$fixture/stale/build.log"
python3 - "$fixture/src/Fixture/Owner.lean" <<'PY'
from pathlib import Path
import sys
p = Path(sys.argv[1]); p.write_text(p.read_text().replace("example : False := True.intro", ""))
PY
printf '\nexample : False := True.intro\n' >> "$fixture/src/Fixture/Consumer.lean"
reject consumer 'command failed'
grep -q 'error: src/Fixture/Consumer.lean:.*Type mismatch' "$fixture/consumer/build.log"
python3 - "$fixture/src/Fixture/Consumer.lean" <<'PY'
from pathlib import Path
import sys
p = Path(sys.argv[1]); p.write_text(p.read_text().replace("example : False := True.intro", ""))
PY
printf '\nset_option linter.unusedVariables true in\ndef unused (n : Nat) : Nat := 0\n' \
  >> "$fixture/src/Fixture/Consumer.lean"
reject warning 'command failed'
grep -q 'warning:' "$fixture/warning/build.log"
python3 - "$fixture/src/Fixture/Consumer.lean" <<'PY'
from pathlib import Path
import sys
p = Path(sys.argv[1]); p.write_text(p.read_text().split("set_option linter.unusedVariables")[0])
PY
# A test-only wrapper removes a real successful output before the entry point verifies it.
mkdir "$fixture/bin"
export FOCUSED_REAL_LAKE
FOCUSED_REAL_LAKE=$(command -v lake)
cat > "$fixture/bin/lake" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
"$FOCUSED_REAL_LAKE" "$@"
for arg in "$@"; do
  case "$arg" in
    -KfocusedBuildDir=*) rm "${arg#*=}/lib/lean/Fixture/Consumer.olean" ;;
  esac
done
SH
chmod +x "$fixture/bin/lake"
PATH="$fixture/bin:$PATH" reject missing 'missing output'
python3 - "$fixture/missing/manifest.json" <<'PY'
import json, sys
from pathlib import Path
record = json.loads(Path(sys.argv[1]).read_text())
assert record["commands"][-2]["exit"] == 0
assert record["commands"][-1]["argv"] == ["lake", "--reconfigure", "env", "true"]
PY
echo 'focused controls: success, stale artifact, failed consumer, warning, missing output passed'
