#!/usr/bin/env bash
# Canonical focused builds through Lake; Python uses only its standard library.
set -euo pipefail
exec python3 - "$0" "$@" <<'PY'
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

checkout = Path(sys.argv[1]).resolve().parent.parent
parser = argparse.ArgumentParser(
    description="Build owners and consumers in a new Lake output directory")
parser.add_argument("--project", type=Path, default=checkout)
parser.add_argument("--output", type=Path, required=True)
for role in ("dependency", "owner", "consumer"):
    parser.add_argument("--" + role, action="append", default=[])
args = parser.parse_args(sys.argv[2:])
project = args.project.resolve()
output = args.output.resolve()
output.mkdir(parents=True, exist_ok=False)
manifest = {"status": "incomplete", "project": str(project), "checkout": str(checkout),
            "started": time.time(), "commands": [],
            "targets": {role: getattr(args, role) for role in ("dependency", "owner", "consumer")}}
log = (output / "build.log").open("w")
config_touched = False

def interrupted(signum, frame):
    raise KeyboardInterrupt(f"received signal {signum}")

signal.signal(signal.SIGTERM, interrupted)

def save():
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")

def run(command, cwd=project):
    entry = {"argv": [str(x) for x in command], "cwd": str(cwd), "exit": None}
    manifest["commands"].append(entry)
    save()
    log.write("$ " + repr(entry["argv"]) + "\n")
    log.flush()
    process = subprocess.Popen(entry["argv"], cwd=cwd, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, text=True, start_new_session=True)
    captured = []
    try:
        for line in process.stdout:
            log.write(line)
            log.flush()
            captured.append(line)
        entry["exit"] = process.wait()
    except BaseException:
        if process.poll() is None:
            os.killpg(process.pid, signal.SIGTERM)
        entry["exit"] = process.wait()
        save()
        raise
    save()
    if entry["exit"]:
        raise RuntimeError(f"command failed ({entry['exit']}): {entry['argv']}")
    return "".join(captured).strip()

def identity(root):
    # Include generated fixtures and untracked sources, independently of Git membership.
    digest = hashlib.sha256()
    count = 0
    for directory, dirs, files in os.walk(root):
        dirs[:] = sorted(d for d in dirs if d not in (".git", ".lake", "Scratch")
                         and (Path(directory) / d).resolve() != output)
        for name in sorted(files):
            path = Path(directory) / name
            if path.suffix not in (".lean", ".sh", ".toml") and name not in (
                    "lean-toolchain", "lake-manifest.json"):
                continue
            digest.update(str(path.relative_to(root)).encode() + b"\0")
            digest.update(hashlib.sha256(path.read_bytes()).digest())
            count += 1
    return {"sha256": digest.hexdigest(), "files": count}

try:
    save()
    if not args.owner or not args.consumer:
        raise ValueError("at least one --owner and --consumer are required")
    modules = list(dict.fromkeys(args.dependency + args.owner + args.consumer))
    for module in modules:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*", module):
            raise ValueError(f"not a canonical module name: {module}")
        if not (project / "src" / (module.replace(".", "/") + ".lean")).is_file():
            raise ValueError(f"missing root-package source: {module}")
    manifest["checkout_revision"] = run(["git", "rev-parse", "HEAD"], checkout)
    manifest["checkout_status"] = run(
        ["git", "status", "--porcelain=v1", "--untracked-files=all"], checkout)
    manifest["checkout_diff_sha256"] = hashlib.sha256(
        run(["git", "diff", "HEAD", "--binary"], checkout).encode()).hexdigest()
    manifest["source_identity"] = identity(project)
    manifest["toolchain"] = (project / "lean-toolchain").read_text().strip()
    lock = json.loads((project / "lake-manifest.json").read_text())
    manifest["lake_manifest"] = lock
    dependencies = []
    for package in lock["packages"]:
        path = (project / lock.get("packagesDir", ".lake/packages") / package["name"]).resolve()
        if not path.is_dir():
            raise ValueError(f"manifest package is not provisioned: {path}")
        dependency = {"name": package["name"], "path": str(path), "source_identity": identity(path)}
        if package.get("type") == "git":
            dependency["revision"] = run(["git", "rev-parse", "HEAD"], path)
            dependency["status"] = run(["git", "status", "--porcelain=v1"], path)
        dependencies.append(dependency)
    manifest["dependencies"] = dependencies
    manifest["lake_version"] = run(["lake", "--version"])
    build = output / "build"
    command = ["lake", "--reconfigure", "-KfocusedBuildDir=" + str(build), "--rehash", "--no-cache",
               "--wfail", "--verbose", "build"] + ["+" + name for name in modules]
    config_touched = True
    run(command)
    artifacts = []
    for module in modules:
        name = module.replace(".", "/")
        for relative in (f"lib/lean/{name}.olean", f"lib/lean/{name}.ilean",
                         f"ir/{name}.setup.json"):
            path = build / relative
            if not path.is_file() or path.stat().st_size == 0:
                raise RuntimeError(f"missing output: {path}")
            artifacts.append(str(path.relative_to(output)))
    manifest["artifacts"] = artifacts
    if identity(project) != manifest["source_identity"]:
        raise RuntimeError("project sources changed during validation")
    for dependency in dependencies:
        if identity(Path(dependency["path"])) != dependency["source_identity"]:
            raise RuntimeError(f"dependency sources changed: {dependency['name']}")
except BaseException as error:
    manifest["status"] = "failed"
    manifest["error"] = str(error)
    log.write(str(error) + "\n")
finally:
    # Lake caches elaborated configuration: restore the ordinary build path on every exit.
    if config_touched:
        try:
            run(["lake", "--reconfigure", "env", "true"])
        except BaseException as error:
            manifest["status"] = "failed"
            manifest["cleanup_error"] = str(error)
    if manifest["status"] == "incomplete":
        manifest["status"] = "passed"
    manifest["finished"] = time.time()
    save()
    log.close()
print(f"focused: {manifest['status']}; evidence: {output}")
sys.exit(0 if manifest["status"] == "passed" else 1)
PY
