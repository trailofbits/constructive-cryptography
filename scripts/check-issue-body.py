#!/usr/bin/env python3
"""Check a local GitHub issue draft against its Markdown template."""

import argparse
from pathlib import Path
import re


TEMPLATES = Path(__file__).resolve().parents[1] / ".github" / "ISSUE_TEMPLATE"


def sections(markdown):
    """Read level-two headings outside fenced examples and their visible contents."""
    result = []
    fence = ""
    for line in re.sub(r"<!--.*?-->", "", markdown, flags=re.DOTALL).splitlines():
        stripped = line.strip()
        if fence:
            if stripped.startswith(fence) and not stripped.strip(fence[0]):
                fence = ""
            elif result and stripped:
                result[-1][1].append(stripped)
            continue
        match = re.match(r"^(`{3,}|~{3,})", stripped)
        if match:
            fence = match[1]
            continue
        elif line.startswith("## "):
            result.append((line[3:].strip(), []))
        if result and stripped and not line.startswith("## "):
            result[-1][1].append(stripped)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("kind", choices=sorted(path.stem for path in TEMPLATES.glob("*.md")))
    parser.add_argument("body", type=Path)
    args = parser.parse_args()
    expected = [name for name, _ in sections((TEMPLATES / f"{args.kind}.md").read_text())]
    body = args.body.read_text()
    if body.lstrip().startswith("---"):
        parser.exit(1, "Remove the template front matter before publishing.\n")
    actual = sections(body)
    if [name for name, _ in actual] != expected:
        parser.exit(1, "Expected these headings in order: " + ", ".join(expected) + "\n")
    for name, content in actual:
        if not content:
            parser.exit(1, f"Fill in the {name} section.\n")


if __name__ == "__main__":
    main()
