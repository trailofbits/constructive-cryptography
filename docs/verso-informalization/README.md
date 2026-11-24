# Isolated Verso Consumer Package (`verso-informalization`)

This package consumes the canonical `Informalization.Core.Explanation.Document` JSON exported by
`Informalization.Render.Json` and renders **ETH CADMO Palatino monographs, papers, chapters, and
slides** without coupling Verso's Lean toolchain pin to `cc-informalization`'s Lean 4.35.0 core.

## Why Isolation?

- **Zero impact on core builds:** The root `lakefile.lean` never imports Verso, and core libraries
  (`Probability`, `RandomSystems`, `ConstructiveCryptography`) remain completely unaffected.
- **Independent toolchain pins:** Verso releases track specific Lean 4 versions. Because this
  directory carries its own `lean-toolchain` and `lakefile.toml`, you can point it at any
  Verso-compatible Lean release while `cc-informalization` stays on Lean 4.35.0.
- **One canonical checked IR:** Lean Infoview (`ProofWidgets`), standalone CADMO HTML
  (`Informalization.Render.Html`), and Verso chapters all render the exact same checked
  `Document` JSON—zero duplicated proof decompilation and zero hand-copied math claims.

## Directory Layout

```text
docs/verso-informalization/
  README.md                          # This guide
  lean-toolchain                     # Independent toolchain pin (default: Lean 4.35.0)
  lakefile.toml                      # Standalone Lake package (offline-ready; optional Verso dep)
  VersoInformalization.lean          # Root library module
  VersoInformalization/
    Schema.lean                      # Canonical Explanation.Document JSON decoder
    CadmoBlocks.lean                 # Reusable ETH CADMO HTML & Verso chapter block builders
  Main.lean                          # `lake exe verso-informalize` CLI
  scripts/
    render_verso_bundle.py           # Zero-dependency offline multi-chapter HTML + Verso stub generator
  tests/
    test_informalization_pipeline.py # End-to-end positive + negative CI & bundle tests
```

## Quick Start 1: Offline Multi-Chapter ETH CADMO Site + Verso Stubs (Python, Zero Deps)

Works immediately offline without downloading Verso's git dependencies:

```bash
python3 docs/verso-informalization/scripts/render_verso_bundle.py \
  --title "Constructive Cryptography: Checked Informalization" \
  --subtitle "ETH CADMO Monograph Edition" \
  --out-dir /tmp/cadmo-site \
  path/to/chapter1.json path/to/chapter2.json
```

You can also weave optional Markdown/Verso prose chapters alongside canonical `Document` JSONs:

```bash
python3 docs/verso-informalization/scripts/render_verso_bundle.py \
  --title "SHA-3 SequenceMAC" \
  --doc path/to/sha3_public_mac.json \
  --chapter path/to/intro.md \
  --out-dir /tmp/sha3-site
```

Or pass a JSON manifest (`--manifest monograph.json`) describing ordered chapters:

```json
{
  "title": "Constructive Cryptography Monograph",
  "subtitle": "Mechanically Checked Proofs",
  "chapters": [
    {
      "slug": "ch01-aead",
      "title": "Authenticated Encryption",
      "json": "exports/aead.json",
      "prose": "prose/ch01-aead.md"
    }
  ]
}
```

Outputs generated in `<out-dir>`:
- `index.html` — ETH CADMO Palatino cover & Table of Contents with axiom audit badges.
- `chapters/<slug>.html` — Full interactive ETH CADMO reader pages (`⊕`/`⊖`, `Paper` ↔ `Auditor`
  mode toggle, right-margin `SymbolInspector` & `GoalState` panels, embedded `Rendering` CC
  diagrams, dark/light ink toggle).
- `verso/<Module>.lean` + `verso/Monograph.lean` — Ready-to-compile Verso `.lean` source stubs
  referencing each chapter's canonical JSON.

## Quick Start 2: Build & Run the Isolated Lean Package

```bash
cd docs/verso-informalization
lake build

# Verify JSON decoding and inspect summary
lake exe verso-informalize inspect /path/to/doc.json

# Emit static ETH CADMO HTML fragment
lake exe verso-informalize render-body /path/to/doc.json /tmp/body.html

# Emit a Verso .lean chapter stub
lake exe verso-informalize verso-stub /path/to/doc.json /tmp/Chapter.lean ChapterOne
```

## Enabling Full Verso Publication Backends (PDF / LaTeX / Slides)

When you are ready to compile full Verso manuals, LaTeX/PDF monographs (`memoir` + `mathpazo`),
or Verso slides:

1. Export your checked theorem(s) from the main `cc-informalization` repo:
   ```lean
   #informalize_json MyNamespace.myTheorem to "exports/my_theorem.json"
   ```
2. Validate the exported JSON with the CI gate:
   ```bash
   python3 scripts/check_informalization.py exports/my_theorem.json
   ```
3. In `docs/verso-informalization/lean-toolchain`, set the Lean version matched by your desired
   Verso release.
4. Uncomment the `[[require]] name = "verso"` block in `docs/verso-informalization/lakefile.toml`
   and run `lake update verso`.
5. Use `VersoInformalization.Schema.loadDocumentFile` and `VersoInformalization.CadmoBlocks`
   inside your Verso document's custom block/role expanders to inject checked `Entry`,
   `ProofNode`, `CalcStep`, `SymbolInspector`, and `Rendering` diagram blocks directly into
   Verso chapters, papers, or slides.

## Automated Quality Gate & Self-Test

Validate any exported `.json` or `.html` artifact (zero-leakage, axiom audit, sibling dedup,
broken inspector keys, English/CADMO typography, and optional Playwright browser checks):

```bash
python3 scripts/check_informalization.py path/to/doc.json path/to/chapter.html
python3 scripts/check_informalization.py --playwright --screenshot /tmp/check.png path/to/chapter.html
```

Run the built-in positive + negative unit test suite:

```bash
python3 docs/verso-informalization/tests/test_informalization_pipeline.py
```
