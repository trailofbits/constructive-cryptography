#!/usr/bin/env python3
"""
Zero-dependency offline ETH CADMO + Verso bundle generator.

Consumes one or more canonical `Informalization.Core.Explanation.Document` JSON
files (exported by `Informalization.Render.Json`) plus optional Markdown/Verso
prose chapters, and generates:
  1. A styled multi-chapter ETH CADMO Palatino HTML monograph site (`index.html`
     + `chapters/<slug>.html`) with interactive `⊕`/`⊖`, `Paper` <-> `Auditor`
     disclosure toggle, right-margin type-aware `SymbolInspector` / `GoalState`,
     and embedded `Rendering` CC diagrams.
  2. Ready-to-use Verso `.lean` chapter source stubs (`verso/<Module>.lean` +
     `verso/Monograph.lean`) referencing the canonical JSON data so Verso
     publication works offline immediately without fetching Verso git deps.

Requires Python 3.9+ standard library only.
"""
from __future__ import annotations

import argparse
import html
import json
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


REPO_ROOT = Path(__file__).resolve().parents[3]
CADMO_CSS_PATH = REPO_ROOT / "src" / "Informalization" / "Render" / "cadmo-reader.css"
CADMO_JS_PATH = REPO_ROOT / "src" / "Informalization" / "Render" / "cadmo-reader.js"
CC_DIAGRAM_CSS_PATH = REPO_ROOT / "src" / "Rendering" / "cc-diagram.css"
CC_INSPECTOR_JS_PATH = REPO_ROOT / "src" / "Rendering" / "inspector.js"


EXTRA_VERSO_SITE_CSS = """
/* Multi-chapter Verso Monograph Navigation & Prose Extensions */
.cadmo-chapter-nav {
  background: var(--cadmo-surface);
  border-bottom: 1px solid var(--cadmo-rule);
  font-family: var(--cadmo-sans);
  font-size: 0.78rem;
}
.cadmo-chapter-nav-inner {
  max-width: calc(var(--cadmo-measure) + var(--cadmo-margin-width) + var(--cadmo-gap) + 4rem);
  margin: 0 auto;
  padding: 0.45rem 2rem;
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  justify-content: space-between;
  gap: 0.5rem 1.25rem;
}
.cadmo-chapter-nav a {
  color: var(--cadmo-accent);
  text-decoration: none;
}
.cadmo-chapter-nav a:hover {
  text-decoration: underline;
}
.cadmo-chapter-prose {
  max-width: calc(var(--cadmo-measure) + var(--cadmo-margin-width) + var(--cadmo-gap) + 4rem);
  margin: 0 auto;
  padding: 1.8rem 2rem 0;
}
.cadmo-chapter-prose-inner {
  max-width: var(--cadmo-measure);
  padding-bottom: 1.4rem;
  border-bottom: 1px solid var(--cadmo-rule);
}
.cadmo-chapter-prose h1,
.cadmo-chapter-prose h2,
.cadmo-chapter-prose h3 {
  font-weight: 400;
  color: var(--cadmo-ink);
  margin: 1.2rem 0 0.5rem;
}
.cadmo-chapter-prose blockquote {
  margin: 0.9rem 0;
  padding: 0.5rem 1rem;
  border-left: 2px solid var(--cadmo-rule-strong);
  background: var(--cadmo-note-bg);
  color: var(--cadmo-ink-soft);
  font-style: italic;
}
.cadmo-toc-list {
  list-style: none;
  padding: 0;
  margin: 1.5rem 0 0;
}
.cadmo-toc-item {
  display: flex;
  flex-wrap: wrap;
  align-items: baseline;
  justify-content: space-between;
  gap: 0.5rem 1rem;
  padding: 0.95rem 0;
  border-bottom: 1px solid var(--cadmo-rule);
}
.cadmo-toc-link {
  font-size: 1.15rem;
  color: var(--cadmo-ink);
  text-decoration: none;
}
.cadmo-toc-link:hover {
  color: var(--cadmo-accent);
}
.cadmo-toc-num {
  font-variant-caps: all-small-caps;
  letter-spacing: 0.08em;
  color: var(--cadmo-accent);
  margin-right: 0.55rem;
}
.cadmo-toc-subtitle {
  width: 100%;
  margin: 0.2rem 0 0;
  font-style: italic;
  font-size: 0.92rem;
  color: var(--cadmo-muted);
}
"""


FALLBACK_CADMO_CSS = """
:root { --cadmo-bg: #fdfcfa; --cadmo-ink: #1c1b19; --cadmo-accent: #1f4e79;
        --cadmo-rule: #dedad0; --cadmo-surface: #f6f4ef; --cadmo-muted: #6e6a62;
        --cadmo-measure: 43rem; --cadmo-margin-width: 21.5rem; --cadmo-gap: 2.75rem;
        --cadmo-serif: "Palatino Linotype", "TeX Gyre Pagella", Palatino, Georgia, serif;
        --cadmo-sans: system-ui, sans-serif; --cadmo-mono: Menlo, monospace; }
body { margin: 0; background: var(--cadmo-bg); color: var(--cadmo-ink);
       font-family: var(--cadmo-serif); line-height: 1.66; }
"""


def read_asset(path: Path, fallback: str = "") -> str:
    if path.is_file():
        return path.read_text(encoding="utf-8")
    return fallback


def escape_json_for_script(raw_json: str) -> str:
    return (
        raw_json.replace("<", "\\u003c")
        .replace(">", "\\u003e")
        .replace("&", "\\u0026")
    )


def escape_css_for_style(css: str) -> str:
    return css.replace("<", "\\3c ")


def slugify(text: str) -> str:
    slug = re.sub(r"[^a-zA-Z0-9]+", "-", text.strip().lower()).strip("-")
    return slug or "chapter"


def to_lean_module_name(slug: str, index: int) -> str:
    parts = [p for p in re.split(r"[^a-zA-Z0-9]+", slug) if p]
    camel = "".join(p[:1].upper() + p[1:] for p in parts)
    if not camel or not camel[0].isalpha():
        camel = f"Chapter{index + 1}{camel}"
    return camel


def render_inline_markdown(text: str) -> str:
    """Minimal zero-dependency inline Markdown (bold, italic, inline code, links)."""
    escaped = html.escape(text)
    escaped = re.sub(r"`([^`]+)`", r"<code>\1</code>", escaped)
    escaped = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", escaped)
    escaped = re.sub(r"\*([^*]+)\*", r"<em>\1</em>", escaped)
    escaped = re.sub(
        r"\[([^\]]+)\]\(([^)]+)\)",
        lambda m: f'<a href="{m.group(2)}">{m.group(1)}</a>',
        escaped,
    )
    return escaped


def render_markdown_to_html(md_text: str) -> str:
    """Convert lightweight Markdown/Verso prose chapters to clean ETH CADMO HTML."""
    lines = md_text.splitlines()
    out: List[str] = []
    para_buf: List[str] = []
    list_buf: List[str] = []
    in_code = False
    code_buf: List[str] = []

    def flush_para() -> None:
        if para_buf:
            joined = " ".join(s.strip() for s in para_buf).strip()
            if joined:
                out.append(f"<p>{render_inline_markdown(joined)}</p>")
            para_buf.clear()

    def flush_list() -> None:
        if list_buf:
            items = "".join(f"<li>{render_inline_markdown(it)}</li>" for it in list_buf)
            out.append(f"<ul>{items}</ul>")
            list_buf.clear()

    for line in lines:
        stripped = line.strip()
        if stripped.startswith("```"):
            flush_para()
            flush_list()
            if in_code:
                out.append(
                    '<pre class="cadmo-pseudocode">'
                    + html.escape("\n".join(code_buf))
                    + "</pre>"
                )
                code_buf.clear()
                in_code = False
            else:
                in_code = True
            continue
        if in_code:
            code_buf.append(line)
            continue

        # Skip Verso block directive markers when splitting/rendering prose
        if stripped.startswith(":::"):
            flush_para()
            flush_list()
            continue

        if not stripped:
            flush_para()
            flush_list()
            continue

        heading_match = re.match(r"^(#{1,4})\s+(.*)$", stripped)
        if heading_match:
            flush_para()
            flush_list()
            level = min(len(heading_match.group(1)) + 1, 4)
            out.append(f"<h{level}>{render_inline_markdown(heading_match.group(2))}</h{level}>")
            continue

        if stripped.startswith("> "):
            flush_para()
            flush_list()
            out.append(f"<blockquote>{render_inline_markdown(stripped[2:])}</blockquote>")
            continue

        list_match = re.match(r"^[-*]\s+(.*)$", stripped)
        if list_match:
            flush_para()
            list_buf.append(list_match.group(1))
            continue

        flush_list()
        para_buf.append(stripped)

    flush_para()
    flush_list()
    if code_buf:
        out.append('<pre class="cadmo-pseudocode">' + html.escape("\n".join(code_buf)) + "</pre>")
    return "\n".join(out)


def split_prose_around_doc_marker(prose_md: str) -> Tuple[str, str]:
    """Allow prose chapters to place `:::cadmo-doc` to wrap prose before & after proofs."""
    marker_re = re.compile(r"^\s*:::cadmo-doc\b.*$", re.MULTILINE)
    m = marker_re.search(prose_md)
    if not m:
        return prose_md, ""
    return prose_md[: m.start()], prose_md[m.end() :]


def render_chapter_html(
    doc: Dict[str, Any],
    chapter_title: str,
    monograph_title: str,
    prose_md: Optional[str],
    prev_link: Optional[Tuple[str, str]],
    next_link: Optional[Tuple[str, str]],
    index_href: str,
    cadmo_css: str,
    cadmo_js: str,
    cc_css: str,
    cc_inspector_js: str,
) -> str:
    payload_str = json.dumps(doc, ensure_ascii=False, separators=(",", ":"))
    json_payload = escape_json_for_script(payload_str)

    nav_parts = [f'<a href="{html.escape(index_href)}">← {html.escape(monograph_title)}</a>']
    pager: List[str] = []
    if prev_link:
        pager.append(f'<a href="{html.escape(prev_link[0])}">‹ {html.escape(prev_link[1])}</a>')
    if next_link:
        pager.append(f'<a href="{html.escape(next_link[0])}">{html.escape(next_link[1])} ›</a>')
    pager_html = " · ".join(pager)
    chapter_nav = (
        '<div class="cadmo-chapter-nav" role="navigation" aria-label="Chapter navigation">'
        '<div class="cadmo-chapter-nav-inner">'
        f"<div>{nav_parts[0]}</div>"
        f"<div>{pager_html}</div>"
        "</div></div>"
    )

    prose_before_html = ""
    prose_after_html = ""
    if prose_md and prose_md.strip():
        before_md, after_md = split_prose_around_doc_marker(prose_md)
        if before_md.strip():
            prose_before_html = (
                '<section class="cadmo-chapter-prose" aria-label="Chapter introduction">'
                f'<div class="cadmo-chapter-prose-inner">{render_markdown_to_html(before_md)}</div>'
                "</section>"
            )
        if after_md.strip():
            prose_after_html = (
                '<section class="cadmo-chapter-prose" aria-label="Chapter discussion">'
                f'<div class="cadmo-chapter-prose-inner">{render_markdown_to_html(after_md)}</div>'
                "</section>"
            )

    inspector_script_tag = (
        f"<script data-cc-inspector>{cc_inspector_js}</script>" if cc_inspector_js.strip() else ""
    )

    full_cadmo_css = escape_css_for_style(cadmo_css + "\n" + EXTRA_VERSO_SITE_CSS)
    full_cc_css = escape_css_for_style(cc_css)

    return (
        "<!doctype html>\n"
        '<html lang="en">\n'
        "<head>\n"
        '  <meta charset="utf-8">\n'
        '  <meta name="viewport" content="width=device-width,initial-scale=1">\n'
        '  <meta name="color-scheme" content="light dark">\n'
        f"  <title>{html.escape(chapter_title)} — {html.escape(monograph_title)}</title>\n"
        f"  <style data-cc-diagram>{full_cc_css}</style>\n"
        f"  <style data-cadmo-reader>{full_cadmo_css}</style>\n"
        "</head>\n"
        "<body>\n"
        f"  {chapter_nav}\n"
        f"  {prose_before_html}\n"
        '  <div id="cadmo-root"></div>\n'
        f"  {prose_after_html}\n"
        f'  <script id="cadmo-document-data" type="application/json">{json_payload}</script>\n'
        f"  <script data-cadmo-controller>{cadmo_js}</script>\n"
        f"  {inspector_script_tag}\n"
        "</body>\n"
        "</html>\n"
    )


def render_index_html(
    monograph_title: str,
    monograph_subtitle: Optional[str],
    chapters: List[Dict[str, Any]],
    cadmo_css: str,
) -> str:
    full_css = escape_css_for_style(cadmo_css + "\n" + EXTRA_VERSO_SITE_CSS)
    items_html: List[str] = []
    for idx, ch in enumerate(chapters):
        doc = ch["doc"]
        entries = doc.get("entries", [])
        has_sorry = any((e.get("axioms") or {}).get("hasSorry", False) for e in entries)
        total_decls = len(entries)
        badge_cls = "cadmo-axiom-pill has-sorry" if has_sorry else "cadmo-axiom-pill"
        badge_txt = "⚠ sorry" if has_sorry else f"✓ {total_decls} checked"
        sub = doc.get("subtitle")
        sub_html = f'<p class="cadmo-toc-subtitle">{html.escape(sub)}</p>' if sub else ""
        items_html.append(
            '<li class="cadmo-toc-item">'
            f'<a class="cadmo-toc-link" href="chapters/{html.escape(ch["slug"])}.html">'
            f'<span class="cadmo-toc-num">Chapter {idx + 1}</span>'
            f'{html.escape(ch["title"])}</a>'
            f'<span class="{badge_cls}">{badge_txt}</span>'
            f"{sub_html}"
            "</li>"
        )

    subtitle_html = (
        f'<p class="cadmo-doc-subtitle">{html.escape(monograph_subtitle)}</p>'
        if monograph_subtitle
        else ""
    )

    return (
        "<!doctype html>\n"
        '<html lang="en">\n'
        "<head>\n"
        '  <meta charset="utf-8">\n'
        '  <meta name="viewport" content="width=device-width,initial-scale=1">\n'
        '  <meta name="color-scheme" content="light dark">\n'
        f"  <title>{html.escape(monograph_title)}</title>\n"
        f"  <style data-cadmo-reader>{full_css}</style>\n"
        "</head>\n"
        "<body>\n"
        '  <div class="cadmo-shell">\n'
        '    <main class="cadmo-main">\n'
        '      <header class="cadmo-doc-header">\n'
        '        <div class="cadmo-kicker">Constructive Cryptography · Verso CADMO Edition</div>\n'
        f'        <h1 class="cadmo-doc-title">{html.escape(monograph_title)}</h1>\n'
        f"        {subtitle_html}\n"
        "      </header>\n"
        '      <section aria-label="Table of contents">\n'
        f'        <ol class="cadmo-toc-list">{"".join(items_html)}</ol>\n'
        "      </section>\n"
        "    </main>\n"
        '    <aside class="cadmo-margin" aria-label="Edition notes">\n'
        '      <div class="cadmo-inspector-card">\n'
        '        <div class="cadmo-inspector-kicker">Checked Informalization</div>\n'
        '        <p style="margin:0.45rem 0 0;color:var(--cadmo-ink-soft);">'
        "Every chapter is rendered directly from canonical Lean-checked "
        "<code>Explanation.Document</code> JSON. Open any chapter to explore "
        "recursive ⊕ proof steps, Paper/Auditor disclosure modes, and type-aware "
        "symbol inspectors."
        "        </p>\n"
        "      </div>\n"
        "    </aside>\n"
        "  </div>\n"
        "</body>\n"
        "</html>\n"
    )


def render_verso_stub(chapter: Dict[str, Any], json_rel_path: str) -> str:
    doc = chapter["doc"]
    mod_name = chapter["module_name"]
    title = chapter["title"]
    subtitle = doc.get("subtitle")
    prose_md = (chapter.get("prose_md") or "").strip()

    entry_blocks: List[str] = []
    for e in doc.get("entries", []):
        decl = e.get("declaration", "unknown")
        header = e.get("header", "Theorem")
        etitle = e.get("title")
        heading = f"{header} ({etitle})" if etitle else f"{header}: {decl}"
        ax = e.get("axioms") or {}
        ax_note = (
            "WARNING: depends on sorryAx"
            if ax.get("hasSorry")
            else "axioms: " + ", ".join(ax.get("axioms", []))
        )
        entry_blocks.append(
            f"## {heading}\n\n"
            f"-- Checked Lean declaration: `{decl}` ({ax_note})\n"
            f':::cadmoEntry "{json_rel_path}" "{decl}"\n'
            ":::\n"
        )

    prose_comment = f"\n{prose_md}\n" if prose_md else ""
    subtitle_line = f"\n> *{subtitle}*\n" if subtitle else ""

    return (
        "/-\n"
        f"Auto-generated Verso chapter stub for: {title}\n"
        f"Canonical checked IR: {json_rel_path}\n"
        "-/\n"
        "import VersoInformalization.Schema\n"
        "import VersoInformalization.CadmoBlocks\n\n"
        f"namespace VersoChapters.{mod_name}\n\n"
        f'def documentJsonPath : System.FilePath := "{json_rel_path}"\n\n'
        "def renderChapterBody : IO String := do\n"
        "  let doc ← VersoInformalization.Schema.loadDocumentFile documentJsonPath\n"
        "  return VersoInformalization.CadmoBlocks.renderDocumentBodyHtml doc\n\n"
        "/-!\n"
        f"# {title}\n"
        f"{subtitle_line}"
        f"{prose_comment}\n"
        + "\n".join(entry_blocks)
        + "-/\n\n"
        f"end VersoChapters.{mod_name}\n"
    )


def render_verso_monograph_index(monograph_title: str, chapters: List[Dict[str, Any]]) -> str:
    imports = "\n".join(f"-- import VersoChapters.{ch['module_name']}" for ch in chapters)
    listing = "\n".join(
        f"- Chapter {i + 1}: {ch['title']} (`{ch['module_name']}.lean` ← `data/{ch['slug']}.json`)"
        for i, ch in enumerate(chapters)
    )
    return (
        "/-\n"
        f"Auto-generated Verso monograph index: {monograph_title}\n"
        "-/\n"
        f"{imports}\n\n"
        "/-!\n"
        f"# {monograph_title}\n\n"
        "Chapters generated from canonical checked `Explanation.Document` JSON:\n\n"
        f"{listing}\n"
        "-/\n"
    )


def load_chapters_from_args(args: argparse.Namespace) -> Tuple[str, Optional[str], List[Dict[str, Any]]]:
    chapters: List[Dict[str, Any]] = []
    monograph_title = args.title
    monograph_subtitle = args.subtitle

    if args.manifest:
        manifest_path = Path(args.manifest).resolve()
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        monograph_title = monograph_title or manifest.get("title") or "Constructive Cryptography"
        monograph_subtitle = monograph_subtitle or manifest.get("subtitle")
        base_dir = manifest_path.parent
        for idx, item in enumerate(manifest.get("chapters", [])):
            json_path = (base_dir / item["json"]).resolve()
            doc = json.loads(json_path.read_text(encoding="utf-8"))
            if args.mode:
                doc["defaultMode"] = args.mode
            prose_md = None
            if item.get("prose"):
                prose_md = (base_dir / item["prose"]).resolve().read_text(encoding="utf-8")
            title = item.get("title") or doc.get("title") or f"Chapter {idx + 1}"
            slug = item.get("slug") or slugify(title)
            chapters.append(
                {
                    "slug": slug,
                    "title": title,
                    "doc": doc,
                    "prose_md": prose_md,
                    "module_name": to_lean_module_name(slug, idx),
                    "source_json": str(json_path),
                }
            )
    else:
        doc_paths = list(args.doc or []) + list(args.inputs or [])
        prose_paths = list(args.chapter or [])
        if not doc_paths:
            raise ValueError("Provide at least one canonical Document JSON file or --manifest.")
        for idx, raw_path in enumerate(doc_paths):
            json_path = Path(raw_path).resolve()
            doc = json.loads(json_path.read_text(encoding="utf-8"))
            if args.mode:
                doc["defaultMode"] = args.mode
            prose_md = None
            if idx < len(prose_paths):
                prose_md = Path(prose_paths[idx]).resolve().read_text(encoding="utf-8")
            title = doc.get("title") or json_path.stem
            slug = slugify(f"{idx + 1:02d}-{title}" if len(doc_paths) > 1 else title)
            chapters.append(
                {
                    "slug": slug,
                    "title": title,
                    "doc": doc,
                    "prose_md": prose_md,
                    "module_name": to_lean_module_name(slug, idx),
                    "source_json": str(json_path),
                }
            )
        if not monograph_title:
            monograph_title = (
                chapters[0]["title"]
                if len(chapters) == 1
                else "Constructive Cryptography · Checked Informalization"
            )
        if not monograph_subtitle and len(chapters) == 1:
            monograph_subtitle = chapters[0]["doc"].get("subtitle")

    return monograph_title, monograph_subtitle, chapters


def build_bundle(
    out_dir: Path,
    monograph_title: str,
    monograph_subtitle: Optional[str],
    chapters: List[Dict[str, Any]],
    emit_verso_stubs: bool = True,
) -> Dict[str, Any]:
    out_dir.mkdir(parents=True, exist_ok=True)
    chapters_dir = out_dir / "chapters"
    data_dir = out_dir / "data"
    chapters_dir.mkdir(parents=True, exist_ok=True)
    data_dir.mkdir(parents=True, exist_ok=True)

    cadmo_css = read_asset(CADMO_CSS_PATH, FALLBACK_CADMO_CSS)
    cadmo_js = read_asset(CADMO_JS_PATH, "")
    cc_css = read_asset(CC_DIAGRAM_CSS_PATH, "")
    cc_inspector_js = read_asset(CC_INSPECTOR_JS_PATH, "")

    generated_html: List[Path] = []
    generated_stubs: List[Path] = []

    for idx, ch in enumerate(chapters):
        prev_link = (
            (f"{chapters[idx - 1]['slug']}.html", chapters[idx - 1]["title"])
            if idx > 0
            else None
        )
        next_link = (
            (f"{chapters[idx + 1]['slug']}.html", chapters[idx + 1]["title"])
            if idx + 1 < len(chapters)
            else None
        )

        # Save self-contained canonical JSON copy in data/
        data_file = data_dir / f"{ch['slug']}.json"
        data_file.write_text(
            json.dumps(ch["doc"], indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
        )

        # Render interactive ETH CADMO chapter HTML
        chapter_html = render_chapter_html(
            doc=ch["doc"],
            chapter_title=ch["title"],
            monograph_title=monograph_title,
            prose_md=ch.get("prose_md"),
            prev_link=prev_link,
            next_link=next_link,
            index_href="../index.html",
            cadmo_css=cadmo_css,
            cadmo_js=cadmo_js,
            cc_css=cc_css,
            cc_inspector_js=cc_inspector_js,
        )
        chapter_path = chapters_dir / f"{ch['slug']}.html"
        chapter_path.write_text(chapter_html, encoding="utf-8")
        generated_html.append(chapter_path)

    # Render monograph cover / ToC index.html
    index_path = out_dir / "index.html"
    index_path.write_text(
        render_index_html(monograph_title, monograph_subtitle, chapters, cadmo_css),
        encoding="utf-8",
    )

    # Emit Verso .lean chapter stubs
    if emit_verso_stubs:
        verso_dir = out_dir / "verso"
        verso_dir.mkdir(parents=True, exist_ok=True)
        for ch in chapters:
            stub_path = verso_dir / f"{ch['module_name']}.lean"
            stub_path.write_text(
                render_verso_stub(ch, f"../data/{ch['slug']}.json"), encoding="utf-8"
            )
            generated_stubs.append(stub_path)
        monograph_stub = verso_dir / "Monograph.lean"
        monograph_stub.write_text(
            render_verso_monograph_index(monograph_title, chapters), encoding="utf-8"
        )
        generated_stubs.append(monograph_stub)

    return {
        "index_html": str(index_path),
        "chapter_htmls": [str(p) for p in generated_html],
        "verso_stubs": [str(p) for p in generated_stubs],
    }


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Render a multi-chapter ETH CADMO HTML site and Verso .lean stubs from canonical Explanation.Document JSON."
    )
    parser.add_argument("inputs", nargs="*", help="Canonical Explanation.Document JSON file(s)")
    parser.add_argument("--doc", action="append", default=[], help="Canonical Document JSON file (repeatable)")
    parser.add_argument(
        "--chapter",
        action="append",
        default=[],
        help="Optional Markdown/Verso prose chapter file paired with --doc/inputs (repeatable)",
    )
    parser.add_argument("--manifest", help="JSON manifest describing a multi-chapter monograph")
    parser.add_argument("--out-dir", default="_site", help="Output directory (default: _site)")
    parser.add_argument("--title", help="Monograph title override")
    parser.add_argument("--subtitle", help="Monograph subtitle override")
    parser.add_argument(
        "--mode",
        choices=["paper", "auditor"],
        help="Override default disclosure mode in generated chapters",
    )
    parser.add_argument(
        "--no-verso-stubs",
        action="store_true",
        help="Skip generating verso/*.lean source stubs",
    )
    args = parser.parse_args(argv)

    try:
        title, subtitle, chapters = load_chapters_from_args(args)
        summary = build_bundle(
            out_dir=Path(args.out_dir).resolve(),
            monograph_title=title,
            monograph_subtitle=subtitle,
            chapters=chapters,
            emit_verso_stubs=not args.no_verso_stubs,
        )
    except Exception as exc:
        print(f"[render_verso_bundle] ERROR: {exc}", file=sys.stderr)
        return 1

    print(f"Generated ETH CADMO Verso bundle in {Path(args.out_dir).resolve()}:")
    print(f"  Index:    {summary['index_html']}")
    for ch_path in summary["chapter_htmls"]:
        print(f"  Chapter:  {ch_path}")
    for stub_path in summary["verso_stubs"]:
        print(f"  Verso:    {stub_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
