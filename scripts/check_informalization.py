#!/usr/bin/env python3
"""
Automated CI Quality Gate for Constructive Cryptography Informalization.

Validates any exported canonical `.json` (`Informalization.Core.Explanation.Document`)
and/or standalone ETH CADMO `.html` artifact against 5 automated gates:
  1. Zero-leakage gate across all reader-facing prose & math strings.
  2. Kernel axiom audit gate (no `sorryAx` / `hasSorry`; standard axioms only unless
     `--allow-axioms` is passed).
  3. Sibling deduplication & structural quality gate (no duplicate sibling ProofNode
     text blocks, no empty statement paragraphs, no broken symbol inspector keys,
     valid JSON schema).
  4. English & CADMO typography lint (crypto article phonology, double spaces, raw
     `interface(s)`, plus HTML bundle CSS/JS/embedded-JSON integrity).
  5. Optional Playwright headless browser smoke test (`--playwright`, `--screenshot`).

Requires Python 3.9+ stdlib only (Playwright is imported lazily only when `--playwright`
is requested).
"""
from __future__ import annotations

import argparse
import dataclasses
import json
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple


STANDARD_AXIOMS: Set[str] = {"propext", "Classical.choice", "Quot.sound"}

# Case-sensitive forbidden leakage patterns in reader-facing prose/math strings
FORBIDDEN_CASE_SENSITIVE: Tuple[str, ...] = (
    "_hyg",
    "_uniq",
    "._",
    "None (",
    "ENNReal.ofReal",
    "NNReal.toReal",
    "Coe.coe",
    "OfNat.ofNat",
    "HSMul.hSMul",
    "AutoParam",
    "autoParam",
    "optParam",
    "fun x =>",
    "match ",
    "asHom",
    "toDDC",
)

# Case-insensitive forbidden Lean / category-theory / legalism patterns
FORBIDDEN_CASE_INSENSITIVE: Tuple[str, ...] = (
    "at interface",
    "whiskering",
    "interface(s)",
    "admissibility closure",
    "visible system",
    "user(s)",
    "query(s)",
    "resource(s)",
)

RAW_LAMBDA_RE = re.compile(r"\bfun\s+[A-Za-z_][A-Za-z0-9_']*\s*=>")

# Common English/crypto article errors checked on joined inline text
ARTICLE_ERROR_PATTERNS: Tuple[Tuple[re.Pattern[str], str], ...] = (
    (re.compile(r"\ba\s+(?:ε|\\varepsilon\b|\\epsilon\b)", re.IGNORECASE), "a ε (use 'an ε')"),
    (re.compile(r"\ba\s+MBO\b"), "a MBO (use 'an MBO')"),
    (re.compile(r"\ban\s+URF\b"), "an URF (use 'a URF')"),
    (re.compile(r"\ban\s+URP\b"), "an URP (use 'a URP')"),
    (re.compile(r"\ba\s+adversary\b", re.IGNORECASE), "a adversary (use 'an adversary')"),
    (re.compile(r"\ba\s+oracle\b", re.IGNORECASE), "a oracle (use 'an oracle')"),
)

VALID_PROOF_NODE_KINDS: Set[str] = {
    "step",
    "calcChain",
    "routineReceipt",
    "flowNote",
    "figure",
}

STYLE_CADMO_RE = re.compile(
    r"<style\b[^>]*\bdata-cadmo-reader\b[^>]*>(.*?)</style>",
    re.IGNORECASE | re.DOTALL,
)
SCRIPT_CONTROLLER_RE = re.compile(
    r"<script\b[^>]*\bdata-cadmo-controller\b[^>]*>(.*?)</script>",
    re.IGNORECASE | re.DOTALL,
)
SCRIPT_DATA_RE = re.compile(
    r"<script\b[^>]*\bid=[\"']cadmo-document-data[\"'][^>]*>(.*?)</script>",
    re.IGNORECASE | re.DOTALL,
)


@dataclasses.dataclass
class Violation:
    gate: str
    file: str
    location: str
    message: str


@dataclasses.dataclass
class FileReport:
    path: str
    kind: str
    violations: List[Violation] = dataclasses.field(default_factory=list)
    entries_checked: int = 0
    inspectors_checked: int = 0
    playwright_status: Optional[str] = None

    @property
    def ok(self) -> bool:
        return len(self.violations) == 0


def snippet(text: str, limit: int = 110) -> str:
    compact = re.sub(r"\s+", " ", text).strip()
    if len(compact) <= limit:
        return compact
    return compact[: limit - 1] + "…"


def inline_raw_texts(inl: Any) -> List[str]:
    """Extract raw string segments from one Inline JSON node."""
    if not isinstance(inl, dict):
        return []
    if "text" in inl:
        v = inl["text"]
        return [v if isinstance(v, str) else str(v.get("value", ""))]
    if "emph" in inl:
        v = inl["emph"]
        return [v if isinstance(v, str) else str(v.get("value", ""))]
    if "inlineMath" in inl:
        v = inl["inlineMath"]
        return [v if isinstance(v, str) else str(v.get("latex", ""))]
    if "displayMath" in inl:
        v = inl["displayMath"]
        if isinstance(v, str):
            return [v]
        return [str(v.get("latex", "")), str(v.get("punct", ""))]
    if "symbol" in inl:
        v = inl["symbol"]
        if isinstance(v, dict):
            return [str(v.get("display", ""))]
    if "citation" in inl:
        v = inl["citation"]
        if isinstance(v, dict):
            parts = [str(v.get("label", ""))]
            if v.get("detail"):
                parts.append(str(v.get("detail", "")))
            return parts
    return []


def pretty_math_for_lint(tex: str) -> str:
    """Normalize common LaTeX macros to readable glyphs for cross-inline article lint."""
    s = (
        tex.replace("\\varepsilon", "ε")
        .replace("\\epsilon", "ε")
        .replace("\\, ", " ")
        .replace("\\; ", " ")
        .replace(" \\,", " ")
        .replace(" \\;", " ")
        .replace("\\,", " ")
        .replace("\\;", " ")
        .replace("\\!", "")
    )
    return re.sub(r"  +", " ", s)


def flatten_inlines_joined(inlines: Any) -> str:
    """Join an Inline array into a continuous rendered text string (for article & dedup checks)."""
    if not isinstance(inlines, list):
        return ""
    parts: List[str] = []
    for inl in inlines:
        if not isinstance(inl, dict):
            continue
        if "text" in inl:
            v = inl["text"]
            parts.append(v if isinstance(v, str) else str(v.get("value", "")))
        elif "emph" in inl:
            v = inl["emph"]
            parts.append(v if isinstance(v, str) else str(v.get("value", "")))
        elif "inlineMath" in inl:
            v = inl["inlineMath"]
            tex = v if isinstance(v, str) else str(v.get("latex", ""))
            parts.append(pretty_math_for_lint(tex))
        elif "displayMath" in inl:
            v = inl["displayMath"]
            tex = v if isinstance(v, str) else str(v.get("latex", ""))
            punct = "" if isinstance(v, str) else str(v.get("punct", ""))
            parts.append(pretty_math_for_lint(tex) + punct)
        elif "symbol" in inl:
            v = inl["symbol"]
            if isinstance(v, dict):
                disp = str(v.get("display", ""))
                parts.append(pretty_math_for_lint(disp) if v.get("isMath", True) else disp)
        elif "citation" in inl:
            v = inl["citation"]
            if isinstance(v, dict):
                parts.append(f"[{v.get('label', '')}]")
    return "".join(parts)


def check_text_leakage(
    text: str, file_path: str, location: str, violations: List[Violation]
) -> None:
    if not text:
        return
    for pat in FORBIDDEN_CASE_SENSITIVE:
        if pat in text:
            violations.append(
                Violation(
                    gate="zero-leakage",
                    file=file_path,
                    location=location,
                    message=f"Forbidden pattern '{pat}' in: {snippet(text)}",
                )
            )
    if RAW_LAMBDA_RE.search(text) and "fun x =>" not in text:
        violations.append(
            Violation(
                gate="zero-leakage",
                file=file_path,
                location=location,
                message=f"Raw Lean lambda syntax found in: {snippet(text)}",
            )
        )
    lower = text.lower()
    for pat in FORBIDDEN_CASE_INSENSITIVE:
        if pat in lower:
            violations.append(
                Violation(
                    gate="zero-leakage",
                    file=file_path,
                    location=location,
                    message=f"Forbidden Lean/non-CC term '{pat}' in: {snippet(text)}",
                )
            )


def check_prose_typography(
    text: str, file_path: str, location: str, violations: List[Violation]
) -> None:
    if not text:
        return
    for rx, desc in ARTICLE_ERROR_PATTERNS:
        if rx.search(text):
            violations.append(
                Violation(
                    gate="typography",
                    file=file_path,
                    location=location,
                    message=f"Article error ({desc}) in: {snippet(text)}",
                )
            )
    if "  " in text:
        violations.append(
            Violation(
                gate="typography",
                file=file_path,
                location=location,
                message=f"Double space in prose: {snippet(text)}",
            )
        )
    if "interface(s)" in text.lower():
        violations.append(
            Violation(
                gate="typography",
                file=file_path,
                location=location,
                message=f"Raw legalism 'interface(s)' in: {snippet(text)}",
            )
        )


def check_inlines(
    inlines: Any,
    inspector_keys: Set[str],
    file_path: str,
    location: str,
    violations: List[Violation],
) -> str:
    """Validate an Inline array for leakage, broken symbol keys, and joined typography."""
    if not isinstance(inlines, list):
        violations.append(
            Violation(
                gate="structure",
                file=file_path,
                location=location,
                message="Expected list of Inline objects",
            )
        )
        return ""

    for idx, inl in enumerate(inlines):
        if not isinstance(inl, dict):
            violations.append(
                Violation(
                    gate="structure",
                    file=file_path,
                    location=f"{location}[{idx}]",
                    message=f"Inline item must be an object, got {type(inl).__name__}",
                )
            )
            continue
        for seg in inline_raw_texts(inl):
            check_text_leakage(seg, file_path, f"{location}[{idx}]", violations)
        if "symbol" in inl:
            sym = inl["symbol"]
            key = sym.get("key") if isinstance(sym, dict) else None
            if not key or key not in inspector_keys:
                violations.append(
                    Violation(
                        gate="structure",
                        file=file_path,
                        location=f"{location}[{idx}]",
                        message=f"Broken inspector symbol key '{key}' (not found in document.inspectors)",
                    )
                )

    joined = flatten_inlines_joined(inlines)
    check_text_leakage(joined, file_path, location, violations)
    check_prose_typography(joined, file_path, location, violations)
    return joined


def check_goal_state(
    goal: Any, file_path: str, location: str, violations: List[Violation]
) -> None:
    if goal is None:
        return
    if not isinstance(goal, dict):
        violations.append(
            Violation(
                gate="structure",
                file=file_path,
                location=location,
                message="GoalState must be an object or null",
            )
        )
        return
    target = goal.get("targetLatex", "")
    check_text_leakage(str(target), file_path, f"{location}.targetLatex", violations)
    target_prose = goal.get("targetProse")
    if target_prose:
        check_text_leakage(str(target_prose), file_path, f"{location}.targetProse", violations)
        check_prose_typography(str(target_prose), file_path, f"{location}.targetProse", violations)
    for idx, ctx in enumerate(goal.get("context") or []):
        if not isinstance(ctx, dict):
            continue
        nm = ctx.get("name")
        if nm is not None:
            check_text_leakage(str(nm), file_path, f"{location}.context[{idx}].name", violations)
        desc = str(ctx.get("description", ""))
        check_text_leakage(desc, file_path, f"{location}.context[{idx}].description", violations)
        check_prose_typography(desc, file_path, f"{location}.context[{idx}].description", violations)


def proof_node_canonical_text(node: Dict[str, Any]) -> str:
    """Compute canonical visible text block for sibling deduplication."""
    kind = node.get("kind")
    if kind == "step":
        raw = flatten_inlines_joined(node.get("content", []))
    elif kind == "routineReceipt":
        raw = str(node.get("summary", ""))
    elif kind == "flowNote":
        raw = str(node.get("text", ""))
    elif kind == "figure":
        cap = flatten_inlines_joined(node.get("caption", []))
        raw = f"{cap} {node.get('html', '')}"
    elif kind == "calcChain":
        intro = flatten_inlines_joined(node.get("intro", []))
        step_parts: List[str] = []
        for item in node.get("steps") or []:
            st = (item or {}).get("step") or {}
            step_parts.append(
                f"{st.get('lhsLatex', '')} {st.get('relationLatex', '')} {st.get('rhsLatex', '')} "
                f"{flatten_inlines_joined(st.get('reason', []))}"
            )
        raw = intro + " | " + " ; ".join(step_parts)
    else:
        raw = ""
    return re.sub(r"\s+", " ", raw).strip()


def check_proof_node_list(
    nodes: Any,
    inspector_keys: Set[str],
    file_path: str,
    location: str,
    violations: List[Violation],
) -> None:
    if not isinstance(nodes, list):
        violations.append(
            Violation(
                gate="structure",
                file=file_path,
                location=location,
                message="Expected list of ProofNode objects",
            )
        )
        return

    seen_siblings: Dict[str, int] = {}
    for idx, node in enumerate(nodes):
        node_loc = f"{location}[{idx}]"
        if not isinstance(node, dict):
            violations.append(
                Violation(
                    gate="structure",
                    file=file_path,
                    location=node_loc,
                    message=f"ProofNode must be an object, got {type(node).__name__}",
                )
            )
            continue

        kind = node.get("kind")
        if kind not in VALID_PROOF_NODE_KINDS:
            violations.append(
                Violation(
                    gate="structure",
                    file=file_path,
                    location=node_loc,
                    message=f"Invalid ProofNode kind '{kind}'",
                )
            )
            continue

        # Sibling deduplication check
        canon = proof_node_canonical_text(node)
        if canon:
            if canon in seen_siblings:
                first_idx = seen_siblings[canon]
                violations.append(
                    Violation(
                        gate="sibling-dedup",
                        file=file_path,
                        location=node_loc,
                        message=(
                            f"Duplicate sibling ProofNode text (matches sibling [{first_idx}]): "
                            f"{snippet(canon)}"
                        ),
                    )
                )
            else:
                seen_siblings[canon] = idx

        # Recursive content + child checks
        if kind == "step":
            check_inlines(
                node.get("content", []), inspector_keys, file_path, f"{node_loc}.content", violations
            )
            check_goal_state(node.get("goal"), file_path, f"{node_loc}.goal", violations)
            check_proof_node_list(
                node.get("children", []),
                inspector_keys,
                file_path,
                f"{node_loc}.children",
                violations,
            )
        elif kind == "calcChain":
            check_inlines(
                node.get("intro", []), inspector_keys, file_path, f"{node_loc}.intro", violations
            )
            check_goal_state(node.get("goal"), file_path, f"{node_loc}.goal", violations)
            steps = node.get("steps", [])
            if not isinstance(steps, list):
                violations.append(
                    Violation(
                        gate="structure",
                        file=file_path,
                        location=f"{node_loc}.steps",
                        message="calcChain.steps must be a list",
                    )
                )
            else:
                for sidx, item in enumerate(steps):
                    sloc = f"{node_loc}.steps[{sidx}]"
                    if not isinstance(item, dict):
                        continue
                    st = item.get("step") or {}
                    for fld in ("lhsLatex", "relationLatex", "rhsLatex"):
                        check_text_leakage(
                            str(st.get(fld, "")), file_path, f"{sloc}.step.{fld}", violations
                        )
                    check_inlines(
                        st.get("reason", []),
                        inspector_keys,
                        file_path,
                        f"{sloc}.step.reason",
                        violations,
                    )
                    check_proof_node_list(
                        item.get("children", []),
                        inspector_keys,
                        file_path,
                        f"{sloc}.children",
                        violations,
                    )
        elif kind == "routineReceipt":
            summary = str(node.get("summary", ""))
            check_text_leakage(summary, file_path, f"{node_loc}.summary", violations)
            check_prose_typography(summary, file_path, f"{node_loc}.summary", violations)
            check_goal_state(node.get("goal"), file_path, f"{node_loc}.goal", violations)
            check_proof_node_list(
                node.get("details", []),
                inspector_keys,
                file_path,
                f"{node_loc}.details",
                violations,
            )
        elif kind == "flowNote":
            text = str(node.get("text", ""))
            check_text_leakage(text, file_path, f"{node_loc}.text", violations)
            check_prose_typography(text, file_path, f"{node_loc}.text", violations)
        elif kind == "figure":
            check_inlines(
                node.get("caption", []),
                inspector_keys,
                file_path,
                f"{node_loc}.caption",
                violations,
            )


def check_inspectors(
    inspectors: Any, file_path: str, violations: List[Violation]
) -> Set[str]:
    keys: Set[str] = set()
    if not isinstance(inspectors, list):
        violations.append(
            Violation(
                gate="structure",
                file=file_path,
                location="document.inspectors",
                message="Expected list of SymbolInspector objects",
            )
        )
        return keys

    for idx, ins in enumerate(inspectors):
        loc = f"inspectors[{idx}]"
        if not isinstance(ins, dict):
            violations.append(
                Violation(
                    gate="structure",
                    file=file_path,
                    location=loc,
                    message="SymbolInspector must be an object",
                )
            )
            continue
        key = ins.get("key")
        if not isinstance(key, str) or not key.strip():
            violations.append(
                Violation(
                    gate="structure",
                    file=file_path,
                    location=f"{loc}.key",
                    message="SymbolInspector missing non-empty string 'key'",
                )
            )
        else:
            keys.add(key)

        disp = str(ins.get("display", ""))
        check_text_leakage(disp, file_path, f"{loc}.display", violations)

        kind = ins.get("kind") or {}
        if not isinstance(kind, dict):
            continue
        if "interfaceTable" in kind and isinstance(kind["interfaceTable"], dict):
            it = kind["interfaceTable"]
            check_text_leakage(
                str(it.get("domainLatex", "")), file_path, f"{loc}.interfaceTable.domainLatex", violations
            )
            bnote = str(it.get("budgetNote", ""))
            check_text_leakage(bnote, file_path, f"{loc}.interfaceTable.budgetNote", violations)
            check_prose_typography(bnote, file_path, f"{loc}.interfaceTable.budgetNote", violations)
            for pidx, row in enumerate(it.get("ports") or []):
                if isinstance(row, dict):
                    for fld in ("port", "queryLatex", "replyLatex"):
                        check_text_leakage(
                            str(row.get(fld, "")),
                            file_path,
                            f"{loc}.interfaceTable.ports[{pidx}].{fld}",
                            violations,
                        )
        elif "mathDefinition" in kind and isinstance(kind["mathDefinition"], dict):
            md = kind["mathDefinition"]
            check_text_leakage(
                str(md.get("equationLatex", "")), file_path, f"{loc}.mathDefinition.equationLatex", violations
            )
            ps = str(md.get("proseSummary", ""))
            check_text_leakage(ps, file_path, f"{loc}.mathDefinition.proseSummary", violations)
            check_prose_typography(ps, file_path, f"{loc}.mathDefinition.proseSummary", violations)
        elif "witnessCard" in kind and isinstance(kind["witnessCard"], dict):
            wc = kind["witnessCard"]
            title = str(wc.get("title", ""))
            check_text_leakage(title, file_path, f"{loc}.witnessCard.title", violations)
            check_prose_typography(title, file_path, f"{loc}.witnessCard.title", violations)
            for ridx, row in enumerate(wc.get("rows") or []):
                if isinstance(row, list) and len(row) == 2:
                    check_text_leakage(str(row[0]), file_path, f"{loc}.witnessCard.rows[{ridx}][0]", violations)
                    check_text_leakage(str(row[1]), file_path, f"{loc}.witnessCard.rows[{ridx}][1]", violations)
        elif "parameter" in kind:
            p = kind["parameter"]
            desc = p if isinstance(p, str) else str((p or {}).get("roleDescription", ""))
            check_text_leakage(desc, file_path, f"{loc}.parameter.roleDescription", violations)
            check_prose_typography(desc, file_path, f"{loc}.parameter.roleDescription", violations)
        elif "ccDiagram" in kind and isinstance(kind["ccDiagram"], dict):
            check_text_leakage(
                str(kind["ccDiagram"].get("summaryLatex", "")),
                file_path,
                f"{loc}.ccDiagram.summaryLatex",
                violations,
            )
    return keys


def check_document(
    doc: Any,
    file_path: str,
    allow_axioms: bool,
    report: FileReport,
) -> None:
    violations = report.violations
    if not isinstance(doc, dict):
        violations.append(
            Violation(
                gate="structure",
                file=file_path,
                location="document",
                message=f"Top-level Document must be a JSON object, got {type(doc).__name__}",
            )
        )
        return

    title = doc.get("title")
    if not isinstance(title, str) or not title.strip():
        violations.append(
            Violation(
                gate="structure",
                file=file_path,
                location="document.title",
                message="Document missing non-empty string 'title'",
            )
        )
    else:
        check_text_leakage(title, file_path, "document.title", violations)
        check_prose_typography(title, file_path, "document.title", violations)

    subtitle = doc.get("subtitle")
    if subtitle is not None:
        check_text_leakage(str(subtitle), file_path, "document.subtitle", violations)
        check_prose_typography(str(subtitle), file_path, "document.subtitle", violations)

    inspectors = doc.get("inspectors", [])
    inspector_keys = check_inspectors(inspectors, file_path, violations)
    report.inspectors_checked = len(inspector_keys)

    entries = doc.get("entries")
    if not isinstance(entries, list):
        violations.append(
            Violation(
                gate="structure",
                file=file_path,
                location="document.entries",
                message="Document missing 'entries' list",
            )
        )
        return

    report.entries_checked = len(entries)
    for idx, entry in enumerate(entries):
        eloc = f"entries[{idx}]"
        if not isinstance(entry, dict):
            violations.append(
                Violation(
                    gate="structure",
                    file=file_path,
                    location=eloc,
                    message="Entry must be a JSON object",
                )
            )
            continue

        decl = entry.get("declaration", f"<entry-{idx}>")
        eloc_named = f"entries[{idx}]({decl})"

        if entry.get("header"):
            check_text_leakage(str(entry["header"]), file_path, f"{eloc_named}.header", violations)
        if entry.get("title"):
            etitle = str(entry["title"])
            check_text_leakage(etitle, file_path, f"{eloc_named}.title", violations)
            check_prose_typography(etitle, file_path, f"{eloc_named}.title", violations)

        # Gate 2: Axiom audit
        ax_obj = entry.get("axioms") or {}
        if not isinstance(ax_obj, dict):
            violations.append(
                Violation(
                    gate="axiom-audit",
                    file=file_path,
                    location=f"{eloc_named}.axioms",
                    message="Entry 'axioms' must be an object",
                )
            )
        else:
            has_sorry = bool(ax_obj.get("hasSorry", False))
            axiom_list = ax_obj.get("axioms") or []
            if has_sorry or "sorryAx" in axiom_list:
                violations.append(
                    Violation(
                        gate="axiom-audit",
                        file=file_path,
                        location=f"{eloc_named}.axioms",
                        message=f"Declaration '{decl}' depends on sorryAx (hasSorry={has_sorry})",
                    )
                )
            if not allow_axioms:
                non_std = [a for a in axiom_list if a not in STANDARD_AXIOMS and a != "sorryAx"]
                if non_std:
                    violations.append(
                        Violation(
                            gate="axiom-audit",
                            file=file_path,
                            location=f"{eloc_named}.axioms",
                            message=(
                                f"Declaration '{decl}' uses non-standard axiom(s): "
                                + ", ".join(non_std)
                            ),
                        )
                    )

        # Ambient setting
        ambient = entry.get("ambient")
        if isinstance(ambient, dict):
            check_inlines(
                ambient.get("summary", []),
                inspector_keys,
                file_path,
                f"{eloc_named}.ambient.summary",
                violations,
            )

        # Gate 3: Statement paragraphs (must be non-empty, no empty paragraphs)
        stmt = entry.get("statement")
        if not isinstance(stmt, list) or len(stmt) == 0:
            violations.append(
                Violation(
                    gate="structure",
                    file=file_path,
                    location=f"{eloc_named}.statement",
                    message="Entry statement must contain at least one paragraph",
                )
            )
        else:
            for pidx, para in enumerate(stmt):
                joined = check_inlines(
                    para,
                    inspector_keys,
                    file_path,
                    f"{eloc_named}.statement[{pidx}]",
                    violations,
                )
                if not joined.strip():
                    violations.append(
                        Violation(
                            gate="structure",
                            file=file_path,
                            location=f"{eloc_named}.statement[{pidx}]",
                            message="Empty statement paragraph",
                        )
                    )

        # Proof tree
        check_proof_node_list(
            entry.get("proof", []),
            inspector_keys,
            file_path,
            f"{eloc_named}.proof",
            violations,
        )


def run_playwright_smoke(
    html_path: Path,
    report: FileReport,
    screenshot_path: Optional[str],
    skip_if_missing: bool,
) -> None:
    try:
        from playwright.sync_api import sync_playwright  # type: ignore
    except ImportError:
        msg = (
            "Playwright Python package not installed "
            "(install via `pip install playwright && playwright install chromium`)."
        )
        if skip_if_missing:
            report.playwright_status = f"skipped ({msg})"
            return
        report.violations.append(
            Violation(gate="playwright", file=str(html_path), location="browser", message=msg)
        )
        return

    console_errors: List[str] = []
    page_errors: List[str] = []
    try:
        with sync_playwright() as p:
            browser = p.chromium.launch(headless=True)
            page = browser.new_page(viewport={"width": 1440, "height": 960})
            page.on(
                "console",
                lambda msg: console_errors.append(msg.text) if msg.type == "error" else None,
            )
            page.on("pageerror", lambda err: page_errors.append(str(err)))
            page.goto(html_path.resolve().as_uri(), wait_until="load")

            # Verify root rendered at least one entry
            if page.locator(".cadmo-entry").count() == 0:
                report.violations.append(
                    Violation(
                        gate="playwright",
                        file=str(html_path),
                        location="#cadmo-root",
                        message="No .cadmo-entry elements rendered in browser",
                    )
                )

            # Verify clicking ⊕ expands children
            toggles = page.locator("button.cadmo-toggle")
            if toggles.count() > 0:
                first_toggle = toggles.first
                before = first_toggle.get_attribute("aria-expanded")
                first_toggle.click()
                after = page.locator("button.cadmo-toggle").first.get_attribute("aria-expanded")
                if before == after or after != "true":
                    report.violations.append(
                        Violation(
                            gate="playwright",
                            file=str(html_path),
                            location="button.cadmo-toggle",
                            message=f"Clicking ⊕ did not expand children (aria-expanded: {before} -> {after})",
                        )
                    )

            # Verify Paper <-> Auditor toggle updates data-mode
            auditor_btn = page.get_by_role("button", name="Auditor")
            paper_btn = page.get_by_role("button", name="Paper")
            if auditor_btn.count() > 0 and paper_btn.count() > 0:
                auditor_btn.first.click()
                mode_auditor = page.evaluate("document.documentElement.dataset.mode")
                if mode_auditor != "auditor":
                    report.violations.append(
                        Violation(
                            gate="playwright",
                            file=str(html_path),
                            location="mode-toggle",
                            message=f"Switching to Auditor did not update data-mode (got {mode_auditor!r})",
                        )
                    )
                paper_btn.first.click()
                mode_paper = page.evaluate("document.documentElement.dataset.mode")
                if mode_paper != "paper":
                    report.violations.append(
                        Violation(
                            gate="playwright",
                            file=str(html_path),
                            location="mode-toggle",
                            message=f"Switching to Paper did not update data-mode (got {mode_paper!r})",
                        )
                    )
            else:
                report.violations.append(
                    Violation(
                        gate="playwright",
                        file=str(html_path),
                        location="mode-toggle",
                        message="Paper / Auditor disclosure mode buttons not found",
                    )
                )

            # Verify clicking an underlined symbol opens the margin inspector
            syms = page.locator("button.cadmo-sym")
            if syms.count() > 0:
                syms.first.click()
                inspector_title = page.locator(".cadmo-margin .cadmo-inspector-title")
                if inspector_title.count() == 0:
                    report.violations.append(
                        Violation(
                            gate="playwright",
                            file=str(html_path),
                            location="button.cadmo-sym",
                            message="Clicking underlined symbol did not open margin inspector card",
                        )
                    )

            if screenshot_path:
                out_shot = Path(screenshot_path)
                out_shot.parent.mkdir(parents=True, exist_ok=True)
                page.screenshot(path=str(out_shot), full_page=True)

            browser.close()
    except Exception as exc:
        if skip_if_missing and "Executable doesn't exist" in str(exc):
            report.playwright_status = f"skipped (Chromium missing: {exc})"
            return
        report.violations.append(
            Violation(
                gate="playwright",
                file=str(html_path),
                location="browser",
                message=f"Playwright execution error: {exc}",
            )
        )
        return

    for err in console_errors:
        report.violations.append(
            Violation(gate="playwright", file=str(html_path), location="console", message=err)
        )
    for err in page_errors:
        report.violations.append(
            Violation(gate="playwright", file=str(html_path), location="pageerror", message=err)
        )
    if not console_errors and not page_errors:
        report.playwright_status = "passed"


def check_file(
    path: Path,
    allow_axioms: bool,
    run_playwright: bool,
    screenshot_path: Optional[str],
    playwright_skip_if_missing: bool,
) -> FileReport:
    suffix = path.suffix.lower()
    if not path.is_file():
        rep = FileReport(path=str(path), kind="missing")
        rep.violations.append(
            Violation(gate="io", file=str(path), location="file", message="File does not exist")
        )
        return rep

    text = path.read_text(encoding="utf-8")

    if suffix == ".json":
        rep = FileReport(path=str(path), kind="json")
        try:
            doc = json.loads(text)
        except json.JSONDecodeError as exc:
            rep.violations.append(
                Violation(
                    gate="structure",
                    file=str(path),
                    location=f"line {exc.lineno}, col {exc.colno}",
                    message=f"Malformed JSON: {exc.msg}",
                )
            )
            return rep
        check_document(doc, str(path), allow_axioms=allow_axioms, report=rep)
        return rep

    if suffix in (".html", ".htm"):
        rep = FileReport(path=str(path), kind="html")

        style_match = STYLE_CADMO_RE.search(text)
        if not style_match or not style_match.group(1).strip():
            rep.violations.append(
                Violation(
                    gate="html-bundle",
                    file=str(path),
                    location="style[data-cadmo-reader]",
                    message="HTML bundle missing non-empty <style data-cadmo-reader> CSS",
                )
            )

        ctrl_match = SCRIPT_CONTROLLER_RE.search(text)
        if not ctrl_match or not ctrl_match.group(1).strip():
            rep.violations.append(
                Violation(
                    gate="html-bundle",
                    file=str(path),
                    location="script[data-cadmo-controller]",
                    message="HTML bundle missing non-empty <script data-cadmo-controller> JS",
                )
            )

        data_match = SCRIPT_DATA_RE.search(text)
        if not data_match or not data_match.group(1).strip():
            rep.violations.append(
                Violation(
                    gate="html-bundle",
                    file=str(path),
                    location="script#cadmo-document-data",
                    message="HTML bundle missing embedded <script id=\"cadmo-document-data\"> JSON",
                )
            )
        else:
            try:
                doc = json.loads(data_match.group(1))
            except json.JSONDecodeError as exc:
                rep.violations.append(
                    Violation(
                        gate="structure",
                        file=str(path),
                        location=f"script#cadmo-document-data (line {exc.lineno}, col {exc.colno})",
                        message=f"Malformed embedded JSON: {exc.msg}",
                    )
                )
            else:
                check_document(doc, str(path), allow_axioms=allow_axioms, report=rep)

        if run_playwright:
            run_playwright_smoke(
                html_path=path,
                report=rep,
                screenshot_path=screenshot_path,
                skip_if_missing=playwright_skip_if_missing,
            )
        return rep

    rep = FileReport(path=str(path), kind="unknown")
    rep.violations.append(
        Violation(
            gate="io",
            file=str(path),
            location="file",
            message=f"Unsupported file extension '{suffix}' (expected .json or .html)",
        )
    )
    return rep


def format_text_report(reports: Sequence[FileReport]) -> str:
    lines: List[str] = []
    total_violations = sum(len(r.violations) for r in reports)
    for rep in reports:
        status = "PASS" if rep.ok else f"FAIL ({len(rep.violations)} issue(s))"
        meta = f"[{rep.kind}] entries={rep.entries_checked} inspectors={rep.inspectors_checked}"
        if rep.playwright_status:
            meta += f" playwright={rep.playwright_status}"
        lines.append(f"{status}: {rep.path}  {meta}")
        for v in rep.violations:
            lines.append(f"  - [{v.gate}] {v.location}: {v.message}")
    lines.append("")
    if total_violations == 0:
        lines.append(f"ALL GATES PASSED across {len(reports)} file(s).")
    else:
        lines.append(
            f"CI GATE FAILED: {total_violations} violation(s) across {len(reports)} file(s)."
        )
    return "\n".join(lines)


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Automated zero-leakage, axiom-audit, structural, typography, and optional Playwright CI gate for CC informalization artifacts."
    )
    parser.add_argument("files", nargs="+", help="Exported .json and/or .html artifact(s)")
    parser.add_argument(
        "--allow-axioms",
        action="store_true",
        help="Allow non-standard Lean axioms (sorryAx / hasSorry still fails)",
    )
    parser.add_argument(
        "--playwright",
        action="store_true",
        help="Run headless Chromium interactive smoke tests on .html inputs",
    )
    parser.add_argument(
        "--playwright-skip-if-missing",
        action="store_true",
        help="When --playwright is set, skip cleanly instead of failing if Playwright/Chromium is unavailable",
    )
    parser.add_argument(
        "--screenshot",
        help="Optional output path for full-page Playwright screenshot (used with --playwright)",
    )
    parser.add_argument(
        "--json-report",
        action="store_true",
        help="Emit structured JSON report instead of human-readable text",
    )
    args = parser.parse_args(argv)

    reports = [
        check_file(
            Path(f),
            allow_axioms=args.allow_axioms,
            run_playwright=args.playwright,
            screenshot_path=args.screenshot,
            playwright_skip_if_missing=args.playwright_skip_if_missing,
        )
        for f in args.files
    ]

    if args.json_report:
        payload = {
            "ok": all(r.ok for r in reports),
            "files": [
                {
                    "path": r.path,
                    "kind": r.kind,
                    "ok": r.ok,
                    "entries_checked": r.entries_checked,
                    "inspectors_checked": r.inspectors_checked,
                    "playwright_status": r.playwright_status,
                    "violations": [dataclasses.asdict(v) for v in r.violations],
                }
                for r in reports
            ],
        }
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        print(format_text_report(reports))

    return 0 if all(r.ok for r in reports) else 1


if __name__ == "__main__":
    raise SystemExit(main())
