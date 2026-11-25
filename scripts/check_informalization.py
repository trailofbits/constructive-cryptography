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

VALID_TIERS: Set[str] = {"legacy", "authored"}
VALID_PROSE_TRUST: Set[str] = {
    "kernelFormula",
    "kernelProvedClaim",
    "typedRef",
    "intuitionGloss",
}

# Case-sensitive forbidden leakage patterns in reader-facing prose/math strings (ALL tiers)
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
    "asHom",
    "toDDC",
    "[UNPROVED: sorry]",
    "sorryAx",
)

# Additional case-sensitive leakage patterns enforced strictly in `--tier authored`
AUTHORED_FORBIDDEN_CASE_SENSITIVE: Tuple[str, ...] = (
    "_vcc_",
    "Exists(",
    "sum(univ",
    "Sigma(",
    "Subtype(",
    "Prod.fst",
    "Prod.snd",
    "BitString(",
    "Unit \\to",
    "Unit →",
    "_proof_",
    "self.",
)

# Regexes catching LeanTeX `\mathrm{...}` renderings and Lean-type fallback prose in `--tier authored`
AUTHORED_FORBIDDEN_REGEXES: Tuple[Tuple[re.Pattern[str], str], ...] = (
    (re.compile(r"\\mathrm\{Exists\}(?:\\!|\\,|\s)*(?:\\left)?\("), "Exists("),
    (re.compile(r"\\mathrm\{sum\}(?:\\!|\\,|\s)*(?:\\left)?\(\s*(?:\\mathrm\{univ\}|univ)"), "sum(univ"),
    (re.compile(r"\\mathrm\{Sigma\}(?:\\!|\\,|\s)*(?:\\left)?\("), "Sigma("),
    (re.compile(r"\\mathrm\{Subtype\}(?:\\!|\\,|\s)*(?:\\left)?\("), "Subtype("),
    (re.compile(r"\\mathrm\{BitString\}(?:\\!|\\,|\s)*(?:\\left)?\("), "BitString("),
    (re.compile(r"\\mathrm\{Unit\}\s*(?:\\to|→)"), "Unit \\to"),
    (
        re.compile(
            r"\b(?:defined as\s+)?an?\s+element of\s+(?:\\\(|\\\[|\$|\s)*"
            r"(?:\\mathrm\{[A-Za-z0-9_.]+\}|"
            r"(?:ProbDist|BitString|SymmetricEncryption|MAC|BlockCipher|PRF|PRP|PRG|"
            r"PRGAdversary|DistAdversary|ShannonCipher|TypedSystem|TypedConverter|"
            r"TypedDistinguisher|ENNReal|NNReal|Finset|Fin|ZMod)\b)",
            re.IGNORECASE,
        ),
        "element of <LeanType>",
    ),
    (
        re.compile(r"\bdefined as\s+an?\s+element of\s+", re.IGNORECASE),
        "Defined as an element of",
    ),
)

# Case-insensitive forbidden Lean / category-theory / legalism patterns (ALL tiers)
FORBIDDEN_CASE_INSENSITIVE: Tuple[str, ...] = (
    "at interface",
    "whiskering",
    "interface(s)",
    "admissibility closure",
    "visible system",
    "user(s)",
    "query(s)",
    "resource(s)",
    "distinguishing distance",
    "transcript distance",
    "standing conventions",
)

# Additional case-insensitive leakage patterns enforced strictly in `--tier authored`
AUTHORED_FORBIDDEN_CASE_INSENSITIVE: Tuple[str, ...] = ()

# L1: Sound formula preservation (dropped arguments / glued alpha macros)
L1_DROPPED_BASE_RE = re.compile(r"\(\\cdot\)\^\{")
L1_EPSILON_RELAX_DEF_RE = re.compile(
    r"^\\mathrm\{epsilonRelaxation\}[^:]*:=\s*\(\\cdot\)\^\{\\(?:mathrm\{error\}|varepsilon|epsilon)\}$"
)
L1_GLUED_ALPHA_RE = re.compile(r"\\alpha[A-Za-z]")

# L2: Valid KaTeX / LaTeX hygiene
L2_DOUBLE_SUB_STRICT_RE = re.compile(
    r"_(?:\{[^{}]+\}|[A-Za-z0-9])_(?:\{[^{}]+\}|[A-Za-z0-9])"
)
L2_DOUBLE_SUB_PROSE_RE = re.compile(
    r"_\{\w+\}_\{|_[A-Za-z0-9]_\{|_\{\w+\}_[A-Za-z0-9]"
)
L2_UNINTERP_RE = re.compile(r"\$\{[^}]+\}")
L2_RAW_TEX_PLAIN_RE = re.compile(r"\\(?:mathcal|mathbf|mathsf|mathbb)(?![A-Za-z])|\[\\,")
MATH_SPAN_RE = re.compile(
    r"\$\$.*?\$\$|\\\[.*?\\\]|(?<!\\)\$.*?(?<!\\)\$|\\\(.*?\\\)",
    re.DOTALL,
)

# L3: Raw Lean / CC module literals forbidden in diagramHtml / svgOrHtml / figure.html
L3_RAW_DIAGRAM_TOKENS: Tuple[str, ...] = (
    "CategoryTheory.",
    "ConstructiveCryptography.",
    "SystemAlgebra.",
    "{real}",
    "{ideal}",
)

# L4: Section & TOC structural integrity (no double-numbered headings)
L4_DOUBLE_SECTION_NUM_RE = re.compile(
    r"^\s*\d+\.\s*(?:Section|§|Chapter|Part)\s*\d",
    re.IGNORECASE,
)
HTML_HEADING_RE = re.compile(r"<h([1-6])\b[^>]*>(.*?)</h\1>", re.IGNORECASE | re.DOTALL)
HTML_TAG_RE = re.compile(r"<[^>]+>")

# L5: Non-algebraic relations that must never be justified "by elementary algebra"
L5_NON_ALGEBRA_RELS: Tuple[str, ...] = ("\\simeq", "\\approx", "\\preceq")

# L6: Node-count soft budgets and core origin exclusions for sibling re-expansion detection
L6_NODE_BUDGET: Dict[str, int] = {"authored": 60, "legacy": 120}
L6_CORE_ORIGIN_PREFIXES: Tuple[str, ...] = ("Eq.", "Or.", "And.", "Exists.")
L6_CORE_ORIGIN_SUFFIXES: Tuple[str, ...] = (".casesOn", ".rec", ".recOn", ".recAux", ".ext")

# L7: JSON payload budget (MB)
L7_MONOGRAPH_ENTRY_THRESHOLD = 20
L7_MONOGRAPH_MAX_MB = 15.0
L7_SMALL_MAX_MB = 2.5

# L9: Trivial cc_calc justifications allowed with empty children + tautological ratio cap
L9_TRIVIAL_CALC_REASONS: Tuple[str, ...] = (
    "by reflexivity",
    "by definition",
    "by rfl",
    "by eq.refl",
    "by le_refl",
    "by le_rfl",
    "by non-expansion",
)
L9_MAX_TAUTOLOGICAL_RATIO = 0.10

# L11: Clean cryptographic prose, subtitles, & ontology phrases
L11_JARGON_SUBTITLE_PATTERNS: Tuple[Tuple[re.Pattern[str], str], ...] = (
    (re.compile(r"\.lean\b"), ".lean"),
    (re.compile(r"\bcc_calc\b"), "cc_calc"),
    (re.compile(r"Verbose-CC"), "Verbose-CC"),
    (re.compile(r"Expr\.mdata"), "Expr.mdata"),
    (re.compile(r"ContextProfile"), "ContextProfile"),
    (re.compile(r"zero per-theorem overlays", re.IGNORECASE), "zero per-theorem overlays"),
)
L11_LET_THIS_RE = re.compile(r"\\text\{let \}\s*(?:\\mathrm\{)?(?:this|_uniq|_hyg)\b")
L11_RAW_LET_RE = re.compile(r"\\text\{let \}")
L11_BY_DITE_RE = re.compile(r"\bby dite\b")
L11_RAW_VAL_RE = re.compile(r"\.\\mathrm\{val\}")
L11_ONTOLOGY_PHRASES: Tuple[str, ...] = (
    "extended nonnegative real",
    "finite cryptographic space",
    "subset with inside interface",
)

# L12: Known polymorphic CC library operator/projection families exempt from collision failure
L12_POLYMORPHIC_FAMILIES: Tuple[Set[str], ...] = (
    {
        "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs",
        "ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin",
    },
    {
        "ConstructiveCryptography.CryptographicAlgebra.distance",
        "SystemAlgebra.RandomSystem.transcriptDistance",
    },
)
L12_POLYMORPHIC_SUFFIXES: Tuple[str, ...] = (".Port", ".perPort", ".behavior")

LOWERCASE_THEOREM_HEADERS: Set[str] = {
    "theorem",
    "lemma",
    "proposition",
    "corollary",
}

EMBEDDED_STYLE_RE = re.compile(r"<style\b", re.IGNORECASE)

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
    "pseudocodeBox",
}

VALID_PRELUDE_KINDS: Set[str] = {
    "definition",
    "construction",
    "attackGame",
    "interfaceSpec",
    "converterDef",
    "symbolTable",
}

VALID_PBOX_KINDS: Set[str] = {
    "attackGame",
    "hybrid",
    "reduction",
    "distinguisher",
    "algorithm",
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
    tier: str = "legacy"
    violations: List[Violation] = dataclasses.field(default_factory=list)
    warnings: List[Violation] = dataclasses.field(default_factory=list)
    metrics: Dict[str, Any] = dataclasses.field(default_factory=dict)
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


def check_no_embedded_styles(
    html_str: Any, file_path: str, location: str, violations: List[Violation]
) -> None:
    if not isinstance(html_str, str) or not html_str:
        return
    if EMBEDDED_STYLE_RE.search(html_str):
        violations.append(
            Violation(
                gate="diagram-style",
                file=file_path,
                location=location,
                message="Embedded <style> tag found inside diagramHtml/HTML field (CSS must be hoisted once in <head>)",
            )
        )


def check_diagram_html(
    html_str: Any, file_path: str, location: str, violations: List[Violation]
) -> None:
    """Validate diagramHtml/svgOrHtml/figure.html for hoisted CSS (L3) and clean labels."""
    check_no_embedded_styles(html_str, file_path, location, violations)
    if not isinstance(html_str, str) or not html_str:
        return
    for tok in L3_RAW_DIAGRAM_TOKENS:
        if tok in html_str:
            violations.append(
                Violation(
                    gate="L3-diagram-hygiene",
                    file=file_path,
                    location=location,
                    message=f"Raw Lean/module token '{tok}' in diagram HTML: {snippet(html_str)}",
                )
            )


def check_soundness_and_latex(
    text: str,
    file_path: str,
    location: str,
    violations: List[Violation],
    *,
    is_math: bool = False,
    check_plain_tex: bool = False,
    allow_epsilon_relax_def: bool = False,
    tier: str = "legacy",
    warnings: Optional[List[Violation]] = None,
) -> None:
    """Enforce L1 (soundness), L2 (KaTeX/LaTeX hygiene), and L11 (clean prose/math)."""
    if not text:
        return

    # L1: Sound formula preservation
    if L1_DROPPED_BASE_RE.search(text):
        if not (allow_epsilon_relax_def and L1_EPSILON_RELAX_DEF_RE.match(text.strip())):
            violations.append(
                Violation(
                    gate="L1-soundness",
                    file=file_path,
                    location=location,
                    message=f"Dropped-argument placeholder '(\\cdot)^{{...}}' in: {snippet(text)}",
                )
            )
    if L1_GLUED_ALPHA_RE.search(text):
        violations.append(
            Violation(
                gate="L1-soundness",
                file=file_path,
                location=location,
                message=f"Glued '\\alpha<Ident>' macro in: {snippet(text)}",
            )
        )

    # L2: Valid KaTeX / LaTeX hygiene
    if L2_UNINTERP_RE.search(text):
        violations.append(
            Violation(
                gate="L2-latex-hygiene",
                file=file_path,
                location=location,
                message=f"Uninterpolated '${{...}}' template placeholder in: {snippet(text)}",
            )
        )
    if is_math:
        if L2_DOUBLE_SUB_STRICT_RE.search(text):
            violations.append(
                Violation(
                    gate="L2-latex-hygiene",
                    file=file_path,
                    location=location,
                    message=f"Invalid double subscript in math expression: {snippet(text)}",
                )
            )
    else:
        if L2_DOUBLE_SUB_PROSE_RE.search(text) or any(
            L2_DOUBLE_SUB_STRICT_RE.search(m.group(0)) for m in MATH_SPAN_RE.finditer(text)
        ):
            violations.append(
                Violation(
                    gate="L2-latex-hygiene",
                    file=file_path,
                    location=location,
                    message=f"Invalid double subscript in prose/math span: {snippet(text)}",
                )
            )
    if check_plain_tex:
        stripped = MATH_SPAN_RE.sub(" ", text)
        if L2_RAW_TEX_PLAIN_RE.search(stripped):
            violations.append(
                Violation(
                    gate="L2-latex-hygiene",
                    file=file_path,
                    location=location,
                    message=f"Raw un-delimited LaTeX control sequence in plain text: {snippet(text)}",
                )
            )

    # L11: Clean cryptographic prose & Lean-ism leaks
    if L11_LET_THIS_RE.search(text):
        violations.append(
            Violation(
                gate="L11-clean-prose",
                file=file_path,
                location=location,
                message=f"Synthetic Lean binding '\\text{{let }} this/...' in: {snippet(text)}",
            )
        )
    elif tier == "authored" and L11_RAW_LET_RE.search(text):
        violations.append(
            Violation(
                gate="L11-clean-prose",
                file=file_path,
                location=location,
                message=f"Raw '\\text{{let }}' binding in --tier authored: {snippet(text)}",
            )
        )
    if L11_BY_DITE_RE.search(text):
        violations.append(
            Violation(
                gate="L11-clean-prose",
                file=file_path,
                location=location,
                message=f"Raw 'by dite' tactic leak in: {snippet(text)}",
            )
        )
    if L11_RAW_VAL_RE.search(text):
        msg = f"Raw '.\\mathrm{{val}}' projection leak in: {snippet(text)}"
        if tier == "authored":
            violations.append(Violation(gate="L11-clean-prose", file=file_path, location=location, message=msg))
        elif warnings is not None:
            warnings.append(Violation(gate="L11-clean-prose", file=file_path, location=location, message=msg))

    lower = text.lower()
    for phrase in L11_ONTOLOGY_PHRASES:
        if phrase in lower:
            msg = f"Lean-ism ontology phrase '{phrase}' in: {snippet(text)}"
            if tier == "authored":
                violations.append(Violation(gate="L11-clean-prose", file=file_path, location=location, message=msg))
            elif warnings is not None:
                warnings.append(Violation(gate="L11-clean-prose", file=file_path, location=location, message=msg))


def check_trust_value(
    obj: Any, file_path: str, location: str, violations: List[Violation]
) -> None:
    if not isinstance(obj, dict):
        return
    for fld in ("trust", "proseTrust"):
        val = obj.get(fld)
        if val is not None and val not in VALID_PROSE_TRUST:
            violations.append(
                Violation(
                    gate="structure",
                    file=file_path,
                    location=f"{location}.{fld}",
                    message=f"Invalid ProseTrust value {val!r} (expected one of {sorted(VALID_PROSE_TRUST)})",
                )
            )


def check_text_leakage(
    text: str, file_path: str, location: str, violations: List[Violation], tier: str = "legacy"
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
    if re.search(r"\bmatch\s+\S[^\n]*\bwith\b", text):
        violations.append(
            Violation(
                gate="zero-leakage",
                file=file_path,
                location=location,
                message=f"Raw Lean match expression found in: {snippet(text)}",
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
    if tier == "authored":
        emitted_authored: Set[str] = set()
        for pat in AUTHORED_FORBIDDEN_CASE_SENSITIVE:
            if pat in text:
                emitted_authored.add(pat)
                violations.append(
                    Violation(
                        gate="zero-leakage",
                        file=file_path,
                        location=location,
                        message=f"Forbidden authored-tier pattern '{pat}' in: {snippet(text)}",
                    )
                )
        for rx, label in AUTHORED_FORBIDDEN_REGEXES:
            if label not in emitted_authored and rx.search(text):
                emitted_authored.add(label)
                violations.append(
                    Violation(
                        gate="zero-leakage",
                        file=file_path,
                        location=location,
                        message=f"Forbidden authored-tier pattern '{label}' in: {snippet(text)}",
                    )
                )
        for pat in AUTHORED_FORBIDDEN_CASE_INSENSITIVE:
            if pat in lower:
                violations.append(
                    Violation(
                        gate="zero-leakage",
                        file=file_path,
                        location=location,
                        message=f"Forbidden authored-tier phrase '{pat}' in: {snippet(text)}",
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
    tier: str = "legacy",
    warnings: Optional[List[Violation]] = None,
) -> str:
    """Validate an Inline array for leakage, broken symbol/dataKey links, and L1/L2/L11/typography."""
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
        check_trust_value(inl, file_path, f"{location}[{idx}]", violations)
        for v in inl.values():
            if isinstance(v, dict):
                check_trust_value(v, file_path, f"{location}[{idx}]", violations)
        seg_is_math = (
            ("inlineMath" in inl)
            or ("displayMath" in inl)
            or ("symbol" in inl and isinstance(inl["symbol"], dict) and bool(inl["symbol"].get("isMath", True)))
        )
        for seg in inline_raw_texts(inl):
            check_text_leakage(seg, file_path, f"{location}[{idx}]", violations, tier=tier)
            check_soundness_and_latex(
                seg,
                file_path,
                f"{location}[{idx}]",
                violations,
                is_math=seg_is_math,
                tier=tier,
                warnings=warnings,
            )

        # L3: Complete symbol key + dataKey resolution across ALL Inline variants
        explicit_dks: List[str] = []
        for attr in ("dataKey", "data-cadmo-key"):
            raw_dk = inl.get(attr)
            if isinstance(raw_dk, str) and raw_dk:
                explicit_dks.append(raw_dk)
        for v in inl.values():
            if isinstance(v, dict):
                for attr in ("dataKey", "data-cadmo-key"):
                    raw_dk = v.get(attr)
                    if isinstance(raw_dk, str) and raw_dk:
                        explicit_dks.append(raw_dk)

        if "symbol" in inl:
            sym = inl["symbol"]
            orig_key = sym.get("key") if isinstance(sym, dict) else None
            first_dk = explicit_dks[0] if explicit_dks else None
            if not orig_key or (orig_key not in inspector_keys and (not first_dk or first_dk not in inspector_keys)):
                violations.append(
                    Violation(
                        gate="structure",
                        file=file_path,
                        location=f"{location}[{idx}]",
                        message=f"Broken inspector symbol key '{orig_key}' (not found in document.inspectors)",
                    )
                )

        for dk in explicit_dks:
            if dk not in inspector_keys:
                violations.append(
                    Violation(
                        gate="L3-dangling-key",
                        file=file_path,
                        location=f"{location}[{idx}]",
                        message=f"Broken inline dataKey '{dk}' (not found in document/section/local inspectors)",
                    )
                )

    joined = flatten_inlines_joined(inlines)
    check_text_leakage(joined, file_path, location, violations, tier=tier)
    check_prose_typography(joined, file_path, location, violations)
    return joined


def check_goal_state(
    goal: Any,
    file_path: str,
    location: str,
    violations: List[Violation],
    tier: str = "legacy",
    warnings: Optional[List[Violation]] = None,
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
    target = str(goal.get("targetLatex", ""))
    check_text_leakage(target, file_path, f"{location}.targetLatex", violations, tier=tier)
    check_soundness_and_latex(
        target, file_path, f"{location}.targetLatex", violations, is_math=True, tier=tier, warnings=warnings
    )
    target_prose = goal.get("targetProse")
    if target_prose:
        tp_str = str(target_prose)
        check_text_leakage(tp_str, file_path, f"{location}.targetProse", violations, tier=tier)
        check_prose_typography(tp_str, file_path, f"{location}.targetProse", violations)
        check_soundness_and_latex(
            tp_str, file_path, f"{location}.targetProse", violations, is_math=False, tier=tier, warnings=warnings
        )
    raw_goal = goal.get("rawLeanGoal")
    if raw_goal:
        raw_str = str(raw_goal)
        for sorry_tok in ("sorryAx", "[UNPROVED: sorry]"):
            if sorry_tok in raw_str:
                violations.append(
                    Violation(
                        gate="zero-leakage",
                        file=file_path,
                        location=f"{location}.rawLeanGoal",
                        message=f"Forbidden pattern '{sorry_tok}' in rawLeanGoal: {snippet(raw_str)}",
                    )
                )
    for idx, ctx in enumerate(goal.get("context") or []):
        if not isinstance(ctx, dict):
            continue
        nm = ctx.get("name")
        if nm is not None:
            nm_str = str(nm)
            check_text_leakage(nm_str, file_path, f"{location}.context[{idx}].name", violations, tier=tier)
            check_soundness_and_latex(
                nm_str,
                file_path,
                f"{location}.context[{idx}].name",
                violations,
                is_math=False,
                tier=tier,
                warnings=warnings,
            )
        desc = str(ctx.get("description", ""))
        check_text_leakage(desc, file_path, f"{location}.context[{idx}].description", violations, tier=tier)
        check_prose_typography(desc, file_path, f"{location}.context[{idx}].description", violations)
        check_soundness_and_latex(
            desc,
            file_path,
            f"{location}.context[{idx}].description",
            violations,
            is_math=False,
            tier=tier,
            warnings=warnings,
        )


def proof_node_canonical_text(node: Dict[str, Any]) -> str:
    """Compute canonical visible text block for sibling deduplication."""
    kind = node.get("kind")
    if kind == "step":
        lead = str(node.get("leadHeading") or "").strip()
        body = flatten_inlines_joined(node.get("content", []))
        raw = f"{lead} {body}".strip() if lead else body
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
    elif kind == "pseudocodeBox":
        title = str(node.get("title", "")).strip()
        box_kind = str(node.get("boxKind", "")).strip()
        line_parts: List[str] = []
        for ln in node.get("lines") or []:
            if isinstance(ln, dict):
                line_parts.append(flatten_inlines_joined(ln.get("inlines", [])))
        raw = f"{box_kind} {title} | " + " ; ".join(line_parts)
    else:
        raw = ""
    return re.sub(r"\s+", " ", raw).strip()


def check_pseudocode_lines(
    lines: Any,
    inspector_keys: Set[str],
    file_path: str,
    location: str,
    violations: List[Violation],
    tier: str = "legacy",
    warnings: Optional[List[Violation]] = None,
) -> None:
    if not isinstance(lines, list):
        violations.append(
            Violation(
                gate="structure",
                file=file_path,
                location=location,
                message="lines must be a list of PseudocodeLine objects",
            )
        )
        return
    for lidx, ln in enumerate(lines):
        lloc = f"{location}[{lidx}]"
        if not isinstance(ln, dict):
            violations.append(
                Violation(
                    gate="structure",
                    file=file_path,
                    location=lloc,
                    message=f"PseudocodeLine must be an object, got {type(ln).__name__}",
                )
            )
            continue
        indent = ln.get("indent", 0)
        if isinstance(indent, bool) or not isinstance(indent, int) or indent < 0:
            violations.append(
                Violation(
                    gate="structure",
                    file=file_path,
                    location=f"{lloc}.indent",
                    message=f"PseudocodeLine.indent must be a non-negative integer, got {indent!r}",
                )
            )
        check_inlines(
            ln.get("inlines", []),
            inspector_keys,
            file_path,
            f"{lloc}.inlines",
            violations,
            tier=tier,
            warnings=warnings,
        )


def check_proof_node_list(
    nodes: Any,
    inspector_keys: Set[str],
    file_path: str,
    location: str,
    violations: List[Violation],
    tier: str = "legacy",
    warnings: Optional[List[Violation]] = None,
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
            check_trust_value(node, file_path, node_loc, violations)
            if node.get("startsParagraph") is not None and not isinstance(node.get("startsParagraph"), bool):
                violations.append(
                    Violation(
                        gate="structure",
                        file=file_path,
                        location=f"{node_loc}.startsParagraph",
                        message="startsParagraph must be a boolean",
                    )
                )
            lead = node.get("leadHeading")
            if lead is not None:
                if not isinstance(lead, str):
                    violations.append(
                        Violation(
                            gate="structure",
                            file=file_path,
                            location=f"{node_loc}.leadHeading",
                            message="leadHeading must be a string or null",
                        )
                    )
                else:
                    check_text_leakage(lead, file_path, f"{node_loc}.leadHeading", violations, tier=tier)
                    check_prose_typography(lead, file_path, f"{node_loc}.leadHeading", violations)
                    check_soundness_and_latex(
                        lead,
                        file_path,
                        f"{node_loc}.leadHeading",
                        violations,
                        is_math=False,
                        tier=tier,
                        warnings=warnings,
                    )
            check_diagram_html(node.get("diagramHtml"), file_path, f"{node_loc}.diagramHtml", violations)
            check_inlines(
                node.get("content", []),
                inspector_keys,
                file_path,
                f"{node_loc}.content",
                violations,
                tier=tier,
                warnings=warnings,
            )
            check_goal_state(
                node.get("goal"), file_path, f"{node_loc}.goal", violations, tier=tier, warnings=warnings
            )
            check_proof_node_list(
                node.get("children", []),
                inspector_keys,
                file_path,
                f"{node_loc}.children",
                violations,
                tier=tier,
                warnings=warnings,
            )
        elif kind == "calcChain":
            check_inlines(
                node.get("intro", []),
                inspector_keys,
                file_path,
                f"{node_loc}.intro",
                violations,
                tier=tier,
                warnings=warnings,
            )
            check_goal_state(
                node.get("goal"), file_path, f"{node_loc}.goal", violations, tier=tier, warnings=warnings
            )
            cid = str(node.get("id") or "")
            cod = str(node.get("originDecl") or "")
            is_cc_calc = (
                cid.startswith(("vcc-calc", "vcc-hybrid-chain"))
                or "cc_calc" in cid.lower()
                or "cc_calc" in cod.lower()
            )
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
                    check_diagram_html(st.get("diagramHtml"), file_path, f"{sloc}.step.diagramHtml", violations)
                    for fld in ("lhsLatex", "relationLatex", "rhsLatex"):
                        fval = str(st.get(fld, ""))
                        check_text_leakage(fval, file_path, f"{sloc}.step.{fld}", violations, tier=tier)
                        check_soundness_and_latex(
                            fval,
                            file_path,
                            f"{sloc}.step.{fld}",
                            violations,
                            is_math=True,
                            tier=tier,
                            warnings=warnings,
                        )
                    reason_joined = check_inlines(
                        st.get("reason", []),
                        inspector_keys,
                        file_path,
                        f"{sloc}.step.reason",
                        violations,
                        tier=tier,
                        warnings=warnings,
                    )
                    rel_latex = str(st.get("relationLatex", ""))
                    if "by elementary algebra" in reason_joined.lower() and any(
                        op in rel_latex for op in L5_NON_ALGEBRA_RELS
                    ):
                        violations.append(
                            Violation(
                                gate="L5-honest-dispatch",
                                file=file_path,
                                location=f"{sloc}.step.reason",
                                message=(
                                    f"False 'by elementary algebra' justification on non-algebraic relation "
                                    f"{rel_latex!r}"
                                ),
                            )
                        )
                    step_children = item.get("children", [])
                    if (
                        tier == "authored"
                        and is_cc_calc
                        and isinstance(step_children, list)
                        and len(step_children) == 0
                    ):
                        rlow = reason_joined.strip().lower()
                        if not any(rlow.startswith(ok_r) for ok_r in L9_TRIVIAL_CALC_REASONS):
                            violations.append(
                                Violation(
                                    gate="L9-cc-calc-subproof",
                                    file=file_path,
                                    location=f"{sloc}.children",
                                    message=(
                                        f"cc_calc step has empty children without trivial reflexivity/definition "
                                        f"reason (got {reason_joined!r})"
                                    ),
                                )
                            )
                    check_proof_node_list(
                        step_children,
                        inspector_keys,
                        file_path,
                        f"{sloc}.children",
                        violations,
                        tier=tier,
                        warnings=warnings,
                    )
        elif kind == "routineReceipt":
            summary = str(node.get("summary", ""))
            check_text_leakage(summary, file_path, f"{node_loc}.summary", violations, tier=tier)
            check_prose_typography(summary, file_path, f"{node_loc}.summary", violations)
            check_soundness_and_latex(
                summary, file_path, f"{node_loc}.summary", violations, is_math=False, tier=tier, warnings=warnings
            )
            check_goal_state(
                node.get("goal"), file_path, f"{node_loc}.goal", violations, tier=tier, warnings=warnings
            )
            check_proof_node_list(
                node.get("details", []),
                inspector_keys,
                file_path,
                f"{node_loc}.details",
                violations,
                tier=tier,
                warnings=warnings,
            )
        elif kind == "flowNote":
            text = str(node.get("text", ""))
            check_text_leakage(text, file_path, f"{node_loc}.text", violations, tier=tier)
            check_prose_typography(text, file_path, f"{node_loc}.text", violations)
            check_soundness_and_latex(
                text, file_path, f"{node_loc}.text", violations, is_math=False, tier=tier, warnings=warnings
            )
        elif kind == "figure":
            check_diagram_html(node.get("html"), file_path, f"{node_loc}.html", violations)
            check_inlines(
                node.get("caption", []),
                inspector_keys,
                file_path,
                f"{node_loc}.caption",
                violations,
                tier=tier,
                warnings=warnings,
            )
        elif kind == "pseudocodeBox":
            box_kind = node.get("boxKind")
            if box_kind is not None:
                if not isinstance(box_kind, str) or box_kind not in VALID_PBOX_KINDS:
                    violations.append(
                        Violation(
                            gate="structure",
                            file=file_path,
                            location=f"{node_loc}.boxKind",
                            message=(
                                f"Invalid pseudocodeBox boxKind {box_kind!r} "
                                f"(expected one of {sorted(VALID_PBOX_KINDS)})"
                            ),
                        )
                    )
            title = node.get("title")
            if title is not None:
                if not isinstance(title, str):
                    violations.append(
                        Violation(
                            gate="structure",
                            file=file_path,
                            location=f"{node_loc}.title",
                            message="pseudocodeBox.title must be a string",
                        )
                    )
                else:
                    check_text_leakage(title, file_path, f"{node_loc}.title", violations, tier=tier)
                    check_prose_typography(title, file_path, f"{node_loc}.title", violations)
                    check_soundness_and_latex(
                        title, file_path, f"{node_loc}.title", violations, is_math=False, tier=tier, warnings=warnings
                    )
            if node.get("lines") is not None:
                check_pseudocode_lines(
                    node.get("lines"),
                    inspector_keys,
                    file_path,
                    f"{node_loc}.lines",
                    violations,
                    tier=tier,
                    warnings=warnings,
                )
            check_goal_state(
                node.get("goal"), file_path, f"{node_loc}.goal", violations, tier=tier, warnings=warnings
            )


def check_section_preludes(
    preludes: Any,
    inspector_keys: Set[str],
    file_path: str,
    location: str,
    violations: List[Violation],
    tier: str = "legacy",
    warnings: Optional[List[Violation]] = None,
) -> None:
    if preludes is None:
        return
    if not isinstance(preludes, list):
        violations.append(
            Violation(
                gate="structure",
                file=file_path,
                location=location,
                message="sectionPreludes must be a list of PreludeBlock objects",
            )
        )
        return
    for pidx, prelude in enumerate(preludes):
        ploc = f"{location}[{pidx}]"
        if not isinstance(prelude, dict):
            violations.append(
                Violation(
                    gate="structure",
                    file=file_path,
                    location=ploc,
                    message=f"PreludeBlock must be an object, got {type(prelude).__name__}",
                )
            )
            continue
        pkind = prelude.get("kind")
        if not isinstance(pkind, str) or pkind not in VALID_PRELUDE_KINDS:
            violations.append(
                Violation(
                    gate="structure",
                    file=file_path,
                    location=f"{ploc}.kind",
                    message=(
                        f"Invalid PreludeBlock kind {pkind!r} "
                        f"(expected one of {sorted(VALID_PRELUDE_KINDS)})"
                    ),
                )
            )
        for fld in ("label", "title"):
            val = prelude.get(fld)
            if val is not None:
                if not isinstance(val, str):
                    violations.append(
                        Violation(
                            gate="structure",
                            file=file_path,
                            location=f"{ploc}.{fld}",
                            message=f"PreludeBlock.{fld} must be a string",
                        )
                    )
                else:
                    check_text_leakage(val, file_path, f"{ploc}.{fld}", violations, tier=tier)
                    check_prose_typography(val, file_path, f"{ploc}.{fld}", violations)
                    check_soundness_and_latex(
                        val,
                        file_path,
                        f"{ploc}.{fld}",
                        violations,
                        is_math=False,
                        tier=tier,
                        warnings=warnings,
                    )
        body = prelude.get("body")
        if body is not None:
            if not isinstance(body, list):
                violations.append(
                    Violation(
                        gate="structure",
                        file=file_path,
                        location=f"{ploc}.body",
                        message="PreludeBlock.body must be a list of Inline paragraphs",
                    )
                )
            else:
                for bidx, para in enumerate(body):
                    check_inlines(
                        para,
                        inspector_keys,
                        file_path,
                        f"{ploc}.body[{bidx}]",
                        violations,
                        tier=tier,
                        warnings=warnings,
                    )
        if prelude.get("lines") is not None:
            check_pseudocode_lines(
                prelude.get("lines"),
                inspector_keys,
                file_path,
                f"{ploc}.lines",
                violations,
                tier=tier,
                warnings=warnings,
            )
        rows = prelude.get("rows")
        if rows is not None:
            if not isinstance(rows, list):
                violations.append(
                    Violation(
                        gate="structure",
                        file=file_path,
                        location=f"{ploc}.rows",
                        message="PreludeBlock.rows must be a list of PreludeRow objects",
                    )
                )
            else:
                for ridx, row in enumerate(rows):
                    rloc = f"{ploc}.rows[{ridx}]"
                    if not isinstance(row, dict):
                        violations.append(
                            Violation(
                                gate="structure",
                                file=file_path,
                                location=rloc,
                                message=f"PreludeRow must be an object, got {type(row).__name__}",
                            )
                        )
                        continue
                    check_inlines(
                        row.get("left", []),
                        inspector_keys,
                        file_path,
                        f"{rloc}.left",
                        violations,
                        tier=tier,
                        warnings=warnings,
                    )
                    check_inlines(
                        row.get("right", []),
                        inspector_keys,
                        file_path,
                        f"{rloc}.right",
                        violations,
                        tier=tier,
                        warnings=warnings,
                    )
        decl_key = prelude.get("declKey")
        if decl_key is not None:
            if not isinstance(decl_key, str) or not decl_key or decl_key not in inspector_keys:
                violations.append(
                    Violation(
                        gate="structure",
                        file=file_path,
                        location=f"{ploc}.declKey",
                        message=(
                            f"Broken prelude declKey {decl_key!r} "
                            "(not found in document/section/local inspectors)"
                        ),
                    )
                )
        check_diagram_html(
            prelude.get("diagramHtml"),
            file_path,
            f"{ploc}.diagramHtml",
            violations,
        )


def check_inspectors(
    inspectors: Any,
    file_path: str,
    violations: List[Violation],
    loc_prefix: str = "inspectors",
    tier: str = "legacy",
    known_keys: Optional[Set[str]] = None,
    warnings: Optional[List[Violation]] = None,
) -> Set[str]:
    keys: Set[str] = set()
    if not isinstance(inspectors, list):
        violations.append(
            Violation(
                gate="structure",
                file=file_path,
                location=loc_prefix,
                message="Expected list of SymbolInspector objects",
            )
        )
        return keys

    for idx, ins in enumerate(inspectors):
        loc = f"{loc_prefix}[{idx}]"
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

    valid_keys = set(known_keys or set()) | keys

    for idx, ins in enumerate(inspectors):
        loc = f"{loc_prefix}[{idx}]"
        if not isinstance(ins, dict):
            continue

        disp = str(ins.get("display", ""))
        check_text_leakage(disp, file_path, f"{loc}.display", violations, tier=tier)
        is_thm_badge = ins.get("roleBadge") == "theorem"
        check_soundness_and_latex(
            disp,
            file_path,
            f"{loc}.display",
            violations,
            is_math=(not is_thm_badge),
            tier=tier,
            warnings=warnings,
        )

        if ins.get("roleBadge") is not None:
            rb = str(ins["roleBadge"])
            check_text_leakage(rb, file_path, f"{loc}.roleBadge", violations, tier=tier)
            check_soundness_and_latex(
                rb, file_path, f"{loc}.roleBadge", violations, is_math=False, tier=tier, warnings=warnings
            )

        if ins.get("docString") is not None:
            ds = str(ins["docString"])
            check_text_leakage(ds, file_path, f"{loc}.docString", violations, tier=tier)
            check_prose_typography(ds, file_path, f"{loc}.docString", violations)
            check_soundness_and_latex(
                ds,
                file_path,
                f"{loc}.docString",
                violations,
                is_math=False,
                check_plain_tex=True,
                tier=tier,
                warnings=warnings,
            )

        for cidx, cl in enumerate(ins.get("clauses") or []):
            cl_str = str(cl)
            check_text_leakage(cl_str, file_path, f"{loc}.clauses[{cidx}]", violations, tier=tier)
            check_soundness_and_latex(
                cl_str,
                file_path,
                f"{loc}.clauses[{cidx}]",
                violations,
                is_math=False,
                tier=tier,
                warnings=warnings,
            )

        for aidx, ap in enumerate(ins.get("sectionAssumptions") or []):
            check_inlines(
                ap,
                valid_keys,
                file_path,
                f"{loc}.sectionAssumptions[{aidx}]",
                violations,
                tier=tier,
                warnings=warnings,
            )

        kind = ins.get("kind") or {}
        if not isinstance(kind, dict):
            continue
        if "interfaceTable" in kind and isinstance(kind["interfaceTable"], dict):
            it = kind["interfaceTable"]
            dom_latex = str(it.get("domainLatex", ""))
            check_text_leakage(dom_latex, file_path, f"{loc}.interfaceTable.domainLatex", violations, tier=tier)
            check_soundness_and_latex(
                dom_latex,
                file_path,
                f"{loc}.interfaceTable.domainLatex",
                violations,
                is_math=True,
                tier=tier,
                warnings=warnings,
            )
            bnote = str(it.get("budgetNote", ""))
            check_text_leakage(bnote, file_path, f"{loc}.interfaceTable.budgetNote", violations, tier=tier)
            check_prose_typography(bnote, file_path, f"{loc}.interfaceTable.budgetNote", violations)
            check_soundness_and_latex(
                bnote,
                file_path,
                f"{loc}.interfaceTable.budgetNote",
                violations,
                is_math=False,
                check_plain_tex=True,
                tier=tier,
                warnings=warnings,
            )
            for pidx, row in enumerate(it.get("ports") or []):
                if isinstance(row, dict):
                    for fld in ("port", "queryLatex", "replyLatex"):
                        rval = str(row.get(fld, ""))
                        check_text_leakage(
                            rval,
                            file_path,
                            f"{loc}.interfaceTable.ports[{pidx}].{fld}",
                            violations,
                            tier=tier,
                        )
                        check_soundness_and_latex(
                            rval,
                            file_path,
                            f"{loc}.interfaceTable.ports[{pidx}].{fld}",
                            violations,
                            is_math=(fld != "port"),
                            tier=tier,
                            warnings=warnings,
                        )
        elif "mathDefinition" in kind and isinstance(kind["mathDefinition"], dict):
            md = kind["mathDefinition"]
            eq_tex = str(md.get("equationLatex", ""))
            check_text_leakage(
                eq_tex,
                file_path,
                f"{loc}.mathDefinition.equationLatex",
                violations,
                tier=tier,
            )
            lean_or_key = str(ins.get("leanName") or ins.get("key") or "")
            check_soundness_and_latex(
                eq_tex,
                file_path,
                f"{loc}.mathDefinition.equationLatex",
                violations,
                is_math=True,
                allow_epsilon_relax_def=("epsilonRelaxation" in lean_or_key),
                tier=tier,
                warnings=warnings,
            )
            ps = str(md.get("proseSummary", ""))
            check_text_leakage(ps, file_path, f"{loc}.mathDefinition.proseSummary", violations, tier=tier)
            check_prose_typography(ps, file_path, f"{loc}.mathDefinition.proseSummary", violations)
            check_soundness_and_latex(
                ps,
                file_path,
                f"{loc}.mathDefinition.proseSummary",
                violations,
                is_math=False,
                check_plain_tex=True,
                tier=tier,
                warnings=warnings,
            )
        elif "dslPseudocode" in kind and isinstance(kind["dslPseudocode"], dict):
            dp = kind["dslPseudocode"]
            body_str = str(dp.get("body") or "").strip()
            src_str = str(dp.get("fullSource") or "").strip()
            if not body_str and not src_str:
                violations.append(
                    Violation(
                        gate="L8-empty-dsl",
                        file=file_path,
                        location=f"{loc}.dslPseudocode",
                        message=f"dslPseudocode card for '{ins.get('key')}' has empty body and fullSource",
                    )
                )
            hdr = str(dp.get("header") or "")
            check_text_leakage(hdr, file_path, f"{loc}.dslPseudocode.header", violations, tier=tier)
            check_soundness_and_latex(
                hdr,
                file_path,
                f"{loc}.dslPseudocode.header",
                violations,
                is_math=False,
                tier=tier,
                warnings=warnings,
            )
        elif "witnessCard" in kind and isinstance(kind["witnessCard"], dict):
            wc = kind["witnessCard"]
            title = str(wc.get("title", ""))
            check_text_leakage(title, file_path, f"{loc}.witnessCard.title", violations, tier=tier)
            check_prose_typography(title, file_path, f"{loc}.witnessCard.title", violations)
            check_soundness_and_latex(
                title, file_path, f"{loc}.witnessCard.title", violations, is_math=False, tier=tier, warnings=warnings
            )
            for ridx, row in enumerate(wc.get("rows") or []):
                if isinstance(row, list) and len(row) == 2:
                    for col in (0, 1):
                        cell = str(row[col])
                        check_text_leakage(
                            cell, file_path, f"{loc}.witnessCard.rows[{ridx}][{col}]", violations, tier=tier
                        )
                        check_soundness_and_latex(
                            cell,
                            file_path,
                            f"{loc}.witnessCard.rows[{ridx}][{col}]",
                            violations,
                            is_math=False,
                            check_plain_tex=True,
                            tier=tier,
                            warnings=warnings,
                        )
        elif "parameter" in kind:
            p = kind["parameter"]
            desc = p if isinstance(p, str) else str((p or {}).get("roleDescription", ""))
            check_text_leakage(desc, file_path, f"{loc}.parameter.roleDescription", violations, tier=tier)
            check_prose_typography(desc, file_path, f"{loc}.parameter.roleDescription", violations)
            check_soundness_and_latex(
                desc,
                file_path,
                f"{loc}.parameter.roleDescription",
                violations,
                is_math=False,
                check_plain_tex=True,
                tier=tier,
                warnings=warnings,
            )
        elif "localShorthand" in kind and isinstance(kind["localShorthand"], dict):
            ls = kind["localShorthand"]
            eq_tex = str(ls.get("equationLatex", ""))
            check_text_leakage(
                eq_tex,
                file_path,
                f"{loc}.localShorthand.equationLatex",
                violations,
                tier=tier,
            )
            check_soundness_and_latex(
                eq_tex,
                file_path,
                f"{loc}.localShorthand.equationLatex",
                violations,
                is_math=True,
                tier=tier,
                warnings=warnings,
            )
            rd = str(ls.get("roleDescription", ""))
            check_text_leakage(rd, file_path, f"{loc}.localShorthand.roleDescription", violations, tier=tier)
            check_prose_typography(rd, file_path, f"{loc}.localShorthand.roleDescription", violations)
            check_soundness_and_latex(
                rd,
                file_path,
                f"{loc}.localShorthand.roleDescription",
                violations,
                is_math=False,
                check_plain_tex=True,
                tier=tier,
                warnings=warnings,
            )
        elif "ccDiagram" in kind and isinstance(kind["ccDiagram"], dict):
            check_diagram_html(
                kind["ccDiagram"].get("svgOrHtml"),
                file_path,
                f"{loc}.ccDiagram.svgOrHtml",
                violations,
            )
            sum_tex = str(kind["ccDiagram"].get("summaryLatex", ""))
            check_text_leakage(
                sum_tex,
                file_path,
                f"{loc}.ccDiagram.summaryLatex",
                violations,
                tier=tier,
            )
            check_soundness_and_latex(
                sum_tex,
                file_path,
                f"{loc}.ccDiagram.summaryLatex",
                violations,
                is_math=True,
                tier=tier,
                warnings=warnings,
            )
    return keys


def _is_noncore_origin(origin: Optional[str]) -> bool:
    if not origin:
        return False
    if origin.startswith(L6_CORE_ORIGIN_PREFIXES) or origin.endswith(L6_CORE_ORIGIN_SUFFIXES):
        return False
    return True


def _collect_proof_body_signatures(nodes: Any) -> Tuple[Set[str], Set[str]]:
    """Collect non-core originDecls and non-trivial canonical step texts for L6 overlap checks."""
    origins: Set[str] = set()
    texts: Set[str] = set()
    if not isinstance(nodes, list):
        return origins, texts
    for node in nodes:
        if not isinstance(node, dict):
            continue
        od = node.get("originDecl")
        if isinstance(od, str) and _is_noncore_origin(od):
            origins.add(od)
        kind = node.get("kind")
        if kind in ("step", "calcChain", "pseudocodeBox"):
            ct = proof_node_canonical_text(node)
            ct_low = ct.lower()
            if len(ct) >= 10 and not ct_low.startswith(
                ("this holds by the assumption", "this holds by the assumed")
            ):
                texts.add(ct)
        for sub_key in ("children", "details"):
            o2, t2 = _collect_proof_body_signatures(node.get(sub_key))
            origins |= o2
            texts |= t2
        if kind == "calcChain":
            for item in node.get("steps") or []:
                if isinstance(item, dict):
                    o3, t3 = _collect_proof_body_signatures(item.get("children"))
                    origins |= o3
                    texts |= t3
    return origins, texts


def _count_proof_nodes(nodes: Any) -> int:
    if not isinstance(nodes, list):
        return 0
    total = 0
    for node in nodes:
        if not isinstance(node, dict):
            continue
        total += 1
        total += _count_proof_nodes(node.get("children"))
        total += _count_proof_nodes(node.get("details"))
        if node.get("kind") == "calcChain":
            for item in node.get("steps") or []:
                if isinstance(item, dict):
                    total += _count_proof_nodes(item.get("children"))
    return total


def check_l6_sibling_reexpansion_and_budget(
    entries: List[Dict[str, Any]],
    file_path: str,
    tier: str,
    violations: List[Violation],
    warnings: List[Violation],
) -> int:
    """Enforce L6: zero sibling proof-body re-expansion (ALL tiers FAIL) and node-count soft budget."""
    sigs_by_decl: Dict[str, Tuple[Set[str], Set[str]]] = {}
    for e in entries:
        decl = e.get("declaration")
        if isinstance(decl, str) and decl:
            sigs_by_decl[decl] = _collect_proof_body_signatures(e.get("proof", []))

    soft_budget = L6_NODE_BUDGET.get(tier, 120)
    max_nodes = 0

    def walk(nodes: Any, cur_decl: str, loc: str) -> None:
        if not isinstance(nodes, list):
            return
        for idx, node in enumerate(nodes):
            if not isinstance(node, dict):
                continue
            nloc = f"{loc}[{idx}]"
            od = node.get("originDecl")
            sub_children = node.get("children") or node.get("details") or []
            if (
                isinstance(od, str)
                and od in sigs_by_decl
                and od != cur_decl
                and isinstance(sub_children, list)
                and len(sub_children) > 0
            ):
                ch_origins, ch_texts = _collect_proof_body_signatures(sub_children)
                sib_origins, sib_texts = sigs_by_decl[od]
                if (ch_origins & sib_origins) or (ch_texts & sib_texts):
                    violations.append(
                        Violation(
                            gate="L6-sibling-reexpansion",
                            file=file_path,
                            location=nloc,
                            message=(
                                f"Proof of '{cur_decl}' re-expands sibling entry '{od}' proof body "
                                "(cite sibling as a leaf instead)"
                            ),
                        )
                    )
            walk(node.get("children"), cur_decl, f"{nloc}.children")
            walk(node.get("details"), cur_decl, f"{nloc}.details")
            if node.get("kind") == "calcChain":
                for sidx, item in enumerate(node.get("steps") or []):
                    if isinstance(item, dict):
                        walk(item.get("children"), cur_decl, f"{nloc}.steps[{sidx}].children")

    for eidx, e in enumerate(entries):
        decl = str(e.get("declaration") or f"<entry-{eidx}>")
        proof = e.get("proof", [])
        walk(proof, decl, f"entries[{eidx}]({decl}).proof")
        cnt = _count_proof_nodes(proof)
        if cnt > max_nodes:
            max_nodes = cnt
        if cnt > soft_budget:
            warnings.append(
                Violation(
                    gate="L6-node-budget",
                    file=file_path,
                    location=f"entries[{eidx}]({decl})",
                    message=f"Entry proof node count {cnt} exceeds soft budget ({soft_budget} for tier={tier})",
                )
            )
    return max_nodes


def _extract_inline_math_tokens(inlines: Any) -> List[str]:
    out: List[str] = []
    if not isinstance(inlines, list):
        return out
    for inl in inlines:
        if not isinstance(inl, dict):
            continue
        if "inlineMath" in inl:
            v = inl["inlineMath"]
            s = (v if isinstance(v, str) else str(v.get("latex", ""))).strip()
            if s:
                out.append(s)
        elif "displayMath" in inl:
            v = inl["displayMath"]
            s = (v if isinstance(v, str) else str(v.get("latex", ""))).strip()
            if s:
                out.append(s)
        elif "symbol" in inl and isinstance(inl["symbol"], dict) and inl["symbol"].get("isMath", True):
            s = str(inl["symbol"].get("display", "")).strip()
            if s:
                out.append(s)
    return out


def _normalize_prose_core(text: str) -> str:
    s = re.sub(r"\s+", " ", text).strip().rstrip(".,;:").strip().lower()
    for prefix in (
        "we claim ",
        "we obtain ",
        "therefore, ",
        "hence, ",
        "thus, ",
        "first, ",
        "second, ",
        "next, ",
        "then, ",
        "finally, ",
        "by substitution of equals, ",
        "by simplification, ",
    ):
        if s.startswith(prefix):
            s = s[len(prefix) :].strip()
    return s


def _is_tautological_1child_step(parent_node: Dict[str, Any], child_node: Dict[str, Any]) -> bool:
    p_inls = parent_node.get("content", [])
    c_inls = child_node.get("content", [])
    p_raw = re.sub(r"\s+", " ", flatten_inlines_joined(p_inls)).strip()
    c_raw = re.sub(r"\s+", " ", flatten_inlines_joined(c_inls)).strip()
    if not c_raw:
        return True
    p_low = p_raw.rstrip(".,;:").strip().lower()
    c_low = c_raw.rstrip(".,;:").strip().lower()
    if c_low == p_low:
        return True
    p_core = _normalize_prose_core(p_raw)
    c_core = _normalize_prose_core(c_raw)
    if c_core and c_core == p_core:
        return True

    p_math = _extract_inline_math_tokens(p_inls)
    c_math = _extract_inline_math_tokens(c_inls)
    all_child_math_in_parent = all(
        any(pm == cm or (len(cm) >= 4 and cm in pm) for pm in p_math) for cm in c_math
    )
    if c_low.startswith("this holds by the assumed "):
        return True
    if not all_child_math_in_parent:
        return False
    if c_low.startswith(("the claim follows from ", "the claim follows directly by ")):
        return True
    if c_low.startswith(("we obtain ", "therefore, ", "hence, ", "thus, ")) and bool(c_math):
        return True
    if c_low.startswith(("by ", "from ")) and ", " in c_low:
        rhs = c_low.split(", ", 1)[1].strip()
        if rhs and (rhs == p_core or rhs in p_core):
            return True
    return False


def check_l9_tautological_toggles(
    entries: List[Dict[str, Any]],
    file_path: str,
    tier: str,
    violations: List[Violation],
) -> Tuple[int, int, float]:
    total_steps = 0
    taut_count = 0

    def walk(nodes: Any) -> None:
        nonlocal total_steps, taut_count
        if not isinstance(nodes, list):
            return
        for node in nodes:
            if not isinstance(node, dict):
                continue
            kind = node.get("kind")
            if kind == "step":
                total_steps += 1
                ch = node.get("children") or []
                if (
                    len(ch) == 1
                    and isinstance(ch[0], dict)
                    and ch[0].get("kind") == "step"
                    and not (ch[0].get("children") or [])
                    and not ch[0].get("diagramHtml")
                    and _is_tautological_1child_step(node, ch[0])
                ):
                    taut_count += 1
                walk(ch)
            elif kind == "calcChain":
                for item in node.get("steps") or []:
                    if isinstance(item, dict):
                        walk(item.get("children"))
            elif kind == "routineReceipt":
                walk(node.get("details"))

    for e in entries:
        walk(e.get("proof", []))

    ratio = (taut_count / total_steps) if total_steps > 0 else 0.0
    if tier == "authored" and ratio > L9_MAX_TAUTOLOGICAL_RATIO:
        violations.append(
            Violation(
                gate="L9-tautological-toggles",
                file=file_path,
                location="document.entries",
                message=(
                    f"1-child tautological leaf toggle ratio {taut_count}/{total_steps} "
                    f"({ratio:.1%}) exceeds {L9_MAX_TAUTOLOGICAL_RATIO:.0%} limit in --tier authored"
                ),
            )
        )
    return total_steps, taut_count, round(ratio, 4)


def _is_polymorphic_exempt_group(lean_names: Set[str]) -> bool:
    for fam in L12_POLYMORPHIC_FAMILIES:
        if lean_names.issubset(fam):
            return True
    for suf in L12_POLYMORPHIC_SUFFIXES:
        if all(nm.endswith(suf) for nm in lean_names):
            return True
    return False


def check_l12_namespace_collisions(
    inspectors: Any,
    file_path: str,
    tier: str,
    violations: List[Violation],
    warnings: List[Violation],
) -> None:
    if not isinstance(inspectors, list):
        return
    by_display: Dict[str, Set[str]] = {}
    for ins in inspectors:
        if not isinstance(ins, dict):
            continue
        disp = str(ins.get("display") or "").strip()
        if not disp:
            continue
        ln = str(ins.get("leanName") or "").strip()
        ident = ln if ln else str(ins.get("key") or "").strip()
        if ident:
            by_display.setdefault(disp, set()).add(ident)

    for disp, names in sorted(by_display.items()):
        if len(names) <= 1 or _is_polymorphic_exempt_group(names):
            continue
        msg = (
            f"Global inspector display {disp!r} collides across distinct definitions: "
            + ", ".join(sorted(names))
        )
        if tier == "authored":
            violations.append(
                Violation(
                    gate="L12-namespace-collision",
                    file=file_path,
                    location="document.inspectors",
                    message=msg,
                )
            )
        else:
            warnings.append(
                Violation(
                    gate="L12-namespace-collision",
                    file=file_path,
                    location="document.inspectors",
                    message=msg,
                )
            )


def check_document(
    doc: Any,
    file_path: str,
    allow_axioms: bool,
    report: FileReport,
    tier: str = "legacy",
) -> None:
    violations = report.violations
    warnings = report.warnings
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
        check_text_leakage(title, file_path, "document.title", violations, tier=tier)
        check_prose_typography(title, file_path, "document.title", violations)
        check_soundness_and_latex(
            title, file_path, "document.title", violations, is_math=False, tier=tier, warnings=warnings
        )
        for rx, tok in L11_JARGON_SUBTITLE_PATTERNS:
            if rx.search(title):
                violations.append(
                    Violation(
                        gate="L11-clean-prose",
                        file=file_path,
                        location="document.title",
                        message=f"Developer-jargon token '{tok}' in document title: {snippet(title)}",
                    )
                )

    subtitle = doc.get("subtitle")
    if subtitle is not None:
        sub_str = str(subtitle)
        check_text_leakage(sub_str, file_path, "document.subtitle", violations, tier=tier)
        check_prose_typography(sub_str, file_path, "document.subtitle", violations)
        check_soundness_and_latex(
            sub_str, file_path, "document.subtitle", violations, is_math=False, tier=tier, warnings=warnings
        )
        for rx, tok in L11_JARGON_SUBTITLE_PATTERNS:
            if rx.search(sub_str):
                violations.append(
                    Violation(
                        gate="L11-clean-prose",
                        file=file_path,
                        location="document.subtitle",
                        message=f"Developer-jargon token '{tok}' in document subtitle: {snippet(sub_str)}",
                    )
                )

    inspectors = doc.get("inspectors", [])
    inspector_keys = check_inspectors(
        inspectors, file_path, violations, tier=tier, warnings=warnings
    )
    report.inspectors_checked = len(inspector_keys)

    # L8: mathDefinition empty-equation ratio metrics
    math_defs = [
        ins
        for ins in (inspectors if isinstance(inspectors, list) else [])
        if isinstance(ins, dict)
        and isinstance(ins.get("kind"), dict)
        and "mathDefinition" in ins["kind"]
    ]
    empty_eqs = sum(
        1
        for ins in math_defs
        if not str(((ins["kind"].get("mathDefinition") or {}).get("equationLatex")) or "").strip()
    )
    report.metrics["math_def_count"] = len(math_defs)
    report.metrics["empty_equation_count"] = empty_eqs
    report.metrics["empty_equation_ratio"] = round((empty_eqs / len(math_defs)) if math_defs else 0.0, 4)

    # L12: Global hover namespace disambiguation
    check_l12_namespace_collisions(inspectors, file_path, tier, violations, warnings)

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
    valid_entries = [e for e in entries if isinstance(e, dict)]

    # L10: Pre-theorem self-contained framing (authored FAIL, legacy WARN)
    if valid_entries and not any(bool(e.get("sectionPreludes")) or bool(e.get("ambient")) for e in valid_entries):
        msg = "Document has zero sectionPreludes or ambient blocks before theorems"
        if tier == "authored":
            violations.append(Violation(gate="L10-framing", file=file_path, location="document.entries", message=msg))
        else:
            warnings.append(Violation(gate="L10-framing", file=file_path, location="document.entries", message=msg))

    # L6: Bounded DAG proof trees & node-count soft budget
    report.metrics["max_nodes_per_entry"] = check_l6_sibling_reexpansion_and_budget(
        valid_entries, file_path, tier, violations, warnings
    )

    # L9: Tautological 1-child leaf ratio
    total_steps, taut_count, taut_ratio = check_l9_tautological_toggles(
        valid_entries, file_path, tier, violations
    )
    report.metrics["total_steps"] = total_steps
    report.metrics["tautological_1child_count"] = taut_count
    report.metrics["tautological_1child_ratio"] = taut_ratio

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

        header = entry.get("header")
        if header:
            header_str = str(header)
            check_text_leakage(header_str, file_path, f"{eloc_named}.header", violations, tier=tier)
            if tier == "authored":
                h_stripped = header_str.strip()
                if h_stripped in LOWERCASE_THEOREM_HEADERS or (
                    h_stripped.lower() in LOWERCASE_THEOREM_HEADERS and h_stripped[:1].islower()
                ):
                    violations.append(
                        Violation(
                            gate="typography",
                            file=file_path,
                            location=f"{eloc_named}.header",
                            message=f"Lowercase theorem header {header_str!r} in --tier authored (must be Title Case)",
                        )
                    )
        if entry.get("title"):
            etitle = str(entry["title"])
            check_text_leakage(etitle, file_path, f"{eloc_named}.title", violations, tier=tier)
            check_prose_typography(etitle, file_path, f"{eloc_named}.title", violations)
            check_soundness_and_latex(
                etitle, file_path, f"{eloc_named}.title", violations, is_math=False, tier=tier, warnings=warnings
            )

        # L4: Section & TOC structural integrity
        sec_title = entry.get("sectionTitle")
        if isinstance(sec_title, str) and sec_title.strip():
            check_text_leakage(sec_title, file_path, f"{eloc_named}.sectionTitle", violations, tier=tier)
            check_prose_typography(sec_title, file_path, f"{eloc_named}.sectionTitle", violations)
            check_soundness_and_latex(
                sec_title,
                file_path,
                f"{eloc_named}.sectionTitle",
                violations,
                is_math=False,
                tier=tier,
                warnings=warnings,
            )
            sec_id = entry.get("sectionId")
            if not isinstance(sec_id, str) or not sec_id.strip():
                violations.append(
                    Violation(
                        gate="L4-section-integrity",
                        file=file_path,
                        location=f"{eloc_named}.sectionId",
                        message=f"Entry with sectionTitle {sec_title!r} has missing/null sectionId",
                    )
                )
            if L4_DOUBLE_SECTION_NUM_RE.match(sec_title):
                violations.append(
                    Violation(
                        gate="L4-section-integrity",
                        file=file_path,
                        location=f"{eloc_named}.sectionTitle",
                        message=f"Double-numbered sectionTitle {sec_title!r}",
                    )
                )
        if entry.get("sectionIntro"):
            sintro = str(entry["sectionIntro"])
            check_text_leakage(sintro, file_path, f"{eloc_named}.sectionIntro", violations, tier=tier)
            check_prose_typography(sintro, file_path, f"{eloc_named}.sectionIntro", violations)
            check_soundness_and_latex(
                sintro,
                file_path,
                f"{eloc_named}.sectionIntro",
                violations,
                is_math=False,
                tier=tier,
                warnings=warnings,
            )

        check_diagram_html(
            entry.get("diagramHtml"), file_path, f"{eloc_named}.diagramHtml", violations
        )

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

        entry_inspector_keys: Set[str] = set(inspector_keys)

        sec_ctx = entry.get("sectionContext")
        if isinstance(sec_ctx, dict):
            sc_keys = check_inspectors(
                sec_ctx.get("inspectors") or [],
                file_path,
                violations,
                f"{eloc_named}.sectionContext.inspectors",
                tier=tier,
                known_keys=entry_inspector_keys,
                warnings=warnings,
            )
            entry_inspector_keys |= sc_keys
            for spidx, spara in enumerate(sec_ctx.get("paragraphs") or []):
                joined = check_inlines(
                    spara,
                    entry_inspector_keys,
                    file_path,
                    f"{eloc_named}.sectionContext.paragraphs[{spidx}]",
                    violations,
                    tier=tier,
                    warnings=warnings,
                )
                if not joined.strip():
                    violations.append(
                        Violation(
                            gate="structure",
                            file=file_path,
                            location=f"{eloc_named}.sectionContext.paragraphs[{spidx}]",
                            message="Empty section context paragraph",
                        )
                    )

        local_ins = entry.get("localInspectors")
        if isinstance(local_ins, list):
            entry_inspector_keys |= check_inspectors(
                local_ins,
                file_path,
                violations,
                f"{eloc_named}.localInspectors",
                tier=tier,
                known_keys=entry_inspector_keys,
                warnings=warnings,
            )

        for rkey in entry.get("referencedKeys") or []:
            if rkey not in entry_inspector_keys:
                violations.append(
                    Violation(
                        gate="structure",
                        file=file_path,
                        location=f"{eloc_named}.referencedKeys",
                        message=f"referencedKey {rkey!r} does not exist in document/section/local inspectors",
                    )
                )

        check_section_preludes(
            entry.get("sectionPreludes"),
            entry_inspector_keys,
            file_path,
            f"{eloc_named}.sectionPreludes",
            violations,
            tier=tier,
            warnings=warnings,
        )

        # Ambient setting
        ambient = entry.get("ambient")
        if isinstance(ambient, dict):
            check_inlines(
                ambient.get("summary", []),
                entry_inspector_keys,
                file_path,
                f"{eloc_named}.ambient.summary",
                violations,
                tier=tier,
                warnings=warnings,
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
                    entry_inspector_keys,
                    file_path,
                    f"{eloc_named}.statement[{pidx}]",
                    violations,
                    tier=tier,
                    warnings=warnings,
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
            entry_inspector_keys,
            file_path,
            f"{eloc_named}.proof",
            violations,
            tier=tier,
            warnings=warnings,
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
            toggles = page.locator("button.cadmo-inline-toggle, button.cadmo-toggle")
            if toggles.count() > 0:
                first_toggle = toggles.first
                before = first_toggle.get_attribute("aria-expanded")
                first_toggle.click()
                after = page.locator("button.cadmo-inline-toggle, button.cadmo-toggle").first.get_attribute("aria-expanded")
                if before == after or after != "true":
                    report.violations.append(
                        Violation(
                            gate="playwright",
                            file=str(html_path),
                            location="button.cadmo-inline-toggle",
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
            syms = page.locator("button.cadmo-sym, .cadmo-ref")
            if syms.count() > 0:
                syms.first.click()
                inspector_title = page.locator(".cadmo-margin .cadmo-inspector-title, .cadmo-margin .cadmo-sidenote-title")
                if inspector_title.count() == 0:
                    report.violations.append(
                        Violation(
                            gate="playwright",
                            file=str(html_path),
                            location="button.cadmo-sym",
                            message="Clicking underlined symbol did not open margin inspector card",
                        )
                    )

            # Verify 0 .cadmo-ref inside sup/sub/.msupsub/.op-limits/delimiters
            blocked_refs = page.locator(
                "sup .cadmo-ref, sub .cadmo-ref, .msupsub .cadmo-ref, "
                ".op-limits .cadmo-ref, .accent-body .cadmo-ref, "
                ".mopen .cadmo-ref, .mclose .cadmo-ref, .mpunct .cadmo-ref, "
                ".mbin .cadmo-ref, .mrel .cadmo-ref"
            ).count()
            if blocked_refs > 0:
                report.violations.append(
                    Violation(
                        gate="playwright",
                        file=str(html_path),
                        location=".cadmo-ref",
                        message=f"Found {blocked_refs} .cadmo-ref hover anchor(s) inside sup/sub/.msupsub/delimiters",
                    )
                )

            # Verify 0 bare numeric digit .cadmo-ref
            digit_refs = page.evaluate(
                "() => Array.from(document.querySelectorAll('.cadmo-ref')).filter(el => /^\\s*[0-9]+\\s*$/.test(el.textContent || '')).length"
            )
            if digit_refs > 0:
                report.violations.append(
                    Violation(
                        gate="playwright",
                        file=str(html_path),
                        location=".cadmo-ref",
                        message=f"Found {digit_refs} bare numeric digit .cadmo-ref hover anchor(s)",
                    )
                )

            # Verify 0 font-prefix collisions across \\mathcal{E}/E, \\mathbf{G}/G, \\mathbb{R}/R, etc.
            font_collisions = page.evaluate(
                """() => {
                  const issues = [];
                  const helpers = window.__cadmoHelpers;
                  if (helpers) {
                    if (helpers.normalizeMathToken('\\\\mathcal{E}') === helpers.normalizeMathToken('E')) {
                      issues.push('Font normalization collision between \\\\mathcal{E} and E');
                    }
                    if (helpers.normalizeMathToken('\\\\mathbf{G}') === helpers.normalizeMathToken('G')) {
                      issues.push('Font normalization collision between \\\\mathbf{G} and G');
                    }
                    if (helpers.normalizeMathToken('\\\\mathbb{R}') !== 'bb:R') {
                      issues.push('Expected normalizeMathToken(\\\\mathbb{R}) === bb:R');
                    }
                  }
                  for (const ref of document.querySelectorAll('.cadmo-ref')) {
                    const tok = ref.dataset ? (ref.dataset.cadmoToken || '') : '';
                    if (!tok || tok.startsWith('key:')) continue;
                    const domPrefix = helpers
                      ? helpers.extractFontPrefixFromDomNode(ref)
                      : '';
                    const tokPrefixMatch = tok.match(/^(cal|bf|sf|bb):/);
                    const tokPrefix = tokPrefixMatch ? (tokPrefixMatch[1] + ':') : '';
                    if (domPrefix !== tokPrefix) {
                      issues.push(`DOM font prefix (${domPrefix || 'plain'}) mismatched token (${tok})`);
                    }
                  }
                  return issues;
                }"""
            )
            if font_collisions:
                for issue in font_collisions:
                    report.violations.append(
                        Violation(
                            gate="playwright",
                            file=str(html_path),
                            location=".cadmo-ref",
                            message=str(issue),
                        )
                    )

            # L2/L3 Playwright checks: 0 KaTeX parse errors, 0 double-numbered headings, mounted diagrams
            katex_errors = page.locator(".katex-error").count()
            if katex_errors > 0:
                report.violations.append(
                    Violation(
                        gate="L2-latex-hygiene",
                        file=str(html_path),
                        location=".katex-error",
                        message=f"Found {katex_errors} KaTeX parse error node(s) in DOM",
                    )
                )

            dbl_headings = page.evaluate(
                """() => Array.from(document.querySelectorAll('.cadmo-section-title, h1, h2, h3, h4'))
                  .map(el => (el.textContent || '').replace(/\\s+/g, ' ').trim())
                  .filter(t => /^\\d+\\.\\s*(?:Section|§|Chapter|Part)\\s*\\d/i.test(t))"""
            )
            for htxt in dbl_headings or []:
                report.violations.append(
                    Violation(
                        gate="L4-section-integrity",
                        file=str(html_path),
                        location="heading",
                        message=f"Double-numbered rendered heading in DOM: {htxt!r}",
                    )
                )

            expected_entry_diags = page.evaluate(
                """() => {
                  const el = document.getElementById('cadmo-document-data');
                  if (!el) return 0;
                  try {
                    const doc = JSON.parse(el.textContent || '{}');
                    return (doc.entries || []).filter(e => !!(e && e.diagramHtml)).length;
                  } catch { return 0; }
                }"""
            )
            if expected_entry_diags and expected_entry_diags > 0:
                mounted_diags = page.locator(".cadmo-entry-diagram .cadmo-diagram-body").count()
                if mounted_diags < expected_entry_diags:
                    report.violations.append(
                        Violation(
                            gate="L3-mounted-visuals",
                            file=str(html_path),
                            location=".cadmo-entry-diagram",
                            message=(
                                f"Expected {expected_entry_diags} mounted entry diagram(s), "
                                f"found {mounted_diags}"
                            ),
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
    tier: str = "legacy",
) -> FileReport:
    suffix = path.suffix.lower()
    if not path.is_file():
        rep = FileReport(path=str(path), kind="missing", tier=tier)
        rep.violations.append(
            Violation(gate="io", file=str(path), location="file", message="File does not exist")
        )
        return rep

    text = path.read_text(encoding="utf-8")

    if suffix == ".json":
        rep = FileReport(path=str(path), kind="json", tier=tier)
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
        check_document(doc, str(path), allow_axioms=allow_axioms, report=rep, tier=tier)
        size_mb = path.stat().st_size / (1024.0 * 1024.0)
        rep.metrics["file_size_mb"] = round(size_mb, 3)
        cap_mb = L7_MONOGRAPH_MAX_MB if rep.entries_checked >= L7_MONOGRAPH_ENTRY_THRESHOLD else L7_SMALL_MAX_MB
        rep.metrics["payload_budget_mb"] = cap_mb
        if size_mb > cap_mb:
            rep.violations.append(
                Violation(
                    gate="L7-payload-budget",
                    file=str(path),
                    location="file",
                    message=(
                        f"JSON size {size_mb:.2f} MB exceeds {cap_mb:.1f} MB budget "
                        f"for {rep.entries_checked} entries"
                    ),
                )
            )
        return rep

    if suffix in (".html", ".htm"):
        rep = FileReport(path=str(path), kind="html", tier=tier)

        # L4: Check static HTML headings for double-numbered sections
        for _, raw_inner in HTML_HEADING_RE.findall(text):
            cleaned_heading = re.sub(r"\s+", " ", HTML_TAG_RE.sub(" ", raw_inner)).strip()
            if L4_DOUBLE_SECTION_NUM_RE.match(cleaned_heading):
                rep.violations.append(
                    Violation(
                        gate="L4-section-integrity",
                        file=str(path),
                        location="html-heading",
                        message=f"Double-numbered HTML heading: {cleaned_heading!r}",
                    )
                )

        style_matches = STYLE_CADMO_RE.findall(text)
        if len(style_matches) != 1 or not style_matches[0].strip():
            rep.violations.append(
                Violation(
                    gate="html-bundle",
                    file=str(path),
                    location="style[data-cadmo-reader]",
                    message=(
                        f"Expected exactly 1 non-empty <style data-cadmo-reader> CSS block, found {len(style_matches)}"
                    ),
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
                check_document(doc, str(path), allow_axioms=allow_axioms, report=rep, tier=tier)

        if run_playwright:
            run_playwright_smoke(
                html_path=path,
                report=rep,
                screenshot_path=screenshot_path,
                skip_if_missing=playwright_skip_if_missing,
            )
        return rep

    rep = FileReport(path=str(path), kind="unknown", tier=tier)
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
    total_warnings = sum(len(r.warnings) for r in reports)
    for rep in reports:
        status = "PASS" if rep.ok else f"FAIL ({len(rep.violations)} issue(s))"
        meta = f"[{rep.kind} tier={rep.tier}] entries={rep.entries_checked} inspectors={rep.inspectors_checked}"
        if "empty_equation_count" in rep.metrics:
            meta += (
                f" empty_eq={rep.metrics['empty_equation_count']}/{rep.metrics.get('math_def_count', 0)}"
                f" ({rep.metrics.get('empty_equation_ratio', 0.0):.1%})"
            )
        if "max_nodes_per_entry" in rep.metrics:
            meta += f" max_nodes={rep.metrics['max_nodes_per_entry']}"
        if "file_size_mb" in rep.metrics:
            meta += f" size={rep.metrics['file_size_mb']:.2f}MB"
        if rep.warnings:
            meta += f" warnings={len(rep.warnings)}"
        if rep.playwright_status:
            meta += f" playwright={rep.playwright_status}"
        lines.append(f"{status}: {rep.path}  {meta}")
        for v in rep.violations:
            lines.append(f"  - [{v.gate}] {v.location}: {v.message}")
        for w in rep.warnings:
            lines.append(f"  - [WARN:{w.gate}] {w.location}: {w.message}")
    lines.append("")
    if total_violations == 0:
        warn_note = f" ({total_warnings} warning(s))" if total_warnings else ""
        lines.append(f"ALL GATES PASSED across {len(reports)} file(s){warn_note}.")
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
        "--tier",
        choices=sorted(VALID_TIERS),
        default="legacy",
        help="CI quality tier: 'legacy' (default, zero-edit legacy repos) or 'authored' (strict Spine-authored monographs)",
    )
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
            tier=args.tier,
        )
        for f in args.files
    ]

    if args.json_report:
        payload = {
            "ok": all(r.ok for r in reports),
            "tier": args.tier,
            "files": [
                {
                    "path": r.path,
                    "kind": r.kind,
                    "tier": r.tier,
                    "ok": r.ok,
                    "entries_checked": r.entries_checked,
                    "inspectors_checked": r.inspectors_checked,
                    "playwright_status": r.playwright_status,
                    "metrics": r.metrics,
                    "warnings": [dataclasses.asdict(w) for w in r.warnings],
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
