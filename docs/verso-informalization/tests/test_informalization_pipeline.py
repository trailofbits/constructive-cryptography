#!/usr/bin/env python3
"""
End-to-end positive and negative test suite for:
  - `scripts/check_informalization.py`
  - `docs/verso-informalization/scripts/render_verso_bundle.py`
  - `docs/verso-informalization` Lean package (`lake exe verso-informalize`, if built)
"""
from __future__ import annotations

import copy
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any, Dict


REPO_ROOT = Path(__file__).resolve().parents[3]
CHECK_SCRIPT = REPO_ROOT / "scripts" / "check_informalization.py"
BUNDLE_SCRIPT = REPO_ROOT / "docs" / "verso-informalization" / "scripts" / "render_verso_bundle.py"
VERSO_PKG_DIR = REPO_ROOT / "docs" / "verso-informalization"
CADMO_READER_JS = REPO_ROOT / "src" / "Informalization" / "Render" / "cadmo-reader.js"
CADMO_READER_CSS = REPO_ROOT / "src" / "Informalization" / "Render" / "cadmo-reader.css"


def find_js_runtime() -> list[str] | None:
    import shutil
    for cand in [
        shutil.which("node"),
        shutil.which("jsc"),
        "/System/Library/Frameworks/JavaScriptCore.framework/Versions/A/Helpers/jsc",
    ]:
        if cand and Path(cand).is_file():
            return [cand]
    return None


def make_clean_fixture() -> Dict[str, Any]:
    """Build a realistic canonical Explanation.Document JSON matching Lean 4.35 ToJson output."""
    return {
        "title": "Authenticated Encryption and Indifferentiable Sponge Composition",
        "subtitle": "Constructive Cryptography Checked Informalization Fixture",
        "defaultMode": "paper",
        "entries": [
            {
                "header": "Theorem",
                "title": "AE from IND-CCA and INT-PTXT",
                "declaration": "Examples.AuthenticatedEncryption.ae_of_ind_cca_int_ptxt",
                "ambient": {
                    "summary": [
                        {"text": {"value": "Let "}},
                        {"symbol": {"key": "sym.key", "display": "\\mathbf{K}", "isMath": True}},
                        {"text": {"value": " be a shared secret key resource with interfaces "}},
                        {"inlineMath": {"latex": "A"}},
                        {"text": {"value": " and "}},
                        {"inlineMath": {"latex": "B"}},
                        {"text": {"value": ", and let "}},
                        {"symbol": {"key": "sym.sec", "display": "\\mathbf{SEC}", "isMath": True}},
                        {"text": {"value": " denote the ideal secure channel."}},
                    ],
                    "suppressedTypeclasses": ["Fintype", "DecidableEq"],
                },
                "statement": [
                    [
                        {"text": {"value": "The protocol "}},
                        {"symbol": {"key": "sym.encdec", "display": "\\pi_{\\mathsf{AE}}", "isMath": True}},
                        {"text": {"value": " constructs the ideal secure channel "}},
                        {"symbol": {"key": "sym.sec", "display": "\\mathbf{SEC}", "isMath": True}},
                        {"text": {"value": " from "}},
                        {"symbol": {"key": "sym.key", "display": "\\mathbf{K}", "isMath": True}},
                        {"text": {"value": " and an authenticated channel within an "}},
                        {"inlineMath": {"latex": "\\varepsilon"}},
                        {"text": {"value": "-ball: "}},
                        {
                            "displayMath": {
                                "latex": "\\mathbf{K} \\parallel \\mathbf{AUTH} \\xrightarrow{\\pi_{\\mathsf{AE}};\\,\\varepsilon} \\mathbf{SEC}^*",
                                "punct": ".",
                            }
                        },
                    ]
                ],
                "diagramHtml": '<div class="ccw"><svg width="180" height="40"><rect x="4" y="4" width="172" height="32"/></svg></div>',
                "proof": [
                    {
                        "kind": "flowNote",
                        "id": "note-1",
                        "text": "We establish the construction via a two-hop hybrid chain separating integrity from confidentiality.",
                        "placement": "margin",
                    },
                    {
                        "kind": "step",
                        "id": "wrap-1",
                        "content": [
                            {"text": {"value": "Unfolding the specification wrapper forwards directly to the hybrid reduction."}}
                        ],
                        "children": [
                            {
                                "kind": "calcChain",
                                "id": "calc-1",
                                "intro": [
                                    {"text": {"value": "By the triangle inequality for distinguishing advantage, we obtain:"}}
                                ],
                                "steps": [
                                    {
                                        "step": {
                                            "lhsLatex": "\\pi_{\\mathsf{AE}}(\\mathbf{K} \\parallel \\mathbf{AUTH})",
                                            "relationLatex": "\\simeq_{\\varepsilon_1}",
                                            "rhsLatex": "\\mathbf{HYB}",
                                            "reason": [
                                                {"text": {"value": "plaintext integrity with an MBO game "}},
                                                {"symbol": {"key": "sym.game", "display": "G", "isMath": True}},
                                            ],
                                            "justification": [],
                                        },
                                        "children": [
                                            {
                                                "kind": "step",
                                                "id": "sub-1",
                                                "content": [
                                                    {"text": {"value": "Because "}},
                                                    {"symbol": {"key": "sym.game", "display": "G", "isMath": True}},
                                                    {"text": {"value": " and the ideal decryption experiment are conditionally equivalent, any adversary distinguishes them only by provoking the bad event."}},
                                                ],
                                                "children": [],
                                                "goal": {
                                                    "context": [
                                                        {
                                                            "name": "D",
                                                            "description": "a q-query distinguisher",
                                                            "isHypothesis": False,
                                                            "usedInGoal": True,
                                                        }
                                                    ],
                                                    "targetLatex": "\\Delta^D(\\pi_{\\mathsf{AE}} R, \\mathbf{HYB}) \\le \\varepsilon_1",
                                                    "targetProse": "The distinguishing advantage is bounded by ε₁.",
                                                },
                                                "originDecl": "Examples.AuthenticatedEncryption.hybrid_ideal_distance_le",
                                                "isWrapper": False,
                                                "defaultExpanded": False,
                                            }
                                        ],
                                    },
                                    {
                                        "step": {
                                            "lhsLatex": "\\mathbf{HYB}",
                                            "relationLatex": "\\simeq_{\\varepsilon_2}",
                                            "rhsLatex": "\\mathbf{SEC}\\sigma",
                                            "reason": [
                                                {"text": {"value": "attaching the simulator "}},
                                                {"inlineMath": {"latex": "\\sigma"}},
                                                {"text": {"value": " on the adversarial interface "}},
                                                {"citation": {"label": "MR16", "detail": "Maurer-Renner 2016 §4.2"}},
                                            ],
                                            "justification": [],
                                        },
                                        "children": [],
                                    },
                                ],
                                "originDecl": "Examples.AuthenticatedEncryption.ae_hybrid_chain",
                            }
                        ],
                        "isWrapper": True,
                        "defaultExpanded": False,
                    },
                    {
                        "kind": "routineReceipt",
                        "id": "routine-1",
                        "summary": "Routine non-negativity and additive bound arithmetic",
                        "stepCount": 3,
                        "details": [
                            {
                                "kind": "step",
                                "id": "routine-detail-1",
                                "content": [
                                    {"text": {"value": "Summing the two non-negative error bounds yields the total bound."}}
                                ],
                                "children": [],
                                "isWrapper": False,
                                "defaultExpanded": False,
                            }
                        ],
                    },
                    {
                        "kind": "figure",
                        "id": "fig-1",
                        "caption": [
                            {"text": {"value": "Parallel composition of "}},
                            {"symbol": {"key": "sym.key", "display": "\\mathbf{K}", "isMath": True}},
                            {"text": {"value": " and the authenticated channel under "}},
                            {"symbol": {"key": "sym.encdec", "display": "\\pi_{\\mathsf{AE}}", "isMath": True}},
                            {"text": {"value": "."}},
                        ],
                        "html": '<div class="ccw"><svg width="160" height="36"><rect x="2" y="2" width="156" height="32"/></svg></div>',
                    },
                ],
                "axioms": {
                    "axioms": ["propext", "Classical.choice", "Quot.sound"],
                    "hasSorry": False,
                },
            }
        ],
        "inspectors": [
            {
                "key": "sym.key",
                "display": "\\mathbf{K}",
                "kind": {
                    "interfaceTable": {
                        "ports": [
                            {"port": "A", "queryLatex": "\\mathsf{get}", "replyLatex": "\\{0,1\\}^\\kappa"},
                            {"port": "B", "queryLatex": "\\mathsf{get}", "replyLatex": "\\{0,1\\}^\\kappa"},
                        ],
                        "domainLatex": "\\{0,1\\}^\\kappa",
                        "budgetNote": "At most one key retrieval per honest interface.",
                    }
                },
                "leanName": "Examples.AuthenticatedEncryption.keyResource",
                "leanType": "TypedSystem KeyInterface",
            },
            {
                "key": "sym.sec",
                "display": "\\mathbf{SEC}",
                "kind": {
                    "mathDefinition": {
                        "equationLatex": "\\mathbf{SEC} = \\mathsf{IdealChannel}(M)",
                        "proseSummary": "Ideal confidential and authentic channel leaking only message lengths.",
                    }
                },
                "leanName": "Examples.AuthenticatedEncryption.secureChannel",
                "leanType": "TypedSystem SecInterface",
            },
            {
                "key": "sym.encdec",
                "display": "\\pi_{\\mathsf{AE}}",
                "kind": {
                    "dslPseudocode": {
                        "header": "Converter π_AE",
                        "body": "on send(m):\n  k <- getKey()\n  c <- Enc(k, m)\n  transmit(c)",
                        "fullSource": "converter pi_AE := ...",
                    }
                },
                "leanName": "Examples.AuthenticatedEncryption.aeProtocol",
                "leanType": "TypedConverter SecInterface (KeyInterface ⊗ AuthInterface)",
            },
            {
                "key": "sym.game",
                "display": "G",
                "kind": {
                    "witnessCard": {
                        "title": "Monotone Binary Output Game",
                        "rows": [
                            ["Bad event", "\\mathsf{forge}"],
                            ["Underlying system", "G^-"],
                        ],
                    }
                },
                "leanName": "Examples.AuthenticatedEncryption.intPtxtGame",
                "leanType": "Game DecInterface",
            },
        ],
    }


def run_check(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(CHECK_SCRIPT), *args],
        capture_output=True,
        text=True,
    )


class TestInformalizationCIAndVersoBundle(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.tmp_path = Path(self.tmp.name)

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def write_json(self, name: str, data: Any) -> Path:
        p = self.tmp_path / name
        p.write_text(json.dumps(data, indent=2, ensure_ascii=False), encoding="utf-8")
        return p

    def test_clean_fixture_passes_json_and_verso_bundle_html(self) -> None:
        fixture = make_clean_fixture()
        json_path = self.write_json("clean.json", fixture)
        prose_path = self.tmp_path / "chapter1.md"
        prose_path.write_text(
            "# Chapter Overview\n\n"
            "This chapter presents a constructive cryptography reduction in Maurer's style.\n\n"
            ":::cadmo-doc\n\n"
            "> Closing remark: every equation above is derived from checked Lean terms.\n",
            encoding="utf-8",
        )

        # 1. Clean JSON passes check_informalization.py
        res = run_check(str(json_path))
        self.assertEqual(res.returncode, 0, msg=res.stdout + res.stderr)
        self.assertIn("ALL GATES PASSED", res.stdout)

        # 2. render_verso_bundle.py builds multi-chapter site + Verso stubs
        out_dir = self.tmp_path / "site"
        bundle_res = subprocess.run(
            [
                sys.executable,
                str(BUNDLE_SCRIPT),
                "--title",
                "CC Monograph Fixture",
                "--doc",
                str(json_path),
                "--chapter",
                str(prose_path),
                "--out-dir",
                str(out_dir),
            ],
            capture_output=True,
            text=True,
        )
        self.assertEqual(bundle_res.returncode, 0, msg=bundle_res.stdout + bundle_res.stderr)
        self.assertTrue((out_dir / "index.html").is_file())
        chapter_htmls = list((out_dir / "chapters").glob("*.html"))
        self.assertEqual(len(chapter_htmls), 1)
        verso_stubs = list((out_dir / "verso").glob("*.lean"))
        self.assertGreaterEqual(len(verso_stubs), 2)

        # 3. Generated chapter HTML passes check_informalization.py (CSS + JS + embedded JSON)
        html_res = run_check(str(chapter_htmls[0]))
        self.assertEqual(html_res.returncode, 0, msg=html_res.stdout + html_res.stderr)
        self.assertIn("ALL GATES PASSED", html_res.stdout)

        # 4. Also verify JSON report format
        json_rep = run_check("--json-report", str(chapter_htmls[0]))
        self.assertEqual(json_rep.returncode, 0, msg=json_rep.stdout + json_rep.stderr)
        parsed = json.loads(json_rep.stdout)
        self.assertTrue(parsed["ok"])
        self.assertEqual(parsed["files"][0]["entries_checked"], 1)
        self.assertEqual(parsed["files"][0]["inspectors_checked"], 4)

    def test_negative_hyg_leakage(self) -> None:
        doc = make_clean_fixture()
        doc["entries"][0]["statement"][0].append({"text": {"value": " where x._hyg.42 holds."}})
        p = self.write_json("neg_hyg.json", doc)
        res = run_check(str(p))
        self.assertNotEqual(res.returncode, 0)
        self.assertIn("_hyg", res.stdout)
        self.assertIn("zero-leakage", res.stdout)

    def test_negative_at_interface_and_whiskering(self) -> None:
        doc = make_clean_fixture()
        doc["entries"][0]["proof"][0]["text"] = "We apply whiskering to the resource at interface A."
        p = self.write_json("neg_cc_vocab.json", doc)
        res = run_check(str(p))
        self.assertNotEqual(res.returncode, 0)
        self.assertIn("at interface", res.stdout)
        self.assertIn("whiskering", res.stdout)

    def test_negative_additional_leak_tokens(self) -> None:
        for bad_token in [
            "ENNReal.ofReal x",
            "NNReal.toReal y",
            "Coe.coe z",
            "OfNat.ofNat 0",
            "HSMul.hSMul a b",
            "AutoParam",
            "optParam",
            "fun x => x",
            "match x with",
            "admissibility closure",
            "visible system",
            "None (h : P)",
            "distinguishing distance",
            "transcript distance",
            "Standing conventions.",
        ]:
            with self.subTest(bad_token=bad_token):
                doc = make_clean_fixture()
                doc["entries"][0]["proof"][0]["text"] = f"Bad phrase: {bad_token}"
                p = self.write_json("neg_tok.json", doc)
                res = run_check(str(p))
                self.assertNotEqual(res.returncode, 0, msg=f"Should reject: {bad_token}")
                self.assertIn("zero-leakage", res.stdout)

    def test_negative_sorry_and_nonstandard_axioms(self) -> None:
        doc = make_clean_fixture()
        doc["entries"][0]["axioms"] = {"axioms": ["propext", "sorryAx"], "hasSorry": True}
        p = self.write_json("neg_sorry.json", doc)
        res = run_check(str(p))
        self.assertNotEqual(res.returncode, 0)
        self.assertIn("axiom-audit", res.stdout)
        self.assertIn("sorryAx", res.stdout)

        # Even with --allow-axioms, sorry must still fail
        res_allow = run_check("--allow-axioms", str(p))
        self.assertNotEqual(res_allow.returncode, 0)

        # Non-standard axiom fails by default, passes with --allow-axioms
        doc2 = make_clean_fixture()
        doc2["entries"][0]["axioms"] = {"axioms": ["propext", "MyCustomAxiom"], "hasSorry": False}
        p2 = self.write_json("neg_custom_ax.json", doc2)
        res2 = run_check(str(p2))
        self.assertNotEqual(res2.returncode, 0)
        self.assertIn("MyCustomAxiom", res2.stdout)
        res2_allow = run_check("--allow-axioms", str(p2))
        self.assertEqual(res2_allow.returncode, 0, msg=res2_allow.stdout)

    def test_negative_duplicate_siblings(self) -> None:
        doc = make_clean_fixture()
        dup_step = {
            "kind": "step",
            "id": "dup-1",
            "content": [{"text": {"value": "By symmetry of the transcript count, both terms agree."}}],
            "children": [],
            "isWrapper": False,
            "defaultExpanded": False,
        }
        dup_step_2 = copy.deepcopy(dup_step)
        dup_step_2["id"] = "dup-2"
        doc["entries"][0]["proof"].extend([dup_step, dup_step_2])
        p = self.write_json("neg_dup.json", doc)
        res = run_check(str(p))
        self.assertNotEqual(res.returncode, 0)
        self.assertIn("sibling-dedup", res.stdout)

    def test_negative_empty_statement_and_broken_symbol_key(self) -> None:
        doc = make_clean_fixture()
        doc["entries"][0]["statement"].append([])
        doc["entries"][0]["statement"][0].append(
            {"symbol": {"key": "sym.nonexistent", "display": "X", "isMath": True}}
        )
        p = self.write_json("neg_struct.json", doc)
        res = run_check(str(p))
        self.assertNotEqual(res.returncode, 0)
        self.assertIn("Empty statement paragraph", res.stdout)
        self.assertIn("sym.nonexistent", res.stdout)

    def test_negative_typography_articles_and_double_space(self) -> None:
        cases = [
            "Within a ε-ball, security holds.",
            "Consider a MBO attached to the game.",
            "Sample an URF uniformly at random.",
            "Any a adversary wins with small probability.",
            "Querying a oracle yields a response.",
            "This sentence has  two spaces.",
            "A resource with interface(s) A.",
        ]
        for sentence in cases:
            with self.subTest(sentence=sentence):
                doc = make_clean_fixture()
                doc["entries"][0]["proof"][0]["text"] = sentence
                p = self.write_json("neg_typo.json", doc)
                res = run_check(str(p))
                self.assertNotEqual(res.returncode, 0, msg=f"Should reject: {sentence}")
                self.assertIn("typography", res.stdout)

        # Also test split-inline article error: text("within a ") + inlineMath("\\varepsilon")
        doc_split = make_clean_fixture()
        doc_split["entries"][0]["statement"] = [
            [
                {"text": {"value": "Security holds within a "}},
                {"inlineMath": {"latex": "\\varepsilon"}},
                {"text": {"value": "-ball."}},
            ]
        ]
        p_split = self.write_json("neg_split_article.json", doc_split)
        res_split = run_check(str(p_split))
        self.assertNotEqual(res_split.returncode, 0)
        self.assertIn("typography", res_split.stdout)

    def test_negative_malformed_json_and_broken_html(self) -> None:
        bad_json = self.tmp_path / "broken.json"
        bad_json.write_text('{"title": "Unclosed', encoding="utf-8")
        res = run_check(str(bad_json))
        self.assertNotEqual(res.returncode, 0)
        self.assertIn("Malformed JSON", res.stdout)

        bad_html = self.tmp_path / "broken.html"
        bad_html.write_text("<!doctype html><html><body>Missing assets</body></html>", encoding="utf-8")
        res_html = run_check(str(bad_html))
        self.assertNotEqual(res_html.returncode, 0)
        self.assertIn("data-cadmo-reader", res_html.stdout)
        self.assertIn("data-cadmo-controller", res_html.stdout)
        self.assertIn("cadmo-document-data", res_html.stdout)

    def test_playwright_flag_graceful_skip_when_missing(self) -> None:
        fixture = make_clean_fixture()
        json_path = self.write_json("pw_clean.json", fixture)
        out_dir = self.tmp_path / "pw_site"
        subprocess.run(
            [sys.executable, str(BUNDLE_SCRIPT), "--doc", str(json_path), "--out-dir", str(out_dir)],
            check=True,
            capture_output=True,
            text=True,
        )
        chapter_html = next((out_dir / "chapters").glob("*.html"))
        res = run_check("--playwright", "--playwright-skip-if-missing", str(chapter_html))
        self.assertEqual(res.returncode, 0, msg=res.stdout + res.stderr)

    def test_lean_verso_informalize_cli_if_built(self) -> None:
        exe = VERSO_PKG_DIR / ".lake" / "build" / "bin" / "verso-informalize"
        if not exe.is_file():
            self.skipTest("verso-informalize Lean binary not yet built")
        fixture = make_clean_fixture()
        json_path = self.write_json("lean_cli.json", fixture)

        res_inspect = subprocess.run([str(exe), "inspect", str(json_path)], capture_output=True, text=True)
        self.assertEqual(res_inspect.returncode, 0, msg=res_inspect.stdout + res_inspect.stderr)
        self.assertIn("Entries: 1", res_inspect.stdout)
        self.assertIn("Inspectors: 4", res_inspect.stdout)

        body_out = self.tmp_path / "body.html"
        res_body = subprocess.run(
            [str(exe), "render-body", str(json_path), str(body_out)], capture_output=True, text=True
        )
        self.assertEqual(res_body.returncode, 0, msg=res_body.stdout + res_body.stderr)
        body_html = body_out.read_text(encoding="utf-8")
        self.assertIn("cadmo-entry", body_html)
        self.assertIn("cadmo-calc-table", body_html)
        self.assertIn("⊕", body_html)

        stub_out = self.tmp_path / "ChapterStub.lean"
        res_stub = subprocess.run(
            [str(exe), "verso-stub", str(json_path), str(stub_out), "FixtureChapter"],
            capture_output=True,
            text=True,
        )
        self.assertEqual(res_stub.returncode, 0, msg=res_stub.stdout + res_stub.stderr)
        stub_txt = stub_out.read_text(encoding="utf-8")
        self.assertIn("namespace VersoChapters.FixtureChapter", stub_txt)
        self.assertIn("ae_of_ind_cca_int_ptxt", stub_txt)

    def test_section_context_and_hover_metadata(self) -> None:
        fixture = make_clean_fixture()
        fixture["inspectors"].append(
            {
                "key": "sym.pred",
                "display": "\\mathrm{supportedSponge}",
                "kind": {
                    "mathDefinition": {
                        "equationLatex": "\\mathrm{supportedSponge}(p) \\iff r > 0 \\wedge c > 0",
                        "proseSummary": "Predicate on sponge parameter tuples.",
                    }
                },
                "leanName": "supportedSponge",
                "leanType": "SpongeParams -> Prop",
                "roleBadge": "predicate",
                "clauses": ["r > 0", "c > 0"],
                "docString": "Valid parameter condition for SHA-3 sponges.",
            }
        )
        entry = fixture["entries"][0]
        entry["sectionTitle"] = "Sponge Parameters"
        entry["sectionId"] = "sec-1"
        entry["sectionContext"] = {
            "sectionId": "sec-1",
            "sectionNumber": 1,
            "paragraphs": [
                [
                    {"text": {"value": "Throughout this section, let "}},
                    {"inlineMath": {"latex": "p"}},
                    {"text": {"value": " be a sponge parameter tuple and assume that "}},
                    {"inlineMath": {"latex": "\\mathrm{supportedSponge}(p)"}},
                    {"text": {"value": "."}},
                ]
            ],
            "inspectors": [
                {
                    "key": "secparam:sec-1:p",
                    "display": "p",
                    "kind": {"parameter": {"roleDescription": "A sponge parameter tuple."}},
                    "leanType": "SpongeParams",
                    "roleBadge": "fixed in §1",
                    "sectionId": "sec-1",
                    "sectionAssumptions": [
                        [
                            {"inlineMath": {"latex": "\\mathrm{supportedSponge}(p)"}},
                            {"text": {"value": " via "}},
                            {"symbol": {"key": "sym.pred", "display": "\\mathrm{supportedSponge}", "isMath": True}},
                        ]
                    ],
                }
            ],
        }
        entry["localInspectors"] = [
            {
                "key": "shorthand:Decl:R",
                "display": "R",
                "kind": {
                    "localShorthand": {
                        "equationLatex": "R = R_{\\mathrm{MAC}}(4 \\cdot m, c_2, 0)",
                        "roleDescription": "Local MAC system shorthand.",
                    }
                },
                "leanType": "TypedSystem ...",
                "roleBadge": "local shorthand",
            }
        ]
        entry["referencedKeys"] = ["secparam:sec-1:p", "shorthand:Decl:R", "sym.pred"]

        json_path = self.write_json("section_hover_clean.json", fixture)
        res = run_check(str(json_path))
        self.assertEqual(res.returncode, 0, msg=res.stdout + res.stderr)

        out_dir = self.tmp_path / "section_hover_site"
        subprocess.run(
            [sys.executable, str(BUNDLE_SCRIPT), "--doc", str(json_path), "--out-dir", str(out_dir)],
            check=True,
            capture_output=True,
            text=True,
        )
        chapter_html = next((out_dir / "chapters").glob("*.html"))
        res_html = run_check(str(chapter_html))
        self.assertEqual(res_html.returncode, 0, msg=res_html.stdout + res_html.stderr)
        html_txt = chapter_html.read_text(encoding="utf-8")
        self.assertIn("Throughout this section, let", html_txt)
        self.assertIn("cadmo-section-context", html_txt)
        self.assertIn("annotateMathReferences", html_txt)
        self.assertIn("cadmo-popover", html_txt)
        self.assertIn("localShorthand", html_txt)

        # Negative test: forbidden leakage in section context / hover docstring must fail CI
        bad = copy.deepcopy(fixture)
        bad["entries"][0]["localInspectors"][0]["docString"] = "Attached at interface A."
        bad_path = self.write_json("section_hover_leak.json", bad)
        res_bad = run_check(str(bad_path))
        self.assertNotEqual(res_bad.returncode, 0)
        self.assertIn("leakage", res_bad.stdout)

        # Verso Lean CLI round-trip with new schema fields if built
        exe = VERSO_PKG_DIR / ".lake" / "build" / "bin" / "verso-informalize"
        if exe.is_file():
            res_cli = subprocess.run([str(exe), "inspect", str(json_path)], capture_output=True, text=True)
            self.assertEqual(res_cli.returncode, 0, msg=res_cli.stdout + res_cli.stderr)
            body_out = self.tmp_path / "section_body.html"
            res_body = subprocess.run(
                [str(exe), "render-body", str(json_path), str(body_out)],
                capture_output=True,
                text=True,
            )
            self.assertEqual(res_body.returncode, 0, msg=res_body.stdout + res_body.stderr)
            self.assertIn("cadmo-section-context", body_out.read_text(encoding="utf-8"))

    def test_two_tier_ci_legacy_vs_authored(self) -> None:
        # Clean fixture must pass both legacy and authored tiers
        clean = make_clean_fixture()
        clean["entries"][0]["proof"].append(
            {
                "kind": "step",
                "id": "claim-step",
                "startsParagraph": True,
                "leadHeading": "Claim 1.",
                "trust": "kernelProvedClaim",
                "content": [
                    {
                        "text": {"value": "For every distinguisher, the advantage stays bounded."},
                        "trust": "kernelFormula",
                    },
                    {
                        "text": {"value": "Intuitively, both hybrids behave identically."},
                        "trust": "intuitionGloss",
                    },
                    {
                        "symbol": {
                            "key": "sym.key",
                            "display": "\\mathbf{K}",
                            "isMath": True,
                        },
                        "dataKey": "sym.key",
                        "trust": "typedRef",
                    },
                ],
                "children": [],
                "isWrapper": False,
                "defaultExpanded": False,
            }
        )
        clean_path = self.write_json("clean_authored.json", clean)
        self.assertEqual(run_check("--tier", "legacy", str(clean_path)).returncode, 0)
        res_auth = run_check("--tier", "authored", str(clean_path))
        self.assertEqual(res_auth.returncode, 0, msg=res_auth.stdout + res_auth.stderr)

        # Authentic mathematical prose like "uniformly random element of \mathcal{K}" must PASS authored tier
        clean_math_prose = make_clean_fixture()
        clean_math_prose["entries"][0]["proof"][0]["text"] = (
            "Sample a uniformly random element of $\\mathcal{K}$ and every element of $R$."
        )
        clean_math_path = self.write_json("clean_math_prose.json", clean_math_prose)
        res_math_prose = run_check("--tier", "authored", str(clean_math_path))
        self.assertEqual(res_math_prose.returncode, 0, msg=res_math_prose.stdout + res_math_prose.stderr)

        # Authored-only leakage tokens pass legacy tier but fail authored tier
        authored_only_tokens = [
            "_vcc_p0",
            "Exists(B => True)",
            "\\mathrm{Exists}\\!\\left(B \\mapsto P\\right)",
            "sum(univ, j => p j)",
            "\\mathrm{sum}\\!\\left(\\mathrm{univ}, k \\mapsto f(k)\\right)",
            "Sigma(x => T)",
            "Subtype(x => P)",
            "h.map Prod.fst",
            "h.map Prod.snd",
            "BitString(L)",
            "Unit \\to A",
            "Unit → A",
            "certificate_proof_1",
            "self.X",
            "an element of \\(\\mathrm{PRGAdversary}(R)\\)",
            "an element of ProbDist(R)",
            "Defined as an element of \\(R\\).",
        ]
        for tok in authored_only_tokens:
            with self.subTest(authored_token=tok):
                doc = make_clean_fixture()
                doc["entries"][0]["proof"][0]["text"] = f"Sample expression: {tok}"
                p = self.write_json("tier_tok.json", doc)
                res_leg = run_check("--tier", "legacy", str(p))
                self.assertEqual(res_leg.returncode, 0, msg=f"legacy should allow {tok}: {res_leg.stdout}")
                res_strict = run_check("--tier", "authored", str(p))
                self.assertNotEqual(res_strict.returncode, 0, msg=f"authored must reject {tok}")
                self.assertIn("zero-leakage", res_strict.stdout)

        # Lowercase headers pass legacy tier but fail authored tier
        for lc_header in ["theorem", "lemma", "proposition", "corollary"]:
            with self.subTest(header=lc_header):
                doc = make_clean_fixture()
                doc["entries"][0]["header"] = lc_header
                p = self.write_json("tier_hdr.json", doc)
                self.assertEqual(run_check("--tier", "legacy", str(p)).returncode, 0)
                res_strict = run_check("--tier", "authored", str(p))
                self.assertNotEqual(res_strict.returncode, 0)
                self.assertIn("Lowercase theorem header", res_strict.stdout)

    def test_reject_embedded_style_in_diagram_html_and_unproved_sorry_both_tiers(self) -> None:
        for tier in ("legacy", "authored"):
            # 1. Embedded <style> inside entry.diagramHtml
            doc_entry_style = make_clean_fixture()
            doc_entry_style["entries"][0]["diagramHtml"] = "<style>.ccw{color:red}</style><div class='ccw'></div>"
            p1 = self.write_json(f"style_entry_{tier}.json", doc_entry_style)
            res1 = run_check("--tier", tier, str(p1))
            self.assertNotEqual(res1.returncode, 0, msg=f"{tier} must reject <style> in entry.diagramHtml")
            self.assertIn("diagram-style", res1.stdout)

            # 2. Embedded <style> inside ProofNode.diagramHtml & CalcStep.diagramHtml
            doc_node_style = make_clean_fixture()
            doc_node_style["entries"][0]["proof"][1]["children"][0]["steps"][0]["step"]["diagramHtml"] = (
                "<STYLE>.x{}</STYLE><div>ok</div>"
            )
            p2 = self.write_json(f"style_step_{tier}.json", doc_node_style)
            res2 = run_check("--tier", tier, str(p2))
            self.assertNotEqual(res2.returncode, 0, msg=f"{tier} must reject <style> in step.diagramHtml")
            self.assertIn("diagram-style", res2.stdout)

            # 3. [UNPROVED: sorry] must fail on BOTH tiers
            doc_sorry = make_clean_fixture()
            doc_sorry["entries"][0]["proof"][0]["text"] = "Subgoal [UNPROVED: sorry] remains open."
            p3 = self.write_json(f"unproved_sorry_{tier}.json", doc_sorry)
            res3 = run_check("--tier", tier, str(p3))
            self.assertNotEqual(res3.returncode, 0, msg=f"{tier} must reject [UNPROVED: sorry]")
            self.assertIn("[UNPROVED: sorry]", res3.stdout)

    def test_font_sensitive_hover_and_dom_noise_suppression_js(self) -> None:
        js_cmd = find_js_runtime()
        if not js_cmd:
            self.skipTest("No JS runtime (node or jsc) available")

        harness = r"""
        const jsSrc = __JS_SRC__;
        // Minimal pure-JS DOM stub to test cadmo-reader.js helpers end-to-end
        class FakeClassList {
          constructor(el) { this.el = el; this._set = new Set(); }
          _syncFromString(str) {
            this._set = new Set(String(str || '').trim().split(/\s+/).filter(Boolean));
          }
          _syncToString() {
            this.el._className = Array.from(this._set).join(' ');
          }
          add(...cls) { cls.forEach(c => this._set.add(c)); this._syncToString(); }
          remove(...cls) { cls.forEach(c => this._set.delete(c)); this._syncToString(); }
          contains(c) { return this._set.has(c); }
        }
        class FakeNode {
          constructor(nodeType, tagName = '') {
            this.nodeType = nodeType;
            this.tagName = tagName.toUpperCase();
            this.childNodes = [];
            this.parentNode = null;
            this.attrs = {};
            this.dataset = {};
            this.style = {};
            this._className = '';
            this.classList = new FakeClassList(this);
            this._text = '';
            this.isConnected = true;
          }
          get className() { return this._className; }
          set className(v) { this._className = String(v || ''); this.classList._syncFromString(this._className); }
          get children() { return this.childNodes.filter(n => n.nodeType === 1); }
          get textContent() {
            if (this.nodeType === 3) return this._text;
            return this.childNodes.map(c => c.textContent).join('');
          }
          set textContent(v) {
            if (this.nodeType === 3) { this._text = String(v || ''); return; }
            this.childNodes = [];
            if (v !== '' && v !== null && v !== undefined) {
              this.appendChild(document.createTextNode(String(v)));
            }
          }
          appendChild(child) {
            if (!child) return child;
            if (child.nodeType === 11) {
              for (const k of [...child.childNodes]) this.appendChild(k);
              return child;
            }
            if (child.parentNode) child.parentNode.removeChild(child);
            child.parentNode = this;
            this.childNodes.push(child);
            return child;
          }
          removeChild(child) {
            const idx = this.childNodes.indexOf(child);
            if (idx >= 0) { this.childNodes.splice(idx, 1); child.parentNode = null; }
            return child;
          }
          insertBefore(newNode, refNode) {
            if (!refNode) return this.appendChild(newNode);
            if (newNode.parentNode) newNode.parentNode.removeChild(newNode);
            const idx = this.childNodes.indexOf(refNode);
            newNode.parentNode = this;
            if (idx >= 0) this.childNodes.splice(idx, 0, newNode);
            else this.childNodes.push(newNode);
            return newNode;
          }
          setAttribute(k, v) {
            this.attrs[k] = String(v);
            if (k === 'class') this.className = v;
            if (k.startsWith('data-')) {
              const camel = k.slice(5).replace(/-([a-z])/g, (_, ch) => ch.toUpperCase());
              this.dataset[camel] = String(v);
            }
          }
          getAttribute(k) { return Object.prototype.hasOwnProperty.call(this.attrs, k) ? this.attrs[k] : null; }
          hasAttribute(k) { return Object.prototype.hasOwnProperty.call(this.attrs, k); }
          addEventListener(ev, fn) {
            this._listeners = this._listeners || {};
            (this._listeners[ev] = this._listeners[ev] || []).push(fn);
          }
          dispatchClick() {
            for (const fn of (this._listeners && this._listeners.click) || []) fn({ stopPropagation() {} });
          }
          matchesSelectorOne(sel) {
            sel = sel.trim();
            if (!sel) return false;
            if (sel.startsWith('[')) {
              const attr = sel.slice(1, -1);
              return this.hasAttribute(attr);
            }
            if (sel.startsWith('.')) return this.classList.contains(sel.slice(1));
            return this.tagName === sel.toUpperCase();
          }
          closest(selectorList) {
            const parts = selectorList.split(',').map(s => s.trim());
            let cur = this;
            while (cur && cur.nodeType === 1) {
              if (parts.some(p => cur.matchesSelectorOne(p))) return cur;
              cur = cur.parentNode;
            }
            return null;
          }
          querySelectorAll(selectorList) {
            const parts = selectorList.split(',').map(s => s.trim());
            const out = [];
            const walk = (node) => {
              for (const ch of node.children) {
                if (parts.some(p => ch.matchesSelectorOne(p))) out.push(ch);
                walk(ch);
              }
            };
            walk(this);
            return out;
          }
          querySelector(selectorList) { return this.querySelectorAll(selectorList)[0] || null; }
        }
        globalThis.document = {
          getElementById: () => null,
          createElement: (tag) => new FakeNode(1, tag),
          createTextNode: (txt) => { const n = new FakeNode(3); n._text = String(txt || ''); return n; },
          createDocumentFragment: () => new FakeNode(11),
          addEventListener: () => {}
        };
        globalThis.window = globalThis;
        eval(jsSrc);
        const H = globalThis.__cadmoHelpers;
        function assert(cond, msg) { if (!cond) throw new Error('ASSERT FAILED: ' + msg); }

        // 1. Font-sensitive normalization checks
        assert(H.normalizeMathToken('\\mathcal{E}') === 'cal:E', 'cal:E');
        assert(H.normalizeMathToken('E') === 'E', 'plain E');
        assert(H.normalizeMathToken('\\mathbf{G}') === 'bf:G', 'bf:G');
        assert(H.normalizeMathToken('G') === 'G', 'plain G');
        assert(H.normalizeMathToken('\\mathcal{B}') === 'cal:B', 'cal:B');
        assert(H.normalizeMathToken('B') === 'B', 'plain B');
        assert(H.normalizeMathToken('\\mathbf{F}') === 'bf:F', 'bf:F');
        assert(H.normalizeMathToken('F') === 'F', 'plain F');
        assert(H.normalizeMathToken('\\mathsf{AE}') === 'sf:AE', 'sf:AE');
        assert(H.normalizeMathToken('\\mathbb{G}') === 'bb:G', 'bb:G');
        assert(H.normalizeMathToken('\\mathbb{R}') === 'bb:R', 'bb:R latex');
        assert(H.normalizeMathToken('ℝ') === 'bb:R', 'bb:R unicode');
        assert(H.isNonHoverableToken('0') === true, 'digit 0 blocked');
        assert(H.isNonHoverableToken('1') === true, 'digit 1 blocked');
        assert(H.isNonHoverableToken('bf:0') === true, 'bf:0 blocked');
        assert(H.stripEmbeddedStyles('<style>.a{}</style><div class="ccw">hi</div>') === '<div class="ccw">hi</div>', 'stripEmbeddedStyles');

        // 2. Offline DOM annotation: {0,1}^L, R^n, and font disambiguation
        const inspectors = [
          { key: 'sym.calE', display: '\\mathcal{E}' },
          { key: 'sym.E', display: 'E' },
          { key: 'sym.bfG', display: '\\mathbf{G}' },
          { key: 'sym.G', display: 'G' },
          { key: 'sym.bbR', display: '\\mathbb{R}' },
          { key: 'sym.L', display: 'L' },
          { key: 'sym.R', display: 'R' },
          { key: 'sym.n', display: 'n' }
        ];
        const scope = H.buildTokenScope(inspectors, [], [], null, [], false);

        const m1 = document.createElement('span');
        m1.className = 'cadmo-math';
        m1.appendChild(H.renderMathNodes('\\{0, 1\\}^L'));
        H.annotateOfflineMathContainer(m1, scope);
        assert(m1.querySelectorAll('.cadmo-ref').length === 0, '{0,1}^L must have 0 .cadmo-ref');

        const m2 = document.createElement('span');
        m2.className = 'cadmo-math';
        m2.appendChild(H.renderMathNodes('R^n'));
        H.annotateOfflineMathContainer(m2, scope);
        const supRefs = m2.querySelectorAll('sup .cadmo-ref');
        assert(supRefs.length === 0, 'R^n sup must have 0 .cadmo-ref');
        const allM2Refs = m2.querySelectorAll('.cadmo-ref');
        assert(allM2Refs.length === 1 && allM2Refs[0].dataset.cadmoToken === 'R', 'R^n annotates only base R');

        const m3 = document.createElement('span');
        m3.className = 'cadmo-math';
        m3.appendChild(H.renderMathNodes('\\mathcal{E} + E + \\mathbf{G} + G'));
        H.annotateOfflineMathContainer(m3, scope);
        const refs3 = m3.querySelectorAll('.cadmo-ref');
        assert(refs3.length === 4, 'expected 4 font-disambiguated refs, got ' + refs3.length);
        assert(refs3[0].dataset.cadmoToken === 'cal:E', 'first must be cal:E');
        assert(refs3[1].dataset.cadmoToken === 'E', 'second must be E');
        assert(refs3[2].dataset.cadmoToken === 'bf:G', 'third must be bf:G');
        assert(refs3[3].dataset.cadmoToken === 'G', 'fourth must be G');

        // 3. Mock KaTeX DOM annotation: block .msupsub/.mopen/.mclose/.mpunct/.op-limits + preserve .mathcal/.mathbf
        const kRoot = document.createElement('span');
        kRoot.className = 'katex-html';
        const base = document.createElement('span');
        base.className = 'base';
        const mopen = document.createElement('span'); mopen.className = 'mopen'; mopen.textContent = '{';
        const d0 = document.createElement('span'); d0.className = 'mord'; d0.textContent = '0';
        const comma = document.createElement('span'); comma.className = 'mpunct'; comma.textContent = ',';
        const mclose = document.createElement('span'); mclose.className = 'mclose';
        const brace = document.createElement('span'); brace.className = 'mclose'; brace.textContent = '}';
        const msup = document.createElement('span'); msup.className = 'msupsub';
        const supL = document.createElement('span'); supL.className = 'mord mathnormal'; supL.textContent = 'L';
        msup.appendChild(supL);
        mclose.appendChild(brace);
        mclose.appendChild(msup);
        const calE = document.createElement('span'); calE.className = 'mord mathcal'; calE.textContent = 'E';
        const plainE = document.createElement('span'); plainE.className = 'mord mathnormal'; plainE.textContent = 'E';
        const bfG = document.createElement('span'); bfG.className = 'mord mathbf'; bfG.textContent = 'G';
        const plainG = document.createElement('span'); plainG.className = 'mord mathnormal'; plainG.textContent = 'G';
        const bbR = document.createElement('span'); bbR.className = 'mord mathbb'; bbR.textContent = 'R';
        [mopen, d0, comma, mclose, calE, plainE, bfG, plainG, bbR].forEach(x => base.appendChild(x));
        kRoot.appendChild(base);
        H.annotateKatexMath(kRoot, scope);
        assert(kRoot.querySelectorAll('.msupsub .cadmo-ref').length === 0, 'KaTeX .msupsub has 0 .cadmo-ref');
        assert(kRoot.querySelectorAll('.mclose .cadmo-ref').length === 0, 'KaTeX .mclose has 0 .cadmo-ref');
        const kRefs = kRoot.querySelectorAll('.cadmo-ref');
        assert(kRefs.length === 5, 'KaTeX expected 5 refs, got ' + kRefs.length);
        assert(kRefs[0].dataset.cadmoToken === 'cal:E', 'KaTeX cal:E');
        assert(kRefs[1].dataset.cadmoToken === 'E', 'KaTeX E');
        assert(kRefs[2].dataset.cadmoToken === 'bf:G', 'KaTeX bf:G');
        assert(kRefs[3].dataset.cadmoToken === 'G', 'KaTeX G');
        assert(kRefs[4].dataset.cadmoToken === 'bb:R', 'KaTeX bb:R');

        // 4. ProofFlow: startsParagraph, leadHeading, and ProseTrust
        const flowOut = H.renderProofFlow([
          {
            kind: 'step',
            id: 's1',
            startsParagraph: true,
            leadHeading: 'Claim 1.',
            trust: 'intuitionGloss',
            content: [{ text: { value: 'First step.' } }],
            children: []
          },
          {
            kind: 'step',
            id: 's2',
            startsParagraph: true,
            leadHeading: 'Game 1.',
            trust: 'kernelProvedClaim',
            content: [{ text: { value: 'Second step.' } }],
            children: []
          }
        ], { depth: 0, scope: null });
        assert(flowOut.length === 2, 'startsParagraph must split into 2 paragraphs');
        assert(flowOut[0].querySelectorAll('.cadmo-para-heading').length === 1, 'leadHeading rendered');
        assert(flowOut[0].querySelectorAll('.cadmo-trust-gloss').length === 1, 'intuitionGloss class rendered');
        const outerSymEl = H.renderInline({
          symbol: { key: 'sym.calE', display: '\\mathcal{E}', isMath: true },
          dataKey: 'sym.calE',
          trust: 'typedRef'
        }, scope);
        assert(outerSymEl.getAttribute('data-cadmo-key') === 'sym.calE', 'outer dataKey on symbol');
        assert(outerSymEl.getAttribute('data-trust') === 'typedRef', 'outer trust on symbol');
        print('JS_TESTS_OK');
        """
        js_src = CADMO_READER_JS.read_text(encoding="utf-8")
        full_js = harness.replace("__JS_SRC__", json.dumps(js_src))
        # Node uses console.log, jsc uses print; define print fallback if needed
        full_js = "if (typeof print === 'undefined') { globalThis.print = console.log; }\n" + full_js
        script_path = self.tmp_path / "test_cadmo_js.js"
        script_path.write_text(full_js, encoding="utf-8")
        res = subprocess.run([*js_cmd, str(script_path)], capture_output=True, text=True)
        self.assertEqual(res.returncode, 0, msg=res.stdout + res.stderr)
        self.assertIn("JS_TESTS_OK", res.stdout)

        # Verify CSS fallback rules exist
        css_txt = CADMO_READER_CSS.read_text(encoding="utf-8")
        self.assertIn("sup .cadmo-ref", css_txt)
        self.assertIn(".msupsub .cadmo-ref", css_txt)
        self.assertIn(".cadmo-trust-gloss", css_txt)

    def test_wave_a_diagrams_witness_sections_font_fallback_and_typography_js(self) -> None:
        js_cmd = find_js_runtime()
        if not js_cmd:
            self.skipTest("No JS runtime (node or jsc) available")

        harness = r"""
        const jsSrc = __JS_SRC__;
        class FakeClassList {
          constructor(el) { this.el = el; this._set = new Set(); }
          _syncFromString(str) {
            this._set = new Set(String(str || '').trim().split(/\s+/).filter(Boolean));
          }
          _syncToString() {
            this.el._className = Array.from(this._set).join(' ');
          }
          add(...cls) { cls.forEach(c => this._set.add(c)); this._syncToString(); }
          remove(...cls) { cls.forEach(c => this._set.delete(c)); this._syncToString(); }
          contains(c) { return this._set.has(c); }
        }
        class FakeNode {
          constructor(nodeType, tagName = '') {
            this.nodeType = nodeType;
            this.tagName = tagName.toUpperCase();
            this.childNodes = [];
            this.parentNode = null;
            this.attrs = {};
            this.dataset = {};
            this.style = {};
            this._className = '';
            this._innerHTML = null;
            this.classList = new FakeClassList(this);
            this._text = '';
            this.isConnected = true;
          }
          get className() { return this._className; }
          set className(v) { this._className = String(v || ''); this.classList._syncFromString(this._className); }
          get children() { return this.childNodes.filter(n => n.nodeType === 1); }
          get innerHTML() {
            if (this._innerHTML !== null && this.childNodes.length === 0) return this._innerHTML;
            return this.childNodes.map(c => c.toHTML()).join('');
          }
          set innerHTML(v) {
            this.childNodes = [];
            this._innerHTML = String(v || '');
          }
          get textContent() {
            if (this.nodeType === 3) return this._text;
            return this.childNodes.map(c => c.textContent).join('');
          }
          set textContent(v) {
            if (this.nodeType === 3) { this._text = String(v || ''); return; }
            this.childNodes = [];
            this._innerHTML = null;
            if (v !== '' && v !== null && v !== undefined) {
              this.appendChild(document.createTextNode(String(v)));
            }
          }
          appendChild(child) {
            if (!child) return child;
            if (child.nodeType === 11) {
              for (const k of [...child.childNodes]) this.appendChild(k);
              return child;
            }
            if (child.parentNode) child.parentNode.removeChild(child);
            child.parentNode = this;
            this.childNodes.push(child);
            return child;
          }
          removeChild(child) {
            const idx = this.childNodes.indexOf(child);
            if (idx >= 0) { this.childNodes.splice(idx, 1); child.parentNode = null; }
            return child;
          }
          insertBefore(newNode, refNode) {
            if (!refNode) return this.appendChild(newNode);
            if (newNode.parentNode) newNode.parentNode.removeChild(newNode);
            const idx = this.childNodes.indexOf(refNode);
            newNode.parentNode = this;
            if (idx >= 0) this.childNodes.splice(idx, 0, newNode);
            else this.childNodes.push(newNode);
            return newNode;
          }
          setAttribute(k, v) {
            this.attrs[k] = String(v);
            if (k === 'class') this.className = v;
            if (k.startsWith('data-')) {
              const camel = k.slice(5).replace(/-([a-z])/g, (_, ch) => ch.toUpperCase());
              this.dataset[camel] = String(v);
            }
          }
          getAttribute(k) { return Object.prototype.hasOwnProperty.call(this.attrs, k) ? this.attrs[k] : null; }
          hasAttribute(k) { return Object.prototype.hasOwnProperty.call(this.attrs, k); }
          addEventListener(ev, fn) {
            this._listeners = this._listeners || {};
            (this._listeners[ev] = this._listeners[ev] || []).push(fn);
          }
          dispatchClick() {
            for (const fn of (this._listeners && this._listeners.click) || []) fn({ stopPropagation() {} });
          }
          matchesSelectorOne(sel) {
            sel = sel.trim();
            if (!sel) return false;
            const tokens = sel.match(/(?:^[A-Za-z0-9_-]+|\.[A-Za-z0-9_-]+|\[[^\]]+\])/g);
            if (!tokens || tokens.join('') !== sel) return false;
            return tokens.every(tok => {
              if (tok.startsWith('[')) return this.hasAttribute(tok.slice(1, -1));
              if (tok.startsWith('.')) return this.classList.contains(tok.slice(1));
              return this.tagName === tok.toUpperCase();
            });
          }
          closest(selectorList) {
            const parts = selectorList.split(',').map(s => s.trim());
            let cur = this;
            while (cur && cur.nodeType === 1) {
              if (parts.some(p => cur.matchesSelectorOne(p))) return cur;
              cur = cur.parentNode;
            }
            return null;
          }
          querySelectorAll(selectorList) {
            const parts = selectorList.split(',').map(s => s.trim());
            const out = [];
            const walk = (node) => {
              for (const ch of node.children) {
                if (parts.some(p => ch.matchesSelectorOne(p))) out.push(ch);
                walk(ch);
              }
            };
            walk(this);
            return out;
          }
          querySelector(selectorList) { return this.querySelectorAll(selectorList)[0] || null; }
          toHTML() {
            if (this.nodeType === 3) return this._text;
            const cls = this._className ? ` class="${this._className}"` : '';
            const attrs = Object.entries(this.attrs).filter(([k]) => k !== 'class').map(([k, v]) => ` ${k}="${v}"`).join('');
            return `<${this.tagName.toLowerCase()}${cls}${attrs}>${this.innerHTML}</${this.tagName.toLowerCase()}>`;
          }
        }
        const rootEl = new FakeNode(1, 'div');
        const dataEl = new FakeNode(1, 'script');
        const bodyEl = new FakeNode(1, 'body');
        const docEl = new FakeNode(1, 'html');
        globalThis.document = {
          documentElement: docEl,
          body: bodyEl,
          getElementById: (id) => id === 'cadmo-root' ? rootEl : (id === 'cadmo-document-data' ? dataEl : null),
          createElement: (tag) => new FakeNode(1, tag),
          createTextNode: (txt) => { const n = new FakeNode(3); n._text = String(txt || ''); return n; },
          createDocumentFragment: () => new FakeNode(11),
          addEventListener: () => {},
          querySelector: () => null
        };
        globalThis.window = globalThis;
        globalThis.addEventListener = () => {};

        const sampleDoc = {
          title: 'Wave A Renderer Fixture',
          subtitle: 'Clean Subtitle',
          defaultMode: 'paper',
          entries: [
            {
              header: 'Theorem',
              title: 'Section Numbering & Diagrams',
              declaration: 'Test.thm1',
              sectionTitle: 'Section 2.1 — Perfect Security',
              sectionId: 'sec-1',
              diagramHtml: '<style>.leak{color:red}</style><div class="ccw"><svg id="entry-svg"></svg></div>',
              statement: [[{ text: { value: 'Let ' } }, { inlineMath: { latex: '\\mathbf{G}' } }, { text: { value: '.' } }]],
              localInspectors: [
                { key: 'ins.bfG', display: '\\mathbf{G}', kind: { parameter: { roleDescription: 'Bold system G' } }, leanType: 'TypedSystem' },
                { key: 'ins.calR1', display: '\\mathcal{R}_1', kind: { parameter: { roleDescription: 'Reduction 1' } }, leanType: 'Converter' },
                { key: 'ins.sfAE', display: '\\mathsf{AE}', kind: { parameter: { roleDescription: 'AE interface' } }, leanType: 'Interface' }
              ],
              referencedKeys: ['ins.cc'],
              proof: [
                {
                  kind: 'step',
                  id: 's-para-1',
                  startsParagraph: true,
                  content: [{ text: { value: 'First paragraph.' } }],
                  children: []
                },
                {
                  kind: 'flowNote',
                  id: 'fn-empty-para',
                  placement: 'paragraph',
                  text: ''
                },
                {
                  kind: 'step',
                  id: 's-para-2',
                  startsParagraph: false,
                  diagramHtml: '<style>.leak2{}</style><div class="ccw"><svg id="childless-step-svg"></svg></div>',
                  content: [{ text: { value: 'Second paragraph via flowNote.' } }],
                  children: []
                },
                {
                  kind: 'step',
                  id: 's-with-diag-children',
                  startsParagraph: true,
                  diagramHtml: '<style>.leak3{}</style><div class="ccw"><svg id="parent-step-svg"></svg></div>',
                  content: [{ text: { value: 'Step with children and diagram.' } }],
                  defaultExpanded: false,
                  children: [
                    {
                      kind: 'step',
                      id: 's-child-1',
                      content: [{ text: { value: 'Child justification.' } }],
                      children: []
                    }
                  ]
                },
                {
                  kind: 'calcChain',
                  id: 'calc-diag',
                  intro: [{ text: { value: 'Computing chain:' } }],
                  steps: [
                    {
                      step: {
                        lhsLatex: 'A',
                        relationLatex: '=',
                        rhsLatex: 'B',
                        reason: [{ text: { value: 'by step' } }],
                        diagramHtml: '<style>.leak4{}</style><div class="ccw"><svg id="calc-step-svg"></svg></div>'
                      },
                      children: []
                    }
                  ]
                },
                {
                  kind: 'figure',
                  id: 'fig-proof-1',
                  caption: [{ text: { value: 'Caption with ' } }, { inlineMath: { latex: '\\mathcal{R}_1' } }],
                  html: '<style>.figleak{}</style><svg id="fig-svg"></svg>'
                }
              ],
              axioms: { axioms: ['propext'], hasSorry: false }
            },
            {
              header: 'Lemma',
              title: 'Unnumbered Section Title',
              declaration: 'Test.lem2',
              sectionTitle: 'Sponge Parameters',
              sectionId: 'sec-2',
              statement: [[{ text: { value: 'Statement.' } }]],
              proof: [],
              axioms: { axioms: ['propext'], hasSorry: false }
            }
          ],
          inspectors: [
            {
              key: 'ins.cc',
              display: 'R',
              kind: {
                ccDiagram: {
                  summaryLatex: 'R \\parallel S',
                  svgOrHtml: '<style>.ccleak{}</style><div class="ccw"><svg id="inspector-svg"></svg></div>'
                }
              },
              leanType: 'TypedSystem'
            },
            {
              key: 'ins.wc',
              display: 'w',
              kind: {
                witnessCard: {
                  title: 'H-Coefficient Witness',
                  rows: [
                    ['Real system', '\\(R\\)'],
                    ['Structure', 'Sample law, real/ideal reveals, transcript classes, and expected error bound']
                  ]
                }
              },
              leanType: 'HCoefficient'
            }
          ]
        };
        dataEl.textContent = JSON.stringify(sampleDoc);
        eval(jsSrc);
        const H = globalThis.__cadmoHelpers;
        function assert(cond, msg) { if (!cond) throw new Error('ASSERT FAILED: ' + msg); }

        // (a) Diagrams & figures mounted cleanly with <style> stripped
        const entryDiag = rootEl.querySelector('details.cadmo-entry-diagram');
        assert(entryDiag !== null, 'entry.diagramHtml must mount details.cadmo-entry-diagram');
        assert(entryDiag.hasAttribute('open'), 'entry.diagramHtml details must be open');
        assert(entryDiag.querySelector('summary').textContent === 'System diagram', 'entry diagram summary');
        const entryDiagBody = entryDiag.querySelector('.cadmo-diagram-body');
        assert(entryDiagBody && entryDiagBody.innerHTML.includes('entry-svg'), 'entry diagram svg mounted');
        assert(!entryDiagBody.innerHTML.includes('<style'), 'entry diagram style stripped');

        const figEl = rootEl.querySelector('figure.cadmo-diagram.cadmo-figure');
        assert(figEl !== null, 'ProofNode.figure must mount figure.cadmo-diagram.cadmo-figure');
        assert(figEl.querySelector('.cadmo-diagram-body').innerHTML.includes('fig-svg'), 'figure svg mounted');
        assert(!figEl.querySelector('.cadmo-diagram-body').innerHTML.includes('<style'), 'figure style stripped');
        const figCap = figEl.querySelector('figcaption');
        assert(figCap && figCap.textContent.includes('Caption with'), 'figure caption mounted');

        // Childless step diagram mounts collapsed details.cadmo-step-diagram directly
        const childlessStepDiag = rootEl.querySelector('details.cadmo-step-diagram');
        assert(childlessStepDiag !== null, 'childless step diagramHtml mounts details.cadmo-step-diagram');
        assert(!childlessStepDiag.hasAttribute('open'), 'step diagram collapsed by default');
        assert(childlessStepDiag.querySelector('summary').textContent === 'Diagram', 'step diagram summary');
        assert(childlessStepDiag.querySelector('.cadmo-diagram-body').innerHTML.includes('childless-step-svg'), 'childless step svg');

        // Expand proofs to verify expanded step.diagramHtml & calcStep.diagramHtml mount inside expanded step
        const controlsEl = rootEl.querySelector('.cadmo-controls');
        const expandBtn = controlsEl.querySelectorAll('button').find(b => b.textContent.includes('Expand proofs'));
        assert(expandBtn, 'Expand proofs button exists');
        const stepWithChildrenToggle = rootEl.querySelectorAll('button.cadmo-inline-toggle');
        assert(stepWithChildrenToggle.length >= 2, 'step and calc step with diagramHtml both get toggles');

        // Inspect inspector ccDiagram
        const ccBody = H.renderInspectorRichBody(sampleDoc.inspectors[0], { compact: false });
        const insDiagNode = ccBody.body.find(n => n.classList && n.classList.contains('cadmo-inspector-diagram'));
        assert(insDiagNode, 'ccDiagram must mount .cadmo-inspector-diagram');
        assert(insDiagNode.querySelector('.cadmo-diagram-body').innerHTML.includes('inspector-svg'), 'ccDiagram svg mounted');
        assert(!insDiagNode.querySelector('.cadmo-diagram-body').innerHTML.includes('<style'), 'ccDiagram style stripped');
        assert(ccBody.body.some(n => n.classList && n.classList.contains('cadmo-display-math')), 'ccDiagram still renders summaryLatex');

        // (b) witnessCard uses renderMixedText
        const wcBody = H.renderInspectorRichBody(sampleDoc.inspectors[1], { compact: false });
        const wcTable = wcBody.body.find(n => n.tagName === 'TABLE');
        assert(wcTable, 'witnessCard renders table');
        const tds = wcTable.querySelectorAll('td');
        assert(tds.length === 2, '2 witnessCard rows');
        assert(tds[0].querySelectorAll('.cadmo-math').length === 1 && tds[0].textContent === 'R', 'witnessCard \\(R\\) renders as inline math');
        assert(tds[1].querySelectorAll('.cadmo-math').length === 0, 'witnessCard English prose must NOT be wrapped in cadmo-math');
        assert(tds[1].textContent.includes('Sample law, real/ideal reveals'), 'witnessCard prose text intact');

        // (c) Double section numbering suppressed when sectionTitle starts with Section/§/Chapter/Part + digit
        const secTitles = rootEl.querySelectorAll('.cadmo-section-title');
        assert(secTitles.length === 2, '2 section titles');
        assert(secTitles[0].textContent === 'Section 2.1 — Perfect Security', 'no double prefix on Section 2.1, got: ' + secTitles[0].textContent);
        assert(secTitles[0].querySelector('.cadmo-section-num') === null, 'no .cadmo-section-num span on Section 2.1');
        assert(secTitles[1].querySelector('.cadmo-section-num').textContent === '2.', 'unnumbered title gets section number');

        // (d) flowNote with placement=paragraph & empty text splits paragraphs with zero stray empty DOM nodes
        const proofParas = rootEl.querySelectorAll('.cadmo-proof-para');
        assert(proofParas.length === 3, 'flowNote splits paragraph cleanly into 3 paras, got ' + proofParas.length);
        assert(rootEl.querySelectorAll('.cadmo-flow-note').length === 0, 'no stray .cadmo-flow-note');
        assert(rootEl.querySelectorAll('.cadmo-para-heading').length === 0, 'no stray empty .cadmo-para-heading');

        // (e) Font-sensitive hover disambiguation + unique bare fallback + blocked SUP/SUB/digits/delims
        const mixedIns = [
          { key: 'sym.calE', display: '\\mathcal{E}' },
          { key: 'sym.E', display: 'E' },
          { key: 'sym.bfG', display: '\\mathbf{G}' },
          { key: 'sym.calR1', display: '\\mathcal{R}_1' },
          { key: 'sym.sfAE', display: '\\mathsf{AE}' }
        ];
        const fScope = H.buildTokenScope(mixedIns, [], [], null, [], false);
        assert(H.resolveTokenCandidates(fScope, 'cal:E')[0].key === 'sym.calE', 'cal:E exact');
        assert(H.resolveTokenCandidates(fScope, 'E')[0].key === 'sym.E', 'plain E exact');
        assert(H.resolveTokenCandidates(fScope, 'bf:E') === null, 'bf:E must not guess among cal:E and E');
        assert(H.resolveTokenCandidates(fScope, 'bf:G')[0].key === 'sym.bfG', 'bf:G exact');
        assert(H.resolveTokenCandidates(fScope, 'G')[0].key === 'sym.bfG', 'unique G falls back to bf:G');
        assert(H.resolveTokenCandidates(fScope, 'AE')[0].key === 'sym.sfAE', 'unique AE falls back to sf:AE');

        const exprSpan = document.createElement('span');
        exprSpan.appendChild(H.renderMathNodes('\\mathbf{G} + \\mathcal{R}_1 + \\{0, 1\\}^E'));
        H.annotateOfflineMathContainer(exprSpan, fScope);
        const refs = exprSpan.querySelectorAll('.cadmo-ref');
        assert(refs.length === 2, 'expected 2 refs (bf:G and cal:R1, blocking {0,1}^E), got ' + refs.length);
        assert(refs[0].dataset.cadmoToken === 'bf:G', 'bf:G annotated');
        assert(refs[1].dataset.cadmoToken === 'cal:R1', 'cal:R1 annotated');
        assert(exprSpan.querySelectorAll('.cadmo-ref').filter(r => r.closest('sup')).length === 0, 'sup blocked');

        // (f) Click Expand proofs and verify step.diagramHtml & calcStep.diagramHtml mount inside .cadmo-expansion
        expandBtn.dispatchClick();
        const expansions = rootEl.querySelectorAll('.cadmo-expansion');
        const expandedStepDiags = expansions.flatMap(ex => ex.querySelectorAll('details.cadmo-step-diagram'));
        assert(expandedStepDiags.length === 2, 'expanded step + calcStep must mount 2 details.cadmo-step-diagram inside .cadmo-expansion, got ' + expandedStepDiags.length);
        const expandedHtmls = expandedStepDiags.map(d => d.querySelector('.cadmo-diagram-body').innerHTML);
        assert(expandedHtmls.some(s => s.includes('parent-step-svg')), 'expanded parent step diagram mounted');
        assert(expandedHtmls.some(s => s.includes('calc-step-svg')), 'expanded calc step diagram mounted');
        assert(expandedHtmls.every(s => !s.includes('<style')), 'expanded step diagrams stripped <style>');
        print('WAVE_A_JS_TESTS_OK');
        """
        js_src = CADMO_READER_JS.read_text(encoding="utf-8")
        full_js = "if (typeof print === 'undefined') { globalThis.print = console.log; }\n" + harness.replace(
            "__JS_SRC__", json.dumps(js_src)
        )
        script_path = self.tmp_path / "test_wave_a_js.js"
        script_path.write_text(full_js, encoding="utf-8")
        res = subprocess.run([*js_cmd, str(script_path)], capture_output=True, text=True)
        self.assertEqual(res.returncode, 0, msg=res.stdout + res.stderr)
        self.assertIn("WAVE_A_JS_TESTS_OK", res.stdout)

        # Verify CSS classes for diagrams, dark-mode theme sync, hover cues, and zero-width goal button
        css_txt = CADMO_READER_CSS.read_text(encoding="utf-8")
        for req_css in [
            ".cadmo-diagram",
            ".cadmo-entry-diagram",
            ".cadmo-step-diagram",
            ".cadmo-inspector-diagram",
            ".cadmo-diagram-body",
            ":root[data-theme=\"dark\"] .cadmo-diagram .ccw",
            ".cadmo-ref:hover",
            "width: 0;",
        ]:
            self.assertIn(req_css, css_txt)

    def test_verso_schema_new_optional_fields_roundtrip(self) -> None:
        exe = VERSO_PKG_DIR / ".lake" / "build" / "bin" / "verso-informalize"
        if not exe.is_file():
            self.skipTest("verso-informalize Lean binary not yet built")
        fixture = make_clean_fixture()
        fixture["entries"][0]["diagramHtml"] = "İ <style>.leak{color:red}</style><div class=\"ccw\">clean-diagram</div>"
        fixture["entries"][0]["proof"].append(
            {
                "kind": "step",
                "id": "claim-verso",
                "startsParagraph": True,
                "leadHeading": "Claim 1.",
                "trust": "intuitionGloss",
                "content": [
                    {"text": {"value": "Author gloss sentence."}, "trust": "intuitionGloss"},
                    {
                        "symbol": {
                            "key": "sym.key",
                            "display": "\\mathbf{K}",
                            "isMath": True,
                        },
                        "dataKey": "sym.key",
                        "trust": "typedRef",
                    },
                ],
                "children": [],
                "isWrapper": False,
                "defaultExpanded": False,
            }
        )
        json_path = self.write_json("verso_new_fields.json", fixture)
        res_inspect = subprocess.run([str(exe), "inspect", str(json_path)], capture_output=True, text=True)
        self.assertEqual(res_inspect.returncode, 0, msg=res_inspect.stdout + res_inspect.stderr)

        body_out = self.tmp_path / "verso_body.html"
        res_body = subprocess.run(
            [str(exe), "render-body", str(json_path), str(body_out), "--auditor"],
            capture_output=True,
            text=True,
        )
        self.assertEqual(res_body.returncode, 0, msg=res_body.stdout + res_body.stderr)
        body_html = body_out.read_text(encoding="utf-8")
        self.assertIn("cadmo-para-break", body_html)
        self.assertIn("cadmo-para-heading", body_html)
        self.assertIn("Claim 1.", body_html)
        self.assertIn("cadmo-trust-gloss", body_html)
        self.assertIn("data-cadmo-key=\"sym.key\"", body_html)
        self.assertIn("clean-diagram", body_html)
        self.assertNotIn("<style>", body_html)


if __name__ == "__main__":
    unittest.main(verbosity=2)
