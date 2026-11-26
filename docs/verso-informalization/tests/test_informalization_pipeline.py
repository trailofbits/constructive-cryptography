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
                            ["Bad event", "\\(\\mathsf{forge}\\)"],
                            ["Underlying system", "\\(G^-\\)"],
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

        // (a) Diagrams & figures mounted cleanly with <style> stripped, default collapsed (P6)
        const entryDiag = rootEl.querySelector('details.cadmo-entry-diagram');
        assert(entryDiag !== null, 'entry.diagramHtml must mount details.cadmo-entry-diagram');
        assert(!entryDiag.hasAttribute('open'), 'entry.diagramHtml details must start collapsed by default (P6)');
        assert(entryDiag.querySelector('summary').textContent === 'System figure', 'entry diagram summary must be System figure');
        const entryDiagBody = entryDiag.querySelector('.cadmo-diagram-body');
        assert(entryDiagBody && entryDiagBody.innerHTML.includes('entry-svg'), 'entry diagram svg mounted');
        assert(!entryDiagBody.innerHTML.includes('<style'), 'entry diagram style stripped');

        const figEl = rootEl.querySelector('figure.cadmo-diagram.cadmo-figure');
        assert(figEl !== null, 'ProofNode.figure must mount figure.cadmo-diagram.cadmo-figure');
        assert(figEl.querySelector('.cadmo-diagram-body').innerHTML.includes('fig-svg'), 'figure svg mounted');
        assert(!figEl.querySelector('.cadmo-diagram-body').innerHTML.includes('<style'), 'figure style stripped');
        const figCap = figEl.querySelector('figcaption');
        assert(figCap && figCap.textContent.includes('Caption with'), 'figure caption mounted');

        // Nested step.diagramHtml must NOT mount clutter inside proof steps (P6)
        assert(rootEl.querySelectorAll('details.cadmo-step-diagram').length === 0, 'step.diagramHtml must not mount details.cadmo-step-diagram');

        // Expand proofs to verify only steps with real children get toggles and 0 step diagrams mount inside ⊕
        const controlsEl = rootEl.querySelector('.cadmo-controls');
        const expandBtn = controlsEl.querySelectorAll('button').find(b => b.textContent.includes('Expand proofs'));
        assert(expandBtn, 'Expand proofs button exists');
        const stepWithChildrenToggle = rootEl.querySelectorAll('button.cadmo-inline-toggle');
        assert(stepWithChildrenToggle.length === 1, 'only step with real children gets a toggle (calcStep diagramHtml alone does not), got ' + stepWithChildrenToggle.length);

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

        // (f) Click Expand proofs and verify zero nested step.diagramHtml / calcStep.diagramHtml inside .cadmo-expansion (P6),
        // plus sentence/math spacing (Pr[Z].To prove and [\,n\,] -> [n]) and setting/motivation preludes
        expandBtn.dispatchClick();
        const expansions = rootEl.querySelectorAll('.cadmo-expansion');
        const expandedStepDiags = expansions.flatMap(ex => ex.querySelectorAll('details.cadmo-step-diagram'));
        assert(expandedStepDiags.length === 0, 'expanded step + calcStep must mount 0 details.cadmo-step-diagram inside .cadmo-expansion (P6), got ' + expandedStepDiags.length);

        const spacedFlow = H.renderProofFlow([
          {
            kind: 'step',
            id: 'sp-1',
            content: [{ inlineMath: { latex: '\\Pr[Z]' } }, { text: { value: '.' } }],
            children: []
          },
          {
            kind: 'calcChain',
            id: 'sp-calc',
            intro: [{ text: { value: 'To prove the claim:' } }],
            steps: [{ step: { lhsLatex: 'A', relationLatex: '=', rhsLatex: 'B', reason: [] }, children: [] }]
          }
        ], { depth: 0, scope: null });
        assert(spacedFlow[0].textContent.includes('Pr[Z]. To prove'), 'calcChain intro must not glue onto previous period, got: ' + spacedFlow[0].textContent);

        const bracketMath = H.renderInline({ inlineMath: { latex: '[\\,U\\,]' } }, null);
        assert(bracketMath.textContent === '[U]', 'index-set [\\,U\\,] must normalize to [U], got: ' + JSON.stringify(bracketMath.textContent));

        const settingPrelude = H.renderPreludeBlock({
          id: 'pre-set',
          kind: 'setting',
          label: 'Setting',
          body: [[{ text: { value: 'Fix seed space ' } }, { inlineMath: { latex: 'S' } }, { text: { value: '.' } }]]
        }, null);
        assert(settingPrelude && settingPrelude.classList.contains('cadmo-prelude-setting'), 'setting prelude class');
        assert(settingPrelude.querySelector('table') === null, 'setting prelude must have zero table chrome');

        const motivPrelude = H.renderPreludeBlock({
          id: 'pre-mot',
          kind: 'motivation',
          body: [[{ text: { value: 'We interpolate in two hops.' } }]]
        }, null);
        assert(motivPrelude && motivPrelude.classList.contains('cadmo-prelude-motivation'), 'motivation prelude class');
        assert(motivPrelude.getAttribute('data-trust') === 'authorGloss', 'motivation prelude gets authorGloss trust');
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

    def _make_wave_b_fixture(self, include_style_in_prelude_diag: bool = False) -> Dict[str, Any]:
        doc = make_clean_fixture()
        diag_prefix = "<style>.prelude-leak{color:red}</style>" if include_style_in_prelude_diag else ""
        entry = doc["entries"][0]
        entry["sectionTitle"] = "Authenticated Encryption"
        entry["sectionId"] = "sec-ae"
        entry["sectionContext"] = {
            "sectionId": "sec-ae",
            "sectionNumber": 3,
            "paragraphs": [
                [
                    {"text": {"value": "Let "}},
                    {"symbol": {"key": "sym.key", "display": "\\mathbf{K}", "isMath": True}},
                    {"text": {"value": " be the shared secret key."}},
                ]
            ],
            "inspectors": [],
        }
        entry["sectionPreludes"] = [
            {
                "id": "prelude-def-1",
                "kind": "definition",
                "label": "Definition 3.1",
                "title": "PRG Security",
                "body": [
                    [
                        {"text": {"value": "A generator "}},
                        {"inlineMath": {"latex": "G"}},
                        {"text": {"value": " is "}},
                        {"inlineMath": {"latex": "\\varepsilon"}},
                        {"text": {"value": "-secure if no distinguisher gains advantage above "}},
                        {"inlineMath": {"latex": "\\varepsilon"}},
                        {"text": {"value": "."}},
                    ]
                ],
                "lines": [],
                "rows": [],
                "declKey": "sym.sec",
                "diagramHtml": None,
            },
            {
                "id": "prelude-game-1",
                "kind": "attackGame",
                "label": "Attack Game 3.1",
                "title": "Authenticated Encryption Game",
                "body": [
                    [{"text": {"value": "The challenger samples a secret key and answers encryption queries."}}]
                ],
                "lines": [
                    {"indent": 0, "inlines": [{"text": {"value": "1. Sample "}}, {"symbol": {"key": "sym.key", "display": "\\mathbf{K}", "isMath": True}}, {"text": {"value": " uniformly."}}]},
                    {"indent": 1, "inlines": [{"text": {"value": "2. On query "}}, {"inlineMath": {"latex": "m"}}, {"text": {"value": ", compute "}}, {"inlineMath": {"latex": "c"}}, {"text": {"value": "."}}]},
                    {"indent": 2, "inlines": [{"text": {"value": "Return ciphertext "}}, {"inlineMath": {"latex": "c"}}, {"text": {"value": "."}}]},
                ],
                "rows": [],
                "declKey": "sym.game",
                "diagramHtml": f'{diag_prefix}<div class="ccw"><svg id="prelude-game-svg" width="80" height="20"></svg></div>',
            },
            {
                "id": "prelude-const-1",
                "kind": "construction",
                "label": "Construction 3.2",
                "title": "Encrypt-then-MAC",
                "body": [
                    [{"text": {"value": "Compose "}}, {"symbol": {"key": "sym.encdec", "display": "\\pi_{\\mathsf{AE}}", "isMath": True}}, {"text": {"value": " sequentially."}}]
                ],
                "lines": [
                    {"indent": 0, "inlines": [{"text": {"value": "on send(m):"}}]},
                    {"indent": 1, "inlines": [{"text": {"value": "output "}}, {"inlineMath": {"latex": "\\pi_{\\mathsf{AE}}(m)"}}]},
                ],
                "rows": [],
            },
            {
                "id": "prelude-iface-1",
                "kind": "interfaceSpec",
                "label": "Interface 3.3",
                "title": "Channel Ports",
                "body": [[{"text": {"value": "Honest ports expose send and receive operations."}}]],
                "lines": [{"indent": 0, "inlines": [{"text": {"value": "port A: send(m)"}}]}],
                "rows": [
                    {"left": [{"inlineMath": {"latex": "A"}}], "right": [{"text": {"value": "Sender port"}}]},
                ],
                "declKey": "sym.key",
            },
            {
                "id": "prelude-conv-1",
                "kind": "converterDef",
                "label": "Converter 3.4",
                "title": "Cipher Converter",
                "body": [[{"text": {"value": "Transforms an authenticated channel into a secure channel."}}]],
                "lines": [
                    {"indent": 0, "inlines": [{"text": {"value": "1. Read key from "}}, {"symbol": {"key": "sym.key", "display": "\\mathbf{K}", "isMath": True}}]},
                    {"indent": 1, "inlines": [{"text": {"value": "2. Emit cipher."}}]},
                ],
                "rows": [],
                "declKey": "sym.encdec",
            },
            {
                "id": "prelude-sym-1",
                "kind": "symbolTable",
                "label": "Notation 3.5",
                "title": "Section Symbols",
                "body": [],
                "lines": [],
                "rows": [
                    {
                        "left": [{"symbol": {"key": "sym.key", "display": "\\mathbf{K}", "isMath": True}}],
                        "right": [{"text": {"value": "Shared uniform secret key"}}],
                    },
                    {
                        "left": [{"symbol": {"key": "sym.sec", "display": "\\mathbf{SEC}", "isMath": True}}],
                        "right": [{"text": {"value": "Ideal confidential and authentic channel"}}],
                    },
                ],
            },
        ]
        entry["proof"].append(
            {
                "kind": "pseudocodeBox",
                "id": "pbox-red-1",
                "title": "Reduction B",
                "boxKind": "reduction",
                "lines": [
                    {"indent": 0, "inlines": [{"text": {"value": "1. Receive input "}}, {"inlineMath": {"latex": "x"}}]},
                    {"indent": 1, "inlines": [{"text": {"value": "2. Invoke "}}, {"symbol": {"key": "sym.game", "display": "G", "isMath": True}}, {"text": {"value": " on "}}, {"inlineMath": {"latex": "x"}}]},
                    {"indent": 2, "inlines": [{"text": {"value": "return bit "}}, {"inlineMath": {"latex": "b'"}}]},
                ],
                "goal": {
                    "context": [{"name": "x", "description": "an input bitstring", "isHypothesis": False, "usedInGoal": True}],
                    "targetLatex": "\\Delta(\\mathbf{K}, \\mathbf{SEC}) \\le \\varepsilon",
                    "targetProse": "The reduction advantage is bounded by ε.",
                },
                "originDecl": "Examples.AuthenticatedEncryption.reductionB",
            }
        )
        return doc

    def test_wave_b_verso_schema_preludes_and_pseudocode_box_roundtrip(self) -> None:
        fixture = self._make_wave_b_fixture(include_style_in_prelude_diag=True)
        json_path = self.write_json("wave_b_schema.json", fixture)

        exe = VERSO_PKG_DIR / ".lake" / "build" / "bin" / "verso-informalize"
        if not exe.is_file():
            self.skipTest("verso-informalize Lean binary not yet built")

        res_inspect = subprocess.run([str(exe), "inspect", str(json_path)], capture_output=True, text=True)
        self.assertEqual(res_inspect.returncode, 0, msg=res_inspect.stdout + res_inspect.stderr)

        body_out = self.tmp_path / "wave_b_body.html"
        res_body = subprocess.run(
            [str(exe), "render-body", str(json_path), str(body_out), "--auditor"],
            capture_output=True,
            text=True,
        )
        self.assertEqual(res_body.returncode, 0, msg=res_body.stdout + res_body.stderr)
        body_html = body_out.read_text(encoding="utf-8")

        # Preludes mount after sectionContext and BEFORE entry article
        idx_ctx = body_html.index("cadmo-section-context")
        idx_pre = body_html.index("cadmo-section-preludes")
        idx_entry = body_html.index("<article class=\"cadmo-entry\"")
        self.assertLess(idx_ctx, idx_pre)
        self.assertLess(idx_pre, idx_entry)

        for kind in ["definition", "attackGame", "construction", "interfaceSpec", "converterDef", "symbolTable"]:
            self.assertIn(f"cadmo-prelude-{kind}", body_html)
        self.assertIn("cadmo-prelude-table", body_html)
        self.assertIn("cadmo-prelude-inspect", body_html)
        self.assertIn("cadmo-pseudocode-box cadmo-pbox-reduction", body_html)
        self.assertIn("padding-left: calc(1 * 1.4em)", body_html)
        self.assertIn("padding-left: calc(2 * 1.4em)", body_html)
        self.assertNotIn("<style>", body_html)
        self.assertIn("prelude-game-svg", body_html)

        # Direct Lean roundtrip check (FromJson -> ToJson -> FromJson == original) + legacy JSON decode
        legacy_path = self.write_json("legacy_compat.json", make_clean_fixture())
        lean_probe = VERSO_PKG_DIR / ".lake" / "roundtrip_probe.lean"
        try:
            lean_probe.write_text(
                f"""import VersoInformalization.Schema
import VersoInformalization.CadmoBlocks
open Lean VersoInformalization.Schema VersoInformalization.CadmoBlocks

#eval show IO Unit from do
  let doc1 ← loadDocumentFile {json.dumps(str(json_path))}
  let encoded := (toJson doc1).compress
  let doc2 ← IO.ofExcept (parseDocumentJson encoded)
  if doc1 != doc2 then
    throw <| IO.userError "Roundtrip mismatch between doc1 and doc2"
  let entry := doc2.entries[0]!
  if entry.sectionPreludes.size != 6 then
    throw <| IO.userError s!"Expected 6 sectionPreludes, got {{entry.sectionPreludes.size}}"
  let hasPbox := entry.proof.any fun
    | .pseudocodeBox _ _ _ _ _ _ => true
    | _ => false
  if !hasPbox then
    throw <| IO.userError "Expected ProofNode.pseudocodeBox after roundtrip"
  let legacy ← loadDocumentFile {json.dumps(str(legacy_path))}
  if !legacy.entries[0]!.sectionPreludes.isEmpty then
    throw <| IO.userError "Expected empty sectionPreludes on legacy doc"
  IO.println "VERSO_ROUNDTRIP_OK"
""",
                encoding="utf-8",
            )
            res_lean = subprocess.run(
                ["lake", "env", "lean", str(lean_probe)],
                cwd=str(VERSO_PKG_DIR),
                capture_output=True,
                text=True,
            )
            self.assertEqual(res_lean.returncode, 0, msg=res_lean.stdout + res_lean.stderr)
            self.assertIn("VERSO_ROUNDTRIP_OK", res_lean.stdout)
        finally:
            if lean_probe.exists():
                lean_probe.unlink()

    def test_wave_b_preludes_and_pseudocode_box_dom_js(self) -> None:
        js_cmd = find_js_runtime()
        if not js_cmd:
            self.skipTest("No JS runtime (node or jsc) available")

        fixture = self._make_wave_b_fixture(include_style_in_prelude_diag=True)
        # Also test a pseudocodeBox nested inside an isWrapper=true step to verify Paper mode preserves it
        fixture["entries"][0]["proof"].append(
            {
                "kind": "step",
                "id": "wrap-pbox",
                "content": [{"text": {"value": "Wrapper forwarding to hybrid box."}}],
                "isWrapper": True,
                "defaultExpanded": False,
                "children": [
                    {
                        "kind": "pseudocodeBox",
                        "id": "pbox-hybrid-wrapped",
                        "title": "Hybrid H_1",
                        "boxKind": "hybrid",
                        "lines": [
                            {"indent": 0, "inlines": [{"text": {"value": "1. Replace "}}, {"symbol": {"key": "sym.key", "display": "\\mathbf{K}", "isMath": True}}, {"text": {"value": " with random."}}]},
                            {"indent": 1, "inlines": [{"text": {"value": "2. Run distinguisher."}}]},
                        ],
                        "goal": None,
                        "originDecl": "Examples.AuthenticatedEncryption.hybrid1",
                    }
                ],
            }
        )

        harness = r"""
        const jsSrc = __JS_SRC__;
        const sampleDoc = __DOC_JSON__;
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
          replaceWith(newNode) {
            if (!this.parentNode) return;
            this.parentNode.insertBefore(newNode, this);
            this.parentNode.removeChild(this);
          }
          contains(target) {
            let cur = target;
            while (cur) {
              if (cur === this) return true;
              cur = cur.parentNode;
            }
            return false;
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
              if (tok.startsWith('[')) {
                const inner = tok.slice(1, -1);
                const eq = inner.indexOf('=');
                if (eq >= 0) {
                  const k = inner.slice(0, eq).trim();
                  const v = inner.slice(eq + 1).trim().replace(/^["']|["']$/g, '');
                  return this.getAttribute(k) === v;
                }
                return this.hasAttribute(inner);
              }
              if (tok.startsWith('.')) return this.classList.contains(tok.slice(1));
              return this.tagName === tok.toUpperCase();
            });
          }
          matches(sel) {
            return sel.split(',').some(p => this.matchesSelectorOne(p));
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
          _queryDescendantChain(parts) {
            if (parts.length === 0) return [];
            const [head, ...tail] = parts;
            const hits = [];
            const walk = (node) => {
              for (const ch of node.children) {
                if (ch.matchesSelectorOne(head)) hits.push(ch);
                walk(ch);
              }
            };
            walk(this);
            if (tail.length === 0) return hits;
            const seen = new Set();
            const out = [];
            for (const h of hits) {
              for (const sub of h._queryDescendantChain(tail)) {
                if (!seen.has(sub)) {
                  seen.add(sub);
                  out.push(sub);
                }
              }
            }
            return out;
          }
          querySelectorAll(selectorList) {
            const branches = selectorList.split(',').map(s => s.trim()).filter(Boolean);
            const seen = new Set();
            const out = [];
            for (const b of branches) {
              const parts = b.split(/\s+/).filter(Boolean);
              for (const el of this._queryDescendantChain(parts)) {
                if (!seen.has(el)) {
                  seen.add(el);
                  out.push(el);
                }
              }
            }
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
          getElementById: (id) => {
            if (id === 'cadmo-root') return rootEl;
            if (id === 'cadmo-document-data') return dataEl;
            return rootEl.querySelectorAll('[id]').find(n => n.getAttribute('id') === id) || null;
          },
          createElement: (tag) => new FakeNode(1, tag),
          createTextNode: (txt) => { const n = new FakeNode(3); n._text = String(txt || ''); return n; },
          createDocumentFragment: () => new FakeNode(11),
          addEventListener: () => {},
          querySelector: () => null
        };
        globalThis.window = globalThis;
        globalThis.addEventListener = () => {};

        // Mock KaTeX to verify KaTeX rendering + hover reference annotation inside preludes & pseudocodeBox
        let katexCalls = 0;
        globalThis.katex = {
          render: (tex, el) => {
            katexCalls += 1;
            const kHtml = document.createElement('span');
            kHtml.className = 'katex-html';
            const base = document.createElement('span');
            base.className = 'base';
            const tok = document.createElement('span');
            tok.className = 'mord';
            tok.textContent = tex;
            base.appendChild(tok);
            kHtml.appendChild(base);
            el.appendChild(kHtml);
          }
        };

        dataEl.textContent = JSON.stringify(sampleDoc);
        eval(jsSrc);
        function assert(cond, msg) { if (!cond) throw new Error('ASSERT FAILED: ' + msg); }

        assert(katexCalls > 0, 'KaTeX must run on math in preludes & pseudocodeBox');

        // 1. Verify DOM order: section-head (with section-context) -> section-preludes -> entry
        const mainEl = rootEl.querySelector('.cadmo-main');
        assert(mainEl !== null, 'main element present');
        const mainKids = mainEl.children;
        const idxSecHead = mainKids.findIndex(el => el.classList.contains('cadmo-section-head'));
        const idxPreludes = mainKids.findIndex(el => el.classList.contains('cadmo-section-preludes'));
        const idxEntry = mainKids.findIndex(el => el.classList.contains('cadmo-entry'));
        assert(idxSecHead >= 0 && idxPreludes > idxSecHead && idxEntry > idxPreludes,
          `Expected sectionHead (${idxSecHead}) < sectionPreludes (${idxPreludes}) < entry (${idxEntry})`);
        assert(mainKids[idxSecHead].querySelector('.cadmo-section-context') !== null, 'sectionContext mounted inside sectionHead');

        // 2. Verify all 6 prelude kinds render cleanly
        const preludesWrap = mainKids[idxPreludes];
        for (const kind of ['definition', 'attackGame', 'construction', 'interfaceSpec', 'converterDef', 'symbolTable']) {
          const el = preludesWrap.querySelector(`.cadmo-prelude-${kind}`);
          assert(el !== null, `Missing prelude kind .cadmo-prelude-${kind}`);
        }
        const symTable = preludesWrap.querySelector('.cadmo-prelude-symbolTable table.cadmo-prelude-table');
        assert(symTable && symTable.querySelectorAll('tr').length === 2, 'symbolTable renders 2 rows');
        assert(symTable.querySelectorAll('button.cadmo-sym').length >= 2, 'symbolTable rows carry interactive symbols');

        // 3. Verify indentation, stripped <style> diagram, and declKey inspect button in preludes
        const gamePrelude = preludesWrap.querySelector('.cadmo-prelude-attackGame');
        const gameLines = gamePrelude.querySelectorAll('.cadmo-pseudocode-line');
        assert(gameLines.length === 3, 'attackGame has 3 pseudocode lines');
        assert(gameLines[0].getAttribute('data-indent') === '0', 'indent 0');
        assert(gameLines[1].getAttribute('data-indent') === '1' && gameLines[1].style.paddingLeft === 'calc(1 * 1.4em)', 'indent 1 padding-left');
        assert(gameLines[2].getAttribute('data-indent') === '2' && gameLines[2].style.paddingLeft === 'calc(2 * 1.4em)', 'indent 2 padding-left');
        const gameDiagBody = gamePrelude.querySelector('.cadmo-prelude-diagram .cadmo-diagram-body');
        assert(gameDiagBody && gameDiagBody.innerHTML.includes('prelude-game-svg'), 'prelude diagramHtml mounted');
        assert(!gameDiagBody.innerHTML.includes('<style'), 'prelude diagramHtml <style> stripped');

        // Clicking declKey inspect button opens margin inspector card
        const inspectBtn = gamePrelude.querySelector('button.cadmo-prelude-inspect');
        assert(inspectBtn !== null && inspectBtn.getAttribute('data-cadmo-key') === 'sym.game', 'prelude declKey inspect button present');
        inspectBtn.dispatchClick();
        const sidenoteTitle = rootEl.querySelector('.cadmo-margin .cadmo-sidenote-title');
        assert(sidenoteTitle && sidenoteTitle.textContent.includes('G'), 'clicking prelude Inspect button opens margin inspector');

        // 4. Verify ProofNode.pseudocodeBox renders in Paper mode (including wrapper-unwrapped hybrid box)
        const pboxesPaper = rootEl.querySelectorAll('figure.cadmo-pseudocode-box');
        assert(pboxesPaper.length === 2, 'Paper mode must render both pseudocodeBox figures, got ' + pboxesPaper.length);
        assert(rootEl.querySelector('figure.cadmo-pbox-reduction') !== null, 'reduction box rendered in Paper mode');
        assert(rootEl.querySelector('figure.cadmo-pbox-hybrid') !== null, 'wrapper-nested hybrid box preserved in Paper mode');
        const redBox = rootEl.querySelector('figure.cadmo-pbox-reduction');
        assert(redBox.querySelector('.cadmo-pbox-kind').textContent === 'Reduction', 'boxKind pill rendered');
        assert(redBox.querySelector('.cadmo-pbox-title').textContent === 'Reduction B', 'box title rendered');
        const redLines = redBox.querySelectorAll('.cadmo-pseudocode-line');
        assert(redLines.length === 3 && redLines[2].style.paddingLeft === 'calc(2 * 1.4em)', 'pseudocodeBox indented lines');
        assert(redBox.querySelectorAll('button.cadmo-sym').length >= 1, 'pseudocodeBox line interactive symbol annotated');

        // 5. Switch to Auditor mode and verify pseudocodeBox + goal button + origin tag work
        const auditorBtn = rootEl.querySelector('.cadmo-controls').querySelectorAll('button').find(b => b.textContent === 'Auditor');
        assert(auditorBtn, 'Auditor mode button present');
        auditorBtn.dispatchClick();
        assert(docEl.dataset.mode === 'auditor', 'mode switched to auditor');
        const pboxesAuditorCollapsed = rootEl.querySelectorAll('figure.cadmo-pseudocode-box');
        assert(pboxesAuditorCollapsed.length === 1, 'Auditor mode preserves top-level pseudocodeBox before expanding wrapper');
        const expandAllBtn = rootEl.querySelector('.cadmo-controls').querySelectorAll('button').find(b => b.textContent.includes('Expand proofs'));
        assert(expandAllBtn, 'Expand proofs button present in Auditor mode');
        expandAllBtn.dispatchClick();
        const pboxesAuditorExpanded = rootEl.querySelectorAll('figure.cadmo-pseudocode-box');
        assert(pboxesAuditorExpanded.length === 2, 'Auditor mode preserves both pseudocodeBox figures after expanding wrapper, got ' + pboxesAuditorExpanded.length);
        const redBoxAud = rootEl.querySelector('figure.cadmo-pbox-reduction');
        assert(redBoxAud.querySelector('.cadmo-origin-tag').textContent.includes('reductionB'), 'originDecl tag shown on pseudocodeBox');
        const goalBtn = redBoxAud.querySelector('button.cadmo-goal-btn');
        assert(goalBtn !== null, 'goal button present on pseudocodeBox');
        goalBtn.dispatchClick();
        const goalSidenote = rootEl.querySelector('.cadmo-margin .cadmo-goal-target');
        assert(goalSidenote && goalSidenote.textContent.includes('SEC'), 'clicking pseudocodeBox goal button opens GoalState in margin');

        print('WAVE_B_JS_TESTS_OK');
        """
        js_src = CADMO_READER_JS.read_text(encoding="utf-8")
        full_js = (
            "if (typeof print === 'undefined') { globalThis.print = console.log; }\n"
            + harness.replace("__JS_SRC__", json.dumps(js_src)).replace("__DOC_JSON__", json.dumps(fixture))
        )
        script_path = self.tmp_path / "test_wave_b_js.js"
        script_path.write_text(full_js, encoding="utf-8")
        res = subprocess.run([*js_cmd, str(script_path)], capture_output=True, text=True)
        self.assertEqual(res.returncode, 0, msg=res.stdout + res.stderr)
        self.assertIn("WAVE_B_JS_TESTS_OK", res.stdout)

        css_txt = CADMO_READER_CSS.read_text(encoding="utf-8")
        for req_css in [
            ".cadmo-section-preludes",
            ".cadmo-prelude-definition",
            ".cadmo-prelude-attackGame",
            ".cadmo-prelude-symbolTable",
            ".cadmo-prelude-interfaceSpec",
            ".cadmo-pseudocode-box",
            ".cadmo-pseudocode-line",
        ]:
            self.assertIn(req_css, css_txt)

    def test_wave_b_ci_gates_preludes_and_pseudocode_box(self) -> None:
        clean = self._make_wave_b_fixture(include_style_in_prelude_diag=False)
        clean_path = self.write_json("wave_b_clean.json", clean)
        for tier in ("legacy", "authored"):
            res = run_check("--tier", tier, str(clean_path))
            self.assertEqual(res.returncode, 0, msg=f"tier={tier}: {res.stdout}\n{res.stderr}")

        # Negative 1: zero-leakage in prelude label, title, body, lines, rows
        leak_locations = [
            ("label", lambda d: d["entries"][0]["sectionPreludes"][0].__setitem__("label", "Def x._hyg.9")),
            ("title", lambda d: d["entries"][0]["sectionPreludes"][0].__setitem__("title", "Game at interface A")),
            ("body", lambda d: d["entries"][0]["sectionPreludes"][0]["body"][0].append({"text": {"value": " via ENNReal.ofReal"}})),
            ("lines", lambda d: d["entries"][0]["sectionPreludes"][1]["lines"][0]["inlines"].append({"text": {"value": " fun x => x"}})),
            ("rows.left", lambda d: d["entries"][0]["sectionPreludes"][5]["rows"][0]["left"].append({"inlineMath": {"latex": "x._hyg.1"}})),
            ("rows.right", lambda d: d["entries"][0]["sectionPreludes"][5]["rows"][0]["right"].append({"text": {"value": " uses whiskering"}})),
        ]
        for label, mutator in leak_locations:
            with self.subTest(prelude_leak=label):
                bad = copy.deepcopy(clean)
                mutator(bad)
                p = self.write_json(f"leak_prelude_{label}.json", bad)
                res = run_check(str(p))
                self.assertNotEqual(res.returncode, 0)
                self.assertIn("zero-leakage", res.stdout)

        # Negative 2: broken declKey & broken symbol key inside sectionPreludes
        bad_decl_key = copy.deepcopy(clean)
        bad_decl_key["entries"][0]["sectionPreludes"][0]["declKey"] = "sym.missing_decl"
        res_dk = run_check(str(self.write_json("bad_prelude_dk.json", bad_decl_key)))
        self.assertNotEqual(res_dk.returncode, 0)
        self.assertIn("sym.missing_decl", res_dk.stdout)

        bad_row_sym = copy.deepcopy(clean)
        bad_row_sym["entries"][0]["sectionPreludes"][5]["rows"][0]["right"].append(
            {"symbol": {"key": "sym.broken_row_sym", "display": "Z", "isMath": True}}
        )
        res_rs = run_check(str(self.write_json("bad_row_sym.json", bad_row_sym)))
        self.assertNotEqual(res_rs.returncode, 0)
        self.assertIn("sym.broken_row_sym", res_rs.stdout)

        # Negative 3: embedded <style> in prelude.diagramHtml
        bad_style = self._make_wave_b_fixture(include_style_in_prelude_diag=True)
        res_st = run_check(str(self.write_json("bad_prelude_style.json", bad_style)))
        self.assertNotEqual(res_st.returncode, 0)
        self.assertIn("diagram-style", res_st.stdout)

        # Negative 4: typography double space inside prelude & pseudocodeBox lines
        bad_space = copy.deepcopy(clean)
        bad_space["entries"][0]["sectionPreludes"][1]["lines"][0]["inlines"][0]["text"]["value"] = "1. Sample  key"
        res_sp = run_check(str(self.write_json("bad_prelude_space.json", bad_space)))
        self.assertNotEqual(res_sp.returncode, 0)
        self.assertIn("typography", res_sp.stdout)

        # Negative 5: pseudocodeBox zero-leakage (title, lines, goal), broken key, and sibling dedup
        pbox_mutations = [
            ("title_leak", "zero-leakage", lambda b: b.__setitem__("title", "Reduction x._hyg.3")),
            ("line_leak", "zero-leakage", lambda b: b["lines"][0]["inlines"].append({"text": {"value": " Coe.coe x"}})),
            ("goal_leak", "zero-leakage", lambda b: b["goal"].__setitem__("targetLatex", "ENNReal.ofReal x")),
            ("broken_key", "sym.missing_pbox", lambda b: b["lines"][0]["inlines"].append({"symbol": {"key": "sym.missing_pbox", "display": "Q", "isMath": True}})),
            ("double_space", "typography", lambda b: b["lines"][0]["inlines"][0]["text"].__setitem__("value", "1. Receive  input ")),
        ]
        for name, expected_msg, mutator in pbox_mutations:
            with self.subTest(pbox=name):
                bad = copy.deepcopy(clean)
                mutator(bad["entries"][0]["proof"][-1])
                res = run_check(str(self.write_json(f"bad_pbox_{name}.json", bad)))
                self.assertNotEqual(res.returncode, 0)
                self.assertIn(expected_msg, res.stdout)

        dup_pbox = copy.deepcopy(clean)
        dup_copy = copy.deepcopy(dup_pbox["entries"][0]["proof"][-1])
        dup_copy["id"] = "pbox-red-2"
        dup_pbox["entries"][0]["proof"].append(dup_copy)
        res_dup = run_check(str(self.write_json("dup_pbox.json", dup_pbox)))
        self.assertNotEqual(res_dup.returncode, 0)
        self.assertIn("sibling-dedup", res_dup.stdout)

    def test_wave_c_l1_soundness_and_l2_latex_hygiene(self) -> None:
        # L1 negative: (\cdot)^{S^*} and \alphaG_{2} fail in ALL tiers
        for label, mutator in [
            (
                "dropped_eps",
                lambda d: d["entries"][0]["statement"][0].append(
                    {"inlineMath": {"latex": "(\\cdot)^{S^*}"}}
                ),
            ),
            (
                "glued_alpha",
                lambda d: d["entries"][0]["proof"][1]["children"][0]["steps"][0]["step"].__setitem__(
                    "lhsLatex", "\\alphaG_{2}"
                ),
            ),
        ]:
            for tier in ("legacy", "authored"):
                with self.subTest(l1=label, tier=tier):
                    bad = make_clean_fixture()
                    mutator(bad)
                    p = self.write_json(f"l1_{label}_{tier}.json", bad)
                    res = run_check("--tier", tier, str(p))
                    self.assertNotEqual(res.returncode, 0)
                    self.assertIn("L1-soundness", res.stdout)

        # L1 positive: epsilonRelaxation definition := (\cdot)^{\mathrm{error}} passes
        pos_l1 = make_clean_fixture()
        pos_l1["inspectors"].append(
            {
                "key": "ConstructiveCryptography.CryptographicAlgebra.Specification.epsilonRelaxation",
                "display": "\\varepsilon\\text{-relax}",
                "kind": {
                    "mathDefinition": {
                        "equationLatex": "\\mathrm{epsilonRelaxation}\\!\\left(\\mathrm{error}\\right) := (\\cdot)^{\\mathrm{error}}",
                        "proseSummary": "Epsilon relaxation operator.",
                    }
                },
                "leanName": "ConstructiveCryptography.CryptographicAlgebra.Specification.epsilonRelaxation",
                "leanType": "ENNReal -> Spec",
            }
        )
        res_pos_l1 = run_check("--tier", "authored", str(self.write_json("l1_eps_def.json", pos_l1)))
        self.assertEqual(res_pos_l1.returncode, 0, msg=res_pos_l1.stdout)

        # L2 negative: double subscripts, ${...}, and raw TeX in plain-text inspector fields
        l2_cases = [
            (
                "dbl_sub_braced",
                lambda d: d["entries"][0]["statement"][0].append({"inlineMath": {"latex": "z_{1}_{2}"}}),
            ),
            (
                "dbl_sub_bare",
                lambda d: d["entries"][0]["statement"][0].append({"inlineMath": {"latex": "z_1_2"}}),
            ),
            (
                "uninterp_template",
                lambda d: d["entries"][0]["proof"][0].__setitem__("text", "Applied routine ${fixedBit false}."),
            ),
            (
                "raw_mathcal_in_roleDesc",
                lambda d: d["entries"][0].__setitem__(
                    "localInspectors",
                    [
                        {
                            "key": "sh.B",
                            "display": "\\mathcal{B}",
                            "kind": {
                                "localShorthand": {
                                    "equationLatex": "\\mathcal{B} = R",
                                    "roleDescription": "Reduction \\mathcal{B} calling [\\,n\\,].",
                                }
                            },
                            "leanType": "Converter",
                        }
                    ],
                ),
            ),
            (
                "raw_mathbf_in_proseSummary",
                lambda d: d["inspectors"][1]["kind"]["mathDefinition"].__setitem__(
                    "proseSummary", "Ideal channel \\mathbf{SEC}."
                ),
            ),
            (
                "raw_tex_in_witnessCard",
                lambda d: d["inspectors"][3]["kind"]["witnessCard"]["rows"][0].__setitem__(
                    1, "\\mathsf{forge}"
                ),
            ),
        ]
        for label, mutator in l2_cases:
            for tier in ("legacy", "authored"):
                with self.subTest(l2=label, tier=tier):
                    bad = make_clean_fixture()
                    mutator(bad)
                    res = run_check("--tier", tier, str(self.write_json(f"l2_{label}_{tier}.json", bad)))
                    self.assertNotEqual(res.returncode, 0)
                    self.assertIn("L2-latex-hygiene", res.stdout)

        # L2 positive: merged z_{1,2} subscript and properly delimited \(\mathcal{B}\) pass
        pos_l2 = make_clean_fixture()
        pos_l2["entries"][0]["statement"][0].append({"inlineMath": {"latex": "z_{1,2}"}})
        pos_l2["entries"][0]["localInspectors"] = [
            {
                "key": "sh.B",
                "display": "\\mathcal{B}",
                "kind": {
                    "localShorthand": {
                        "equationLatex": "\\mathcal{B} = R",
                        "roleDescription": "Reduction \\(\\mathcal{B}\\) on block length \\([\\,n\\,]\\).",
                    }
                },
                "leanType": "Converter",
            }
        ]
        res_pos_l2 = run_check("--tier", "authored", str(self.write_json("l2_clean.json", pos_l2)))
        self.assertEqual(res_pos_l2.returncode, 0, msg=res_pos_l2.stdout)

    def test_wave_c_l3_diagrams_l4_sections_and_l5_honest_dispatch(self) -> None:
        # L3 negative: dangling dataKey on inlineMath + raw Lean tokens in every diagramHtml slot
        bad_dk = make_clean_fixture()
        bad_dk["entries"][0]["statement"][0].append(
            {"inlineMath": {"latex": "X"}, "dataKey": "sym.dangling_math_key"}
        )
        res_dk = run_check(str(self.write_json("l3_bad_dk.json", bad_dk)))
        self.assertNotEqual(res_dk.returncode, 0)
        self.assertIn("L3-dangling-key", res_dk.stdout)

        for tok in ("CategoryTheory.", "ConstructiveCryptography.", "SystemAlgebra.", "{real}", "{ideal}"):
            for slot_name, mutator in [
                ("entry", lambda d, t=tok: d["entries"][0].__setitem__("diagramHtml", f"<svg>{t}</svg>")),
                (
                    "calcStep",
                    lambda d, t=tok: d["entries"][0]["proof"][1]["children"][0]["steps"][0]["step"].__setitem__(
                        "diagramHtml", f"<svg>{t}</svg>"
                    ),
                ),
                (
                    "ccDiagram",
                    lambda d, t=tok: d["inspectors"].append(
                        {
                            "key": "sym.diag",
                            "display": "D",
                            "kind": {"ccDiagram": {"summaryLatex": "D", "svgOrHtml": f"<svg>{t}</svg>"}},
                            "leanName": "Test.D",
                            "leanType": "TypedSystem",
                        }
                    ),
                ),
            ]:
                with self.subTest(tok=tok, slot=slot_name):
                    bad = make_clean_fixture()
                    mutator(bad)
                    res = run_check(str(self.write_json("l3_diag.json", bad)))
                    self.assertNotEqual(res.returncode, 0)
                    self.assertIn("L3-diagram-hygiene", res.stdout)

        # L4 negative: sectionTitle with null sectionId + double-numbered sectionTitle + static HTML heading
        bad_sec_id = make_clean_fixture()
        bad_sec_id["entries"][0]["sectionTitle"] = "Section 2.1 — Perfect Security"
        bad_sec_id["entries"][0]["sectionId"] = None
        res_sid = run_check(str(self.write_json("l4_null_sid.json", bad_sec_id)))
        self.assertNotEqual(res_sid.returncode, 0)
        self.assertIn("L4-section-integrity", res_sid.stdout)

        bad_dbl = make_clean_fixture()
        bad_dbl["entries"][0]["sectionTitle"] = "1. Section 2.1 — Perfect Security"
        bad_dbl["entries"][0]["sectionId"] = "sec-1"
        res_dbl = run_check(str(self.write_json("l4_dbl.json", bad_dbl)))
        self.assertNotEqual(res_dbl.returncode, 0)
        self.assertIn("L4-section-integrity", res_dbl.stdout)

        bad_html = self.tmp_path / "l4_bad_heading.html"
        clean_json_str = json.dumps(make_clean_fixture())
        bad_html.write_text(
            "<!doctype html><html><head><style data-cadmo-reader>body{}</style></head><body>"
            "<h2><span>1.</span> Section 2.1 — Perfect Security</h2>"
            "<script data-cadmo-controller>console.log(1)</script>"
            f"<script id='cadmo-document-data'>{clean_json_str}</script></body></html>",
            encoding="utf-8",
        )
        res_html = run_check(str(bad_html))
        self.assertNotEqual(res_html.returncode, 0)
        self.assertIn("L4-section-integrity", res_html.stdout)

        # L4 positive: clean sectionTitle + non-null sectionId passes
        pos_sec = make_clean_fixture()
        pos_sec["entries"][0]["sectionTitle"] = "Section 2.1 — Perfect Security"
        pos_sec["entries"][0]["sectionId"] = "sec-1"
        self.assertEqual(run_check("--tier", "authored", str(self.write_json("l4_clean.json", pos_sec))).returncode, 0)

        # L5 negative: "by elementary algebra" on \simeq / \approx / \preceq
        for rel in ("\\simeq_{\\varepsilon}", "\\approx_{\\delta}", "\\preceq"):
            with self.subTest(rel=rel):
                bad_l5 = make_clean_fixture()
                st = bad_l5["entries"][0]["proof"][1]["children"][0]["steps"][0]["step"]
                st["relationLatex"] = rel
                st["reason"] = [{"text": {"value": "by elementary algebra"}}]
                res_l5 = run_check(str(self.write_json("l5_bad.json", bad_l5)))
                self.assertNotEqual(res_l5.returncode, 0)
                self.assertIn("L5-honest-dispatch", res_l5.stdout)

        # L5 positive: "by elementary algebra" on "=" is valid
        pos_l5 = make_clean_fixture()
        st_pos = pos_l5["entries"][0]["proof"][1]["children"][0]["steps"][0]["step"]
        st_pos["relationLatex"] = "="
        st_pos["reason"] = [{"text": {"value": "by elementary algebra"}}]
        self.assertEqual(run_check("--tier", "authored", str(self.write_json("l5_ok.json", pos_l5))).returncode, 0)

    def test_wave_c_l6_l7_l8_dag_budget_and_definitions(self) -> None:
        # L6 negative: sibling entry body re-expansion inside children
        def make_two_entry_doc(reexpand: bool, premise_only: bool = False) -> Dict[str, Any]:
            doc = make_clean_fixture()
            sib = copy.deepcopy(doc["entries"][0])
            sib["declaration"] = "Examples.SibLemma"
            sib["title"] = "Sibling Lemma"
            sib["proof"] = [
                {
                    "kind": "step",
                    "id": "sib-internal-1",
                    "content": [{"text": {"value": "Internal sibling lemma proof step with enough length."}}],
                    "children": [],
                    "originDecl": "Examples.InternalSiblingHelper",
                }
            ]
            caller = copy.deepcopy(doc["entries"][0])
            caller["declaration"] = "Examples.CallerTheorem"
            caller["title"] = "Caller Theorem"
            children = []
            if reexpand:
                children = [copy.deepcopy(sib["proof"][0])]
            elif premise_only:
                children = [
                    {
                        "kind": "step",
                        "id": "hyp-prem-0",
                        "content": [{"text": {"value": "This holds by the assumed hypothesis."}}],
                        "children": [],
                        "isWrapper": True,
                    },
                    {
                        "kind": "step",
                        "id": "app-IndependentPremise-1",
                        "content": [{"text": {"value": "Applying independent premise helper establishes the side condition."}}],
                        "originDecl": "Examples.IndependentPremiseHelper",
                        "children": [],
                        "isWrapper": False,
                    },
                ]
            caller["proof"] = [
                {
                    "kind": "step",
                    "id": "call-sib",
                    "content": [{"text": {"value": "Applying Sibling Lemma establishes the bound."}}],
                    "originDecl": "Examples.SibLemma",
                    "children": children,
                }
            ]
            doc["entries"] = [sib, caller]
            return doc

        res_reexp = run_check(str(self.write_json("l6_reexp.json", make_two_entry_doc(reexpand=True))))
        self.assertNotEqual(res_reexp.returncode, 0)
        self.assertIn("L6-sibling-reexpansion", res_reexp.stdout)

        # L6 positive: leaf citation (children=[]) AND call-site premise-only children pass
        self.assertEqual(
            run_check("--tier", "authored", str(self.write_json("l6_leaf.json", make_two_entry_doc(False)))).returncode,
            0,
        )
        self.assertEqual(
            run_check(
                "--tier", "authored", str(self.write_json("l6_prem.json", make_two_entry_doc(False, premise_only=True)))
            ).returncode,
            0,
        )

        # L6 soft budget warning (> 60 nodes in authored) does not fail exit code
        heavy = make_clean_fixture()
        heavy["entries"][0]["proof"] = [
            {
                "kind": "step",
                "id": f"s-{i}",
                "content": [{"text": {"value": f"Distinct independent proof observation number {i}."}}],
                "children": [],
            }
            for i in range(65)
        ]
        res_heavy = run_check("--tier", "authored", "--json-report", str(self.write_json("l6_heavy.json", heavy)))
        self.assertEqual(res_heavy.returncode, 0, msg=res_heavy.stdout)
        parsed_heavy = json.loads(res_heavy.stdout)
        self.assertGreater(parsed_heavy["files"][0]["metrics"]["max_nodes_per_entry"], 60)
        self.assertTrue(any(w["gate"] == "L6-node-budget" for w in parsed_heavy["files"][0]["warnings"]))

        # L7 negative: < 20 entries JSON exceeding 2.5 MB fails L7-payload-budget
        bloated = make_clean_fixture()
        bloated["entries"][0]["proof"][0]["text"] = "Clean prose padding. " + ("x" * (2_700_000))
        res_l7 = run_check(str(self.write_json("l7_bloat.json", bloated)))
        self.assertNotEqual(res_l7.returncode, 0)
        self.assertIn("L7-payload-budget", res_l7.stdout)

        # L8 negative: dslPseudocode with empty body and empty fullSource fails; empty-eq ratio recorded
        bad_dsl = make_clean_fixture()
        bad_dsl["inspectors"][2]["kind"]["dslPseudocode"] = {"header": "Empty", "body": "", "fullSource": ""}
        res_dsl = run_check(str(self.write_json("l8_empty_dsl.json", bad_dsl)))
        self.assertNotEqual(res_dsl.returncode, 0)
        self.assertIn("L8-empty-dsl", res_dsl.stdout)

        metrics_doc = make_clean_fixture()
        metrics_doc["inspectors"][1]["kind"]["mathDefinition"]["equationLatex"] = ""
        res_m = run_check("--json-report", str(self.write_json("l8_metrics.json", metrics_doc)))
        self.assertEqual(res_m.returncode, 0, msg=res_m.stdout)
        m_json = json.loads(res_m.stdout)["files"][0]["metrics"]
        self.assertEqual(m_json["math_def_count"], 1)
        self.assertEqual(m_json["empty_equation_count"], 1)
        self.assertEqual(m_json["empty_equation_ratio"], 1.0)

    def test_wave_c_l9_l10_l11_and_l12_gates(self) -> None:
        # L9a negative: dropped cc_calc step subproof fails in authored, passes in legacy
        bad_cc_calc = make_clean_fixture()
        bad_cc_calc["entries"][0]["proof"].append(
            {
                "kind": "calcChain",
                "id": "vcc-hybrid-chain-2",
                "intro": [{"text": {"value": "Proceeding through the hybrid chain:"}}],
                "steps": [
                    {
                        "step": {
                            "lhsLatex": "H_0",
                            "relationLatex": "=",
                            "rhsLatex": "H_1",
                            "reason": [{"text": {"value": "by isolating the first PRG call"}}],
                        },
                        "children": [],
                    }
                ],
            }
        )
        p_cc_calc = self.write_json("l9_cc_calc.json", bad_cc_calc)
        self.assertEqual(run_check("--tier", "legacy", str(p_cc_calc)).returncode, 0)
        res_cc_calc = run_check("--tier", "authored", str(p_cc_calc))
        self.assertNotEqual(res_cc_calc.returncode, 0)
        self.assertIn("L9-cc-calc-subproof", res_cc_calc.stdout)

        # L9a positive: cc_calc step with children OR trivial reflexivity reason passes authored
        ok_cc_calc = copy.deepcopy(bad_cc_calc)
        ok_cc_calc["entries"][0]["proof"][-1]["steps"][0]["step"]["reason"] = [{"text": {"value": "by reflexivity"}}]
        self.assertEqual(
            run_check("--tier", "authored", str(self.write_json("l9_cc_calc_refl.json", ok_cc_calc))).returncode,
            0,
        )

        # L9b negative: > 10% tautological 1-child leaf toggles fails authored
        taut_doc = make_clean_fixture()
        taut_doc["entries"][0]["proof"] = [
            {
                "kind": "step",
                "id": f"taut-parent-{i}",
                "content": [{"inlineMath": {"latex": f"x_{i} = y_{i}"}}],
                "children": [
                    {
                        "kind": "step",
                        "id": f"taut-child-{i}",
                        "content": [
                            {"text": {"value": "We obtain "}},
                            {"inlineMath": {"latex": f"x_{i} = y_{i}"}},
                            {"text": {"value": "."}},
                        ],
                        "children": [],
                    }
                ],
            }
            for i in range(4)
        ]
        p_taut = self.write_json("l9_taut.json", taut_doc)
        self.assertEqual(run_check("--tier", "legacy", str(p_taut)).returncode, 0)
        res_taut = run_check("--tier", "authored", str(p_taut))
        self.assertNotEqual(res_taut.returncode, 0)
        self.assertIn("L9-tautological-toggles", res_taut.stdout)

        # L10 negative: missing sectionPreludes and ambient fails authored, warns legacy
        no_frame = make_clean_fixture()
        no_frame["entries"][0]["ambient"] = None
        p_noframe = self.write_json("l10_noframe.json", no_frame)
        res_nf_leg = run_check("--tier", "legacy", "--json-report", str(p_noframe))
        self.assertEqual(res_nf_leg.returncode, 0)
        self.assertTrue(any(w["gate"] == "L10-framing" for w in json.loads(res_nf_leg.stdout)["files"][0]["warnings"]))
        res_nf_auth = run_check("--tier", "authored", str(p_noframe))
        self.assertNotEqual(res_nf_auth.returncode, 0)
        self.assertIn("L10-framing", res_nf_auth.stdout)

        # L11 negatives (all tiers): jargon subtitles, \text{let } this, by dite
        for field_val in [
            "Generic informalization of Foo.lean",
            "Contains cc_calc trace",
            "Verbose-CC Benchmark",
            "Expr.mdata decompiler",
            "ContextProfile lattice",
            "Zero per-theorem overlays",
        ]:
            for tier in ("legacy", "authored"):
                with self.subTest(subtitle=field_val, tier=tier):
                    bad = make_clean_fixture()
                    bad["subtitle"] = field_val
                    res = run_check("--tier", tier, str(self.write_json("l11_sub.json", bad)))
                    self.assertNotEqual(res.returncode, 0)
                    self.assertIn("L11-clean-prose", res.stdout)

        for math_leak in ["\\text{let } this = x \\text{ in } x", "by dite"]:
            for tier in ("legacy", "authored"):
                with self.subTest(leak=math_leak, tier=tier):
                    bad = make_clean_fixture()
                    bad["entries"][0]["statement"][0].append({"inlineMath": {"latex": math_leak}})
                    res = run_check("--tier", tier, str(self.write_json("l11_all.json", bad)))
                    self.assertNotEqual(res.returncode, 0)
                    self.assertIn("L11-clean-prose", res.stdout)

        # L11 authored-only failures (legacy warns on .\mathrm{val} & ontology phrases; allows user \text{let })
        for authored_leak, expect_legacy_warn in [
            ("k.\\mathrm{val} = 0", True),
            ("an extended nonnegative real", True),
            ("a finite cryptographic space", True),
            ("a subset with inside interface P", True),
            ("\\text{let } B = q \\text{ in } B", False),
        ]:
            with self.subTest(authored_leak=authored_leak):
                doc = make_clean_fixture()
                doc["entries"][0]["proof"][0]["text"] = f"Check: {authored_leak}."
                p = self.write_json("l11_auth.json", doc)
                res_leg = run_check("--tier", "legacy", "--json-report", str(p))
                self.assertEqual(res_leg.returncode, 0, msg=res_leg.stdout)
                if expect_legacy_warn:
                    self.assertTrue(
                        any(w["gate"] == "L11-clean-prose" for w in json.loads(res_leg.stdout)["files"][0]["warnings"])
                    )
                res_auth = run_check("--tier", "authored", str(p))
                self.assertNotEqual(res_auth.returncode, 0)
                self.assertIn("L11-clean-prose", res_auth.stdout)

        # L12 negative: duplicate global display across distinct leanNames fails authored, warns legacy
        dup_disp = make_clean_fixture()
        dup_disp["inspectors"].extend(
            [
                {
                    "key": "sym.hyb.par",
                    "display": "\\mathbf{Hybrid}",
                    "kind": {"mathDefinition": {"equationLatex": "H_1 = 1", "proseSummary": "Parallel hybrid."}},
                    "leanName": "Paper.parallelHybridDist",
                    "leanType": "Dist",
                },
                {
                    "key": "sym.hyb.seq",
                    "display": "\\mathbf{Hybrid}",
                    "kind": {"mathDefinition": {"equationLatex": "H_2 = 2", "proseSummary": "Sequential hybrid."}},
                    "leanName": "Paper.seqHybridDist",
                    "leanType": "Dist",
                },
            ]
        )
        p_l12 = self.write_json("l12_dup.json", dup_disp)
        res_l12_leg = run_check("--tier", "legacy", "--json-report", str(p_l12))
        self.assertEqual(res_l12_leg.returncode, 0)
        self.assertTrue(
            any(w["gate"] == "L12-namespace-collision" for w in json.loads(res_l12_leg.stdout)["files"][0]["warnings"])
        )
        res_l12_auth = run_check("--tier", "authored", str(p_l12))
        self.assertNotEqual(res_l12_auth.returncode, 0)
        self.assertIn("L12-namespace-collision", res_l12_auth.stdout)

        # L12 positive: identical leanName OR polymorphic CC families (Constructs/ConstructsWithin, *.Port) pass authored
        poly_disp = make_clean_fixture()
        poly_disp["inspectors"].extend(
            [
                {
                    "key": "Constructs",
                    "display": "\\xrightarrow{\\pi}",
                    "kind": {"mathDefinition": {"equationLatex": "A \\to B", "proseSummary": "Exact construction."}},
                    "leanName": "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs",
                    "leanType": "Prop",
                },
                {
                    "key": "ConstructsWithin",
                    "display": "\\xrightarrow{\\pi}",
                    "kind": {"mathDefinition": {"equationLatex": "A \\to_{\\varepsilon} B", "proseSummary": "Approx construction."}},
                    "leanName": "ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin",
                    "leanType": "Prop",
                },
                {
                    "key": "Commons.AE.Port",
                    "display": "\\mathrm{Port}",
                    "kind": {"mathDefinition": {"equationLatex": "\\mathrm{Port}", "proseSummary": "AE port."}},
                    "leanName": "Commons.AE.Port",
                    "leanType": "Type",
                },
                {
                    "key": "Commons.Evaluation.Port",
                    "display": "\\mathrm{Port}",
                    "kind": {"mathDefinition": {"equationLatex": "\\mathrm{Port}", "proseSummary": "Eval port."}},
                    "leanName": "Commons.Evaluation.Port",
                    "leanType": "Type",
                },
            ]
        )
        res_poly = run_check("--tier", "authored", str(self.write_json("l12_poly.json", poly_disp)))
        self.assertEqual(res_poly.returncode, 0, msg=res_poly.stdout)

    def test_iter3_math_accents_prose_formatting_and_chrome_suppression(self) -> None:
        # 1. CI linter accepts PreludeBlock kind="setting" (and "motivation")
        doc = make_clean_fixture()
        entry = doc["entries"][0]
        entry["sectionTitle"] = "Authenticated Encryption"
        entry["sectionId"] = "sec-ae"
        entry["sectionContext"] = {
            "sectionId": "sec-ae",
            "sectionNumber": 1,
            "paragraphs": [[{"text": {"value": "Legacy context should be suppressed in JS."}}]],
            "inspectors": [],
        }
        entry["sectionPreludes"] = [
            {
                "id": "pre-setting",
                "kind": "setting",
                "label": "Setting",
                "body": [[{"text": {"value": "Maurer--Renner setting with *perfectly secure* ciphers."}}]],
                "diagramHtml": entry["diagramHtml"],
            },
            {
                "id": "pre-const",
                "kind": "construction",
                "label": "Construction 1",
                "title": "Two-Stage Distinguisher (Maurer--Renner §5)",
                "body": [[{"text": {"value": "**Stage 1:** sample "}}, {"inlineMath": {"latex": "k \\xleftarrow{\\$} \\{0,1\\}^{8r}"}}]],
                "lines": [],
                "rows": [],
                "diagramHtml": entry["diagramHtml"],
            },
        ]
        p_setting = self.write_json("iter3_setting_clean.json", doc)
        for tier in ("legacy", "authored"):
            res = run_check("--tier", tier, str(p_setting))
            self.assertEqual(res.returncode, 0, msg=f"tier={tier}: {res.stdout}\n{res.stderr}")

        # 2. JS renderer checks: missing math commands, accents, emphasis/dashes, and suppression
        js_cmd = find_js_runtime()
        if not js_cmd:
            self.skipTest("No JS runtime (node or jsc) available")

        harness = r"""
        const jsSrc = __JS_SRC__;
        const sampleDoc = __DOC_JSON__;
        class FakeClassList {
          constructor(el) { this.el = el; this._set = new Set(); }
          _syncFromString(str) { this._set = new Set(String(str || '').trim().split(/\s+/).filter(Boolean)); }
          _syncToString() { this.el._className = Array.from(this._set).join(' '); }
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
          set innerHTML(v) { this.childNodes = []; this._innerHTML = String(v || ''); }
          get textContent() {
            if (this.nodeType === 3) return this._text;
            return this.childNodes.map(c => c.textContent).join('');
          }
          set textContent(v) {
            if (this.nodeType === 3) { this._text = String(v || ''); return; }
            this.childNodes = [];
            this._innerHTML = null;
            if (v !== '' && v !== null && v !== undefined) this.appendChild(document.createTextNode(String(v)));
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
          addEventListener() {}
          matchesSelectorOne(sel) {
            sel = sel.trim();
            if (!sel) return false;
            const tokens = sel.match(/(?:^[A-Za-z0-9_-]+|\.[A-Za-z0-9_-]+|\[[^\]]+\])/g);
            if (!tokens || tokens.join('') !== sel) return false;
            return tokens.every(tok => {
              if (tok.startsWith('[')) {
                const inner = tok.slice(1, -1);
                const eq = inner.indexOf('=');
                if (eq >= 0) {
                  return this.getAttribute(inner.slice(0, eq).trim()) === inner.slice(eq + 1).trim().replace(/^["']|["']$/g, '');
                }
                return this.hasAttribute(inner);
              }
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
            const parts = selectorList.split(',').map(s => s.trim()).filter(Boolean);
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
        sampleDoc.subtitle = 'Maurer--Renner simulator witnesses';
        dataEl.textContent = JSON.stringify(sampleDoc);
        eval(jsSrc);
        const H = globalThis.__cadmoHelpers;
        function assert(cond, msg) { if (!cond) throw new Error('ASSERT FAILED: ' + msg); }

        // (a) Missing LaTeX commands & stacked arrows
        const symsWrap = document.createElement('span');
        symsWrap.appendChild(H.renderMathNodes("\\pi' \\triangleright E,\\; (H \\triangleleft \\sigma)S,\\; (\\Phi, \\bullet, \\parallel, \\circ),\\; A \\setminus B,\\; \\bigsqcup_i \\sqcup X_i,\\; a \\leftarrow b"));
        const symsTxt = symsWrap.textContent;
        assert(symsTxt.includes('▷') && !symsTxt.includes('triangleright'), 'triangleright -> ▷: ' + symsTxt);
        assert(symsTxt.includes('◁') && !symsTxt.includes('triangleleft'), 'triangleleft -> ◁: ' + symsTxt);
        assert(symsTxt.includes('•') && !symsTxt.includes('bullet'), 'bullet -> •: ' + symsTxt);
        assert(symsTxt.includes('∘') && symsTxt.includes('∖') && symsTxt.includes('⊔') && symsTxt.includes('←'), 'circ/setminus/sqcup/leftarrow');

        const xarrWrap = document.createElement('span');
        xarrWrap.appendChild(H.renderMathNodes('k \\xleftarrow{\\$} \\{0,1\\}^{8r},\\; A \\xleftarrow[D]{\\$} B,\\; \\mathbf{R} \\xrightarrow{\\pi} \\mathbf{S}'));
        const xarrows = xarrWrap.querySelectorAll('.cadmo-xarrow');
        assert(xarrows.length === 3, '3 stacked xarrows rendered');
        assert(!xarrWrap.textContent.includes('xleftarrow') && !xarrWrap.textContent.includes('xrightarrow'), 'no literal arrow cmd');
        assert(xarrows[0].querySelector('.cadmo-xarrow-top').textContent === '$', 'xleftarrow{$} top is $');
        assert(xarrows[0].querySelector('.cadmo-xarrow-mid').textContent === '←', 'xleftarrow mid is ←');
        assert(xarrows[1].querySelector('.cadmo-xarrow-bot').textContent === 'D', 'xleftarrow[D]{$} bot is D');
        assert(xarrows[2].querySelector('.cadmo-xarrow-mid').textContent === '→', 'xrightarrow mid is →');

        // (b) Accent rendering & font-aware hover matching on \hat{\mathbf{G}}
        const accWrap = document.createElement('span');
        accWrap.appendChild(H.renderMathNodes('\\hat{\\mathbf{G}} + \\hat{\\mathbf{S}} + \\tilde{z} + \\overline{Z}'));
        const accEls = accWrap.querySelectorAll('.cadmo-accent');
        assert(accEls.length === 4, '4 accent nodes');
        assert(accEls[0].classList.contains('cadmo-accent-hat') && accEls[0].querySelector('.cadmo-bf').textContent === 'G', 'hat{mathbf{G}} preserves cadmo-bf inside cadmo-accent-hat');
        assert(accEls[1].classList.contains('cadmo-accent-hat') && accEls[1].querySelector('.cadmo-bf').textContent === 'S', 'hat{mathbf{S}} preserves cadmo-bf');
        assert(accEls[2].classList.contains('cadmo-accent-tilde') && accEls[2].textContent === 'z', 'tilde{z}');
        assert(accEls[3].classList.contains('cadmo-accent-bar') && accEls[3].textContent === 'Z', 'overline{Z}');
        assert(H.normalizeMathToken('\\hat{\\mathbf{G}}') === 'bf:G', 'normalizeMathToken(\\hat{\\mathbf{G}}) === bf:G');
        const gScope = H.buildTokenScope([{ key: 'param:G', display: '\\hat{\\mathbf{G}}' }], [], [], null, [], false);
        H.annotateOfflineMathContainer(accWrap, gScope);
        const gRefs = accWrap.querySelectorAll('.cadmo-ref');
        assert(gRefs.length === 1 && gRefs[0].dataset.cadmoToken === 'bf:G', '\\hat{\\mathbf{G}} annotated with bf:G');

        // (c) Inline emphasis, stray-* preservation, and en/em dashes
        const proseNode = H.renderMixedText('A cipher is *perfectly secure* with **Stage 1:** in Maurer--Renner (200--n) and B* and C* and 2 * 3 + 4 * 5 --- end $S^*$');
        const ems = proseNode.querySelectorAll('em');
        const strongs = proseNode.querySelectorAll('strong');
        assert(ems.length === 1 && ems[0].textContent === 'perfectly secure', 'only balanced *italics* matched, got ' + ems.length);
        assert(strongs.length === 1 && strongs[0].textContent === 'Stage 1:', 'balanced **bold** matched');
        assert(proseNode.textContent.includes('Maurer\u2013Renner'), 'en-dash in Maurer--Renner');
        assert(proseNode.textContent.includes('(200\u2013n)'), 'en-dash in (200--n)');
        assert(proseNode.textContent.includes('B* and C*'), 'stray B* and C* untouched');
        assert(proseNode.textContent.includes('2 * 3 + 4 * 5'), 'arithmetic * untouched');
        assert(proseNode.textContent.includes('\u2014 end'), 'em-dash --- converted');
        const dashOnly = H.renderMixedText('--');
        assert(dashOnly.textContent === '\u2013', 'standalone -- inline converted to en-dash');

        // (d) Subtitle dash, legacy SECTION CONTEXT. suppression on setting prelude, and duplicate SYSTEM FIGURE suppression
        assert(rootEl.querySelector('.cadmo-doc-subtitle').textContent === 'Maurer\u2013Renner simulator witnesses', 'subtitle dashes converted');
        assert(rootEl.querySelector('.cadmo-section-context') === null, 'SECTION CONTEXT. suppressed when section has setting prelude');
        assert(rootEl.querySelectorAll('.cadmo-prelude-diagram').length === 0, 'redundant prelude SYSTEM FIGURE suppressed on setting and matching construction');
        assert(rootEl.querySelectorAll('.cadmo-entry-diagram').length === 1, 'entry SYSTEM FIGURE still mounted');

        print('ITER3_JS_TESTS_OK');
        """
        js_src = CADMO_READER_JS.read_text(encoding="utf-8")
        full_js = (
            "if (typeof print === 'undefined') { globalThis.print = console.log; }\n"
            + harness.replace("__JS_SRC__", json.dumps(js_src)).replace("__DOC_JSON__", json.dumps(doc))
        )
        script_path = self.tmp_path / "test_iter3_js.js"
        script_path.write_text(full_js, encoding="utf-8")
        res_js = subprocess.run([*js_cmd, str(script_path)], capture_output=True, text=True)
        self.assertEqual(res_js.returncode, 0, msg=res_js.stdout + res_js.stderr)
        self.assertIn("ITER3_JS_TESTS_OK", res_js.stdout)

        # 3. CSS checks: empty TOC + single header rule + Paper-mode calm inline vars + accent/xarrow styles
        css_txt = CADMO_READER_CSS.read_text(encoding="utf-8")
        for req_css in [
            ".cadmo-toc:empty",
            ".cadmo-doc-header + .cadmo-section-head",
            ".cadmo-accent-hat::before",
            ".cadmo-xarrow",
            "border-bottom: 1px dotted transparent",
            '[data-mode="auditor"] .cadmo-ref',
        ]:
            self.assertIn(req_css, css_txt)

    def test_iter4_tilde_underline_primes_hat_display_and_audit_regex(self) -> None:
        js_cmd = find_js_runtime()
        if not js_cmd:
            self.skipTest("No JS runtime (node or jsc) available")

        audit_py_path = REPO_ROOT / "scripts" / "visual_browser_audit.py"
        audit_ns: Dict[str, Any] = {}
        audit_src = audit_py_path.read_text(encoding="utf-8")
        # Extract AUDIT_JS string safely via AST without importing/running main
        import ast
        tree = ast.parse(audit_src, filename=str(audit_py_path))
        audit_js = None
        for node in tree.body:
            if isinstance(node, ast.Assign):
                for tgt in node.targets:
                    if isinstance(tgt, ast.Name) and tgt.id == "AUDIT_JS":
                        audit_js = ast.literal_eval(node.value)
        self.assertIsInstance(audit_js, str)

        harness = r"""
        const jsSrc = __JS_SRC__;
        const auditJs = __AUDIT_JS__;
        class FakeClassList {
          constructor(el) { this.el = el; this._set = new Set(); }
          _syncFromString(str) { this._set = new Set(String(str || '').trim().split(/\s+/).filter(Boolean)); }
          _syncToString() { this.el._className = Array.from(this._set).join(' '); }
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
          get nodeValue() { return this.nodeType === 3 ? this._text : null; }
          get textContent() {
            if (this.nodeType === 3) return this._text;
            return this.childNodes.map(c => c.textContent).join('');
          }
          set textContent(v) {
            if (this.nodeType === 3) { this._text = String(v || ''); return; }
            this.childNodes = [];
            if (v !== '' && v !== null && v !== undefined) this.appendChild(document.createTextNode(String(v)));
          }
          get innerText() { return this.textContent; }
          cloneNode(deep = false) {
            const copy = new FakeNode(this.nodeType, this.tagName);
            copy._text = this._text;
            copy.attrs = { ...this.attrs };
            copy.dataset = { ...this.dataset };
            copy.className = this._className;
            if (deep) {
              for (const ch of this.childNodes) copy.appendChild(ch.cloneNode(true));
            }
            return copy;
          }
          remove() {
            if (this.parentNode) this.parentNode.removeChild(this);
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
          addEventListener() {}
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
            const parts = selectorList.split(',').map(s => s.trim()).filter(Boolean);
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

        const docEl = new FakeNode(1, 'html');
        docEl.scrollWidth = 1000;
        docEl.clientWidth = 1000;
        const bodyEl = new FakeNode(1, 'body');
        const mainEl = new FakeNode(1, 'main');
        mainEl.className = 'cadmo-main';
        bodyEl.appendChild(mainEl);

        globalThis.document = {
          documentElement: docEl,
          body: bodyEl,
          getElementById: () => null,
          createElement: (tag) => new FakeNode(1, tag),
          createTextNode: (txt) => { const n = new FakeNode(3); n._text = String(txt || ''); return n; },
          createDocumentFragment: () => new FakeNode(11),
          addEventListener: () => {},
          querySelectorAll: (sel) => bodyEl.querySelectorAll(sel),
          querySelector: (sel) => bodyEl.querySelector(sel)
        };
        globalThis.window = globalThis;
        eval(jsSrc);
        const H = globalThis.__cadmoHelpers;
        function assert(cond, msg) { if (!cond) throw new Error('ASSERT FAILED: ' + msg); }

        // 1. LaTeX ~ non-breaking space conversion in prose
        const refProse = H.renderMixedText(
          'See Proposition~1, Lemma~4, Distinguisher~1, Theorem~1, Section~2, Table~1, Definition~2.1, Eq.~(1), Section~$2$, and Lemma~\\(4\\).'
        );
        const refText = refProse.textContent;
        assert(!refText.includes('~'), 'No literal ~ in ref prose: ' + refText);
        assert(refText.includes('Proposition\u00A01'), 'Proposition~1 -> NBSP');
        assert(refText.includes('Lemma\u00A04'), 'Lemma~4 -> NBSP');
        assert(refText.includes('Distinguisher\u00A01'), 'Distinguisher~1 -> NBSP');
        assert(refText.includes('Theorem\u00A01'), 'Theorem~1 -> NBSP');
        assert(refText.includes('Section\u00A02'), 'Section~2 -> NBSP');
        assert(refText.includes('Table\u00A01'), 'Table~1 -> NBSP');
        assert(refText.includes('Definition\u00A02.1'), 'Definition~2.1 -> NBSP');
        assert(refText.includes('Eq.\u00A0(1)'), 'Eq.~(1) -> NBSP');
        assert(refText.includes('Section\u00A02'), 'Section~$2$ -> NBSP');
        assert(refText.includes('Lemma\u00A04.'), 'Lemma~\\(4\\) -> NBSP');

        const safeTilde = H.renderMixedText('Sampling a ~ X and b ~ Y, ~10, and https://example.com/~alice, plus $a ~ b$.');
        assert(safeTilde.textContent.includes('a ~ X and b ~ Y'), 'standalone a ~ X preserved');
        assert(safeTilde.textContent.includes('~10'), 'prefix ~10 preserved');
        assert(safeTilde.textContent.includes('https://example.com/~alice'), 'URL ~ preserved');
        assert(!safeTilde.textContent.includes('\u00A0'), 'no spurious NBSP on standalone ~ or math ~');

        // 2. \underline{d} in renderMathNodes
        const underWrap = document.createElement('span');
        underWrap.className = 'cadmo-math';
        underWrap.appendChild(H.renderMathNodes('1/D^{\\underline{d}} + \\underline{\\mathbf{x} + 1}'));
        const uSpans = underWrap.querySelectorAll('.cadmo-math-underline');
        assert(uSpans.length === 2, 'expected 2 .cadmo-math-underline spans, got ' + uSpans.length);
        assert(uSpans[0].closest('sup') !== null, '\\underline{d} stays inside <sup>');
        assert(uSpans[0].textContent === 'd', 'first underline arg is d');
        assert(uSpans[1].querySelector('.cadmo-bf').textContent === 'x', 'recursive renderMathNodes inside \\underline');
        assert(!/underline/i.test(underWrap.textContent), 'must not render literal underline/underlined: ' + underWrap.textContent);
        assert(H.normalizeMathToken('\\underline{d}') === 'd', 'normalizeMathToken strips \\underline');

        // 3. Consecutive primes H, H', H'', H'''
        const primeWrap = document.createElement('span');
        primeWrap.className = 'cadmo-math';
        primeWrap.appendChild(H.renderMathNodes("H, H', H'', H'''"));
        assert(primeWrap.textContent === 'H, H\u2032, H\u2033, H\u2034', 'primes render cleanly: ' + primeWrap.textContent);
        const primeScope = H.buildTokenScope([
          { key: 'p:H', display: 'H' },
          { key: 'p:Hp', display: "H'" },
          { key: 'p:Hpp', display: "H''" }
        ], [], [], null, [], false);
        H.annotateOfflineMathContainer(primeWrap, primeScope);
        const primeRefs = primeWrap.querySelectorAll('.cadmo-ref');
        assert(primeRefs.length === 3, 'H, H\', H\'\' annotated separately, got ' + primeRefs.length);
        assert(primeRefs[0].dataset.cadmoToken === 'H', 'first ref is H');
        assert(primeRefs[1].dataset.cadmoToken === "H'", "second ref is H'");
        assert(primeRefs[2].dataset.cadmoToken === "H''", "third ref is H''");

        // 4. \hat{\mathbf{G}}^{-} inside displayMath
        const dispScope = H.buildTokenScope([{ key: 'param:G', display: '\\hat{\\mathbf{G}}' }], [], [], null, [], false);
        const dispEl = H.renderInline({
          displayMath: { latex: '\\Delta^{D}(\\alpha\\,\\hat{\\mathbf{G}}^{-}, \\alpha\\,\\mathbf{T}) \\le \\varepsilon', punct: '.' }
        }, dispScope);
        assert(dispEl.classList.contains('cadmo-display-math'), 'displayMath renders .cadmo-display-math');
        const dispHat = dispEl.querySelector('.cadmo-accent.cadmo-accent-hat');
        assert(dispHat !== null, 'displayMath contains .cadmo-accent.cadmo-accent-hat');
        assert(dispHat.querySelector('.cadmo-bf').textContent === 'G', 'hat wraps \\mathbf{G}');
        const dispRef = dispHat.closest('.cadmo-ref');
        assert(dispRef !== null && dispRef.dataset.cadmoToken === 'bf:G', 'displayMath hat G annotated with bf:G');

        // 5. visual_browser_audit.py AUDIT_JS regex checks
        function runAuditOnParagraphs(paraSpecs) {
          mainEl.childNodes = [];
          for (const spec of paraSpecs) {
            const p = document.createElement('p');
            if (spec.mathText !== undefined) {
              const m = document.createElement('span');
              m.className = 'cadmo-math';
              m.textContent = spec.mathText;
              p.appendChild(m);
            } else {
              p.textContent = spec.text;
            }
            mainEl.appendChild(p);
          }
          return eval(auditJs);
        }

        const cleanBot = runAuditOnParagraphs([
          { text: 'On a fresh query, Ideal returns ⊥, outputs ⊥, dec(c) = ⊥, dec(c) ≠ ⊥, c ↦ ⊥, or returns (⊥) and M ∪ {⊥}.' }
        ]);
        assert(cleanBot.proseIssues.length === 0, 'legitimate crypto rejection ⊥ must pass, got: ' + JSON.stringify(cleanBot.proseIssues));

        for (const badBot of [
          'By hypothesis, ⊥.',
          'This gives ⊥.',
          'Which yields ⊥.',
          'We derive ⊥.',
          'If (h : ⊥) then false.'
        ]) {
          const rep = runAuditOnParagraphs([{ text: badBot }]);
          assert(rep.proseIssues.some(x => x.rule === 'raw-lean-ast-leak'), 'must flag Lean falsum: ' + badBot);
        }

        const underRep1 = runAuditOnParagraphs([{ text: 'Bound is 1/Dunderlined here.' }]);
        assert(underRep1.proseIssues.some(x => x.rule === 'unrendered-underline'), 'must flag Dunderlined');

        const underRep2 = runAuditOnParagraphs([{ mathText: 'underline d' }]);
        assert(underRep2.proseIssues.some(x => x.rule === 'unrendered-underline'), 'must flag underline in math');

        for (const badTilde of ['See Proposition~1.', 'By Lemma~4.', 'In Distinguisher~1.', 'By Theorem~1.']) {
          const rep = runAuditOnParagraphs([{ text: badTilde }]);
          assert(rep.proseIssues.some(x => x.rule === 'literal-latex-tilde-ref'), 'must flag tilde ref: ' + badTilde);
        }

        const notMemRep = runAuditOnParagraphs([{ text: 'For every τ, if ¬ (τ ∈ T_bad), then bound holds.' }]);
        assert(notMemRep.proseIssues.some(x => x.rule === 'raw-negated-membership'), 'must flag ¬ (τ ∈ S)');

        print('ITER4_JS_TESTS_OK');
        """
        js_src = CADMO_READER_JS.read_text(encoding="utf-8")
        full_js = (
            "if (typeof print === 'undefined') { globalThis.print = console.log; }\n"
            + harness.replace("__JS_SRC__", json.dumps(js_src)).replace("__AUDIT_JS__", json.dumps(audit_js))
        )
        script_path = self.tmp_path / "test_iter4_js.js"
        script_path.write_text(full_js, encoding="utf-8")
        res = subprocess.run([*js_cmd, str(script_path)], capture_output=True, text=True)
        self.assertEqual(res.returncode, 0, msg=res.stdout + res.stderr)
        self.assertIn("ITER4_JS_TESTS_OK", res.stdout)

        # Verify CSS rules for .cadmo-math-underline and .cadmo-display-math vertical padding
        css_txt = CADMO_READER_CSS.read_text(encoding="utf-8")
        self.assertIn(".cadmo-math-underline", css_txt)
        self.assertIn("padding: 0.45em 0 0.22em", css_txt)


if __name__ == "__main__":
    unittest.main(verbosity=2)
