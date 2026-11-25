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
                                    {"text": {"value": "By the triangle inequality for distinguishing distance, we obtain:"}}
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
                        [{"inlineMath": {"latex": "\\mathrm{supportedSponge}(p)"}}]
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


if __name__ == "__main__":
    unittest.main(verbosity=2)
