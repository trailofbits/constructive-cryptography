/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Informalization.Grammar
import Informalization.ExprLatex
import Informalization.Semantics.IR
import Informalization.Semantics.LanguageDesign
import Informalization.Semantics.Registry
import Informalization.Semantics.Canonical
import Informalization.Semantics.CanonicalRandomSystems
import Informalization.Semantics.CBC
import Informalization.Semantics.ProofEvidence
import Informalization.Semantics.CanonicalProof
import Informalization.Semantics.EvidenceCompression
import Informalization.Semantics.Symbols
import Informalization.Semantics.Plan
import Informalization.Semantics.Discourse
import Informalization.Semantics.Realize
import Informalization.Semantics.Validation
import Informalization.Semantics.Report
import Informalization.MassotMiller
import Informalization.MassotMiller.Hover
import Informalization.MassotMiller.InfoTree
import Informalization.MassotMiller.Ontology
import Informalization.MassotMiller.English
import Informalization.MassotMiller.Decompiler
import Informalization.MassotMiller.Describe
import Informalization.MassotMillerWeb

/-! # Generic Lean informalization backend -/
