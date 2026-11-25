/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.Core.Spine
import Informalization.Verbose.Trace
import Informalization.Verbose.ProseInterp
import Informalization.Verbose.Syntax

/-!
# Verbose Constructive Cryptography Authoring Layer

Exports:
* `Informalization.Verbose.Trace`: zero-cost `Expr.mdata` trace tags and the priority-500
  `ProofGraph.RuleExplainer` rendering Verbose-CC proofs in Ueli Maurer's voice;
* `Informalization.Verbose.Syntax`: `scoped` controlled natural-language tactics under
  `namespace VerboseCC` (`open scoped VerboseCC`).
-/
