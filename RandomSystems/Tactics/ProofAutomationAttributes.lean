/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Attr.Register

/-!
# Random Systems proof-automation attributes

The attributes live in a dependency-free registration module so Random
Systems declarations can register exact normalization and structural closure
facts without importing the tactic implementation.
-/

/-- Terminating equations that put Random Systems expressions into their
documented normal form. -/
register_simp_attr rs_normalization

/-- Probability-law and common-domain closure facts for standard Random
Systems constructors. -/
register_simp_attr rs_side_condition
