/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Attr.Register

/-- `dist_simp` is a curated simp set for distribution normalization.
Use as `simp only [dist_simp]`. -/
register_simp_attr dist_simp
