/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Set.Defs

set_option autoImplicit false

/-!
# Resource specifications

This module owns only the carrier-independent definition of a specification.
Construction, relaxation, metric, and parallel laws belong to their respective
semantic modules.
-/

namespace AbstractCryptography

/-- A specification is the set of resources satisfying it.

Maurer--Renner 2016, Section 2.3 (printed p. 5): “often a specification is
understood as the subset of a universe Φ of objects, namely those that satisfy
the specification.” -/
abbrev Specification (Φ : Type*) := Set Φ

end AbstractCryptography
