/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import AbstractCryptography

/-!
# Constructive-cryptography use of the selected AC surface

This non-default smoke test expresses Maurer11 Definition 3's availability and
security inequalities as two selected construction judgments.  The four tuple
converters are already assembled, so the test checks the AC/CC boundary without
enumerating or hard-coding an interface type.
-/

open AbstractCryptography
open scoped AbstractCryptography

namespace ConstructiveCryptography.SelectedSurface.Tests

universe u v w

variable {I : Type u} {Γ : I → Type v} {Φ : Type w}
variable [∀ i, Monoid (Γ i)] [MulAction (∀ i, Γ i) Φ]
variable [PseudoEMetricSpace Φ]

example {availableReal adversarialReal idealBottom simulator : ∀ i, Γ i}
    {R S : Φ} {eps : ENNReal}
    (havailable : edist (availableReal • R) (idealBottom • S) ≤ eps)
    (hsecurity : edist (adversarialReal • R) (simulator • S) ≤ eps) :
    (({R} : Set Φ) —[availableReal]→
        Relaxation.epsilonRelaxation eps ({idealBottom • S} : Set Φ)) ∧
      (({R} : Set Φ) —[adversarialReal]→
        Relaxation.epsilonRelaxation eps ({simulator • S} : Set Φ)) := by
  constructor
  · ac_construct using havailable
  · ac_construct using hsecurity

end ConstructiveCryptography.SelectedSurface.Tests
