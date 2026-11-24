import Rendering.Widget
import Rendering.Export

/-! Representative diagrams for visual inspection. Open any command in the
Lean infoview. The terms use only the public, carrier-independent CC algebra. -/

-- These tests deliberately retain the commands that drive the infoview.
set_option linter.hashCommand false

open CategoryTheory CategoryTheory.MonoidalCategory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra

namespace Rendering.Gallery
variable {C : Type} [Category C] [MonoidalCategory C]
variable {Phi : C → Type} [ResourceTheory C Phi] [CompatiblePseudoMetric C Phi]
variable {A B D E : C}
variable (c : A ⟶ B) (d : B ⟶ D) (e : A ⟶ E)
variable (R : Phi D) (S : Phi E) (T : Phi A)
variable (ε : ENNReal)

#guard_msgs in
#cc_diagram_show c • (d • R)
#guard_msgs in
#cc_diagram_show (attach_serial (Phi := Phi) c d R)
#guard_msgs in
#cc_diagram_show parallel (Phi := Phi) R (parallel (Phi := Phi) S T)
#guard_msgs in
#cc_diagram_show ((d ⊗ₘ e) • parallel (Phi := Phi) R S)
#guard_msgs in
#cc_diagram_show (attach_parallel (Phi := Phi) d e R S)
#guard_msgs in
#cc_diagram_show distance (Phi := Phi) (c • (d • R)) T ≤ ε
#guard_msgs in
#cc_diagram_show Specification.ConstructsWithin (Phi := Phi) d
  ({R} : ConstructiveCryptography.Specification (Phi D))
  ({d • R} : ConstructiveCryptography.Specification (Phi B)) ε

-- Repeated converters, wide labels, escaping, and deeply nested boundaries.
variable (f : A ⟶ A)
variable (resourceWithAnIntentionallyVeryLongNameThatMustRemainFullyReadable : Phi A)
variable («<img src=x onerror=alert(1)>» : Phi A)
#guard_msgs in
#cc_diagram_show f • f • f • f • f • f • T
#guard_msgs in
#cc_diagram_show resourceWithAnIntentionallyVeryLongNameThatMustRemainFullyReadable
#guard_msgs in
#cc_diagram_show «<img src=x onerror=alert(1)>»
#guard_msgs in
#cc_diagram_show parallel (Phi := Phi) (parallel (Phi := Phi) R S)
  (parallel (Phi := Phi) (parallel (Phi := Phi) T T) T)
#guard_msgs in
#cc_diagram_show distance (Phi := Phi) R R = 0
#guard_msgs in
#cc_diagram_show distance (Phi := Phi) R R ≤ (ε + ε + ε)
#guard_msgs in
#cc_diagram_show (c ≫ d)

variable {InterfaceWithAnIntentionallyLongNameThatMustNotBecomeAnAlphabet : C}
variable (longPort : A ⟶ InterfaceWithAnIntentionallyLongNameThatMustNotBecomeAnAlphabet)
variable (longResource : Phi InterfaceWithAnIntentionallyLongNameThatMustNotBecomeAnAlphabet)
#guard_msgs in
#cc_diagram_show longPort • longResource
#guard_msgs in
#cc_diagram_show parallel (Phi := Phi) longResource (parallel (Phi := Phi) T longResource)
#guard_msgs in
#cc_diagram_show dummy (C := C) (Phi := Phi)
#guard_msgs in
#cc_diagram_show distance (Phi := Phi) R R < ε
#guard_msgs in
#cc_diagram_show distance (Phi := Phi) R R ≤ (⊤ : ENNReal)
#guard_msgs in
#cc_diagram_show Specification.Constructs (Phi := Phi) d
  (∅ : ConstructiveCryptography.Specification (Phi D))
  ({d • R} : ConstructiveCryptography.Specification (Phi B))

-- A live tactic goal and a calculation exercise RPC-backed code and navigation.
example : attach (Phi := Phi) (c ≫ d) R = attach c (attach d R) := by
  exact attach_serial c d R

-- A non-CC bookkeeping subgoal must label its enclosing-statement fallback.
example : attach (Phi := Phi) (c ≫ d) R = attach c (attach d R) := by
  have bookkeeping : True := by
    trivial
  exact (fun _ : True => attach_serial c d R) bookkeeping

example : attach (Phi := Phi) (𝟙 D ≫ 𝟙 D) R = R := by
  calc
    attach (Phi := Phi) (𝟙 D ≫ 𝟙 D) R = attach (𝟙 D) (attach (𝟙 D) R) :=
      attach_serial (𝟙 D) (𝟙 D) R
    _ = attach (𝟙 D) R := attach_identity _
    _ = R := attach_identity _

end Rendering.Gallery

namespace Rendering.LiveLabels
variable {C : Type} [Category C] {Phi : C → Type} [ResourceTheory C Phi]
variable {A B : C} (c : A ⟶ B)
variable (resourceWithAnIntentionallyVeryLongNameThatMustRemainFullyReadable : Phi B)

-- InteractiveCode must wrap as safely as the static mathematical label.
example :
    attach c resourceWithAnIntentionallyVeryLongNameThatMustRemainFullyReadable =
    attach c resourceWithAnIntentionallyVeryLongNameThatMustRemainFullyReadable := by
  rfl

end Rendering.LiveLabels
