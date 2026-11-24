import Tests.Rendering.Labels

/-! Interface domains, dependent alphabets and hover/navigation in the actual infoview. -/

set_option linter.hashCommand false

open SystemAlgebra DSLExamples CategoryTheory

#cc_diagram_show Counter (budget := 3)
#cc_diagram_show BoundedCounter 7 (budget := 2)
#cc_diagram_show WriteThrough (budget := 3)
#cc_diagram_show FirstRequests 2 (budget := 5)
#cc_diagram_show Counter.perPort (budget := fun i => match i with | .next => 2 | .read => 5)
#cc_diagram_show DSLTests.ParallelOutside.Forward (budget := (2, 5)) •
  DSLTests.ParallelOutside.EmptyCell
    (budget := DSLTests.ParallelOutside.Forward.bound * (2 + 5))
#cc_diagram_show TypedSystem.parallel (FreshBits (budget := 0)) (SecretBit (budget := 4))

attribute [local cc_diagram "SB"] Rendering.PseudocodeTests.aliasOfSecret
#cc_diagram_show Rendering.PseudocodeTests.aliasOfSecret
#cc_diagram_show 𝟙 (Rendering.InterfaceInfoTests.HigherOrder 2)
#cc_diagram_show 𝟙 Interface.unit
#cc_diagram_show Rendering.PseudocodeTests.«σ with spaces» (budget := 2)

section Abstract
variable {C : Type} [Category C] {Phi : C → Type}
  [ConstructiveCryptography.ResourceTheory C Phi]
variable {A B : C} (c : A ⟶ B) (R : Phi B)
#cc_diagram_show c • R
end Abstract

section Symbolic
variable {A B : Interface} (c : A ⟶ B) (R : TypedSystem B)
#cc_diagram_show c • R
end Symbolic

#cc_diagram_show 𝟙 (Rendering.InterfaceInfoTests.StructuredAlphabet 2)

#cc_diagram_show 𝟙 (Interface.tensor
  (Interface.queryBudget Counter.Port Counter.Input Counter.Output 3) (Cache 3))

assert_display Rendering.LabelTests.exportedLabelTarget as "Seventeen"

section DisplayNames
local cc_diagram_name "Counter₃" := Counter (budget := 3)
local cc_diagram_name "I₃" :=
  Interface.queryBudget Counter.Port Counter.Input Counter.Output 3
attribute [local cc_diagram "BC"] BoundedCounter
#cc_diagram_show Counter (budget := 3)
#cc_diagram_show Counter (budget := 4)
#cc_diagram_show BoundedCounter 7 (budget := 2)
#cc_diagram_show 𝟙
  (Interface.queryBudget Counter.Port Counter.Input Counter.Output 3) • Counter (budget := 3)
local cc_diagram_name "Counter pass-through" := 𝟙
  (Interface.queryBudget Counter.Port Counter.Input Counter.Output 3) • Counter (budget := 3)
#cc_diagram_show 𝟙
  (Interface.queryBudget Counter.Port Counter.Input Counter.Output 3) • Counter (budget := 3)
local cc_diagram_name "Independent bits" :=
  TypedSystem.parallel (FreshBits (budget := 3)) (SecretBit (budget := 3))
#cc_diagram_show TypedSystem.parallel (FreshBits (budget := 3)) (SecretBit (budget := 3))
local cc_diagram_name "Identity pair" := (𝟙 (Cache 3)) ≫ (𝟙 (Cache 3))
#cc_diagram_show (𝟙 (Cache 3)) ≫ (𝟙 (Cache 3))
attribute [local cc_diagram "CacheI"] Cache
#cc_diagram_show 𝟙 (Interface.tensor (Cache 3) (Cache 4))
#cc_diagram_show 𝟙 (Interface.tensor
  (Interface.queryBudget Counter.Port Counter.Input Counter.Output 3) (Cache 3))
end DisplayNames
