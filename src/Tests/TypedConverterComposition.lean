import RandomSystems.Typed.Interface

/-!
# Direct and serial converter certificates

The trimmed serial wiring of `α` (outside, bound `2`) and `β` (inside, bound `3`), certified
directly with bound `7` rather than the product `3 * 2`, is the typed composition of `α` and `β`.
-/

open SystemAlgebra

/-- The direct bound `7` differs from the serial bound `3 * 2`. -/
example {A B C : Interface}
    {α : InsideOutsideSystem A.I B.I A.X A.Y B.X B.Y}
    {β : InsideOutsideSystem B.I C.I B.X B.Y C.X C.Y}
    (hα : IsDDCFrom B.domain A.domain 2 α)
    (hβ : IsDDCFrom C.domain B.domain 3 β)
    (hγ : IsDDCFrom C.domain A.domain 7 (trim (serialM α β))) :
    TypedConverter.ofDDC (trim (serialM α β)) hγ =
      TypedConverter.comp (TypedConverter.ofDDC α hα) (TypedConverter.ofDDC β hβ) :=
  TypedConverter.ofDDC_eq_comp hα hβ hγ rfl
