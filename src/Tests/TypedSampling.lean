import RandomSystems.Typed.Functional

/-!
# Retained sampling through typed operations

The same Boolean choice is used in each attached system and in each transformed system.
-/

open Probability SystemAlgebra

example {A B : Interface} (α : TypedConverter A B) (R : Bool → TypedSystem B) :
    α • TypedSystem.sample (𝒰[Bool]).1 R =
      TypedSystem.sample (𝒰[Bool]).1 (fun b => α • R b) :=
  TypedConverter.smul_sample α _ R

example {A : Interface} (R : Bool → TypedSystem A) :
    TypedSystem.sample (Distribution.fTransform not (𝒰[Bool]).1) R =
      TypedSystem.sample (𝒰[Bool]).1 (fun b => R (not b)) :=
  TypedSystem.sample_fTransform _ not R
