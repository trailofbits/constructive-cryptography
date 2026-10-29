import RandomSystems.Typed.Functional

/-!
# Retained sampling through typed operations

One sample `k ← P` is drawn before the interaction and retained, never redrawn per query:
attaching `α` sends every inside query to the same `R k`, and sampling `f(P)` is sampling `P`
and keeping `R (f k)`, for any map `f`, injective or not, and any probability law `P`.
-/

open Probability SystemAlgebra

example {A B : Interface} (α : TypedConverter A B) (R : Bool → TypedSystem B) :
    α • TypedSystem.sample (𝒰[Bool]).1 R =
      TypedSystem.sample (𝒰[Bool]).1 (fun b => α • R b) :=
  TypedConverter.smul_sample α _ R

example {A : Interface} (R : Bool → TypedSystem A) :
    TypedSystem.sample (Distribution.fTransform not (𝒰[Bool]).1) R =
      TypedSystem.sample (𝒰[Bool]).1 (fun b => R (not b)) :=
  TypedSystem.sample_fTransform not _ R

/-- A constant map merges both Boolean sample values into one value. -/
example {A : Interface} (R : Unit → TypedSystem A) :
    TypedSystem.sample (Distribution.fTransform (fun _ : Bool => ()) (𝒰[Bool]).1) R =
      TypedSystem.sample (𝒰[Bool]).1 (fun _ => R ()) :=
  TypedSystem.sample_fTransform (fun _ : Bool => ()) _ R

/-- A map-first call works for an arbitrary probability law, without assuming uniformity. -/
example {A : Interface} (f : Bool → Bool) (P : Distribution Bool)
    [Distribution.IsProbability P] (R : Bool → TypedSystem A) :
    TypedSystem.sample (Distribution.fTransform f P) R =
      TypedSystem.sample P (fun k => R (f k)) :=
  TypedSystem.sample_fTransform f P R
