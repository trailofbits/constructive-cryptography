module

public import Probability.Kernel
public import RandomSystems.Typed.Functional

/-!
# Retained sampling through typed operations

A draw `k ← P` is retained throughout the interaction. Normalized laws pass directly to
`TypedSystem.sample`. Attaching `α` sends every inside query
to the same `R k`, and sampling `f(P)` is sampling `P`
and keeping `R (f k)`, for any map `f`, injective or not, and any probability law `P`.
-/

@[expose] public section

open Probability SystemAlgebra

example {A B : Interface} (α : TypedConverter A B) (R : Bool → TypedSystem B) :
    α • TypedSystem.sample 𝒰[Bool] R =
      TypedSystem.sample 𝒰[Bool] (fun b => α • R b) :=
  TypedConverter.smul_sample α _ R

example {A : Interface} (R : Bool → TypedSystem A) :
    TypedSystem.sample (Distribution.ProbDist.map not 𝒰[Bool]) R =
      TypedSystem.sample 𝒰[Bool] (fun b => R (not b)) :=
  TypedSystem.sample_fTransform not _ R

/-- A constant map merges both Boolean sample values into one value. -/
example {A : Interface} (R : Unit → TypedSystem A) :
    TypedSystem.sample (Distribution.ProbDist.map (fun _ : Bool => ()) 𝒰[Bool]) R =
      TypedSystem.sample 𝒰[Bool] (fun _ : Bool => R ()) :=
  TypedSystem.sample_fTransform (fun _ : Bool => ()) _ R

/-- A map-first call works for an arbitrary probability law, without assuming uniformity. -/
example {A : Interface} (f : Bool → Bool) (P : Distribution Bool)
    [Distribution.IsProbability P] (R : Bool → TypedSystem A) :
    TypedSystem.sample (Distribution.fTransform f P) R =
      TypedSystem.sample P (fun k => R (f k)) :=
  TypedSystem.sample_fTransform f P R
