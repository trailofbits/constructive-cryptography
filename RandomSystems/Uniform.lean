/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.RandomSystem
import Probability.Counting

/-!
# Uniform fixed-interface random systems

Maurer 2002, Definition 4 (printed p. 7), states: “A uniform random function
(URF) R : X → Y (a uniform random permutation (URP) P on X) is a random
function with uniform distribution over all functions from X to Y
(permutations on X).”  `urf` and `urp` push those finite uniform laws through
`System.functionEvaluator`.

All declarations use finite-support PDSs.  `unif` is the repository-defined
constant-function law.  `finiteBeacon Y n := urf (Fin n) Y` is a finite
round-indexed table; it is not Maurer's unbounded beacon.
-/

namespace RandomSystems

open Probability (Distribution)

universe u v

noncomputable section

namespace PDS

variable {X : Type u} {Y : Type v}

/-! ## The objects -/

/-- Maurer 2002, Definition 4 (printed p. 7): a URF is “a random function with
uniform distribution over all functions from `X` to `Y`.”  The sampled
function is read as a DDS by `System.functionEvaluator`. -/
def urf (X : Type u) (Y : Type v) [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] :
    PDS X Y :=
  Distribution.fTransform System.functionEvaluator (Distribution.uniform (X → Y))

/-- Maurer 2002, Definition 4 (printed p. 7): a URP is a random function with
“uniform distribution over all ... permutations on `X`.” -/
def urp (X : Type u) [Fintype X] [DecidableEq X] : PDS X X :=
  Distribution.fTransform (fun π : Equiv.Perm X => System.functionEvaluator (π : X → X))
    (Distribution.uniform (Equiv.Perm X))

/-- Sample one uniform value and expose it through a constant-function DDS.
Repeated queries receive the sampled value again. -/
def unif (X : Type u) (Y : Type v) [Fintype Y] [Nonempty Y] : PDS X Y :=
  Distribution.fTransform (fun y : Y => System.functionEvaluator (fun _ : X => y))
    (Distribution.uniform Y)

/-- A finite round-indexed table of independent uniform values.  This is the
URF on `Fin n`; it is not Maurer 2002, Definition 4's unbounded beacon. -/
def finiteBeacon (Y : Type v) [Fintype Y] [Nonempty Y] (n : ℕ) :
    PDS (Fin n) Y :=
  urf (Fin n) Y

theorem finiteBeacon_eq_urf (Y : Type v) [Fintype Y] [Nonempty Y] (n : ℕ) :
    finiteBeacon Y n = urf (Fin n) Y := rfl

/-! ## Probability laws -/

theorem isProbDist_urf (X : Type u) (Y : Type v) [Fintype X] [DecidableEq X] [Fintype Y]
    [Nonempty Y] : (urf X Y).isProbDist :=
  Distribution.fTransform_isProbDist _ Distribution.uniform_isProbDist

theorem isProbDist_urp (X : Type u) [Fintype X] [DecidableEq X] : (urp X).isProbDist :=
  Distribution.fTransform_isProbDist _ Distribution.uniform_isProbDist

theorem isProbDist_unif (X : Type u) (Y : Type v) [Fintype Y] [Nonempty Y] :
    (unif X Y).isProbDist :=
  Distribution.fTransform_isProbDist _ Distribution.uniform_isProbDist

theorem isProbDist_finiteBeacon (Y : Type v) [Fintype Y] [Nonempty Y]
    (n : ℕ) : (finiteBeacon Y n).isProbDist :=
  isProbDist_urf (Fin n) Y

/-! ## Common domain -/

/-- Every pushforward of function evaluators has the domain of all nonempty
histories. -/
theorem hasDomain_fTransform_functionEvaluator {A : Type*} (g : A → (X → Y))
    (D : Distribution A) :
    HasDomain (Distribution.fTransform (fun a => System.functionEvaluator (g a)) D)
      {l : List X | l ≠ []} := by
  intro s hs
  obtain ⟨a, -, rfl⟩ := Distribution.exists_mem_support_of_mem_support_fTransform _ _ hs
  exact System.dom_functionEvaluator (g a)

theorem hasDomain_urf (X : Type u) (Y : Type v) [Fintype X] [DecidableEq X] [Fintype Y]
    [Nonempty Y] : HasDomain (urf X Y) {l : List X | l ≠ []} :=
  hasDomain_fTransform_functionEvaluator (fun f => f) _

theorem hasDomain_urp (X : Type u) [Fintype X] [DecidableEq X] :
    HasDomain (urp X) {l : List X | l ≠ []} :=
  hasDomain_fTransform_functionEvaluator (fun π : Equiv.Perm X => (π : X → X)) _

theorem hasDomain_unif (X : Type u) (Y : Type v) [Fintype Y] [Nonempty Y] :
    HasDomain (unif X Y) {l : List X | l ≠ []} :=
  hasDomain_fTransform_functionEvaluator (fun y : Y => fun _ : X => y) _

theorem hasDomain_finiteBeacon (Y : Type v) [Fintype Y] [Nonempty Y]
    (n : ℕ) :
    HasDomain (finiteBeacon Y n) {l : List (Fin n) | l ≠ []} :=
  hasDomain_urf (Fin n) Y

end PDS

end

end RandomSystems
