import RandomSystems.System.RandomObjects
import RandomSystems.System.AttachEngineFully

/-!
Scratch prototype for the universal-carrier API question.

This file imports the repository's real Random Systems definitions but changes
nothing in the repository.  It tests three carrier presentations:

1. the existing indexed family plus its canonical inclusion into `Phi`;
2. a universal-first public resource API;
3. carriers which are literally a tagged dependent sum or the untagged image.
-/

namespace PhiInheritancePrototype

open RandomSystems
open Classical

noncomputable section

universe u

/-! ## Existing family and universal carrier -/

abbrev Sigma : Type (u + 1) := ↥converterMonoidAt.{u}

noncomputable def thetaToy : Sigma.{u} := 1

noncomputable def VnTyped (M X : Type u)
    [Fintype M] [DecidableEq M]
    [Fintype X] [DecidableEq X] [Nonempty X] : PDS M X :=
  PDS.urf M X

-- The existing API works when the inclusion is explicit.
example (M X : Type u)
    [Fintype M] [DecidableEq M]
    [Fintype X] [DecidableEq X] [Nonempty X] : Phi.{u} :=
  thetaToy • (RandomSystems.ofTyped (VnTyped M X) : Phi.{u})

-- The registered coercion works when an expected `Phi` is supplied locally.
example (M X : Type u)
    [Fintype M] [DecidableEq M]
    [Fintype X] [DecidableEq X] [Nonempty X] : Phi.{u} :=
  thetaToy • (VnTyped M X : Phi.{u})

-- But the completely bare paper-level term does not elaborate in the current
-- API: the homogeneous action expects `Phi`, whereas the RHS is `PDS M X`.
#guard_msgs (error) in
example (M X : Type u)
    [Fintype M] [DecidableEq M]
    [Fintype X] [DecidableEq X] [Nonempty X] : Phi.{u} :=
  thetaToy • VnTyped M X

/-! ## Alternative A: canonical inclusion exposed through heterogeneous action -/

section HeterogeneousBridge

/-- A typed PDS is accepted as the right operand, included canonically, and
the result is the universal carrier.  This is a syntax/API bridge; it does not
make `PDS M X` a subtype of `Phi`, nor does it define a homogeneous action on
the typed fiber. -/
local instance typedPDSHSMul {M X : Type u} :
    HSMul Sigma.{u} (PDS M X) Phi.{u} where
  hSMul sigma resource := sigma • (resource : Phi.{u})

-- This is the requested use-site syntax: no `ofTyped`, cast, or ascription.
example (M X : Type u)
    [Fintype M] [DecidableEq M]
    [Fintype X] [DecidableEq X] [Nonempty X] : Phi.{u} :=
  thetaToy • VnTyped M X

-- Chaining works after the first heterogeneous step, because its output is Phi.
example (M X : Type u)
    [Fintype M] [DecidableEq M]
    [Fintype X] [DecidableEq X] [Nonempty X] : Phi.{u} :=
  thetaToy • (thetaToy • VnTyped M X)

end HeterogeneousBridge

/-! ## Alternative B: universal-first public resource constructors -/

/-- The typed implementation is included once, inside the named resource.
The abstract-facing resource therefore already inhabits `Phi`. -/
noncomputable def VnPhi (M X : Type u)
    [Fintype M] [DecidableEq M]
    [Fintype X] [DecidableEq X] [Nonempty X] : Phi.{u} :=
  RandomSystems.ofTyped (VnTyped M X)

-- The ordinary homogeneous action now gives the paper-level syntax directly.
example (M X : Type u)
    [Fintype M] [DecidableEq M]
    [Fintype X] [DecidableEq X] [Nonempty X] : Phi.{u} :=
  thetaToy • VnPhi M X

/-! ## Alternative C1: literal tagged dependent sum -/

/-- This is literally the disjoint/dependent sum of all typed PDS fibers.
Unlike the current `Phi`, it retains `M` and `X` as data and keeps two copies
of extensionally identical universal behavior when they have different tags. -/
def TaggedPDS : Type (u + 1) :=
  Σ M : Type u, Σ X : Type u, PDS M X

noncomputable def VnTagged (M X : Type u)
    [Fintype M] [DecidableEq M]
    [Fintype X] [DecidableEq X] [Nonempty X] : TaggedPDS.{u} :=
  ⟨M, X, VnTyped M X⟩

/-- With a tagged-sum carrier, a general converter must itself be an
endomorphism of the tagged sum (and must choose the output signature). -/
abbrev TaggedConverter : Type (u + 1) := Function.End TaggedPDS.{u}

noncomputable def thetaTagged : TaggedConverter.{u} := 1

-- Bare application works because the named resource is already packaged.
example (M X : Type u)
    [Fintype M] [DecidableEq M]
    [Fintype X] [DecidableEq X] [Nonempty X] : TaggedPDS.{u} :=
  thetaTagged • VnTagged M X

/-! ## Alternative C2: literal untagged union/image as a subtype -/

/-- This carrier is the literal untagged union of the images of all typed PDS
fibers in the existing universal behavior space.  Signature witnesses are a
property and are erased by subtype proof irrelevance. -/
def ImagePhi : Type (u + 1) :=
  {R : Phi.{u} // R ∈ RandomSystems.typed.{u}}

noncomputable def VnImage (M X : Type u)
    [Fintype M] [DecidableEq M]
    [Fintype X] [DecidableEq X] [Nonempty X] : ImagePhi.{u} :=
  ⟨RandomSystems.ofTyped (VnTyped M X), RandomSystems.ofTyped_mem_typed _⟩

/-- An endomorphism of `Phi` acts on the image carrier only together with a
closure proof.  This requirement is absent when the carrier is all of `Phi`. -/
structure ImageConverter : Type (u + 1) where
  toFun : Function.End Phi.{u}
  preserves_typed : ∀ R ∈ RandomSystems.typed.{u},
    toFun R ∈ RandomSystems.typed.{u}

instance : SMul ImageConverter.{u} ImagePhi.{u} where
  smul sigma resource :=
    ⟨sigma.toFun resource.1, sigma.preserves_typed resource.1 resource.2⟩

noncomputable def thetaImage : ImageConverter.{u} where
  toFun := 1
  preserves_typed := by
    intro R hR
    exact hR

-- Again the bare expression works, but every admitted converter now owes a
-- proof that it preserves the union of typed images.
example (M X : Type u)
    [Fintype M] [DecidableEq M]
    [Fintype X] [DecidableEq X] [Nonempty X] : ImagePhi.{u} :=
  thetaImage • VnImage M X

end

end PhiInheritancePrototype
