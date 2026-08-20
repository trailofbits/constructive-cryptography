import RandomSystems.System.RandomObjects
import RandomSystems.System.Phi

/-!
# Scratch: the top-level universal Random Systems instantiation

`Phi` is the repository's universal Random Systems PDS.  `SigmaDDC` is made
from valid universal DDC programs themselves, not from endomorphisms.  The
interpretation into an action is installed once below.
-/

namespace Scratch.Universal

open Probability (Distribution)

universe u

noncomputable section

open RandomSystems
open RandomSystems.Converter

abbrev Phi : Type (u + 1) := RandomSystems.Phi.{u}

/-- One genuine universal-alphabet CR18 DDC. -/
abbrev DDCAtom : Type (u + 1) :=
  {nu : Converter.ProtocolFn Uni.{u} Uni.{u} Uni.{u} Uni.{u} //
    Converter.IsDDC nu}

/-- Exact serial syntax over DDCs.  This is the concrete `Sigma`, not a set of
endomorphisms; its leaves remain inspectable Random Systems programs. -/
abbrev SigmaDDC : Type (u + 1) := FreeMonoid DDCAtom.{u}

def applyDDCAtom (alpha : DDCAtom.{u}) (S : Phi.{u}) : Phi.{u} :=
  PDS.applyLaw (Converter.toDDC alpha.1) S

def ddcAction : SigmaDDC.{u} →* Function.End Phi.{u} :=
  FreeMonoid.lift applyDDCAtom

/-- The single model-boundary instance that gives all DDC words `*` and `•`. -/
instance : MulAction SigmaDDC.{u} Phi.{u} :=
  MulAction.compHom _ ddcAction

@[simp] theorem ddcAtom_smul (alpha : DDCAtom.{u}) (S : Phi.{u}) :
    (FreeMonoid.of alpha : SigmaDDC.{u}) • S = applyDDCAtom alpha S := by
  show ddcAction (FreeMonoid.of alpha) S = _
  simp [ddcAction]

/-- Internal typed-to-universal boundary for the round resource. -/
def Rnn (X : Type u) [Fintype X] [DecidableEq X] [Nonempty X] : Phi.{u} :=
  RandomSystems.ofTyped (PDS.urf X X)

/-- Turn a typed block former into one universal inner query.  This is only a
one-round CBC-shaped probe; its purpose is to exercise the carrier boundary. -/
def cbcQuery {M X : Type u} (bf : M → List X) : Uni.{u} → Uni.{u} := by
  classical
  exact fun q =>
    if h : (System.decode M q).Dom then
      match (bf ((System.decode M q).get h)).getLast? with
      | some x => System.encode X x
      | none => q
    else q

def cbcAtom {M X : Type u} (bf : M → List X) : DDCAtom.{u} :=
  ⟨Converter.simpleFn (cbcQuery bf) id, Converter.isDDC_simpleFn _ _⟩

/-- Public construction object: already a member of concrete `SigmaDDC`. -/
def cbcDDC {M X : Type u} (bf : M → List X) : SigmaDDC.{u} :=
  FreeMonoid.of (cbcAtom bf)

section DeterministicSmoke

variable {M X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]
variable (bf : M → List X)

example : Monoid SigmaDDC.{u} := inferInstance
example : MulAction SigmaDDC.{u} Phi.{u} := inferInstance

#check cbcDDC bf • Rnn X
#check cbcDDC bf * cbcDDC bf

example : (cbcDDC bf * cbcDDC bf) • Rnn X =
    cbcDDC bf • (cbcDDC bf • Rnn X) := by
  rw [mul_smul]

end DeterministicSmoke

/-! ## Probabilistic converters -/

/-- CR18 Definition 3.17 at the same universal signature. -/
abbrev PDCAtom : Type (u + 1) := Distribution DDCAtom.{u}

/-- A protocol of probabilistic converters.  Free serial syntax keeps the
abstract monoid laws exact; each letter is still actual PDC data. -/
abbrev SigmaPDC : Type (u + 1) := FreeMonoid PDCAtom.{u}

def applyPDCAtom (alpha : PDCAtom.{u}) (S : Phi.{u}) : Phi.{u} :=
  Distribution.fTransform
    (fun p : DDCAtom.{u} × System.DDS Uni.{u} Uni.{u} =>
      Converter.DDC.apply (Converter.toDDC p.1.1) p.2)
    (Distribution.prod alpha S)

def pdcAction : SigmaPDC.{u} →* Function.End Phi.{u} :=
  FreeMonoid.lift applyPDCAtom

instance : MulAction SigmaPDC.{u} Phi.{u} :=
  MulAction.compHom _ pdcAction

def pointPDC (alpha : DDCAtom.{u}) : PDCAtom.{u} :=
  Finsupp.single alpha 1

/-- Deterministic converters enter probabilistic `Sigma` as point masses. -/
def deterministic (alpha : SigmaDDC.{u}) : SigmaPDC.{u} :=
  FreeMonoid.lift (fun atom => FreeMonoid.of (pointPDC atom)) alpha

def randomizedCBC {M X : Type u} (bf : M → List X) : SigmaPDC.{u} :=
  FreeMonoid.of (pointPDC (cbcAtom bf))

section ProbabilisticSmoke

variable {M X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]
variable (bf : M → List X)

example : Monoid SigmaPDC.{u} := inferInstance
example : MulAction SigmaPDC.{u} Phi.{u} := inferInstance

#check randomizedCBC bf • Rnn X
#check randomizedCBC bf * randomizedCBC bf

example : (randomizedCBC bf * randomizedCBC bf) • Rnn X =
    randomizedCBC bf • (randomizedCBC bf • Rnn X) := by
  rw [mul_smul]

end ProbabilisticSmoke

end

end Scratch.Universal
