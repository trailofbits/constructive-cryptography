import RandomSystems.System.RandomObjects
import RandomSystems.System.Phi

/-!
# Scratch: a homogeneous abstract-cryptography instance with DDCs primary

The abstract layer asks only for a monoid `Sigma` and a `MulAction Sigma Phi`.
Here `Phi` is literally the Random Systems PDS carrier and `Sigma` is a free
monoid of valid concrete DDC programs.  It is not a subtype of `Phi → Phi`.
-/

namespace Scratch.Homogeneous

open Probability (Distribution)

universe u

noncomputable section

open RandomSystems
open RandomSystems.Converter

/-- Concrete DDC generators at one fixed resource signature. -/
abbrev DDCGenerator (X Y : Type u) :=
  {nu : Converter.ProtocolFn X Y X Y // Converter.IsDDC nu}

/-- The concrete converter carrier.  A word is a serially composed DDC.
Free syntax gives exact unit/associativity without identifying a DDC with an
endomorphism and without assuming false raw equality of protocol functions. -/
abbrev DDC (X Y : Type u) := FreeMonoid (DDCGenerator X Y)

/-- The resource carrier is exactly a Random Systems PDS. -/
abbrev Phi (X Y : Type u) := PDS X Y

/-- Interpret one concrete DDC generator on a PDS. -/
def applyGenerator {X Y : Type u}
    (alpha : DDCGenerator X Y) (S : Phi X Y) : Phi X Y :=
  PDS.applyLaw (Converter.toDDC alpha.1) S

/-- The interpretation is defined once at the model boundary. -/
def actionHom (X Y : Type u) : DDC X Y →* Function.End (Phi X Y) :=
  FreeMonoid.lift fun alpha => applyGenerator alpha

/-- This is the Random Systems instantiation of the abstract action class. -/
instance (X Y : Type u) : MulAction (DDC X Y) (Phi X Y) :=
  MulAction.compHom _ (actionHom X Y)

@[simp] theorem letter_smul {X Y : Type u}
    (alpha : DDCGenerator X Y) (S : Phi X Y) :
    (FreeMonoid.of alpha : DDC X Y) • S = applyGenerator alpha S := by
  show actionHom X Y (FreeMonoid.of alpha) S = _
  simp [actionHom]

/-- A minimal same-signature CBC-shaped generator. -/
def cbcGenerator {X : Type u} [Inhabited X]
    (bf : X → List X) : DDCGenerator X X :=
  ⟨Converter.simpleFn (fun x => (bf x).getLastD default) id,
    Converter.isDDC_simpleFn _ _⟩

/-- The application's public CBC converter is already an element of `Sigma`. -/
def cbcDDC {X : Type u} [Inhabited X] (bf : X → List X) : DDC X X :=
  FreeMonoid.of (cbcGenerator bf)

def Rnn (X : Type u) [Fintype X] [DecidableEq X] [Nonempty X] : Phi X X :=
  PDS.urf X X

section Smoke

variable {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X]
variable (bf bg : X → List X)

-- The abstract algebra is inherited from the concrete instance.
example : Monoid (DDC X X) := inferInstance
example : MulAction (DDC X X) (Phi X X) := inferInstance

-- Concrete converter composition and converter/resource application are plain
-- abstract `*` and `•`, with no endomorphism packaging at either use site.
#check cbcDDC bf * cbcDDC bg
#check cbcDDC bf • Rnn X

example : (cbcDDC bf * cbcDDC bg) • Rnn X =
    cbcDDC bf • (cbcDDC bg • Rnn X) := by
  rw [mul_smul]

end Smoke

end

end Scratch.Homogeneous
