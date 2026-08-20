import RandomSystems.System.RandomObjects
import RandomSystems.Converter.Cascade

/-!
# Scratch: the signature-indexed Random Systems interface

This file deliberately keeps the concrete Random Systems objects primary.
There is no `Function.End` converter carrier.  The heterogeneous operations
are the categorical operations suggested directly by the four alphabets of a
DDC.
-/

namespace Scratch.Typed

open Probability (Distribution)

universe u

noncomputable section

open RandomSystems
open RandomSystems.Converter

/-- A genuine CR18 DDC program together with the two Definition 3.8 clauses. -/
abbrev DDC (U V X Y : Type u) :=
  {nu : Converter.ProtocolFn U V X Y // Converter.IsDDC nu}

/-- Serial composition is composition of concrete DDC programs. -/
def DDC.comp {W Z U V X Y : Type u}
    (alpha : DDC W Z U V) (beta : DDC U V X Y) : DDC W Z X Y :=
  ⟨Converter.comp alpha.1 beta.1,
    Converter.serial_composition_is_ddc alpha.2 beta.2⟩

/-- A signature-changing multiplication notation.  It is categorical rather
than a homogeneous `Monoid`: the middle alphabets have to match. -/
instance {W Z U V X Y : Type u} :
    HMul (DDC W Z U V) (DDC U V X Y) (DDC W Z X Y) where
  hMul := DDC.comp

/-- Application is supplied once at the Random Systems instance boundary. -/
def DDC.applyPDS {U V X Y : Type u}
    (alpha : DDC U V X Y) (S : PDS X Y) : PDS U V :=
  PDS.applyLaw (Converter.toDDC alpha.1) S

/-- The abstract action notation now applies every concrete DDC directly. -/
instance {U V X Y : Type u} :
    HSMul (DDC U V X Y) (PDS X Y) (PDS U V) where
  hSMul := DDC.applyPDS

/-- The one interpretation law required by serial composition is discharged
once, from the repository's `Converter.apply_toDDC_comp`. -/
theorem mul_smul {W Z U V X Y : Type u}
    (alpha : DDC W Z U V) (beta : DDC U V X Y) (S : PDS X Y) :
    (alpha * beta) • S = alpha • (beta • S) := by
  change PDS.applyLaw (Converter.toDDC (Converter.comp alpha.1 beta.1)) S =
    PDS.applyLaw (Converter.toDDC alpha.1)
      (PDS.applyLaw (Converter.toDDC beta.1) S)
  unfold PDS.applyLaw
  rw [Distribution.fTransform_fTransform]
  apply congrArg (fun f => Distribution.fTransform f S)
  funext s
  exact Converter.apply_toDDC_comp alpha.1 beta.1 s alpha.2.1

/-- A one-round CBC-shaped converter: form one block query from the message,
ask the inner `(X,X)` resource, and relay its answer.  It is intentionally
minimal; the CBC iteration is irrelevant to this interface experiment. -/
def cbcProgram {M X : Type u} [Inhabited X]
    (bf : M → List X) : Converter.ProtocolFn M X X X :=
  Converter.simpleFn (fun m => (bf m).getLastD default) id

def cbcDDC {M X : Type u} [Inhabited X]
    (bf : M → List X) : DDC M X X X :=
  ⟨cbcProgram bf, Converter.isDDC_simpleFn _ _⟩

def Rnn (X : Type u) [Fintype X] [DecidableEq X] [Nonempty X] : PDS X X :=
  PDS.urf X X

section Smoke

variable {M X : Type u} [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X]
variable (bf : M → List X)

-- The requested application-level shape, with no lifting at the use site.
#check cbcDDC bf • Rnn X

-- Signature-compatible concrete DDCs compose using the abstract notation.
#check cbcDDC bf * cbcDDC (M := X) (fun x => [x])

example : (cbcDDC bf * cbcDDC (M := X) (fun x => [x])) • Rnn X =
    cbcDDC bf • (cbcDDC (M := X) (fun x => [x]) • Rnn X) :=
  mul_smul _ _ _

end Smoke

end

end Scratch.Typed
