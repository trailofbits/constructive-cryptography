import RandomSystems.System.RandomObjects
import RandomSystems.Converter.Cascade

/-!
# Scratch: PDC-on-PDS application with concrete probabilistic converters

CR18 Definition 3.17 makes a PDC a law over DDCs.  This file models exactly
that object and supplies its application once, by independent sampling and
pushforward along deterministic DDC application.
-/

namespace Scratch.Probabilistic

open Probability (Distribution)

universe u

noncomputable section

open RandomSystems
open RandomSystems.Converter

abbrev DDC (U V X Y : Type u) :=
  {nu : Converter.ProtocolFn U V X Y // Converter.IsDDC nu}

/-- CR18 Definition 3.17, at typed signatures. -/
abbrev PDC (U V X Y : Type u) := Distribution (DDC U V X Y)

def DDC.applyPDS {U V X Y : Type u}
    (alpha : DDC U V X Y) (S : PDS X Y) : PDS U V :=
  PDS.applyLaw (Converter.toDDC alpha.1) S

instance {U V X Y : Type u} :
    HSMul (DDC U V X Y) (PDS X Y) (PDS U V) where
  hSMul := DDC.applyPDS

/-- Sample the PDC and PDS independently, then run concrete DDC application. -/
def PDC.applyPDS {U V X Y : Type u}
    (alpha : PDC U V X Y) (S : PDS X Y) : PDS U V :=
  Distribution.fTransform
    (fun p : DDC U V X Y × System.DDS X Y =>
      Converter.DDC.apply (Converter.toDDC p.1.1) p.2)
    (Distribution.prod alpha S)

instance {U V X Y : Type u} :
    HSMul (PDC U V X Y) (PDS X Y) (PDS U V) where
  hSMul := PDC.applyPDS

def PDC.ofDDC {U V X Y : Type u} (alpha : DDC U V X Y) : PDC U V X Y :=
  Finsupp.single alpha 1

/-- Independent probabilistic serial composition, still as concrete PDC data. -/
def PDC.comp {W Z U V X Y : Type u}
    (alpha : PDC W Z U V) (beta : PDC U V X Y) : PDC W Z X Y :=
  Distribution.fTransform
    (fun p : DDC W Z U V × DDC U V X Y =>
      ⟨Converter.comp p.1.1 p.2.1,
        Converter.serial_composition_is_ddc p.1.2 p.2.2⟩)
    (Distribution.prod alpha beta)

instance {W Z U V X Y : Type u} :
    HMul (PDC W Z U V) (PDC U V X Y) (PDC W Z X Y) where
  hMul := PDC.comp

def cbcDDC {M X : Type u} [Inhabited X]
    (bf : M → List X) : DDC M X X X :=
  ⟨Converter.simpleFn (fun m => (bf m).getLastD default) id,
    Converter.isDDC_simpleFn _ _⟩

def randomizedCBC {M X : Type u} [Inhabited X]
    (bf : M → List X) : PDC M X X X :=
  PDC.ofDDC (cbcDDC bf)

def Rnn (X : Type u) [Fintype X] [DecidableEq X] [Nonempty X] : PDS X X :=
  PDS.urf X X

section Smoke

variable {M X : Type u} [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X]
variable (bf : M → List X)

#check cbcDDC bf • Rnn X
#check randomizedCBC bf • Rnn X
#check randomizedCBC bf * randomizedCBC (M := X) (fun x => [x])

end Smoke

end

end Scratch.Probabilistic
