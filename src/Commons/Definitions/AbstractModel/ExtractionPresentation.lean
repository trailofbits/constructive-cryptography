module

public import Commons.Definitions.AbstractModel.Extraction
public import RandomSystems.Typed.Automaton

/-!
# Deterministic presentations of extraction

`registersDDC` is the certified register program; `extractionDDS` attaches it to fixed
observations. `extractionPDG` retains one joint `(p,x)` draw for that DDS and `extracted x`.
Its domain certificate comes from the converter's domain map, so the original command
allowance and separate final submission are unchanged.

## References

1. U. Maurer, C. Portmann, and J. Zhu. *Unifying Generic Group Models*.
   Cryptology ePrint Archive, Paper 2020/996, 2020.
-/

@[expose] public section

namespace Commons.AbstractModel

open Probability SystemAlgebra

variable
  -- `S` carries register values, `P` model parameters, and `M` their operations.
  -- `ι` indexes registers; `input` selects the register initially containing the secret.
  {S P ι : Type} (M : Commons.AbstractModel S P) [DecidableEq ι]
  [Fintype S] [Fintype ι] [Fintype M.Operation] [Fintype M.Query]
  [∀ ρ, Fintype (M.Reply ρ)] (input : ι)
  -- `k` bounds ordinary commands; final submission remains separate.
  (k : ℕ)

/-- The completed-history register program with its existing one-call domain certificate. -/
noncomputable def registersDDC
    -- `z = (p,x)` fixes the model parameter and initial secret for the whole interaction.
    (z : P × S) :
    {a : InsideOutsideSystem (M.interface input k).I (M.observationInterface k).I
      (M.interface input k).X (M.interface input k).Y
      (M.observationInterface k).X (M.observationInterface k).Y //
      IsDDCFrom (M.observationInterface k).domain (M.interface input k).domain 1 a} :=
  ⟨DDC.ofProgramOn [] (M.registerProgram input z.1 z.2) (M.interface input k).domain,
    TypedConverter.ofCostedProgram_isDDCFrom
      (A := M.interface input k) (B := M.observationInterface k) (q := k)
      [] (M.registerProgram input z.1 z.2)
      (M.registerProgram_bounded input z.1 z.2) M.observationCost
      (M.registerProgram_costs input z.1 z.2) (M.observationCost_sum_le input k)
      (fun _ hne hlen => ⟨hne, hlen⟩)⟩

/-- Attach the register DDC to fixed observations: the deterministic visible system at `(p,x)`. -/
noncomputable def extractionDDS (z : P × S) :
    DDS (Σ i, (M.interface input k).X i) (Σ i, (M.interface input k).Y i) :=
  let observation := (M.observationInterface k).automatonDDS
    (fun (_ : Unit) ρ values => ((), M.evaluate z.1 ρ values)) ()
  DDC.attach ⟨(registersDDC M input k z).1,
    ⟨1, (registersDDC M input k z).2.isDDC⟩⟩
    ⟨observation.1, observation.2.1⟩

/-- The attachment admits exactly the original command domain, including terminal submission. -/
lemma extractionDDS_domain (z : P × S) :
    HasDomain (M.interface input k).inputDomain (extractionDDS M input k z).1 := by
  let observation := (M.observationInterface k).automatonDDS
    (fun (_ : Unit) ρ values => ((), M.evaluate z.1 ρ values)) ()
  exact HasDomain.ofInputs ((registersDDC M input k z).2.mapsDomain
    (M.interface input k).nonempty_prefix _ observation.2.1
    observation.2.2.1 observation.2.2.2).2

/-- Draw `(p,x) ← D` once, pairing its visible DDS with the original-secret condition
[1, Figure 1, p. 8]: "The game is won if x' = x". -/
noncomputable def extractionPDG
    -- `D` may correlate `p` and `x`; both the system and condition use this same draw.
    (D : Distribution.ProbDist (P × S)) :
    Distribution.ProbDist
      {g : DDG (Σ i, (M.interface input k).X i) (Σ i, (M.interface input k).Y i) //
      HasDomain (M.interface input k).inputDomain g.1.1} :=
  D.map fun z => ⟨(extractionDDS M input k z, M.extracted z.2),
    extractionDDS_domain M input k z⟩

end Commons.AbstractModel
