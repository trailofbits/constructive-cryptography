module

public import Commons.Definitions.AbstractModel.ExtractionPresentation
public import RandomSystems.Typed.CallFunctional
public import Probability.Kernel

/-!
# The extraction system's discrete presentation

`registersConverter_smul_observations_mass` presents fixed attachment by its composed DDS.
`extractionSystem_presents` then applies the retained-mixture law to the joint draw `(p,x)`.
This correspondence supplies the visible-system certificate for the extraction game.
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

/-- Fixed attachment gives each transcript the indicator that its composed DDS answers it. -/
lemma registersConverter_smul_observations_mass (z : P × S)
    (h : List ((Σ i, (M.interface input k).X i) × (Σ i, (M.interface input k).Y i))) :
    (M.registersConverter input k z.1 z.2 • M.observations k z.1).1 h =
      (Distribution.ProbDist.single z).1.mass
        (fun w => Replies (extractionDDS M input k w).1 (h.map Prod.fst) (h.map Prod.snd)) := by
  change (M.registersConverter input k z.1 z.2 •
    TypedSystem.ofFunction (A := M.observationInterface k) (M.evaluate z.1)).1 h = _
  let observation := (M.observationInterface k).automatonDDS
    (fun (_ : Unit) ρ values => ((), M.evaluate z.1 ρ values)) ()
  -- Present only the fixed observation component by its existing deterministic evaluator.
  have presentation : TypedSystem.ofFunction (A := M.observationInterface k)
      (M.evaluate z.1) = TypedSystem.ofPDS (Distribution.ProbDist.single observation) :=
    (TypedSystem.ofDeterministic_eq_ofFunction (A := M.observationInterface k)
      (M.evaluate z.1)
      observation.1 observation.2
      (Interface.automatonDDS_eq_ofFunction (M.observationInterface k)
        (fun (_ : Unit) => M.evaluate z.1) ())).symm
  rw [presentation]
  -- Attachment transports that component presentation through the unchanged register converter.
  refine (TypedConverter.ofDDC_smul_ofPDS_mass
    (A := M.interface input k) (B := M.observationInterface k)
    (registersDDC M input k z).2
    (Distribution.ProbDist.single observation) h).trans ?_
  simp only [Distribution.ProbDist.single, Distribution.mass_single]
  rfl

/-- Forgetting the sampled condition presents exactly the composed extraction system. -/
lemma extractionSystem_presents
    -- `D` is the common joint draw retained by the system and its discrete presentation.
    (D : Distribution.ProbDist (P × S)) :
    (M.extractionSystem input k D).1 =
      PDS.behavior (PDG.underlying (extractionPDG M input k D).1)
        (PDG.underlying_probability (extractionPDG M input k D).2) := by
  apply RandomSystem.ext
  intro h
  -- The retained joint sample mixes the fixed component presentations.
  have mixture := RandomSystem.mix_mass_of_presentations D
    (fun z => (M.registersConverter input k z.1 z.2 • M.observations k z.1).1)
    (fun z => (Distribution.ProbDist.single z).1)
    (fun z => (extractionDDS M input k z).1)
    (fun z _ => registersConverter_smul_observations_mass M input k z) h
  simp only [Distribution.ProbDist.single, Distribution.bindK_single_one] at mixture
  refine mixture.trans ?_
  -- Forgetting the hidden condition leaves the same deterministic system for every draw.
  change _ = behaviorMass _ _ _
  simp only [PDG.underlying, behaviorMass, Distribution.mass_fTransform,
    extractionPDG, Distribution.ProbDist.map_val]

end Commons.AbstractModel
