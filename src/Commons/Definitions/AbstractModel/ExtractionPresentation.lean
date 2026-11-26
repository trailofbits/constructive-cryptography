module

public import Commons.Definitions.AbstractModel.Extraction
public import RandomSystems.PDS.Function

/-!
# Deterministic presentations of extraction

`extractionDDS` attaches the certified `registersDDC` to fixed observations.
`extractionPDG` retains one joint `(p,x)` draw for that DDS and `extracted x`.
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
  (input : ι)
  -- `k` bounds ordinary commands; final submission remains separate.
  (k : ℕ)

/-- Attach the register DDC to fixed observations: the deterministic visible system at `(p,x)`. -/
noncomputable def extractionDDS (z : P × S) :
    DDS (M.Command ι) (Σ i, M.Output i) :=
  let converter := M.registersDDC input k (M.operate z.1) z.2
  DDC.attach ⟨converter.1, ⟨1, converter.2.isDDC⟩⟩ (M.observationsDDS k z.1)

/-- The attachment admits the original command domain, including terminal submission. -/
lemma extractionDDS_domain (z : P × S) :
    HasDomain (Domain.ofInputs (M.Admitted input k) (k + 1) (fun _ h => h.length_le))
      (extractionDDS M input k z).1 := by
  let E : List (Σ ρ, Fin (M.queryArity ρ) → S) → Prop :=
    fun xs => xs ≠ [] ∧ xs.length ≤ k
  let hE : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p :=
    ⟨fun h => h.1 rfl, fun hp hne hh => ⟨hne, hp.length_le.trans hh.2⟩⟩
  let observation := M.observationsDDS k z.1
  exact HasDomain.ofInputs ((M.registersDDC input k (M.operate z.1) z.2).2.mapsDomain
    ⟨fun h => h.1 rfl, fun hp hne hh => hh.prefix hp hne⟩ observation.1 observation.2
    (DDS.ofFunction_repliesAtQueriedInterface E hE
      (fun v => ⟨v.1, M.evaluate z.1 v.1 v.2⟩) (fun _ _ _ => rfl))
    (DDS.ofFunction_dom E hE _)).2

/-- Draw `(p,x) ← D` once, pairing its visible DDS with the original-secret condition
[1, Figure 1, p. 8]: "The game is won if x' = x". -/
noncomputable def extractionPDG
    -- `D` may correlate `p` and `x`; both the system and condition use this same draw.
    (D : Distribution.ProbDist (P × S)) :
    Distribution.ProbDist
      {g : DDG (M.Command ι) (Σ i, M.Output i) //
      HasDomain (Domain.ofInputs (M.Admitted input k) (k + 1)
        (fun _ h => h.length_le)) g.1.1} :=
  D.map fun z => ⟨(extractionDDS M input k z, M.extracted z.2),
    extractionDDS_domain M input k z⟩

end Commons.AbstractModel
