import Examples.PRGLengthExtension
import Examples.AuthenticatedEncryption.Security

/-! # Unrestricted per-distinguisher reductions

`AdmissibleDistinguishers.all` admits every compatible stopping distinguisher behavior; each
check installs it locally, and the closure hypotheses of the theorems are then discharged by
`AdmissibleDistinguishers.all_closedUnder`. Choosing each assumption's own advantage as its
error makes the assumption reflexive (`le_rfl`) and specializes the existing substitution
theorems to explicit bounds for every distinguisher, each hop read at `Dρ` (Banfi 2023, §2.3.3,
printed p. 16: `ε'(D) := ε(D ∘ ρ)`). The bounds are symbolic in the PRG or scheme, budgets and
`D`; no computational or negligibility claim is made.
The PRG check uses the fresh-seed systems of `Examples.PRGLengthExtension`; the AE check uses
the corrected four-hop chain of `AuthenticatedEncryption.ae_of_ind_cca_int_ptxt`.
-/

namespace SystemAlgebra.Tests.AllDistinguishers
open ConstructiveCryptography
open Commons Probability Probability.Distribution SystemAlgebra SystemAlgebra.Interface
open Examples.PRGLengthExtension
open scoped SystemAlgebra

/-- Importing `all` and both examples installs no `AdmissibleDistinguishers` instance on
interfaces: the security model stays unselected. -/
example : True := by
  fail_if_success
    have : ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher :=
      inferInstance
  trivial

/-- `Adv_H(D) ≤ Adv_G(D𝓡₁) + Adv_G(D𝓡₂)` for every compatible `D`.
Each PRG query samples a fresh uniform seed, as in `PRGSamples`. -/
example {S : Type} [Fintype S] [Nonempty S] (G : S → S × S)
    (q : Evaluation.Port → ℕ)
    (D : (TypedDistinguisher (Evaluation.perPort Unit (S × S × S) q))) :
    D.advantage (PRGReal.perPort (H G) (budget := q))
        (MemorylessSource.perPort (S × S × S) 𝒰[S × S × S]) ≤
      (D.absorb (𝓡₁.perPort G)).advantage
        (PRGReal.perPort G) (MemorylessSource.perPort (S × S) 𝒰[S × S]) +
      (D.absorb (𝓡₂.perPort S)).advantage
        (PRGReal.perPort G) (MemorylessSource.perPort (S × S) 𝒰[S × S]) := by
  let : ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher :=
    ConstructiveCryptography.AdmissibleDistinguishers.all
  -- The PRG assumption at `Adv_G` bounds itself; under `all` both reductions preserve admission
  -- and `D ∈ Set.univ` is admitted.
  exact prg_length_extension G
    (fun d => d.advantage (PRGReal.perPort G) (MemorylessSource.perPort (S × S) 𝒰[S × S]))
    (fun _ _ => le_rfl) (AdmissibleDistinguishers.all_closedUnder _)
    (AdmissibleDistinguishers.all_closedUnder _) D (Set.mem_univ D)

section AuthenticatedEncryption

open CategoryTheory
open scoped NNReal

variable {K M C : Type} [Fintype K] [Fintype M] [Fintype C] [DecidableEq K] [DecidableEq M]
  [DecidableEq C] [Nonempty M] (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ)

local notation "Adv_ptxt" D:arg =>
  Domain.DistinguisherBehavior.advantage D
    (Prod.fst (AE.INTPTXT.systems scheme q)) (Prod.snd (AE.INTPTXT.systems scheme q))
local notation "Adv_cca" D:arg =>
  Domain.DistinguisherBehavior.advantage D
    (Prod.fst (AE.INDCCA.systems scheme q)) (Prod.snd (AE.INDCCA.systems scheme q))

/-- The corrected AE chain at each assumption's actual advantage: two `int-ptxt` terms,
two `ind-cca` terms at the absorbed contexts, and the collision error `q_enc² / |M|`.
There is no premise restricting `D` to a selected computational class. -/
example (D : (TypedDistinguisher (AE.perPort M C q))) :
    D.advantage (AE.Secure.systems scheme q).1 (AE.Secure.systems scheme q).2 ≤
      Adv_ptxt D +
        Adv_cca (D.absorb ρ^ptxt) +
        Adv_ptxt (D.absorb (ρ^ptxt ≫ ρ^cca)) +
        Adv_cca (D.absorb (ρ^ptxt ≫ ρ^cca ≫ ρ^ptxt)) +
        ((q .enc) ^ 2 / Fintype.card M : ℝ≥0) := by
  let : ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher :=
    ConstructiveCryptography.AdmissibleDistinguishers.all
  -- Each assumption at its own advantage bounds itself; under `all` both transformations
  -- preserve admission and `D ∈ Set.univ` is admitted.
  exact AuthenticatedEncryption.ae_of_ind_cca_int_ptxt scheme q
    (fun d => Adv_ptxt d) (fun d => Adv_cca d)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (AdmissibleDistinguishers.all_closedUnder _)
    (AdmissibleDistinguishers.all_closedUnder _) D (Set.mem_univ D)

end AuthenticatedEncryption

end SystemAlgebra.Tests.AllDistinguishers
