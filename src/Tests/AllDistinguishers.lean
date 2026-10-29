import Examples.PRGLengthExtension
import Examples.AuthenticatedEncryption.Security

/-! # Unrestricted per-distinguisher reductions

`AdmissibleDistinguishers.all` admits every compatible stopping distinguisher behavior; each
check selects it locally. Choosing each assumption's own advantage as its error makes the
assumption reflexive (`le_rfl`) and specializes the existing substitution theorems to explicit
bounds for every distinguisher, each hop read at `D ∘ ρ` (Banfi 2023, §2.3.3, printed p. 16:
`ε'(D) := ε(D ∘ ρ)`). The bounds are symbolic in the PRG or scheme, budgets and `D`; no
computational or negligibility claim is made.
The PRG check uses the fresh-seed systems of `Examples.PRGLengthExtension`; the AE check uses
the corrected four-hop chain of `AuthenticatedEncryption.ae_of_ind_cca_int_ptxt`.
-/

namespace SystemAlgebra.Tests.AllDistinguishers
open Commons Probability Probability.Distribution SystemAlgebra SystemAlgebra.Interface
open Examples.PRGLengthExtension
open scoped SystemAlgebra

/-- Importing the choice leaves the ambient security model unselected. -/
example : True := by
  fail_if_success have : AdmissibleDistinguishers := inferInstance
  trivial

/-- `Adv_H(D) ≤ Adv_G(D ∘ 𝓡₁) + Adv_G(D ∘ 𝓡₂)` for every compatible `D`.
Each PRG query samples a fresh uniform seed, as in `PRGSamples`. -/
example {S : Type} [Fintype S] [Nonempty S] (G : S → S × S)
    (q : Evaluation.Port → ℕ)
    (D : (Evaluation.perPort Unit (S × S × S) q).inputDomain.DistinguisherBehavior) :
    D.advantage (PRGReal.perPort (H G) (budget := q))
        (MemorylessSource.perPort (S × S × S) 𝒰[S × S × S]) ≤
      (D.absorb (Evaluation.perPort Unit (S × S) (𝓡₁.insideBudget G q)).nonempty_prefix
          (Evaluation.perPort Unit (S × S × S) q).nonempty_prefix (𝓡₁.perPort G)).advantage
        (PRGReal.perPort G) (MemorylessSource.perPort (S × S) 𝒰[S × S]) +
      (D.absorb (Evaluation.perPort Unit (S × S) (𝓡₂.insideBudget S q)).nonempty_prefix
          (Evaluation.perPort Unit (S × S × S) q).nonempty_prefix (𝓡₂.perPort S)).advantage
        (PRGReal.perPort G) (MemorylessSource.perPort (S × S) 𝒰[S × S]) := by
  let := AdmissibleDistinguishers.all
  -- The PRG assumption at `Adv_G` bounds itself; `D ∈ Set.univ` discharges admissibility.
  exact prg_length_extension G
    (fun d => d.advantage (PRGReal.perPort G) (MemorylessSource.perPort (S × S) 𝒰[S × S]))
    (fun _ _ => le_rfl) D (Set.mem_univ D)

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
example (D : (AE.perPort M C q).inputDomain.DistinguisherBehavior) :
    D.advantage (AE.Secure.systems scheme q).1 (AE.Secure.systems scheme q).2 ≤
      Adv_ptxt D +
        Adv_cca (D.absorb (AE.perPort M C q).nonempty_prefix
          (AE.perPort M C q).nonempty_prefix ρ^ptxt) +
        Adv_ptxt (D.absorb (AE.perPort M C q).nonempty_prefix
          (AE.perPort M C q).nonempty_prefix (ρ^ptxt ≫ ρ^cca)) +
        Adv_cca (D.absorb (AE.perPort M C q).nonempty_prefix
          (AE.perPort M C q).nonempty_prefix (ρ^ptxt ≫ ρ^cca ≫ ρ^ptxt)) +
        ((q .enc) ^ 2 / Fintype.card M : ℝ≥0) := by
  let := AdmissibleDistinguishers.all
  -- Each assumption at its own advantage bounds itself; `D ∈ Set.univ` is admissible.
  exact AuthenticatedEncryption.ae_of_ind_cca_int_ptxt scheme q
    (fun d => Adv_ptxt d) (fun d => Adv_cca d)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) D (Set.mem_univ D)

end AuthenticatedEncryption

end SystemAlgebra.Tests.AllDistinguishers
