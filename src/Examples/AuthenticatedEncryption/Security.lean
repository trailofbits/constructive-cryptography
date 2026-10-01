import Examples.AuthenticatedEncryption.Collision
import ConstructiveCryptography.Tactics.Substitution

/-!
# Authenticated encryption: `(ind-cca, int-ptxt) → ae`

Banfi, Theorem 2.3.10(4) (printed pp. 24–25), corrected. The printed chain uses `int-ptxt`,
`ind-cca`, `int-ptxt` and then claims `ρ^ptxt ∘ ρ^cca ∘ ρ^ptxt(⟦E_k, D_k⟧) ≈ ρ^ae(E_k)` up to
`q_e² / 2^ℓ`; that last step fails when a later message equals an earlier replacement
message. The correction uses `ind-cca` a second time, then compares the doubly randomized hybrid
with the ideal, with a collision bound over every pair of an original and a replacement message
(`hybrid_ideal_distance_le`).

The proof is Banfi's sequence of steps (§2.3.1): each step substitutes one assumption inside its
context `ρ`, losing the assumption's error at the distinguisher with `ρ` absorbed, `ε(D ∘ ρ)`
(§2.3.3), and the statistical step loses `q_e² / |M|` at the budget `q` per port. The chain is
also counted (`correctedChain`: two uses of each assumption). In distance form
(`real_ideal_distance_le`), `⟦E_k, D_k⟧` is within
`2 Δ(⟦E_k, D_k⟧, ρ^ptxt(⟦E_k, D_k⟧)) + 2 Δ(⟦E_k, D_k⟧, ρ^cca(⟦E_k, D_k⟧)) + q_e² / |M|` of
`ρ^ae(E_k)`.

## Main definitions

* `Assumption`, `assumptionSystems`: `ind-cca` and `int-ptxt`, with their systems
* `correctedChain`: the counted chain `int-ptxt, ind-cca, int-ptxt, ind-cca`

## Main results

* `ae_of_ind_cca_int_ptxt`: `(ind-cca, int-ptxt) → ae` for the admitted distinguishers, for the
  notions `AE.INDCCA`, `AE.INTPTXT` and `AE.Secure` of `Commons.Definitions.AEAD`
* `correctedChain_cca`, `correctedChain_ptxt`: two uses of each assumption
* `real_ideal_distance_le`: the distance form
-/

open CategoryTheory
open Commons
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open SystemAlgebra SystemAlgebra.Interface
open scoped SystemAlgebra

namespace AuthenticatedEncryption

variable {K M C : Type} [Fintype K] [Fintype M] [Fintype C] [DecidableEq K] [DecidableEq M]
  [DecidableEq C] [Nonempty M] (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ)

/-- `⟦E_k, D_k⟧` for `k ← Gen`, at the budget `q` per port. -/
local notation "⟦" "E_k" "," "D_k" "⟧" => AE.Real.perPort scheme (budget := q)

/-- `⟦E$_k, D^⊥⟧ = ρ^ae(E_k)` for `k ← Gen`, at the budget `q` per port. -/
local notation "⟦" "E$_k" "," "D^⊥" "⟧" =>
  (AE.Ideal.perPort M C • Encryption.Real.perPort scheme : Interface.Resource (AE.perPort M C q))

/-- **`(ind-cca, int-ptxt) → ae`, corrected** (Banfi, Theorem 2.3.10(4)). For the admitted
distinguishers, which are closed under absorbing converters, `int-ptxt` within `εptxt` and
`ind-cca` within `εcca` give `ae`, losing each assumption's error at the distinguisher with the
context of its use absorbed, and `q_e² / |M|` for the collision step. -/
theorem ae_of_ind_cca_int_ptxt [AdmissibleDistinguishers]
    (εptxt εcca : (AE.perPort M C q).inputDomain.DistinguisherBehavior → ENNReal)
    (ptxt : AE.INTPTXT scheme εptxt) (cca : AE.INDCCA scheme εcca) :
    AE.Secure scheme fun D =>
      εptxt D + εcca (absorb ρ^ptxt D) + εptxt (absorb (ρ^ptxt ≫ ρ^cca) D) +
        εcca (absorb (ρ^ptxt ≫ ρ^cca ≫ ρ^ptxt) D) +
        ENNReal.ofReal ((q .enc : ℝ) ^ 2 / Fintype.card M) := by
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    ⟦E_k, D_k⟧ ≃[εptxt] ρ^ptxt • ⟦E_k, D_k⟧ := ptxt
    _ ≃[εcca ∘ absorb ρ^ptxt] ρ^ptxt • ρ^cca • ⟦E_k, D_k⟧ :=
      AdmissibleDistinguishers.substitutesWithin_context ρ^ptxt cca
    _ ≃[εptxt ∘ absorb (ρ^ptxt ≫ ρ^cca)] ρ^ptxt • ρ^cca • ρ^ptxt • ⟦E_k, D_k⟧ :=
      AdmissibleDistinguishers.substitutesWithin_context (ρ^ptxt ≫ ρ^cca) ptxt
    _ ≃[εcca ∘ absorb (ρ^ptxt ≫ ρ^cca ≫ ρ^ptxt)]
        ρ^ptxt • ρ^cca • ρ^ptxt • ρ^cca • ⟦E_k, D_k⟧ :=
      AdmissibleDistinguishers.substitutesWithin_context (ρ^ptxt ≫ ρ^cca ≫ ρ^ptxt) cca
    _ ≈[ENNReal.ofReal ((q .enc : ℝ) ^ 2 / Fintype.card M)] ⟦E$_k, D^⊥⟧ :=
      hybrid_ideal_distance_le scheme q

/-- The two assumptions of the implication. -/
inductive Assumption
  | cca
  | ptxt
  deriving DecidableEq

/-- The systems of each assumption, the pairs `AE.INDCCA.systems` and `AE.INTPTXT.systems`,
indexed by Banfi's direction bit: `X_{i,false} = X₀` and `X_{i,true} = X₁`. -/
noncomputable def assumptionSystems (i : Assumption) (b : Bool) : Resource (AE.perPort M C q) :=
  let X := match i with
    | .cca => AE.INDCCA.systems scheme q
    | .ptxt => AE.INTPTXT.systems scheme q
  bif b then X.2 else X.1

/-- **The corrected chain** `int-ptxt, ind-cca, int-ptxt, ind-cca` from `⟦E_k, D_k⟧` to the
hybrid `ρ^ptxt ∘ ρ^cca ∘ ρ^ptxt ∘ ρ^cca(⟦E_k, D_k⟧)`. -/
noncomputable def correctedChain :
    SubstitutionRelation.Implication (fun _ : Assumption => AE.perPort M C q)
      (assumptionSystems scheme q) (AE.perPort M C q) 3 := by
  cc_calc counted (assumptionSystems scheme q)
    ⟦E_k, D_k⟧ = 𝟙 _ • assumptionSystems scheme q .ptxt false := (identity_attach _).symm
    _ ≃ 𝟙 _ • assumptionSystems scheme q .ptxt true := Assumption.ptxt
    _ = ρ^ptxt • assumptionSystems scheme q .cca false := by
      rw [identity_attach]; rfl
    _ ≃ ρ^ptxt • assumptionSystems scheme q .cca true := Assumption.cca
    _ = (ρ^ptxt ≫ ρ^cca) • assumptionSystems scheme q .ptxt false := by
      rw [comp_smul]; rfl
    _ ≃ (ρ^ptxt ≫ ρ^cca) • assumptionSystems scheme q .ptxt true := Assumption.ptxt
    _ = (ρ^ptxt ≫ ρ^cca ≫ ρ^ptxt) • assumptionSystems scheme q .cca false := by
      rw [comp_smul, comp_smul, comp_smul]; rfl
    _ ≃ (ρ^ptxt ≫ ρ^cca ≫ ρ^ptxt) • assumptionSystems scheme q .cca true := Assumption.cca
    _ = Hybrid scheme q := by
      rw [comp_smul, comp_smul]; rfl

/-- The corrected chain uses `ind-cca` twice. -/
theorem correctedChain_cca : (correctedChain scheme q).usageCount .cca = 2 := by
  cc_usage
  rfl

/-- The corrected chain uses `int-ptxt` twice. -/
theorem correctedChain_ptxt : (correctedChain scheme q).usageCount .ptxt = 2 := by
  cc_usage
  rfl

/-- **The distance form**: `⟦E_k, D_k⟧` is within twice its `int-ptxt` distance, twice its
`ind-cca` distance, and `q_e² / |M|` of `ρ^ae(E_k)`. -/
theorem real_ideal_distance_le :
    Δ ⟦E_k, D_k⟧ ⟦E$_k, D^⊥⟧ ≤
      Δ ⟦E_k, D_k⟧ (ρ^ptxt • ⟦E_k, D_k⟧) + Δ ⟦E_k, D_k⟧ (ρ^cca • ⟦E_k, D_k⟧) +
        Δ ⟦E_k, D_k⟧ (ρ^ptxt • ⟦E_k, D_k⟧) + Δ ⟦E_k, D_k⟧ (ρ^cca • ⟦E_k, D_k⟧) +
        ENNReal.ofReal ((q .enc : ℝ) ^ 2 / Fintype.card M) := by
  cc_calc statistical
    ⟦E_k, D_k⟧ ≈[Δ ⟦E_k, D_k⟧ (ρ^ptxt • ⟦E_k, D_k⟧)] ρ^ptxt • ⟦E_k, D_k⟧ := le_rfl
    _ ≈[Δ ⟦E_k, D_k⟧ (ρ^cca • ⟦E_k, D_k⟧)] ρ^ptxt • ρ^cca • ⟦E_k, D_k⟧ :=
      distance_attach_le _ _ _
    _ ≈[Δ ⟦E_k, D_k⟧ (ρ^ptxt • ⟦E_k, D_k⟧)] ρ^ptxt • ρ^cca • ρ^ptxt • ⟦E_k, D_k⟧ :=
      (distance_attach_le _ _ _).trans (distance_attach_le _ _ _)
    _ ≈[Δ ⟦E_k, D_k⟧ (ρ^cca • ⟦E_k, D_k⟧)] ρ^ptxt • ρ^cca • ρ^ptxt • ρ^cca • ⟦E_k, D_k⟧ :=
      ((distance_attach_le _ _ _).trans (distance_attach_le _ _ _)).trans
        (distance_attach_le _ _ _)
    _ ≈[ENNReal.ofReal ((q .enc : ℝ) ^ 2 / Fintype.card M)] ⟦E$_k, D^⊥⟧ :=
      hybrid_ideal_distance_le scheme q

end AuthenticatedEncryption
