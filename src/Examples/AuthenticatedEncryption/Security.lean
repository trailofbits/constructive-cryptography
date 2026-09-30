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

The chain is counted (`correctedChain`: two uses of each assumption) and quantitative
(`ae_of_ind_cca_int_ptxt`): each assumption use loses its advantage at the distinguisher
reduced through the transformations before it, and the statistical step loses `q_e² / |M|`, at
the budget `q` per port. In distance form (`real_ideal_distance_le`), the real system is within
`2 Δ(⟦E_k, D_k⟧, ρ^ptxt ⟦E_k, D_k⟧) + 2 Δ(⟦E_k, D_k⟧, ρ^cca ⟦E_k, D_k⟧) + q_e² / |M|` of the
ideal.

## Main definitions

* `Assumption`, `assumptionSystems`: `ind-cca` and `int-ptxt`, with their systems
* `correctedChain`: the counted chain `int-ptxt, ind-cca, int-ptxt, ind-cca`

## Main results

* `correctedChain_cca`, `correctedChain_ptxt`: two uses of each assumption
* `ae_of_ind_cca_int_ptxt`: `(ind-cca, int-ptxt) → ae` for the admitted distinguishers, for the notions `AE.INDCCA`, `AE.INTPTXT` and `AE.Secure` of
  `Commons.Definitions.AEAD`
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

/-- **The corrected chain** `int-ptxt, ind-cca, int-ptxt, ind-cca` from the real system to the
hybrid `ρ^ptxt ∘ ρ^cca ∘ ρ^ptxt ∘ ρ^cca(⟦E_k, D_k⟧)`. -/
noncomputable def correctedChain :
    SubstitutionRelation.Implication (fun _ : Assumption => AE.perPort M C q)
      (assumptionSystems scheme q) (AE.perPort M C q) 3 := by
  cc_calc counted (assumptionSystems scheme q)
    AE.Real.perPort scheme = 𝟙 _ • assumptionSystems scheme q .ptxt false :=
      (identity_attach _).symm
    _ ≃ 𝟙 _ • assumptionSystems scheme q .ptxt true := Assumption.ptxt
    _ = AE.PTXT.perPort M C • assumptionSystems scheme q .cca false := by
      rw [identity_attach]; rfl
    _ ≃ AE.PTXT.perPort M C • assumptionSystems scheme q .cca true := Assumption.cca
    _ = (AE.PTXT.perPort M C ≫ AE.CCA.perPort M C) • assumptionSystems scheme q .ptxt false := by
      rw [comp_smul]; rfl
    _ ≃ (AE.PTXT.perPort M C ≫ AE.CCA.perPort M C) • assumptionSystems scheme q .ptxt true :=
      Assumption.ptxt
    _ = ((AE.PTXT.perPort M C ≫ AE.CCA.perPort M C) ≫ AE.PTXT.perPort M C) •
        assumptionSystems scheme q .cca false := by
      rw [comp_smul, comp_smul, comp_smul]; rfl
    _ ≃ ((AE.PTXT.perPort M C ≫ AE.CCA.perPort M C) ≫ AE.PTXT.perPort M C) •
        assumptionSystems scheme q .cca true := Assumption.cca
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

/-- **`(ind-cca, int-ptxt) → ae`, corrected** (Banfi, Theorem 2.3.10(4)). For the admitted
distinguishers, which are closed under reduction, `int-ptxt` with loss `ε_ptxt` and `ind-cca`
with loss `ε_cca` give `ae` with the losses of the four uses at the reduced distinguishers,
plus `q_e² / |M|` for the collision step. -/
theorem ae_of_ind_cca_int_ptxt [AdmissibleDistinguishers]
    (εptxt εcca : (AE.perPort M C q).inputDomain.Distinguisher → ENNReal)
    (ptxt : AE.INTPTXT scheme εptxt) (cca : AE.INDCCA scheme εcca) :
    AE.Secure scheme fun D =>
      εptxt D + εcca (reduction (AE.PTXT.perPort M C) D) +
        εptxt (reduction (AE.CCA.perPort M C) (reduction (AE.PTXT.perPort M C) D)) +
        εcca (reduction (AE.PTXT.perPort M C) (reduction (AE.CCA.perPort M C)
          (reduction (AE.PTXT.perPort M C) D))) +
        ENNReal.ofReal ((q .enc : ℝ) ^ 2 / Fintype.card M) := by
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    AE.Real.perPort scheme ≃[εptxt] AE.PTXT.perPort M C • AE.Real.perPort scheme := ptxt
    _ ≃[fun D => εcca (reduction (AE.PTXT.perPort M C) D)]
        AE.PTXT.perPort M C • (AE.CCA.perPort M C • AE.Real.perPort scheme) :=
      AdmissibleDistinguishers.substitutesWithin_attach _ cca
    _ ≃[fun D => εptxt (reduction (AE.CCA.perPort M C) (reduction (AE.PTXT.perPort M C) D))]
        AE.PTXT.perPort M C • (AE.CCA.perPort M C • (AE.PTXT.perPort M C • AE.Real.perPort scheme)) :=
      AdmissibleDistinguishers.substitutesWithin_attach _ (AdmissibleDistinguishers.substitutesWithin_attach _ ptxt)
    _ ≃[fun D => εcca (reduction (AE.PTXT.perPort M C) (reduction (AE.CCA.perPort M C)
          (reduction (AE.PTXT.perPort M C) D)))]
        AE.PTXT.perPort M C • (AE.CCA.perPort M C • (AE.PTXT.perPort M C •
          (AE.CCA.perPort M C • AE.Real.perPort scheme))) :=
      AdmissibleDistinguishers.substitutesWithin_attach _ (AdmissibleDistinguishers.substitutesWithin_attach _
        (AdmissibleDistinguishers.substitutesWithin_attach _ cca))
    _ ≈[ENNReal.ofReal ((q .enc : ℝ) ^ 2 / Fintype.card M)]
        (AE.Ideal.perPort M C (budget := q) • Encryption.Real.perPort scheme :
          Interface.Resource (AE.perPort M C q)) :=
      hybrid_ideal_distance_le scheme q

/-- **The distance form**: the real system is within twice its `int-ptxt` distance, twice its
`ind-cca` distance, and `q_e² / |M|` of the ideal. -/
theorem real_ideal_distance_le :
    Δ (AE.Real.perPort scheme (budget := q))
        ((AE.Ideal.perPort M C (budget := q) • Encryption.Real.perPort scheme :
          Interface.Resource (AE.perPort M C q))) ≤
      Δ (AE.Real.perPort scheme (budget := q)) (AE.PTXT.perPort M C • AE.Real.perPort scheme) +
        Δ (AE.Real.perPort scheme (budget := q)) (AE.CCA.perPort M C • AE.Real.perPort scheme) +
        Δ (AE.Real.perPort scheme (budget := q)) (AE.PTXT.perPort M C • AE.Real.perPort scheme) +
        Δ (AE.Real.perPort scheme (budget := q)) (AE.CCA.perPort M C • AE.Real.perPort scheme) +
        ENNReal.ofReal ((q .enc : ℝ) ^ 2 / Fintype.card M) := by
  cc_calc statistical
    AE.Real.perPort scheme ≈[Δ (AE.Real.perPort scheme) (AE.PTXT.perPort M C • AE.Real.perPort scheme)]
        AE.PTXT.perPort M C • AE.Real.perPort scheme := le_rfl
    _ ≈[Δ (AE.Real.perPort scheme) (AE.CCA.perPort M C • AE.Real.perPort scheme)]
        AE.PTXT.perPort M C • (AE.CCA.perPort M C • AE.Real.perPort scheme) := le_rfl
    _ ≈[Δ (AE.Real.perPort scheme) (AE.PTXT.perPort M C • AE.Real.perPort scheme)]
        AE.PTXT.perPort M C • (AE.CCA.perPort M C • (AE.PTXT.perPort M C • AE.Real.perPort scheme)) :=
      (distance_attach_le _ _ _).trans (distance_attach_le _ _ _)
    _ ≈[Δ (AE.Real.perPort scheme) (AE.CCA.perPort M C • AE.Real.perPort scheme)]
        AE.PTXT.perPort M C • (AE.CCA.perPort M C • (AE.PTXT.perPort M C •
          (AE.CCA.perPort M C • AE.Real.perPort scheme))) :=
      ((distance_attach_le _ _ _).trans (distance_attach_le _ _ _)).trans
        (distance_attach_le _ _ _)
    _ ≈[ENNReal.ofReal ((q .enc : ℝ) ^ 2 / Fintype.card M)]
        (AE.Ideal.perPort M C (budget := q) • Encryption.Real.perPort scheme :
          Interface.Resource (AE.perPort M C q)) :=
      hybrid_ideal_distance_le scheme q

end AuthenticatedEncryption
