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
context `ρ`, losing the assumption's error at the distinguisher with `ρ` absorbed, `ε(Dρ)`
(§2.3.3), and the statistical step loses `q_e² / |M|` at the budget `q` per port. The admitted
distinguishers are an arbitrary selected class; the theorem asks only that the two
transformations `ρ^ptxt` and `ρ^cca` preserve it, and the closure of each composite context is
composed from these two proofs. The statistical step needs the domination of the decision
advantage by the transcript distance (`Interface.distinguisherAdvantageDominated`). The chain is
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
open scoped SystemAlgebra NNReal

namespace AuthenticatedEncryption

variable {K M C : Type} [Fintype K] [Fintype M] [Fintype C] [DecidableEq K] [DecidableEq M]
  [DecidableEq C] [Nonempty M] (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ)

/-- `⟦E_k, D_k⟧` for `k ← Gen`, at the budget `q` per port. -/
local notation "⟦" "E_k" "," "D_k" "⟧" => AE.Real.perPort scheme (budget := q)

/-- `⟦E$_k, D^⊥⟧ = ρ^ae(E_k)` for `k ← Gen`, at the budget `q` per port. -/
local notation "⟦" "E$_k" "," "D^⊥" "⟧" =>
  (AE.Ideal.perPort M C • Encryption.Real.perPort scheme : TypedSystem (AE.perPort M C q))

/-- **`(ind-cca, int-ptxt) → ae`, corrected** (Banfi, Theorem 2.3.10(4)). If `ρ^ptxt` and
`ρ^cca` preserve the admitted distinguishers, then `int-ptxt` within `εptxt` and `ind-cca`
within `εcca` give `ae`, losing each assumption's error at the distinguisher with the context
of its use absorbed, and `q_e² / |M|` for the collision step. -/
theorem ae_of_ind_cca_int_ptxt
    [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    -- `εptxt d`, `εcca d`: the errors of `int-ptxt` and `ind-cca` against each distinguisher.
    (εptxt εcca : (TypedDistinguisher (AE.perPort M C q)) → ENNReal)
    -- `ptxt`: `⟦E_k, D_k⟧ ≃[εptxt] ρ^ptxt(⟦E_k, D_k⟧)`; `cca`: the same for `ρ^cca` and `εcca`.
    (ptxt : AE.INTPTXT scheme εptxt) (cca : AE.INDCCA scheme εcca)
    -- `closedPtxt`, `closedCca`: absorbing `ρ^ptxt`, resp. `ρ^cca`, keeps admitted distinguishers
    -- admitted. Closure is assumed only for these two; the composite contexts compose them.
    (closedPtxt : AdmissibleDistinguishers.ClosedUnder
      (Phi := TypedSystem) (D := TypedDistinguisher)
      (ρ^ptxt : AE.perPort M C q ⟶ AE.perPort M C q))
    (closedCca : AdmissibleDistinguishers.ClosedUnder
      (Phi := TypedSystem) (D := TypedDistinguisher)
      (ρ^cca : AE.perPort M C q ⟶ AE.perPort M C q)) :
    AE.Secure scheme fun D =>
      εptxt D +
        εcca (D.absorb ρ^ptxt) +
        εptxt (D.absorb (ρ^ptxt ≫ ρ^cca)) +
        εcca (D.absorb (ρ^ptxt ≫ ρ^cca ≫ ρ^ptxt)) +
        ((q .enc) ^ 2 / Fintype.card M : ℝ≥0) := by
  -- The hybrids, as systems (the distinguisher D on the left; `X = ⟦E_k, D_k⟧`):
  --
  --   D ─ X                                   start
  --   D ─ ρ^ptxt ─ X                          ≃[εptxt(D)]                   int-ptxt
  --   D ─ ρ^ptxt ─ ρ^cca ─ X                  ≃[εcca(Dρ^ptxt)]              ind-cca in context
  --   D ─ ρ^ptxt ─ ρ^cca ─ ρ^ptxt ─ X         ≃[εptxt(D(ρ^ptxt ≫ ρ^cca))]   int-ptxt in context
  --   D ─ ρ^ptxt ─ ρ^cca ─ ρ^ptxt ─ ρ^cca ─ X ≃[εcca(D(ρ^ptxt ≫ ρ^cca ≫ ρ^ptxt))]
  --   D ─ ⟦E$_k, D^⊥⟧                         ≈[q_e² / |M|]   hybrid_ideal_distance_le
  --
  -- `cc_calc mixed` reads the model of the goal; its statistical last step uses the domination
  -- instance `distinguisherAdvantageDominated`. The losses add up.
  cc_calc mixed
    -- `int-ptxt` itself, with no context.
    ⟦E_k, D_k⟧ ≃[εptxt] ρ^ptxt • ⟦E_k, D_k⟧ := ptxt
    -- `ind-cca` inside the context `ρ^ptxt`, admitted by `closedPtxt`.
    _ ≃[fun D => εcca (D.absorb ρ^ptxt)] ρ^ptxt • ρ^cca • ⟦E_k, D_k⟧ :=
      AdmissibleDistinguishers.substitutesWithin_context ρ^ptxt closedPtxt cca
    -- `int-ptxt` inside `ρ^ptxt ≫ ρ^cca`; its closure is composed in category order.
    _ ≃[fun D => εptxt (D.absorb (ρ^ptxt ≫ ρ^cca))]
        ρ^ptxt • ρ^cca • ρ^ptxt • ⟦E_k, D_k⟧ :=
      AdmissibleDistinguishers.substitutesWithin_context (ρ^ptxt ≫ ρ^cca)
        (closedPtxt.comp closedCca) ptxt
    -- `ind-cca` inside `ρ^ptxt ≫ (ρ^cca ≫ ρ^ptxt)`, with closure composed in the same grouping.
    _ ≃[fun D => εcca (D.absorb (ρ^ptxt ≫ ρ^cca ≫ ρ^ptxt))]
        ρ^ptxt • ρ^cca • ρ^ptxt • ρ^cca • ⟦E_k, D_k⟧ :=
      AdmissibleDistinguishers.substitutesWithin_context (ρ^ptxt ≫ ρ^cca ≫ ρ^ptxt)
        (closedPtxt.comp (closedCca.comp closedPtxt)) cca
    -- The statistical step: the doubly randomized hybrid is within `q_e² / |M|` of the ideal.
    _ ≈[((q .enc) ^ 2 / Fintype.card M : ℝ≥0)] ⟦E$_k, D^⊥⟧ :=
      hybrid_ideal_distance_le scheme q

/-- The two assumptions of the implication. -/
inductive Assumption
  | cca
  | ptxt
  deriving DecidableEq

/-- The systems of each assumption, the pairs `AE.INDCCA.systems` and `AE.INTPTXT.systems`,
indexed by Banfi's direction bit: `X_{i,false} = X₀` and `X_{i,true} = X₁`. -/
noncomputable def assumptionSystems (i : Assumption) (b : Bool) : TypedSystem (AE.perPort M C q) :=
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
lemma correctedChain_cca : (correctedChain scheme q).usageCount .cca = 2 := by
  cc_usage
  rfl

/-- The corrected chain uses `int-ptxt` twice. -/
lemma correctedChain_ptxt : (correctedChain scheme q).usageCount .ptxt = 2 := by
  cc_usage
  rfl

/-- **The distance form**: `⟦E_k, D_k⟧` is within twice its `int-ptxt` distance, twice its
`ind-cca` distance, and `q_e² / |M|` of `ρ^ae(E_k)`. -/
theorem real_ideal_distance_le :
    Δ ⟦E_k, D_k⟧ ⟦E$_k, D^⊥⟧ ≤
      Δ ⟦E_k, D_k⟧ (ρ^ptxt • ⟦E_k, D_k⟧) + Δ ⟦E_k, D_k⟧ (ρ^cca • ⟦E_k, D_k⟧) +
        Δ ⟦E_k, D_k⟧ (ρ^ptxt • ⟦E_k, D_k⟧) + Δ ⟦E_k, D_k⟧ (ρ^cca • ⟦E_k, D_k⟧) +
        ((q .enc) ^ 2 / Fintype.card M : ℝ≥0) := by
  cc_calc statistical
    ⟦E_k, D_k⟧ ≈[Δ ⟦E_k, D_k⟧ (ρ^ptxt • ⟦E_k, D_k⟧)] ρ^ptxt • ⟦E_k, D_k⟧ := le_rfl
    _ ≈[Δ ⟦E_k, D_k⟧ (ρ^cca • ⟦E_k, D_k⟧)] ρ^ptxt • ρ^cca • ⟦E_k, D_k⟧ :=
      distance_attach_le _ _ _
    _ ≈[Δ ⟦E_k, D_k⟧ (ρ^ptxt • ⟦E_k, D_k⟧)] ρ^ptxt • ρ^cca • ρ^ptxt • ⟦E_k, D_k⟧ :=
      (distance_attach_le _ _ _).trans (distance_attach_le _ _ _)
    _ ≈[Δ ⟦E_k, D_k⟧ (ρ^cca • ⟦E_k, D_k⟧)] ρ^ptxt • ρ^cca • ρ^ptxt • ρ^cca • ⟦E_k, D_k⟧ :=
      ((distance_attach_le _ _ _).trans (distance_attach_le _ _ _)).trans
        (distance_attach_le _ _ _)
    _ ≈[((q .enc) ^ 2 / Fintype.card M : ℝ≥0)] ⟦E$_k, D^⊥⟧ :=
      hybrid_ideal_distance_le scheme q

end AuthenticatedEncryption
