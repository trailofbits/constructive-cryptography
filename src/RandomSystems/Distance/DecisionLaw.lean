module

public import RandomSystems.Distance.Distinguisher
public import Probability.Kernel

/-!
# Laws of final decisions

`Domain.Distinguisher.decisionLaw` samples the distinguisher, runs its compatible query
strategy, and observes the final bit of the completed transcript. `decisionLaw_true`
identifies its probability of `true` with `P.probability R`.

`guessingLaw P R hR` first samples one uniform bit `b`, runs `P` against `R b`, and retains
`(b, guess)`. `guessingLaw_success` gives `(1 - p₀ + p₁) / 2` for the event `guess = b`.
Here `p_b = Pr[P(R b) = true]`; the hidden bit selects the system for the entire interaction.

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
2. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace SystemAlgebra.Domain.Distinguisher

open Probability Distribution

variable
  -- `I` carries ports; `X i`, `Y i` their finite query and reply alphabets.
  {I : Type} [Fintype I] {X Y : I → Type}
  [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  -- `𝒟` specifies the admitted exchanges; `P` is a normalized law of compatible stopping DDDs.
  {𝒟 : Domain (Σ i, X i) (Σ i, Y i)} (P : 𝒟.Distinguisher)

open Classical in
/-- Draw `D ∼ P` and a completed transcript from `R.sLaw`; return its final decision.
`DecisionCompatible.producesDecision` ensures that every supported transcript ends in a
Boolean decision, so the complement of `(dec, true)` is `(dec, false)`. -/
noncomputable def decisionLaw
    -- `R` supplies the replies; `hR` puts each reply at the queried port.
    (R : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟) (hR : R.RepliesAtQueriedInterface) :
    ProbDist Bool :=
  P.bind fun D => ProbDist.map
    (fun h => if ⟨.dec, true⟩ ∈ (trim D.1) (dHist (h.map Prod.snd)) then true else false)
    -- The bound chosen by `IsDDD` completes the interaction before observing its decision.
    ⟨R.sLaw (ddeOf D.2.1).1 D.2.1.2.1.choose,
      R.sLaw_isProbDist (D.2.2.environment D.2.1 R hR) _⟩

/-- Each Boolean mass is the probability of that final decision on the completed transcript. -/
lemma decisionLaw_apply
    -- `R` supplies port-correct replies; `b` is the final decision being tested.
    (R : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟) (hR : R.RepliesAtQueriedInterface)
    (b : Bool) :
    (decisionLaw P R hR).1 b = P.1.sum fun D w => w *
      (R.sLaw (ddeOf D.2.1).1 D.2.1.2.1.choose).mass
        (fun h => ⟨.dec, b⟩ ∈ (trim D.1) (dHist (h.map Prod.snd))) := by
  classical
  rw [decisionLaw, ProbDist.bind_val, bindK_apply]
  apply Finsupp.sum_congr
  intro D _
  congr 1
  rw [ProbDist.map_val, fTransform_apply_eq_mass]
  apply mass_congr_of_support
  intro h hh
  -- Compatibility and the stopping bound give one decision on every supported transcript.
  obtain ⟨c, hc⟩ := D.2.2.producesDecision D.2.1 hR hh
  have unique (a : Bool) :
      ⟨.dec, a⟩ ∈ (trim D.1) (dHist (h.map Prod.snd)) ↔ a = c := by
    constructor
    · intro ha
      exact eq_of_heq (Sigma.mk.inj_iff.mp (Part.mem_unique ha hc)).2
    · rintro rfl
      exact hc
  rw [unique true, unique b]
  cases c <;> cases b <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]

/-- The final decision law assigns `true` exactly `P.probability R`. -/
lemma decisionLaw_true
    -- `R` is the tested system, with replies at the queried ports by `hR`.
    (R : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟) (hR : R.RepliesAtQueriedInterface) :
    (decisionLaw P R hR).1 true = P.probability R :=
  decisionLaw_apply P R hR true

/-- Draw `b ∼ 𝒰[Bool]`, run `P` against `R b`, and return `(b, guess)`.
[1, equation (4.7), p. 92] uses an “unbiased random bit, independent of anything else”. -/
noncomputable def guessingLaw
    -- `R false`, `R true` are the two worlds; each respects the queried port by `hR`.
    (R : Bool → RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟)
    (hR : ∀ b, (R b).RepliesAtQueriedInterface) : ProbDist (Bool × Bool) :=
  ProbDist.jointLaw 𝒰[Bool] fun b => decisionLaw P (R b) (hR b)

/-- Correct guessing has probability `(1 - p₀ + p₁) / 2`, where `p_b = Pr[P(R b) = true]`.
[2, proof of Theorem 2.10, p. 26] gives “½(1 − p₀ + p₁)”. -/
theorem guessingLaw_success
    -- `R` supplies the two worlds on one domain, with port-correct replies `hR`.
    (R : Bool → RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟)
    (hR : ∀ b, (R b).RepliesAtQueriedInterface) :
    (guessingLaw P R hR).1.mass (fun bg => bg.2 = bg.1) =
      (1 - P.probability (R false) + P.probability (R true)) / 2 := by
  classical
  -- Split on the uniform hidden bit and evaluate the matching decision in each world.
  simp only [guessingLaw, ProbDist.jointLaw, ProbDist.bind_val, mass_bindK,
    ProbDist.map_val, mass_fTransform, mass_singleton]
  change (uniform Bool).sum (fun b w => w * (decisionLaw P (R b) (hR b)).1 b) = _
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
  simp only [Fintype.sum_bool, uniform_apply, Fintype.card_bool, Nat.cast_ofNat]
  -- In world zero, a correct guess is the complement of outputting `true`.
  have h := (decisionLaw P (R false) (hR false)).2.2
  rw [weight_eq_sum, Fintype.sum_bool, decisionLaw_true] at h
  rw [decisionLaw_true]
  linarith

end SystemAlgebra.Domain.Distinguisher
