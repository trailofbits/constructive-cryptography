import RandomSystems.Cumulative.Completion
import RandomSystems.Distance.Observation
import RandomSystems.Typed.Interface
import Probability.Kernel
import Mathlib.Data.Set.Finite.List

/-!
# H-coefficient bounds through conditional transcript completions

Two systems `R S : TypedSystem A` are compared through completed laws of `(h, z)`: the public
history `h` followed by a record `z : Z` drawn from a conditional law, `K_R h` for `R` and
`K_S h` for `S`. The two kernels may differ and may both be probabilistic. The record is drawn
after the interaction ends, so it cannot influence the environment's next query, and
forgetting it returns the ordinary transcript laws.

```text
  R ── public history h ── z ← K_R h ──▶ (h, z)     real completed law
  S ── public history h ── z ← K_S h ──▶ (h, z)     ideal completed law
                                           │
                                       forget z
                                           ▼
                                 ordinary transcript laws
```

`RandomSystem.kernelLaw_completionKernel` supplies a real kernel `K_R` from the actual record
of a sampled presentation of `R`, without changing its joint law.

## Main definitions

* `BoundedTranscript A`: the public histories within the interface bound, a finite alphabet
* `boundedTranscriptLaw R E n hE`: the public transcript law on that alphabet

## Main results

* `fTransform_boundedTranscriptLaw`: decoding the finite alphabet recovers `R.sLaw E n`
* `transcriptDistance_le_of_completion`: ratio and expected error of the completed laws bound
  `Δ(R, S)`. It instantiates `RandomSystem.transcriptDistance_le_of_observation_ratio` in
  `Distance.Observation` with the two kernel laws and `π = Prod.fst`. That theorem bounds, for
  each compatible `E` stopping within `n` queries:

```text
  δ(R.sLaw E n, S.sLaw E n)
    = δ(fst_* realLaw, fst_* idealLaw)      fTransform_fst_kernelLaw (marginals)
    ≤ δ(realLaw, idealLaw)                  statDist_fTransform_le [1, Lemma 3]
    ≤ 𝔼_idealLaw[ε]                         statDist_le_expect_of_ratio [2, Lemma 2.2.1]
    ≤ b                                     hypothesis `bound`
```

Here `realLaw = kernelLaw R K_R E n` and `idealLaw = kernelLaw S K_S E n`. The pointwise ratio
on masses becomes a ratio on these laws because both carry the same factor `[Good E n h]`.

## References

1. D. Lanzenberger and U. Maurer. Coupling of Random Systems. In *Theory of Cryptography
   (TCC 2020)*, Springer, 2020. Cryptology ePrint Archive, Paper 2020/1187.
2. Jha. *Provable Security of Symmetric-key Cryptographic Schemes*.
-/

namespace SystemAlgebra.TypedSystem

open Probability RandomSystem
open scoped NNReal

/-- Public histories within the interface's existing bound,
`BoundedTranscript A = {h // h.length ≤ A.bound}`. It contains every history of positive
probability and depends on neither system nor environment. It is a `def` so that the `Fintype`
instance below is found at `BoundedTranscript A`, indexed by the interface `A`. -/
def BoundedTranscript (A : Interface) : Type :=
  {h : List ((Σ i, A.X i) × (Σ i, A.Y i)) // h.length ≤ A.bound}

/-- Lists of length at most `A.bound` over the finite alphabet of query–reply pairs. -/
noncomputable instance (A : Interface) : Fintype (BoundedTranscript A) :=
  (List.finite_length_le ((Σ i, A.X i) × (Σ i, A.Y i)) A.bound).fintype

open Classical in
/-- Encode a history in the finite alphabet: `boundedTranscript A h = ⟨h, _⟩` if
`h.length ≤ A.bound`, and `⟨[], _⟩` otherwise. Only histories with zero mass under every
system's transcript law take the fallback branch. -/
noncomputable def boundedTranscript (A : Interface)
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i))) : BoundedTranscript A :=
  if hl : h.length ≤ A.bound then ⟨h, hl⟩ else ⟨[], Nat.zero_le _⟩

/-- The public transcript law on the finite alphabet,
`boundedTranscriptLaw R E n hE = (boundedTranscript A)_* (R.sLaw E n)`. -/
noncomputable def boundedTranscriptLaw {A : Interface}
    -- `R : TypedSystem A`: the observed system on interface `A`.
    (R : TypedSystem A)
    -- `E`: an environment on `A`'s queries and replies, observed for `n` rounds; `hE`: it
    -- respects `A`'s domain, which makes `R.sLaw E n` a probability law.
    (E : DDE (Σ i, A.X i) (Σ i, A.Y i)) (n : ℕ) (hE : A.inputDomain.Compatible E) :
    Distribution.ProbDist (BoundedTranscript A) :=
  Distribution.PMF ⟨R.1.sLaw E.1 n, R.1.sLaw_isProbDist (hE _ R.2) n⟩ (boundedTranscript A)

/-- Decoding the finite alphabet recovers the public transcript law:
`val_* (boundedTranscriptLaw R E n hE) = R.sLaw E n`. -/
lemma fTransform_boundedTranscriptLaw
    -- `R : TypedSystem A`: the observed system on interface `A`.
    {A : Interface} (R : TypedSystem A)
    -- `E`: an environment observed for `n` rounds; `hE`: it respects `A`'s domain.
    (E : DDE (Σ i, A.X i) (Σ i, A.Y i)) (n : ℕ) (hE : A.inputDomain.Compatible E) :
    Distribution.fTransform Subtype.val (boundedTranscriptLaw R E n hE).1 = R.1.sLaw E.1 n := by
  classical
  -- `val_* (boundedTranscript A)_* (R.sLaw E n) = (val ∘ boundedTranscript A)_* (R.sLaw E n)`.
  change Distribution.fTransform Subtype.val
    (Distribution.fTransform (boundedTranscript A) (R.1.sLaw E.1 n)) = _
  refine (Distribution.fTransform_fTransform
    (fun h : BoundedTranscript A => h.val) (boundedTranscript A) _).trans ?_
  -- It suffices that `val ∘ boundedTranscript A` is the identity on the support.
  conv_rhs => rw [← Distribution.fTransform_id (R.1.sLaw E.1 n)]
  apply Distribution.fTransform_congr_support
  intro h hh
  -- A history longer than `A.bound` has mass zero, so a support point lies within the bound.
  have hl : h.length ≤ A.bound := by
    by_contra hn
    have hz := R.1.mass_eq_zero_of_bound_lt (Nat.lt_of_not_ge hn)
    exact Finsupp.mem_support_iff.mp hh (by simp only [sLaw_apply, hz, ite_self])
  -- Representation bookkeeping: expose the subtype behind `BoundedTranscript A`, then the
  -- encoding takes its first branch and returns `h`.
  change (if hl : h.length ≤ A.bound then
    (⟨h, hl⟩ : {h : List _ // h.length ≤ A.bound}) else ⟨[], Nat.zero_le _⟩).val = h
  rw [dif_pos hl]

/-- Any two normalized terminal completions certify the distance of the original systems:
if `(1 − ε(h, z)) · S(h) · K_S h z ≤ R(h) · K_R h z` for every `(h, z)` and the ideal
expectation of `ε` is at most `b` under every compatible stopping environment, then
`Δ(R, S) ≤ b`.

[2, Lemma 2.2.1, p. 20]: “Adv_{O₁;O₀}(A) ≤ ϵ_bad + Ex[ϵ_ratio(Θ₀)]”. Here the single error
function `ε` includes any bad-event contribution. -/
theorem transcriptDistance_le_of_completion
    -- `A : Interface` fixes the public ports, query/reply alphabets and admissible histories;
    -- `R S : TypedSystem A` are the real and ideal systems.
    {A : Interface} (R S : TypedSystem A)
    -- `Z` is the record type. `realCompletion h = K_R h` and `idealCompletion h = K_S h` are
    -- the conditional record laws given history `h`; they may differ.
    {Z : Type}
    (realCompletion idealCompletion :
      List ((Σ i, A.X i) × (Σ i, A.Y i)) → Distribution.ProbDist Z)
    -- `ε(h, z)`: a real scalar loss; `hε` gives `ε ≥ 0`, and `ε` may exceed one. `b` is the
    -- distance budget in `ℝ≥0`.
    (ε : List ((Σ i, A.X i) × (Σ i, A.Y i)) × Z → ℝ)
    (hε : ∀ τ, 0 ≤ ε τ) {b : ℝ≥0}
    -- `ratio`: `(1 − ε τ) · S(h) · K_S h z ≤ R(h) · K_R h z` at `τ = (h, z)`. It contains no
    -- environment; a fixed environment multiplies both sides by the same indicator.
    (ratio : ∀ τ, (1 - ε τ) * kernelMass S.1 (fun h => (idealCompletion h).1) τ ≤
      kernelMass R.1 (fun h => (realCompletion h).1) τ)
    -- `bound`: `𝔼[ε] ≤ b` under the ideal completed law, for every adaptive `E` compatible
    -- with `A`'s domain that stops within `n` queries.
    (bound : ∀ (E : DDE (Σ i, A.X i) (Σ i, A.Y i)) n,
      QueryBounded n E → A.inputDomain.Compatible E →
      (kernelLaw S.1 (fun h => (idealCompletion h).1) E.1 n).expect ε ≤ b) :
    R.1.transcriptDistance S.1 ≤ b := by
  -- `observation T K E n` is the completed law `kernelLaw T K E n` on `(h, z)`. It is a
  -- probability law: its masses are nonnegative, and its weight equals that of its exact
  -- marginal `fst_* = T.sLaw E n`, which is one for compatible `E`.
  let observation (T : TypedSystem A)
      (K : List ((Σ i, A.X i) × (Σ i, A.Y i)) → Distribution.ProbDist Z)
      (E : DDE (Σ i, A.X i) (Σ i, A.Y i)) (n : ℕ)
      (_hn : QueryBounded n E) (hE : A.inputDomain.Compatible E) :
      Distribution.ProbDist (List ((Σ i, A.X i) × (Σ i, A.Y i)) × Z) :=
    ⟨kernelLaw T.1 (fun h => (K h).1) E.1 n,
      kernelLaw_nonNeg T.1 (fun h => (K h).2.1) E.1 n, by
        rw [← Distribution.weight_fTransform Prod.fst,
          fTransform_fst_kernelLaw T.1 (fun h => (K h).2)]
        exact (T.1.sLaw_isProbDist (hE _ T.2) n).weight_eq⟩
  -- Apply the observation theorem with the common projection `π = Prod.fst`; the exact
  -- marginals `fst_* = sLaw` link both completed laws to the public laws.
  refine RandomSystem.transcriptDistance_le_of_observation_ratio R.1 S.1 Prod.fst
    (observation R realCompletion) (observation S idealCompletion)
    (fun E n _ _ => fTransform_fst_kernelLaw R.1 (fun h => (realCompletion h).2) E.1 n)
    (fun E n _ _ => fTransform_fst_kernelLaw S.1 (fun h => (idealCompletion h).2) E.1 n)
    ε hε ?_ bound
  -- Remaining: the mass ratio on the completed laws, `kernelLaw = [Good E n h] · kernelMass`.
  intro E n _ _ τ
  change (1 - ε τ) * kernelLaw S.1 (fun h => (idealCompletion h).1) E.1 n τ ≤
    kernelLaw R.1 (fun h => (realCompletion h).1) E.1 n τ
  rw [kernelLaw_apply, kernelLaw_apply]
  split_ifs
  -- `h` is a history of `E`: both laws equal the masses, and `ratio τ` compares them.
  · exact ratio τ
  -- Otherwise both laws vanish: `(1 − ε τ) · 0 ≤ 0`.
  · simp only [mul_zero, le_refl]

end SystemAlgebra.TypedSystem
