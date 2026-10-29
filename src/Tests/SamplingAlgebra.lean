import RandomSystems.Typed.SamplingAlgebra
import ConstructiveCryptography.Notation

/-!
# Retained samples in attachment and parallel proofs

Consumers of `RandomSystems.Typed.SamplingAlgebra`: independent initial draws are grouped,
reordered and moved through attachment `α •` and parallel composition `∥`. The laws are
arbitrary normalized distributions on possibly infinite sample types.

A counterexample shows that the laws do not split one retained draw: one shared uniform bit
`b`, replying `(b, b)`, differs from two independent uniform bits `b, c`, replying `(b, c)`,
since the reply `(false, true)` has probability `0` against `1/4`.
-/

namespace SystemAlgebra.Tests.SamplingAlgebra

open Probability
open scoped SystemAlgebra

/-- Attachment to a product draw: `α • sample (P × Q) R` draws `k ← P` and `l ← Q` once and
attaches `α` to the retained `R (k, l)`. -/
example {A B : Interface} {K L : Type} (α : TypedConverter A B)
    (P : Distribution K) [Distribution.IsProbability P]
    (Q : Distribution L) [Distribution.IsProbability Q]
    (R : K × L → TypedSystem B) :
    α • TypedSystem.sample (P.prod Q) R =
      TypedSystem.sample P (fun k => TypedSystem.sample Q (fun l => α • R (k, l))) := by
  -- Split the product draw, then move `α` inside the draw `k ← P`.
  rw [TypedSystem.sample_prod, TypedConverter.smul_sample]
  -- Move `α` inside the draw `l ← Q`, onto `R (k, l)`.
  simp only [TypedConverter.smul_sample]

/-- Reordering two independent draws behind an attached converter keeps the selected system. -/
example {A B : Interface} {K L : Type} (α : TypedConverter A B)
    (P : Distribution K) [Distribution.IsProbability P]
    (Q : Distribution L) [Distribution.IsProbability Q]
    (R : K → L → TypedSystem B) :
    α • TypedSystem.sample P (fun k => TypedSystem.sample Q (R k)) =
      TypedSystem.sample Q (fun l => TypedSystem.sample P (fun k => α • R k l)) := by
  -- Exchange the two draws, then move `α` inside both.
  rw [TypedSystem.sample_comm P Q R]
  simp only [TypedConverter.smul_sample]

/-- A product draw used only by the right component moves outside `R ∥ ·` and splits into two
draws; the left system is the same `R` for every pair `(k, l)`. -/
example {A B : Interface} {K L : Type} (R : TypedSystem A)
    (P : Distribution K) [Distribution.IsProbability P]
    (Q : Distribution L) [Distribution.IsProbability Q]
    (S : K × L → TypedSystem B) :
    R ∥ TypedSystem.sample (P.prod Q) S =
      TypedSystem.sample P (fun k =>
        TypedSystem.sample Q (fun l => R ∥ S (k, l))) := by
  -- Move the draw `(k, l) ← P × Q` outside the parallel composition, then split it.
  rw [TypedSystem.parallel_sample_right, TypedSystem.sample_prod]

/-! ### Independence boundary -/

/-- One port with query alphabet `X = {⋆}` and reply alphabet `Y = {false, true}²`.
Suppressing the sole port label, the nonempty input domain is `D = {[⋆]}`: one query. -/
abbrev pairReplyInterface : Interface :=
  Interface.queryBudget Unit (fun _ => Unit) (fun _ => Bool × Bool) 1

/-- Deterministic system `R_p`: on its sole allowed query `⋆`, return the fixed pair `p`.
Its cumulative mass is `R_p(h) = 1` for `h = []` or `h = [(⋆, p)]`, and `0` otherwise;
the sole port label is suppressed. -/
noncomputable def replyPair (p : Bool × Bool) : TypedSystem pairReplyInterface :=
  TypedSystem.ofFunction fun _ _ => p

/-- The transcript `h = [(⋆, (false, true))]`, suppressing the sole port label.
Its unequal reply coordinates distinguish a shared bit from two independent bits. -/
def mixedPairTranscript : List
    ((Σ i, pairReplyInterface.X i) × (Σ i, pairReplyInterface.Y i)) :=
  [(⟨(), ()⟩, ⟨(), (false, true)⟩)]

/-- **One retained draw is not two draws.** On the one query `⋆`, a shared uniform bit never
gives the reply `(false, true)`; two independent uniform bits give it with probability `1/4`.
Here `U` is the uniform law on `Bool`.

```text
   ⋆  ┌───────────────┐              ⋆  ┌───────────────┐
  ────┤ b ← U, once   │      ≠      ────┤ b ← U, once   │
  ⇒   │ R_(b, b)      │             ⇒   │ c ← U, once   │
      └───────────────┘                 │ R_(b, c)      │
                                        └───────────────┘
   Pr[⇒ (false, true)] = 0               Pr[⇒ (false, true)] = 1/4
``` -/
example :
    TypedSystem.sample (Distribution.uniform Bool) (fun b => replyPair (b, b)) ≠
      TypedSystem.sample (Distribution.uniform Bool) (fun b =>
        TypedSystem.sample (Distribution.uniform Bool) (fun c => replyPair (b, c))) := by
  -- Equal systems would assign the same probability to this one-query transcript.
  intro he
  have hm := congrArg (fun R : TypedSystem pairReplyInterface => R.1 mixedPairTranscript) he
  -- Both Boolean values have positive sampling mass, so the sums cover both values.
  have hs : (Distribution.uniform Bool).support = Finset.univ := by
    ext b
    simp only [Finsupp.mem_support_iff, Distribution.uniform_apply, Fintype.card_bool,
      Nat.cast_ofNat, one_div, ne_eq, inv_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
      Fintype.univ_bool, Finset.mem_insert, Finset.mem_singleton, Bool.eq_true_or_eq_false_self]
  -- Expand both masses: `∑_b ½ · [(b, b) = (false, true)] = 0` on the left and
  -- `∑_{b,c} ½ · ½ · [(b, c) = (false, true)] = 1/4` on the right.
  norm_num [TypedSystem.sample_mass, TypedSystem.ofFunction_mass, replyPair,
    pairReplyInterface, mixedPairTranscript, Distribution.uniform_apply, hs] at hm
  -- Evaluating the remaining reply predicates would force the false equality `0 = 1/4`.
  simp only [Prod.mk.injEq, Bool.false_eq_true, and_true, ↓reduceIte, Bool.true_eq_false,
    and_false, add_zero, one_div, and_self, mul_zero, zero_add, zero_eq_mul, inv_eq_zero,
    OfNat.ofNat_ne_zero, or_self] at hm

#print axioms TypedSystem.sample_prod
#print axioms TypedSystem.sample_comm
#print axioms TypedSystem.parallel_sample_right

end SystemAlgebra.Tests.SamplingAlgebra
