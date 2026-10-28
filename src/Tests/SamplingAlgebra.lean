import RandomSystems.Typed.SamplingAlgebra
import ConstructiveCryptography.Notation

/-!
# Retained samples in attachment and parallel proofs

These consumers group, reorder and move independent initial draws through typed operations.
The laws are arbitrary normalized distributions on possibly infinite sample types. Parallel
composition uses the public `∥` notation in this test layer; the foundational module stays
independent of the CC notation import.

A final counterexample separates one shared Boolean draw from two independent draws by
the probability of a mixed reply, making the independence requirement observable.
-/

namespace SystemAlgebra.Tests.SamplingAlgebra

open Probability
open scoped SystemAlgebra

/-- Attaching a converter preserves the component chosen by a product draw. Grouping that
draw as two independent choices lets attachment act on the resulting component. -/
example {A B : Interface} {K L : Type} (α : TypedConverter A B)
    (P : Distribution K) [Distribution.IsProbability P]
    (Q : Distribution L) [Distribution.IsProbability Q]
    (R : K × L → TypedSystem B) :
    α • TypedSystem.sample (P.prod Q) R =
      TypedSystem.sample P (fun k => TypedSystem.sample Q (fun l => α • R (k, l))) := by
  -- Split the product and carry attachment through the first retained draw.
  rw [TypedSystem.sample_prod, TypedConverter.smul_sample]
  -- The second draw is retained as well; attachment acts on R (k, l).
  simp only [TypedConverter.smul_sample]

/-- Reordering two independent choices inside an attached system keeps the same outside
behavior. This is the sampling step used when exchanging a sampled key and a random function. -/
example {A B : Interface} {K L : Type} (α : TypedConverter A B)
    (P : Distribution K) [Distribution.IsProbability P]
    (Q : Distribution L) [Distribution.IsProbability Q]
    (R : K → L → TypedSystem B) :
    α • TypedSystem.sample P (fun k => TypedSystem.sample Q (R k)) =
      TypedSystem.sample Q (fun l => TypedSystem.sample P (fun k => α • R k l)) := by
  -- Exchange the independent choices before carrying attachment through them.
  rw [TypedSystem.sample_comm P Q R]
  simp only [TypedConverter.smul_sample]

/-- A fixed left system stays independent of the right component's retained pair. Moving the
pair outside and splitting it must not make the left system depend on either sample. -/
example {A B : Interface} {K L : Type} (R : TypedSystem A)
    (P : Distribution K) [Distribution.IsProbability P]
    (Q : Distribution L) [Distribution.IsProbability Q]
    (S : K × L → TypedSystem B) :
    R ∥ TypedSystem.sample (P.prod Q) S =
      TypedSystem.sample P (fun k =>
        TypedSystem.sample Q (fun l => R ∥ S (k, l))) := by
  -- Move the retained pair outside the parallel system, then split its independent law.
  rw [TypedSystem.parallel_sample_right, TypedSystem.sample_prod]

/-! ## Independence boundary -/

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

/-- A shared bit cannot give the reply `(false, true)`, whereas two independent uniform
bits give it with probability `1/4`. Thus the product and commutation laws cannot replace
a retained shared draw by independent draws. -/
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
    simp [Finsupp.mem_support_iff, Distribution.uniform_apply]
  -- The shared draw gives mass zero to the mixed reply; the independent draws give 1/4.
  norm_num [TypedSystem.sample_mass, TypedSystem.ofFunction_mass, replyPair,
    pairReplyInterface, mixedPairTranscript, Distribution.uniform_apply, hs] at hm
  simp [Prod.mk.injEq] at hm

#print axioms TypedSystem.sample_prod
#print axioms TypedSystem.sample_comm
#print axioms TypedSystem.parallel_sample_right

end SystemAlgebra.Tests.SamplingAlgebra
