module

public import RandomSystems.Typed.Functional
public import RandomSystems.Typed.Automaton
public import Tests.JointLaw

/-!
# Dependent retained presentations

The existing nonuniform law `first : ProbDist ℕ` chooses `n`, then another draw `m` chooses
one constant system with reply `even(n+m)`. The conditional system laws depend on `n`.
Flattening the two choices preserves both replies of that one retained system: opposite
replies have probability zero.
-/

@[expose] public noncomputable section

namespace Tests.MixturePresentation

open Probability Probability.Distribution SystemAlgebra
open Probability.Tests.JointLaw (first)

/-- Two queries at one port, each returning a Boolean reply. -/
abbrev observations : Interface := Interface.queryBudget Unit (fun _ => Unit) (fun _ => Bool) 2

/-- The deterministic resource retains `b` and returns it on both queries. -/
def constant (b : Bool) : {s : InterfaceSystem observations.I observations.X observations.Y //
    IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ observations.domain h} :=
  observations.automatonDDS (fun (_ : Unit) _ _ => ((), b)) ()

/-- The existing evaluator correspondence gives the fixed reply DDS on this interface. -/
lemma constant_eq_ofFunction (b : Bool) :
    (constant b).1 = (DDS.ofFunction observations.domain observations.nonempty_prefix
      (fun q => ⟨q.1, b⟩)).1 :=
  Interface.automatonDDS_eq_ofFunction observations (fun (_ : Unit) _ _ => b) ()

/-- Given `n`, draw `m` with masses `2/3` at 0 and `1/3` at 1, retaining `even(n+m)`. -/
def conditional (n : ℕ) := first.map fun m => constant ((n + m) % 2 == 0)

/-- The dependent DDS draw flattens while its outer index still ranges over infinite `ℕ`. -/
lemma flatten :
    TypedSystem.sample first.1 (fun n => TypedSystem.ofPDS (conditional n)) =
      TypedSystem.ofPDS (first.bind conditional) :=
  TypedSystem.sample_ofPDS first conditional

/-- The second reply contradicts the first; a retained constant system cannot produce this. -/
def oppositeReplies : List
    ((Σ i, observations.X i) × (Σ i, observations.Y i)) :=
  [(⟨(), ()⟩, ⟨(), false⟩), (⟨(), ()⟩, ⟨(), true⟩)]

/-- Neither branch of the dependent sampling law resamples a reply between calls. -/
lemma opposite_replies_mass :
    (TypedSystem.ofPDS (first.bind conditional)).1 oppositeReplies = 0 := by
  rw [← flatten, TypedSystem.sample_mass]
  apply Finset.sum_eq_zero
  intro n _
  have impossible (m : ℕ) :
      ¬ Replies (constant ((n + m) % 2 == 0)).1
        (oppositeReplies.map Prod.fst) (oppositeReplies.map Prod.snd) := by
    rw [constant_eq_ofFunction]
    rw [DDS.replies_ofFunction_iff]
    simp only [oppositeReplies, List.map_cons, List.map_nil, List.cons.injEq,
      Sigma.mk.inj_iff, heq_eq_eq, true_and, and_true]
    rintro ⟨_, hfalse, htrue⟩
    exact Bool.false_ne_true (hfalse.trans htrue.symm)
  change _ * behaviorMass (conditional n).1 _ _ = 0
  rw [conditional, ProbDist.map_val, behaviorMass, mass_fTransform,
    mass_eq_zero_of_forall_not _ impossible, mul_zero]

/-- The conditional laws differ: after index 0 the reply is true with mass 2/3, after 1 with 1/3. -/
example :
    (TypedSystem.ofPDS (conditional 0)).1 [(⟨(), ()⟩, ⟨(), true⟩)] = 2 / 3 ∧
    (TypedSystem.ofPDS (conditional 1)).1 [(⟨(), ()⟩, ⟨(), true⟩)] = 1 / 3 := by
  have probability (n : ℕ) :
      (TypedSystem.ofPDS (conditional n)).1 [(⟨(), ()⟩, ⟨(), true⟩)] =
        first.1.mass (fun m => (n + m) % 2 == 0) := by
    change behaviorMass (conditional n).1 _ _ = _
    rw [conditional, behaviorMass, ProbDist.map_val, mass_fTransform]
    apply mass_congr
    intro m
    rw [constant_eq_ofFunction, DDS.replies_ofFunction_iff]
    have admitted : observations.domain [⟨(), ()⟩] :=
      ⟨List.cons_ne_nil _ _, by simp only [List.length_singleton]; omega⟩
    simp only [List.map_cons, List.map_nil, List.cons_ne_nil, false_or, true_and,
      List.cons.injEq, and_true, Sigma.mk.inj_iff, heq_eq_eq]
    exact ⟨fun h => h.2.symm, fun h => ⟨admitted, h.symm⟩⟩
  constructor <;> rw [probability] <;>
    norm_num [Probability.Tests.JointLaw.first, ProbDist.map_val, mass_fTransform,
      mass_eq_sum, ProbDist.uniform, uniform_apply, Fin.sum_univ_succ]

/-- Signed presentations need agree only at the supported outer index 0; at every other
natural-number index the zero law fails to present this probability-one constant system. -/
example (h : List ((Σ i, observations.X i) × (Σ i, observations.Y i))) :
    RandomSystem.mix (ProbDist.single (0 : ℕ))
        (fun _ => (TypedSystem.ofDeterministic (constant false).1 (constant false).2).1) h =
      (bindK (ProbDist.single (0 : ℕ)).1
        (fun n => if n = 0 then Finsupp.single false (-1) + Finsupp.single true 2 else 0)).mass
        (fun _ => Replies (constant false).1 (h.map Prod.fst) (h.map Prod.snd)) := by
  apply RandomSystem.mix_mass_of_presentations
  intro n hn t
  have hn0 : n = 0 := by simpa [ProbDist.single] using hn
  subst n
  rw [TypedSystem.ofDeterministic_mass]
  simp only [ite_true, mass_add, mass_single]
  split_ifs <;> norm_num

#print axioms RandomSystem.mix_mass_of_presentations
#print axioms TypedSystem.sample_ofPDS
#print axioms constant_eq_ofFunction
#print axioms flatten
#print axioms opposite_replies_mass

end Tests.MixturePresentation
