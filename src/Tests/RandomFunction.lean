module

public import Commons.Definitions.Ideal
public import Probability.Kernel

/-!
# Retained nonuniform random functions

At input `false`, the reply is `true` with probability `1/3`; input `true` always gives
`false`. Two reads of the first entry have probability `1/3`, rather than the independent
draw probability `1/9`. Conflicting replies at the same entry have mass zero.
The lazy presentation preserves these laws under attachment and retains optional `none` replies.
-/

@[expose] public section

namespace Tests.RandomFunction

open Commons SystemAlgebra Probability Probability.Distribution

/-- One Boolean evaluation port, with at most two queries. -/
abbrev bitEval : Interface := Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) 2

/-- The reply law has masses `2/3` at `false` and `1/3` at `true`. -/
noncomputable def biased : ProbDist Bool :=
  ⟨Finsupp.single false (2 / 3) + Finsupp.single true (1 / 3), by
    constructor
    · intro b
      cases b <;> norm_num [Finsupp.add_apply, Finsupp.single_apply]
    · norm_num only [weight_add, weight_single]⟩

/-- `false` selects the biased law; `true` selects the point law at `false`. -/
noncomputable def entryLaw (x : Bool) : ProbDist Bool :=
  if x then ProbDist.single false else biased

/-- The retained table is assembled from independent input-dependent entries. -/
noncomputable def tableLaw : ProbDist (Unit → Bool → Bool) :=
  ProbDist.piDep (fun _ => ProbDist.piDep entryLaw)

lemma table_entry_mass (x y : Bool) :
    tableLaw.1.mass (fun f => f () x = y) = entryLaw x y := by
  classical
  have outer := congrArg Subtype.val
    (ProbDist.map_pi_apply (fun _ : Unit => ProbDist.pi entryLaw) ())
  have inner := congrArg Subtype.val (ProbDist.map_pi_apply entryLaw x)
  change fTransform (fun f => f ()) (pi (fun _ : Unit => (ProbDist.pi entryLaw).1)) =
    (ProbDist.pi entryLaw).1 at outer
  change fTransform (fun f => f x) (ProbDist.pi entryLaw).1 = (entryLaw x).1 at inner
  have law : tableLaw.1 = pi (fun _ : Unit => (ProbDist.pi entryLaw).1) := by
    simp only [tableLaw, ProbDist.piDep_val, piDep_eq_pi, ProbDist.pi_val]
  rw [law, ← mass_fTransform (fun f : Unit → Bool → Bool => f ())
    _ (fun f => f x = y), outer,
    ← mass_fTransform (fun f : Bool → Bool => f x) _ (fun z => z = y), inner,
    mass_singleton]

lemma repeat_mass (x y : Bool) :
    (randomFunction bitEval (fun _ => entryLaw)).1
      [(⟨(), x⟩, ⟨(), y⟩), (⟨(), x⟩, ⟨(), y⟩)] = entryLaw x y := by
  classical
  rw [randomFunction, TypedSystem.sample_ofFunction_mass_eq]
  change tableLaw.1.mass _ = _
  rw [← table_entry_mass x y]
  apply mass_congr
  intro f
  simp only [bitEval, Interface.queryBudget, List.map_cons, List.map_nil,
    List.length_cons, List.length_nil, List.mem_cons, List.not_mem_nil,
    or_false, or_self, forall_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and,
    reduceCtorEq, false_or, ne_eq, not_false_eq_true, le_refl, eq_comm]

/-- Repetition reads one entry: the joint probability is `1/3`. -/
theorem nonuniform_repeat_mass :
    (randomFunction bitEval (fun _ => entryLaw)).1
      [(⟨(), false⟩, ⟨(), true⟩), (⟨(), false⟩, ⟨(), true⟩)] = 1 / 3 := by
  rw [repeat_mass]
  norm_num [entryLaw, biased, Finsupp.single_apply]

/-- The other input has its own point law. -/
example : (randomFunction bitEval (fun _ => entryLaw)).1
    [(⟨(), true⟩, ⟨(), false⟩), (⟨(), true⟩, ⟨(), false⟩)] = 1 := by
  rw [repeat_mass]
  norm_num [entryLaw, ProbDist.single, Finsupp.single_apply]

/-- A retained entry cannot supply two different replies. -/
example : (randomFunction bitEval (fun _ => entryLaw)).1
    [(⟨(), false⟩, ⟨(), true⟩), (⟨(), false⟩, ⟨(), false⟩)] = 0 := by
  classical
  rw [randomFunction, TypedSystem.sample_ofFunction_mass_eq]
  apply mass_eq_zero_of_forall_not
  intro f hf
  have first : (⟨(), true⟩ : Σ i, bitEval.Y i) = ⟨(), f () false⟩ :=
    hf.2 _ (List.mem_cons_self ..)
  have second : (⟨(), false⟩ : Σ i, bitEval.Y i) = ⟨(), f () false⟩ :=
    hf.2 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have same : true = false := eq_of_heq (Sigma.mk.inj_iff.mp (first.trans second.symm)).2
  cases same

/-- Lazy repetition retains one biased draw, so the probability is `1/3`. -/
example : (randomFunction.lazy bitEval (fun _ => entryLaw)).1
    [(⟨(), false⟩, ⟨(), true⟩), (⟨(), false⟩, ⟨(), true⟩)] = 1 / 3 := by
  rw [randomFunction.lazy_eq]
  exact nonuniform_repeat_mass

/-- An arbitrary compatible converter sees the same retained nonuniform function. -/
example {B : Interface} (α : TypedConverter B bitEval) :
    α • randomFunction.lazy bitEval (fun _ => entryLaw) =
      α • randomFunction bitEval (fun _ => entryLaw) := by
  rw [randomFunction.lazy_eq]

-- The two ports carry genuinely different reply types; `none` is an ordinary retained reply.
interface MixedReplies
  bit() → Bool
  optional() → Option Bool

/-- The bit port is biased; the optional port returns `none` with probability `2/3`. -/
noncomputable def mixedLaws (q : ℕ) :
    ∀ i, (MixedReplies q).X i → ProbDist ((MixedReplies q).Y i)
  | .bit, () => biased
  | .optional, () => biased.map (fun b => if b then some true else none)

open Classical in
/-- A stored optional `none` is a hit: the table and reply are both retained with certainty. -/
example :
    let records : ∀ i, List ((MixedReplies 2).X i × (MixedReplies 2).Y i) :=
      Function.update (fun _ => []) .optional [((), none)]
    randomFunction.tableLaw (MixedReplies 2) (mixedLaws 2) records .optional () =
      ProbDist.single (records, none) := by
  intro records
  apply Subtype.ext
  simp only [randomFunction.tableLaw, ProbStep.recordReplies, randomFunction.replyLaw,
    records, Function.update_self, List.lookup_cons_self, Option.elim_some,
    Option.isNone_some, Bool.false_eq_true, ite_false, ProbDist.map_val,
    ProbDist.single, fTransform_single]

/-- The lazy correspondence also handles the heterogeneous optional-valued table. -/
example : randomFunction.lazy (MixedReplies 2) (mixedLaws 2) =
    randomFunction (MixedReplies 2) (mixedLaws 2) :=
  randomFunction.lazy_eq (MixedReplies 2) (mixedLaws 2)

#print axioms Commons.randomFunction.tableLaw_simulates
#print axioms Commons.randomFunction.lazy_eq

#print axioms Commons.randomFunction
#print axioms Commons.URF.eq_randomFunction
#print axioms nonuniform_repeat_mass

end Tests.RandomFunction
