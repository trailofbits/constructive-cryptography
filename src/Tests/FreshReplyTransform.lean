module

public import Commons.Definitions.ReplyTransform

/-!
# Fresh replies across repeated calls

`freshBits` draws an auxiliary uniform bit on every invocation. Its two replies `false, true`
have probability `1/4`. `retainedBits` chooses one bit for both replies and gives that transcript
probability zero. The source contract therefore checks sampling scope across invocations.
-/

@[expose] public section

namespace Tests.FreshReplyTransform

open Commons Commons.Evaluation SystemAlgebra Probability Probability.Distribution

/-- Two `eval(())` queries, each returning a bit. -/
abbrev bitInterface : Interface := Evaluation.perPort Unit Bool (fun _ => 2)

/-- The transcript of two evaluations returning `false` and then `true`. -/
def mixedReplies : List
    ((Σ i, bitInterface.X i) × (Σ i, bitInterface.Y i)) :=
  [(⟨.eval, ()⟩, ⟨.eval, false⟩), (⟨.eval, ()⟩, ⟨.eval, true⟩)]

/-- Each evaluation draws a fresh fair bit and ignores the inside source's independent reply. -/
noncomputable def freshBits : TypedSystem bitInterface :=
  sampleReplies 𝒰[Bool] (fun b (_ : Bool) => b) (fun _ => 2) •
    MemorylessSource.perPort Bool 𝒰[Bool] (budget := fun _ => 2)

/-- Sample a fair bit once and return that same bit on both evaluations. -/
noncomputable def retainedBits : TypedSystem bitInterface :=
  TypedSystem.sample 𝒰[Bool] (fun b => TypedSystem.ofFunction fun _ _ => b)

/-- A fresh reply law `P` assigns the product `P(false) * P(true)` to two replies. -/
lemma two_reply_probability (P : ProbDist Bool) :
    (TypedSystem.ofMemoryless bitInterface (fun _ _ => P)).1 mixedReplies =
      P.1 false * P.1 true := by
  have d1 : bitInterface.inputDomain [] ⟨.eval, ()⟩ := by
    constructor
    · exact List.cons_ne_nil _ _
    · intro i; cases i
      norm_num [restrict_cons_self, restrict_nil]
  have d2 : bitInterface.inputDomain [(⟨.eval, ()⟩, ⟨.eval, false⟩)] ⟨.eval, ()⟩ := by
    constructor
    · exact List.cons_ne_nil _ _
    · intro i; cases i
      norm_num [restrict_cons_self, restrict_nil]
  -- Each admitted reply multiplies the preceding transcript mass by its fresh probability.
  change RandomSystem.memoryless bitInterface.inputDomain (RandomSystem.portLaw (fun _ _ => P))
    ([(⟨.eval, ()⟩, ⟨.eval, false⟩)] ++ [(⟨.eval, ()⟩, ⟨.eval, true⟩)]) = _
  rw [RandomSystem.memoryless_snoc, ite_eq_left d2, RandomSystem.portLaw_apply_mk]
  change RandomSystem.memoryless bitInterface.inputDomain (RandomSystem.portLaw (fun _ _ => P))
    ([] ++ [(⟨.eval, ()⟩, ⟨.eval, false⟩)]) * _ = _
  rw [RandomSystem.memoryless_snoc, ite_eq_left d1, RandomSystem.portLaw_apply_mk,
    RandomSystem.mass_nil, one_mul]

/-- The public component contract makes the auxiliary bits independent across calls. -/
lemma freshBits_probability : freshBits.1 mixedReplies = 1 / 4 := by
  rw [freshBits, sampleReplies_smul_memorylessSource, MemorylessSource.eq_ofMemoryless]
  rw [two_reply_probability]
  -- At the scalar probability leaf, discarding the independent reply recovers the first factor.
  change (fTransform Prod.fst (prod (uniform Bool) (uniform Bool))) false *
    (fTransform Prod.fst (prod (uniform Bool) (uniform Bool))) true = 1 / 4
  rw [fTransform_fst_prod, weight_uniform, one_smul]
  norm_num [uniform_apply]

/-- A retained bit cannot produce two different replies. -/
lemma retainedBits_probability : retainedBits.1 mixedReplies = 0 := by
  rw [retainedBits, TypedSystem.sample_mass]
  apply Finset.sum_eq_zero
  intro b _
  -- No fixed bit agrees with both the false reply and the true reply.
  have incompatible : ¬ (∀ z ∈ mixedReplies, z.2 = ⟨z.1.1, b⟩) := by
    intro replies
    have hf : false = b := by
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using
        replies _ List.mem_cons_self
    have ht : true = b := by
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using
        replies _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    exact Bool.noConfusion (hf.trans ht.symm)
  rw [TypedSystem.ofFunction_mass, ite_eq_right (fun h => incompatible h.2), mul_zero]

/-- Fresh sampling cannot be replaced by one draw shared by all invocations. -/
example : freshBits ≠ retainedBits := by
  intro he
  have hm := congrArg (fun R : TypedSystem bitInterface => R.1 mixedReplies) he
  rw [freshBits_probability, retainedBits_probability] at hm
  norm_num at hm

#print axioms TypedConverter.sampleReplies_smul_ofMemoryless
#print axioms sampleReplies_smul_memorylessSource
#print axioms freshBits_probability

end Tests.FreshReplyTransform
