module

public import Commons.Definitions.Ideal

/-!
# Retained uniform table of `Commons.URF`

`Commons.URF.eq_sample` and `Commons.URF.smul_eq_sample` expose the retained uniform function
table at any `Fintype` enumeration of `∀ i, A.X i → A.Y i`, without unfolding `Commons.URF`.
The checks below rewrite `Commons.URF` and its converter attachments at an explicit non-default
`Fintype` enumeration while preserving the domain, and verify directly from the exposed table
equation that two queries to the same port and input consult the same retained entry:
disagreeing answers have probability `0`, and matching answers on a Boolean evaluation interface
have probability `1 / 2`.
-/

@[expose] public section

namespace Tests.URFRetainedTable

open Commons SystemAlgebra Probability Probability.Distribution
open scoped SystemAlgebra

/-- Single-port Boolean evaluation with total query budget `2`. -/
abbrev bitEval : Interface := Evaluation Bool Bool 2

/-- Every port of `bitEval` has nonempty reply alphabet `Bool`. -/
instance : ∀ i, Nonempty (bitEval.Y i) := by
  intro i
  cases i
  exact ⟨false⟩

/-- Identify each table on `bitEval` with its pair of outputs `(f .eval false, f .eval true)`. -/
def tableEquiv : (∀ i, bitEval.X i → bitEval.Y i) ≃ Bool × Bool where
  toFun f := (f .eval false, f .eval true)
  invFun p i x := by
    cases i
    exact if x then p.2 else p.1
  left_inv f := by
    funext i x
    cases i
    cases x <;> rfl
  right_inv p := by
    cases p
    rfl

/-- An explicit `Fintype` enumeration of `bitEval` tables constructed from `Bool × Bool`,
distinct from `Pi.instFintype`. -/
@[instance_reducible]
def customTableFintype : Fintype (∀ i, bitEval.X i → bitEval.Y i) :=
  Fintype.ofEquiv (Bool × Bool) tableEquiv.symm

open Classical in
/-- Two `Fintype` enumerations of the table space induce the same raw and normalized uniform
laws. -/
example :
    @Distribution.uniform _ customTableFintype _ =
      Distribution.uniform (∀ i, bitEval.X i → bitEval.Y i) ∧
    @ProbDist.uniform _ customTableFintype _ =
      𝒰[∀ i, bitEval.X i → bitEval.Y i] :=
  ⟨uniform_congr_fintype customTableFintype _, ProbDist.uniform_congr_fintype customTableFintype _⟩

/-- `Commons.URF` rewrites to a retained uniform table at `customTableFintype` without changing
its domain or unfolding `Commons.URF`. -/
example :
    Commons.URF bitEval =
      TypedSystem.sample (@Distribution.uniform _ customTableFintype _)
        TypedSystem.ofFunction := by
  rw [URF.eq_sample (inst := customTableFintype)]

/-- With `customTableFintype` installed locally, `URF.eq_sample` also matches the normalized
uniform law `𝒰[...].1`. -/
example :
    let _ : Fintype (∀ i, bitEval.X i → bitEval.Y i) := customTableFintype
    Commons.URF bitEval =
      TypedSystem.sample 𝒰[∀ i, bitEval.X i → bitEval.Y i].1 TypedSystem.ofFunction := by
  let _ : Fintype (∀ i, bitEval.X i → bitEval.Y i) := customTableFintype
  rw [URF.eq_sample]
  rfl

/-- Attaching any domain-preserving converter `α` to `Commons.URF` rewrites at
`customTableFintype` without unfolding `Commons.URF`. -/
example {B : Interface}
    -- `α` translates outside queries on `B` into admitted queries on `bitEval`.
    (α : TypedConverter B bitEval) :
    α • Commons.URF bitEval =
      TypedSystem.sample (@Distribution.uniform _ customTableFintype _)
        (fun f => α • TypedSystem.ofFunction f) := by
  rw [URF.smul_eq_sample (inst := customTableFintype)]

/-- Repeating the same port and input cannot produce two different replies, proved directly from
`URF.eq_sample` without unfolding `Commons.URF`. -/
lemma urf_repeat_ne_mass_zero
    -- `A` fixes ports, alphabets and domain, with nonempty reply alphabets.
    (A : Interface) [∀ i, Nonempty (A.Y i)]
    -- `i(x)` is queried twice; `y₁` and `y₂` are distinct candidate replies.
    (i : A.I) (x : A.X i) (y₁ y₂ : A.Y i) (hne : y₁ ≠ y₂) :
    (Commons.URF A).1 [(⟨i, x⟩, ⟨i, y₁⟩), (⟨i, x⟩, ⟨i, y₂⟩)] = 0 := by
  classical
  -- Rewrite via the exposed retained-table equation without unfolding `Commons.URF`.
  rw [URF.eq_sample, TypedSystem.sample_ofFunction_mass_eq]
  apply mass_eq_zero_of_forall_not
  intro f hf
  -- Both reads evaluate the same retained entry `f i x`.
  have h₁ : (⟨i, y₁⟩ : Σ j, A.Y j) = ⟨i, f i x⟩ := hf.2 _ (List.mem_cons_self ..)
  have h₂ : (⟨i, y₂⟩ : Σ j, A.Y j) = ⟨i, f i x⟩ :=
    hf.2 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  exact hne (eq_of_heq (Sigma.mk.inj_iff.mp (h₁.trans h₂.symm)).2)

/-- Two reads of the same Boolean input consult the same retained table entry, so observing the
same reply `y` twice has probability `1 / 2`, proved from `URF.eq_sample` at
`customTableFintype`. -/
lemma bitEval_repeat_eq_mass
    -- `x` is the repeated Boolean input; `y` is the matching reply observed on both queries.
    (x y : Bool) :
    (Commons.URF bitEval).1
      [(⟨.eval, x⟩, ⟨.eval, y⟩), (⟨.eval, x⟩, ⟨.eval, y⟩)] = 1 / 2 := by
  let _ : Fintype (∀ i, bitEval.X i → bitEval.Y i) := customTableFintype
  let h : List ((Σ i, bitEval.X i) × Σ i, bitEval.Y i) :=
    [(⟨.eval, x⟩, ⟨.eval, y⟩), (⟨.eval, x⟩, ⟨.eval, y⟩)]
  -- Expose the retained uniform table at `customTableFintype`.
  change (Commons.URF bitEval).1 h = 1 / 2
  rw [URF.eq_sample, TypedSystem.sample_ofFunction_mass_eq]
  -- The 2-query history is admitted by `bitEval.domain`, and both queries constrain `f .eval x`.
  have hadm : h = [] ∨ bitEval.domain (h.map Prod.fst) :=
    Or.inr ⟨by simp only [h, List.map_cons, ne_eq, reduceCtorEq, not_false_eq_true], by
      simp only [h, List.map_cons, List.map_nil, List.length_cons, List.length_nil, le_refl]⟩
  have hmass :
      (Distribution.uniform (∀ i, bitEval.X i → bitEval.Y i)).mass
        (fun f => (h = [] ∨ bitEval.domain (h.map Prod.fst)) ∧
          ∀ z ∈ h, z.2 = ⟨z.1.1, f z.1.1 z.1.2⟩) =
      (Distribution.uniform (∀ i, bitEval.X i → bitEval.Y i)).mass
        (fun f => f .eval x = y) := by
    apply mass_congr
    intro f
    rw [and_iff_right hadm]
    simp only [h, List.mem_cons, List.not_mem_nil, or_false, or_self,
      forall_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and, eq_comm]
  rw [hmass]
  -- Push the uniform table along `tableEquiv` to `Bool × Bool` and project onto coordinate `x`.
  rw [← fTransform_equiv_uniform tableEquiv.symm, mass_fTransform, ← prod_uniform]
  cases x with
  | false =>
    change (prod (Distribution.uniform Bool) (Distribution.uniform Bool)).mass
      (fun p => p.1 = y) = 1 / 2
    rw [mass_prod_fst (R := fun b : Bool => b = y), weight_uniform, mul_one,
      mass_singleton, uniform_apply, Fintype.card_bool]
    norm_num
  | true =>
    change (prod (Distribution.uniform Bool) (Distribution.uniform Bool)).mass
      (fun p => p.2 = y) = 1 / 2
    rw [mass_prod_snd (R := fun b : Bool => b = y), weight_uniform, one_mul,
      mass_singleton, uniform_apply, Fintype.card_bool]
    norm_num

#print axioms Probability.Distribution.uniform_congr_fintype
#print axioms Probability.Distribution.ProbDist.uniform_congr_fintype
#print axioms Commons.URF.eq_sample
#print axioms Commons.URF.smul_eq_sample

end Tests.URFRetainedTable
