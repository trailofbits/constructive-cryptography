import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Part
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
/-!
# Finite distributions

A distribution on `A` is a finitely supported function `A →₀ ℝ`. A probability
distribution is a nonnegative distribution of weight `1`. Source:
Lanzenberger–Maurer, *Coupling of Random Systems*, Definitions 1, 2 and 4.

## Main definitions

* `Distribution A`, `weight`, `NonNeg`, `isProbDist`, `IsProbability`, `ProbDist`
* `mass X P`: the mass of the event `P`; `restrict`, `evalSet`, `evalPred`
* `uniform A`: the uniform distribution on a finite type
* `marginal`, `marginalAt`: marginals of a joint distribution
* `fTransform f X`: the pushforward of `X` along `f`
* `RV`, `PMF`, `condPMF`: random variables, their laws and conditional laws,
  with the notations `ℙ⟦X⟧` and `ℙ⟦X | Y⟧`
* `prod`, `iidPow`, `clonePow`, `pi`: independent products

## Main results

* the mass calculus: additivity, complements, monotonicity, `mass_le_weight`
* pushforward: `mass_fTransform`, `weight_fTransform`, `fTransform_comp`,
  `fTransform_prod`, `fTransform_equiv_uniform`
* products: `prod_apply`, `weight_prod`, `mass_prod_fst`, `mass_prod_snd`,
  `mass_prod_eq_sum`, `weight_pi`, `marginalAt_pi`, `fTransform_pi_castLE` (the first `k'` of `k`
  independent samples)
* probability is preserved by pushforward, products and finite mixtures:
  `fTransform_isProbDist`, `prod_isProbDist`, `isProbDist_sum_smul`
-/

noncomputable section

open scoped BigOperators NNReal

namespace Probability

/-- A finite distribution over `A`: a finitely supported function `A → ℝ`.

Paper Definition 1: "A distribution X : A → ℝ≥0 with finite support."
We do NOT require weight = 1 (sub-distributions appear in Theorem 1 proof),
and the codomain is the signed reals: non-negativity is a predicate
(`Distribution.NonNeg`), not part of the carrier. -/
abbrev Distribution (A : Type*) := A →₀ ℝ

namespace Distribution

set_option linter.unusedSectionVars false

-- Decidability policy: these classical instances serve PROOFS only.  Any
-- lemma whose STATEMENT contains a decidability-dependent term
-- (`Finset.filter`, `if`) must take the instance as an explicit binder
-- (`[DecidablePred p]` / `[DecidableEq B]`), so the statement instantiates
-- with the caller's ambient instance and `rw`/`simp` match in both classical
-- and `[DecidableEq]`-world files.
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {A : Type*} {B : Type*} {Ω : Type*} {C : Type*}
variable [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
variable [Fintype Ω] [Nonempty Ω] [Fintype C] [Nonempty C]

/-- The weight (total mass) of a distribution.
Paper: `|X| := ∑_{a ∈ A} X(a)`. -/
def weight (X : Distribution A) : ℝ :=
  X.sum fun _ w => w

/-- Pointwise non-negativity of a finite-support mass function.  Over the
signed carrier `A →₀ ℝ` this is no longer structural; honest distributions
carry it as a predicate. -/
def NonNeg {A : Type*} (X : Distribution A) : Prop := ∀ a, 0 ≤ X a

omit [Fintype A] [Nonempty A] in
theorem NonNeg.weight_nonneg {X : Distribution A} (hX : X.NonNeg) : 0 ≤ X.weight :=
  Finset.sum_nonneg fun a _ => hX a

omit [Nonempty A] in
/-- On a finite carrier, support-based weight is the ordinary sum over all
points.  (Needs `Fintype A` but not `Nonempty A` — the latter is a section-variable leak.) -/
theorem weight_eq_sum (X : Distribution A) :
    X.weight = ∑ a : A, X a := by
  simpa [weight] using
    (Finsupp.sum_fintype (f := X) (g := fun _ w => w) (h := by intro _; rfl))

/-- The weight is the sum over **any** finite set containing the support:
points outside the support carry no mass.  This is the `Fintype`-free
companion of `weight_eq_sum`, and the form needed on carriers that are
genuinely infinite (transcript spaces, system laws). -/
theorem weight_eq_sum_of_support_subset {A : Type*} (X : Distribution A)
    {s : Finset A} (hs : X.support ⊆ s) :
    X.weight = ∑ a ∈ s, X a :=
  Finsupp.sum_of_support_subset X hs (fun _ w => w) (fun _ _ => rfl)

omit [Nonempty A] in
/-- A mass function on a finite carrier as a finite-support distribution. -/
def ofFiniteMassFunction (law : A → ℝ) : Distribution A :=
  Finsupp.onFinset Finset.univ law (by intro a _; exact Finset.mem_univ a)

omit [Nonempty A] in
@[simp]
theorem ofFiniteMassFunction_apply (law : A → ℝ) (a : A) :
    ofFiniteMassFunction law a = law a := by
  simp [ofFiniteMassFunction]

omit [Nonempty A] in
/-- The total weight of a finite mass function as a distribution is the sum of
its masses over the carrier. -/
theorem weight_ofFiniteMassFunction (law : A → ℝ) :
    (ofFiniteMassFunction law).weight = ∑ a : A, law a := by
  simp [weight_eq_sum, ofFiniteMassFunction]

/-- A distribution is a probability distribution if it is pointwise
non-negative and its weight is 1.  (Over the `NNReal` carrier the first
conjunct was structural; over `ℝ` it is part of the definition, so the
`ProbDist` boundary keeps its meaning.) -/
def isProbDist (X : Distribution A) : Prop := X.NonNeg ∧ X.weight = 1

/-- Lanzenberger, Definition 2.1 (p. 11): “A probability distribution is a
distribution X with weight 1”. The signed carrier also requires nonnegativity. -/
class IsProbability (X : Distribution A) : Prop where
  nonNeg : X.NonNeg
  weight_eq_one : X.weight = 1

omit [Fintype A] [Nonempty A] in
/-- The probability capability supplies the underlying distribution predicate. -/
theorem IsProbability.isProbDist (X : Distribution A) [IsProbability X] : X.isProbDist :=
  ⟨IsProbability.nonNeg, IsProbability.weight_eq_one⟩

omit [Fintype A] [Nonempty A] in
theorem isProbDist.nonNeg {X : Distribution A} (hX : X.isProbDist) : X.NonNeg := hX.1

omit [Fintype A] [Nonempty A] in
theorem isProbDist.weight_eq {X : Distribution A} (hX : X.isProbDist) : X.weight = 1 :=
  hX.2

/-- Probability distributions are distributions with total mass one. -/
abbrev ProbDist (A : Type*) := {X : Distribution A // X.isProbDist}

instance (X : ProbDist A) : IsProbability X.val := ⟨X.property.1, X.property.2⟩

/-- Probability distributions evaluate like their underlying mass functions. -/
instance : CoeFun (ProbDist A) (fun _ => A → ℝ) where
  coe X := X.val

/-- Represent a probability law by its finite support subtype.

This is useful when a downstream side condition should range over exactly the
samples that can occur under the law, without requiring the whole ambient
carrier to be finite or relevant. -/
noncomputable def supportProbDist {A : Type*} (D : ProbDist A) :
    ProbDist {a : A // a ∈ D.val.support} :=
  ⟨ofFiniteMassFunction (fun a : {a : A // a ∈ D.val.support} => D.val a.1), by
    refine ⟨fun a => by simpa using D.property.nonNeg a.1, ?_⟩
    rw [weight_ofFiniteMassFunction]
    rw [← D.property.weight_eq]
    unfold weight
    rw [Finsupp.sum]
    exact Finset.sum_attach D.val.support (fun a => D.val a)⟩

@[simp]
theorem supportProbDist_apply {A : Type*} (D : ProbDist A)
    (a : {a : A // a ∈ D.val.support}) :
    supportProbDist D a = D.val a.1 := by
  rfl

omit [Fintype A] [Nonempty A] in
/-- A unit point mass is a probability distribution. -/
theorem isProbDist_single (a : A) :
    isProbDist (Finsupp.single a (1 : ℝ) : Distribution A) := by
  constructor
  · intro b
    rw [Finsupp.single_apply]
    split <;> norm_num
  · rw [weight, Finsupp.sum_single_index rfl]

omit [Fintype A] [Nonempty A] in
/-- The point mass at `a`. -/
noncomputable def ProbDist.single (a : A) : ProbDist A :=
  ⟨Finsupp.single a 1, isProbDist_single a⟩

omit [Fintype A] [Nonempty A] in
/-- A probability distribution has a sample. -/
theorem ProbDist.nonempty (P : ProbDist A) : Nonempty A := by
  by_contra hA
  rw [not_nonempty_iff] at hA
  have hw := P.2.2
  rw [weight, Finsupp.sum, Finset.eq_empty_of_isEmpty P.1.support] at hw
  simp at hw

omit [Fintype A] [Nonempty A] in
/-- A unit point mass has the probability capability. -/
instance (a : A) : IsProbability (Finsupp.single a (1 : ℝ) : Distribution A) :=
  ⟨(isProbDist_single a).1, (isProbDist_single a).2⟩

/-- Evaluate a distribution on a subset.
Paper: `X(B) := ∑_{a ∈ B} X(a)`. -/
def evalSet (X : Distribution A) (B : Finset A) : ℝ :=
  ∑ a ∈ B, X a

/-- Event mass of a distribution, summed over its finite support.

This is the support-based form of CR18/LM20 Definition 1 notation
`X(A) := ∑_{a ∈ A} X(a)`. Unlike `evalPred`, it does not require
`Fintype A`; the finite support is already carried by `Distribution A = A →₀ ℝ`. -/
noncomputable def mass (X : Distribution A) (P : A → Prop) : ℝ :=
  X.sum fun a w => if P a then w else 0

omit [Fintype A] [Nonempty A] in
/-- Event mass of a non-negative distribution is non-negative. -/
theorem NonNeg.mass_nonneg {X : Distribution A} (hX : X.NonNeg) (P : A → Prop) :
    0 ≤ X.mass P :=
  Finset.sum_nonneg fun a _ => by
    by_cases h : P a <;> simp [h, hX a]

omit [Fintype A] [Nonempty A] in
/-- Event mass is additive in the distribution: `(X + Y)(P) = X(P) + Y(P)`.
Signed layer, no `Fintype` — the companion of `weight_smul`/`mass_smul`
(`Probability.Lift`) on the additive side. -/
theorem mass_add (X Y : Distribution A) (P : A → Prop) :
    (X + Y).mass P = X.mass P + Y.mass P := by
  classical
  unfold mass
  rw [Finsupp.sum_add_index' (fun a => by simp)
    (fun a b₁ b₂ => by by_cases h : P a <;> simp [h])]

omit [Fintype A] [Nonempty A] in
/-- Event mass as a filtered sum over **any** finite set containing the
support: the summands vanish off the support, so the value does not depend on
which superset is chosen.  This is the working form of `mass` on carriers that
are genuinely infinite, and the companion of
`Distribution.weight_eq_sum_of_support_subset` and
`Probability.statDist_eq_sum_of_support_subset`.

The decidability of `P` is an explicit binder, per this file's decidability
policy: the statement contains a `Finset.filter`, so it must instantiate with
the caller's ambient instance. -/
theorem mass_eq_sum_of_support_subset (X : Distribution A) {s : Finset A}
    (hs : X.support ⊆ s) (P : A → Prop) [DecidablePred P] :
    X.mass P = ∑ a ∈ s.filter P, X a := by
  classical
  rw [Finset.sum_filter, mass,
    Finsupp.sum_of_support_subset X hs _ (fun a _ => by simp)]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : P a <;> simp [h]

/-- Restrict a distribution to an event, dropping all mass outside it. -/
noncomputable def restrict {A : Type*} (X : Distribution A) (P : A → Prop) : Distribution A :=
  Finsupp.filter P X

@[simp]
theorem restrict_apply {A : Type*} (X : Distribution A) (P : A → Prop) (a : A) :
    X.restrict P a = if P a then X a else 0 := by
  simp [restrict, Finsupp.filter_apply]

/-- Restriction preserves non-negativity. -/
theorem NonNeg.restrict {A : Type*} {X : Distribution A} (hX : X.NonNeg) (P : A → Prop) :
    (X.restrict P).NonNeg := fun a => by
  rw [restrict_apply]
  by_cases h : P a <;> simp [h, hX a]

/-- The mass of `P` after restricting to `Q` is the mass of `P ∩ Q`. -/
theorem mass_restrict {A : Type*} (X : Distribution A) (P Q : A → Prop) :
    (X.restrict Q).mass P = X.mass (fun a => P a ∧ Q a) := by
  unfold restrict mass Finsupp.sum
  simp only [Finsupp.support_filter, Finsupp.filter_apply]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases hP : P a <;> by_cases hQ : Q a <;> simp [hP, hQ]

theorem mass_true {A : Type*} (X : Distribution A) :
    X.mass (fun _ => True) = X.weight := by
  unfold mass weight
  simp

/-- A pointwise-impossible event has zero mass. -/
theorem mass_eq_zero_of_forall_not {A : Type*} (X : Distribution A) {P : A → Prop}
    (h : ∀ a, ¬ P a) : X.mass P = 0 := by
  unfold mass Finsupp.sum
  exact Finset.sum_eq_zero fun a _ => if_neg (h a)

/-- Mass depends only on the event up to logical equivalence. -/
theorem mass_congr {A : Type*} (X : Distribution A) {P Q : A → Prop} (h : ∀ a, P a ↔ Q a) :
    X.mass P = X.mass Q := by
  unfold mass
  congr 1
  funext a w
  simp only [h a]

/-- `mass_congr` with the equivalence required only on the support — mass sums
over the support, so that is all it reads. -/
theorem mass_congr_of_support {A : Type*} (X : Distribution A) {P Q : A → Prop}
    (h : ∀ a ∈ X.support, (P a ↔ Q a)) : X.mass P = X.mass Q := by
  unfold mass
  refine Finsupp.sum_congr fun a ha => ?_
  simp only [h a ha]

open scoped Classical in
/-- An event and its complement partition the total mass: `X(P) + X(¬P) = |X|`. -/
theorem mass_add_compl {A : Type*} (X : Distribution A) (P : A → Prop) :
    X.mass P + X.mass (fun a => ¬ P a) = X.weight := by
  unfold mass weight Finsupp.sum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by by_cases h : P a <;> simp [h]

/-- **Splitting one event by another**: `X(Q) = X(P ∧ Q) + X(¬P ∧ Q)`.  The
relative form of `mass_add_compl`, which is the case `Q = True`.  Signed layer:
the pointwise indicator identity, summed. -/
theorem mass_and_add_mass_not_and {A : Type*} (X : Distribution A) (P Q : A → Prop) :
    X.mass (fun a => P a ∧ Q a) + X.mass (fun a => ¬ P a ∧ Q a) = X.mass Q := by
  classical
  simp only [Distribution.mass, Finsupp.sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hp : P a <;> by_cases hq : Q a <;> simp [hp, hq]

/-- The mass of an event never exceeds the total mass of a non-negative
distribution: `X(P) ≤ |X|`. -/
theorem mass_le_weight {A : Type*} {X : Distribution A} (hX : X.NonNeg) (P : A → Prop) :
    X.mass P ≤ X.weight := by
  rw [← mass_add_compl X P]
  exact le_add_of_nonneg_right (hX.mass_nonneg _)

/-- Monotonicity of event mass: a weaker event carries at least as much mass. -/
theorem mass_mono {A : Type*} {X : Distribution A} (hX : X.NonNeg) {P Q : A → Prop}
    (h : ∀ a, P a → Q a) : X.mass P ≤ X.mass Q := by
  classical
  simp only [Distribution.mass, Finsupp.sum]
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases hP : P a
  · simp [hP, h a hP]
  · by_cases hQ : Q a <;> simp [hP, hQ, hX a]

/-- **A single atom is below the mass of any event it satisfies**: `X a ≤ X(P)`
when `P a`.  Non-negativity is what makes the other summands harmless — the
signed-carrier form of `Finset.single_le_sum` for `Distribution.mass`.

A support atom witnessing an event forces that event to carry positive mass,
so an event of mass zero has no witness in the support. -/
theorem apply_le_mass {A : Type*} {X : Distribution A} (hX : X.NonNeg)
    {P : A → Prop} {a : A} (ha : P a) : X a ≤ X.mass P := by
  classical
  by_cases hsupport : a ∈ X.support
  · unfold Distribution.mass Finsupp.sum
    calc X a = (if P a then X a else 0) := (if_pos ha).symm
      _ ≤ _ := Finset.single_le_sum
          (f := fun a' => if P a' then X a' else 0)
          (fun a' _ => by by_cases h : P a' <;> simp [h, hX a']) hsupport
  · rw [Finsupp.notMem_support_iff.mp hsupport]
    exact hX.mass_nonneg _

/-- `mass_mono` with the implication required only on the support — mass is
a support sum, so off-support behavior of the events is irrelevant. -/
theorem mass_mono_on_support {A : Type*} {X : Distribution A} (hX : X.NonNeg)
    {P Q : A → Prop} (h : ∀ a ∈ X.support, P a → Q a) :
    X.mass P ≤ X.mass Q := by
  classical
  simp only [Distribution.mass, Finsupp.sum]
  refine Finset.sum_le_sum fun a ha => ?_
  by_cases hP : P a
  · simp [hP, h a ha hP]
  · by_cases hQ : Q a <;> simp [hP, hQ, hX a]

/-- Subadditivity over a disjunction — the two-event union bound. -/
theorem mass_or_le {A : Type*} {X : Distribution A} (hX : X.NonNeg) (P Q : A → Prop) :
    X.mass (fun a => P a ∨ Q a) ≤ X.mass P + X.mass Q := by
  classical
  simp only [Distribution.mass, Finsupp.sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases hpq : P a ∨ Q a
  · rw [if_pos hpq]
    rcases hpq with hp | hq
    · rw [if_pos hp]
      refine le_add_of_nonneg_right ?_
      by_cases hq : Q a <;> simp [hq, hX a]
    · rw [if_pos hq]
      refine le_add_of_nonneg_left ?_
      by_cases hp : P a <;> simp [hp, hX a]
  · rw [if_neg hpq]
    push Not at hpq
    simp [hpq.1, hpq.2]

/-- The `Finset`-indexed union bound — `mass_or_le` iterated. -/
theorem mass_exists_le {A ι : Type*} {X : Distribution A} (hX : X.NonNeg) (s : Finset ι)
    (P : ι → A → Prop) :
    X.mass (fun a => ∃ i ∈ s, P i a) ≤ ∑ i ∈ s, X.mass (P i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using le_of_eq (mass_eq_zero_of_forall_not X (by simp))
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      refine le_trans (le_trans (mass_mono hX (Q := fun x => P a x ∨ ∃ i ∈ t, P i x)
        (by rintro x ⟨i, hi, hix⟩
            rcases Finset.mem_insert.mp hi with rfl | hi'
            · exact Or.inl hix
            · exact Or.inr ⟨i, hi', hix⟩))
        (mass_or_le hX _ _)) ?_
      linarith [ih]

/-- Restricting to an event leaves exactly the mass of that event. -/
theorem weight_restrict {A : Type*} (X : Distribution A) (P : A → Prop) :
    (X.restrict P).weight = X.mass P := by
  rw [← mass_true (X.restrict P), mass_restrict]
  simp

end Distribution

namespace CryptoNotation

/-- Event-mass notation:
- `Pr[φ(x) | x ←$ D]` expands to `Distribution.mass D (fun x => φ x)`.

This follows CR18/LM20 Definition 1: distributions are finite-support mass
functions, and event probability/mass is obtained by summing the weights in the
event over that support. -/
scoped syntax "Pr[" term " | " Lean.Parser.Term.funBinder " ←$ " term "]" : term
scoped macro_rules
  | `(Pr[$body | $b:funBinder ←$ $D]) =>
      `(Probability.Distribution.mass $D (fun $b => $body))

/-- Conditional event-mass notation:
- `Pr[φ(x) | x ←$ D, ψ(x)]` expands to
  `Distribution.cond D (fun x => φ x) (fun x => ψ x)`.

The result is partial, undefined exactly when the conditioning event has mass
zero. -/
scoped syntax "Pr[" term " | " Lean.Parser.Term.funBinder " ←$ " term ", " term "]" : term
scoped macro_rules
  | `(Pr[$body | $b:funBinder ←$ $D, $cond]) =>
      `(Probability.Distribution.cond $D (fun $b => $body) (fun $b => $cond))

end CryptoNotation

namespace Distribution

set_option linter.unusedSectionVars false

-- Decidability policy: these classical instances serve PROOFS only.  Any
-- lemma whose STATEMENT contains a decidability-dependent term
-- (`Finset.filter`, `if`) must take the instance as an explicit binder
-- (`[DecidablePred p]` / `[DecidableEq B]`), so the statement instantiates
-- with the caller's ambient instance and `rw`/`simp` match in both classical
-- and `[DecidableEq]`-world files.
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {A : Type*} {B : Type*} {Ω : Type*} {C : Type*}
variable [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
variable [Fintype Ω] [Nonempty Ω] [Fintype C] [Nonempty C]

/-- Evaluate a distribution on a predicate: the total mass of elements satisfying `P`.

`evalPred X P = ∑_{a : P(a)} X(a)`

This finite-carrier predicate evaluator is equivalent to
`evalSet X (Finset.univ.filter P)`. Prefer `mass` when the finite support of
the distribution itself should supply the finiteness, as in CR18. -/
def evalPred (X : Distribution A) (P : A → Prop) : ℝ :=
  ∑ a ∈ Finset.univ.filter P, X a

@[simp]
theorem evalPred_eq_evalSet (X : Distribution A) (P : A → Prop) :
    X.evalPred P = X.evalSet (Finset.univ.filter P) := by
  rfl

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
  [Fintype Ω] [Nonempty Ω] [Fintype C] [Nonempty C] in
/-- The uniform distribution over a finite nonempty type.
`uniform A` assigns mass `1 / |A|` to each element. -/
def uniform (A : Type*) [Fintype A] [Nonempty A] : Distribution A :=
  Finsupp.equivFunOnFinite.invFun (fun _ => (1 : ℝ) / (Fintype.card A : ℝ))

/-! ### Uniform distribution lemmas -/

/-- Pointwise evaluation of the uniform distribution. -/
theorem uniform_apply (a : A) :
    (uniform A) a = 1 / (Fintype.card A : ℝ) := by
  simp [uniform, Finsupp.equivFunOnFinite]

/-- The uniform distribution is pointwise non-negative. -/
theorem uniform_nonNeg : (uniform A).NonNeg := fun a => by
  rw [uniform_apply]
  positivity

/-- The uniform distribution has weight 1. -/
theorem weight_uniform :
    (uniform A).weight = 1 := by
  rw [weight_eq_sum]
  have h_card_pos : (0 : ℝ) < (Fintype.card A : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  rw [Finset.sum_congr rfl (fun a _ => uniform_apply a)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel₀]
  exact_mod_cast h_card_pos.ne'

/-- The uniform distribution is a probability distribution. -/
theorem uniform_isProbDist :
    (uniform A).isProbDist := ⟨uniform_nonNeg, weight_uniform⟩

instance : IsProbability (uniform A) := ⟨uniform_nonNeg, weight_uniform⟩

/-- The unique probability distribution on a one-point sample space. -/
def unitProbDist : ProbDist PUnit :=
  ⟨uniform PUnit, uniform_isProbDist⟩

/-- The marginal distribution obtained by projecting onto the first component.

Paper Definition 2: Given a joint distribution X_{A×B}, the marginal X_A is
  X_A(a) := ∑_{b ∈ B} X_{A×B}(a, b). -/
def marginal (X : Distribution (A × B)) : Distribution A :=
  X.sum (fun ⟨a, _⟩ w => Finsupp.single a w)

/-- The marginal of a distribution over a finite product, projected to one
coordinate.

For a family of alphabets `X : ι → Type*`, a point of the product is a function
`x : (i : ι) → X i`. The marginal at `j : ι` is the pushforward by evaluation
at `j`, i.e. `x ↦ x j`. -/
def marginalAt {ι : Type*} {X : ι → Type*}
    (F : Distribution ((i : ι) → X i)) (j : ι) : Distribution (X j) :=
  F.sum (fun x w => Finsupp.single (x j) w)

/-- Pointwise form of `marginalAt`: the mass at `xj` is the mass of the fiber
of product points whose `j`-th coordinate equals `xj`. -/
theorem marginalAt_apply {ι : Type*} {X : ι → Type*}
    (F : Distribution ((i : ι) → X i)) (j : ι) (xj : X j) :
    marginalAt F j xj = F.mass (fun x => x j = xj) := by
  unfold marginalAt mass
  simp only [Finsupp.sum_apply, Finsupp.single_apply]

/-- The f-transformation of a distribution.

Paper Definition 4: Given a distribution X over A and f : A → B,
  (f(X))(b) := ∑_{a : f(a) = b} X(a).

This is the pushforward measure in the discrete case. -/
def fTransform (f : A → B) (X : Distribution A) : Distribution B :=
  X.sum (fun a w => Finsupp.single (f a) w)

/-- Pushforward composes. -/
theorem fTransform_fTransform {A B C : Type*}
    (f : B → C) (g : A → B) (X : Distribution A) :
    fTransform f (fTransform g X) = fTransform (f ∘ g) X := by
  show Finsupp.mapDomain f (Finsupp.mapDomain g X) = Finsupp.mapDomain (f ∘ g) X
  exact (Finsupp.mapDomain_comp (v := X)).symm

/-- Pointwise evaluation of a pushforward is the mass of the fiber. -/
theorem fTransform_apply_eq_mass {A B : Type*}
    (f : A → B) (X : Distribution A) (b : B) :
    fTransform f X b = X.mass (fun a => f a = b) := by
  unfold fTransform mass
  simp only [Finsupp.sum_apply, Finsupp.single_apply]

/-- Evaluating a pushforward at an image point of an injective map recovers the
original mass. -/
theorem fTransform_injective_apply {A B : Type*}
    (X : Distribution A) (f : A → B) (hf : Function.Injective f) (a : A) :
    fTransform f X (f a) = X a := by
  simp only [fTransform, Finsupp.sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.single_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro a' _ hne
    simp [hf.ne hne]
  · intro ha
    simp [Finsupp.notMem_support_iff.mp ha]

/-- Evaluating a pushforward away from the image of the map gives zero mass. -/
theorem fTransform_apply_of_forall_ne {A B : Type*}
    (X : Distribution A) (f : A → B) (b : B) (h : ∀ a, f a ≠ b) :
    fTransform f X b = 0 := by
  simp only [fTransform, Finsupp.sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro a _
  simp [h a]

/-- Every support element of a pushforward has a support witness in the source
distribution. -/
theorem mem_support_fTransform {A B : Type*} (f : A → B) (X : Distribution A) {b : B}
    (hb : b ∈ (fTransform f X).support) : ∃ a ∈ X.support, f a = b := by
  classical
  have hsub : (fTransform f X).support ⊆ X.support.image f := Finsupp.mapDomain_support
  simpa [fTransform] using hsub hb

/-- A weighted sum over a pushforward pulls the summand back. -/
theorem sum_fTransform_mul {A B : Type*} (f : A → B) (X : Distribution A) (g : B → ℝ) :
    (fTransform f X).sum (fun b w => w * g b) = X.sum (fun a w => w * g (f a)) := by
  classical
  unfold fTransform
  exact Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

/-- Event mass under a pushforward is event mass of the preimage. -/
theorem mass_fTransform {A B : Type*}
    (f : A → B) (X : Distribution A) (P : B → Prop) :
    (fTransform f X).mass P = X.mass (fun a => P (f a)) := by
  unfold fTransform mass
  show (Finsupp.mapDomain f X).sum (fun b w => if P b then w else 0) =
      X.sum (fun a w => if P (f a) then w else 0)
  rw [Finsupp.sum_mapDomain_index
    (fun b => by by_cases hb : P b <;> simp [hb])
    (fun b m₁ m₂ => by by_cases hb : P b <;> simp [hb])]

/-- Pushforward preserves total mass. -/
theorem weight_fTransform {A B : Type*}
    (f : A → B) (X : Distribution A) :
    (fTransform f X).weight = X.weight := by
  unfold weight
  show (Finsupp.mapDomain f X).sum (fun _ w => w) = X.sum (fun _ w => w)
  rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]

/-- Pushforward preserves non-negativity: the mass at each image point is a
sum of non-negative source masses. -/
theorem NonNeg.fTransform {A B : Type*} {X : Distribution A} (hX : X.NonNeg)
    (f : A → B) : (Distribution.fTransform f X).NonNeg := fun b => by
  rw [fTransform_apply_eq_mass]
  exact hX.mass_nonneg _

/-- Pushforward preserves total probability mass. -/
theorem fTransform_isProbDist {A B : Type*} (f : A → B) {X : Distribution A}
    (hX : X.isProbDist) : (fTransform f X).isProbDist := by
  refine ⟨hX.nonNeg.fTransform f, ?_⟩
  rw [weight_fTransform]
  exact hX.weight_eq

instance {A B : Type*} (f : A → B) (X : Distribution A) [IsProbability X] :
    IsProbability (fTransform f X) :=
  ⟨(fTransform_isProbDist f (IsProbability.isProbDist X)).1,
    (fTransform_isProbDist f (IsProbability.isProbDist X)).2⟩

/-- `isProbDist` normalizes through pushforward — for a non-negative source
law.  (Over the signed carrier the unconditional `↔` is false: a pushforward
can merge cancelling signed masses into a non-negative law.) -/
theorem isProbDist_fTransform {A B : Type*} (f : A → B) {X : Distribution A}
    (hX : X.NonNeg) :
    (fTransform f X).isProbDist ↔ X.isProbDist := by
  constructor
  · intro h
    refine ⟨hX, ?_⟩
    rw [← weight_fTransform f X]
    exact h.weight_eq
  · exact fTransform_isProbDist f

/-- An injective pushforward reflects non-negativity: every source mass shows
up unmerged at its image point. -/
theorem NonNeg.of_fTransform_injective {A B : Type*} {X : Distribution A} {f : A → B}
    (hf : Function.Injective f) (h : (Distribution.fTransform f X).NonNeg) : X.NonNeg :=
  fun a => by
    have := h (f a)
    rwa [fTransform_injective_apply X f hf] at this

/-- `isProbDist` normalizes through an **injective** pushforward with no
side condition: injectivity rules out merging cancelling signed masses. -/
@[simp]
theorem isProbDist_fTransform_of_injective {A B : Type*} {f : A → B}
    (hf : Function.Injective f) (X : Distribution A) :
    (fTransform f X).isProbDist ↔ X.isProbDist := by
  constructor
  · intro h
    have hX : X.NonNeg := NonNeg.of_fTransform_injective hf h.nonNeg
    exact (isProbDist_fTransform f hX).mp h
  · exact fTransform_isProbDist f

/-- Dividing every mass by `c` divides the total mass by `c`. -/
theorem weight_mapRange_div {A : Type*} (X : Distribution A) (c : ℝ) :
    weight (Finsupp.mapRange (fun w => w / c) (by simp) X : Distribution A) =
      X.weight / c := by
  unfold weight
  rw [Finsupp.sum_mapRange_index]
  · unfold Finsupp.sum
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _ha
    exact div_eq_mul_inv (X a) c
  · intro a
    simp

/-! ### Random variables -/

/-- A random variable is a function from a sample space to a value space.

This is intentionally only an abbreviation, matching Mathlib's discipline:
random variables are functions; distributions over their values are obtained
by pushforward. -/
abbrev RV : Type _ :=
  Ω → A

/-- The probability mass function induced by a random variable.

`PMF p X` is the low-level Lean form of the paper notation `P_X`: the
ambient random experiment has mass function `p` on outcomes `ω`, and
`P_X(a) = ∑_{ω : X ω = a} p(ω)`.

Paper-facing notation below suppresses `p`, matching Maurer's convention that
probabilities are taken in the current random experiment. -/
def PMF (p : ProbDist Ω) (X : RV (Ω := Ω) (A := A)) : ProbDist A :=
  ⟨fTransform X p.val, fTransform_isProbDist X p.property⟩

/-- Paper-facing PMF notation in the current random experiment.

The notation intentionally omits the low-level experiment mass `p`, following
CR18/Maurer notation. In Lean, it expands using the ambient variable named
`p : ProbDist Ω`. -/
syntax "ℙ⟦" term "⟧" : term
syntax "ℙ⟦" term "⟧[" term "]" : term
macro "ℙ⟦" X:term "⟧" : term => do
  let p := Lean.mkIdent `p
  `(Probability.Distribution.PMF $p $X)
macro "ℙ⟦" X:term "⟧[" x:term "]" : term => do
  let p := Lean.mkIdent `p
  `(Probability.Distribution.PMF $p $X $x)

/-! ### Function-valued random variables -/

/-- Conditional law of a random variable given an event on the sample space.

`condPMF p X E` is undefined exactly when `p(E) = 0`. When it is defined, its
mass at `a` is `Pr[X = a ∧ E] / Pr[E]`. -/
noncomputable def condPMF {Ω A : Type*} (p : ProbDist Ω)
    (X : RV (Ω := Ω) (A := A)) (E : Ω → Prop) : Part (ProbDist A) :=
  ⟨p.val.mass E ≠ 0,
    fun hE =>
      ⟨Finsupp.mapRange (fun w => w / p.val.mass E) (by simp)
        (fTransform X (p.val.restrict E)), by
          constructor
          · intro a
            rw [Finsupp.mapRange_apply]
            exact div_nonneg
              (((p.property.nonNeg.restrict E).fTransform X) a)
              (p.property.nonNeg.mass_nonneg E)
          · rw [weight_mapRange_div, weight_fTransform, weight_restrict]
            exact div_self hE⟩⟩

theorem condPMF_apply {Ω A : Type*} (p : ProbDist Ω)
    (X : RV (Ω := Ω) (A := A)) (E : Ω → Prop)
    (hE : p.val.mass E ≠ 0) (a : A) :
    (condPMF p X E).get hE a =
      p.val.mass (fun ω => X ω = a ∧ E ω) / p.val.mass E := by
  unfold condPMF
  rw [Finsupp.mapRange_apply, fTransform_apply_eq_mass, mass_restrict]

/-- Paper-facing conditional PMF notation in the current random experiment.

`ℙ⟦X | Y⟧` is the partial function `(x, y) ↦ P_{X|Y}(x, y)`;
`ℙ⟦X | Y⟧[x, y]` is its partial value at `(x, y)`.

The notation intentionally omits the low-level experiment mass `p`, following
CR18/Maurer notation. In Lean, it expands using the ambient variable named
`p : ProbDist Ω`. -/
syntax "ℙ⟦" term " | " term "⟧" : term
syntax "ℙ⟦" term " | " term "⟧[" term ", " term "]" : term
macro "ℙ⟦" X:term " | " Y:term "⟧" : term => do
  let p := Lean.mkIdent `p
  `(Probability.Distribution.condPMFOf $p $X $Y)
macro "ℙ⟦" X:term " | " Y:term "⟧[" x:term ", " y:term "]" : term => do
  let p := Lean.mkIdent `p
  `(Probability.Distribution.condPMFOf $p $X $Y $x $y)

/-! ### Evaluating `fTransform` -/

omit [Nonempty A] [Fintype B] [Nonempty B] in
/-- Fiber-sum form of `fTransform` evaluation.

`(fTransform f X) b` is the total mass of all `a` such that `f a = b`.

The decidability of the fiber predicate is an explicit parameter rather than
this file's classical local instance: the statement's `Finset.filter` then
instantiates with the caller's ambient instance, whether classical or derived
from `[DecidableEq B]`, so `rw` matches goals in both instance policies. -/
theorem fTransform_apply_eq_sum
    (f : A → B) (X : Distribution A) (b : B)
    [DecidablePred fun a : A => f a = b] :
    (fTransform f X) b =
      ∑ a ∈ (Finset.univ : Finset A).filter (fun a => f a = b), X a := by
  classical
  simp only [fTransform, Finsupp.sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.single_apply]
  rw [← Finset.sum_filter (p := fun a => f a = b)]
  apply Finset.sum_subset
  · exact Finset.filter_subset_filter _ (Finset.subset_univ _)
  · intro a ha1 ha2
    have hfa : f a = b := (Finset.mem_filter.mp ha1).2
    have ha_supp : a ∉ X.support := by
      intro ha_supp
      apply ha2
      exact Finset.mem_filter.mpr ⟨ha_supp, hfa⟩
    exact Finsupp.notMem_support_iff.mp ha_supp

/-- Pushforward of a uniform distribution evaluated at a point equals
the fiber cardinality divided by the total cardinality.

`(fTransform f (uniform A)) b = |{a : f a = b}| / |A|`

As in `fTransform_apply_eq_sum`, the fiber decidability is an explicit
parameter so the statement's filter matches the caller's ambient instance. -/
theorem fTransform_uniform_apply
    (f : A → B) (b : B)
    [DecidablePred fun a : A => f a = b] :
    (fTransform f (uniform A)) b =
      ((Finset.univ.filter (fun a => f a = b)).card : ℝ)
        / (Fintype.card A : ℝ) := by
  rw [fTransform_apply_eq_sum]
  simp only [uniform_apply, Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- If every fiber of `f : A -> B` has the cardinality expected for a uniform
map, pushing the uniform distribution on `A` forward along `f` gives the
uniform distribution on `B`. -/
theorem fTransform_uniform_eq_uniform_of_card_fiber_mul
    {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    [DecidableEq B]
    (f : A → B)
    (hfiber : ∀ b : B,
      ((Finset.univ.filter (fun a : A => f a = b)).card) * Fintype.card B =
        Fintype.card A) :
    fTransform f (uniform A) = uniform B := by
  classical
  ext b
  rw [fTransform_uniform_apply, uniform_apply]
  let c : ℝ := ((Finset.univ.filter (fun a : A => f a = b)).card : ℝ)
  let d : ℝ := (Fintype.card B : ℝ)
  have hcardA : (Fintype.card A : ℝ) = c * d := by
    dsimp [c, d]
    exact_mod_cast (hfiber b).symm
  have hc_ne : c ≠ 0 := by
    dsimp [c]
    have hfiber_pos : 0 < (Finset.univ.filter (fun a : A => f a = b)).card := by
      by_contra hnot
      have hzero : (Finset.univ.filter (fun a : A => f a = b)).card = 0 := by omega
      have hA_zero : Fintype.card A = 0 := by
        rw [← hfiber b]
        simp [hzero]
      exact (Fintype.card_pos (α := A)).ne' hA_zero
    exact_mod_cast (Nat.ne_of_gt hfiber_pos)
  rw [hcardA]
  have hdr : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast (Fintype.card_pos (α := B)).ne'
  field_simp
  simp [c, d]

/-- Summing against a pushforward distribution pulls the summand back. -/
theorem fTransform_sum_mul
    (X : Distribution A) (f : A → B) (g : B → ℝ) :
    (∑ b : B, (fTransform f X) b * g b) = ∑ a : A, X a * g (f a) := by
  classical
  simp only [fTransform, Finsupp.sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.single_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [ite_mul, zero_mul]
  trans ∑ x ∈ X.support, X x * g (f x)
  · apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_eq_single (f a)]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · intro h
      exact False.elim (h (Finset.mem_univ (f a)))
  · rw [← Finset.sum_subset (Finset.subset_univ X.support)]
    intro a _ ha
    simp [Finsupp.notMem_support_iff.mp ha]

/-- Evaluating a predicate after a pushforward is the same as evaluating the
pulled-back predicate before the pushforward. -/
theorem evalPred_fTransform
    (X : Distribution A) (f : A → B) (P : B → Prop) :
    (fTransform f X).evalPred P = X.evalPred (fun a => P (f a)) := by
  classical
  unfold evalPred
  calc
    ∑ b ∈ Finset.univ.filter P, (fTransform f X) b =
        ∑ b : B, (fTransform f X) b * if P b then (1 : ℝ) else 0 := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro b _
          by_cases h : P b <;> simp [h]
    _ = ∑ a : A, X a * if P (f a) then (1 : ℝ) else 0 := by
          exact fTransform_sum_mul X f (fun b => if P b then (1 : ℝ) else 0)
    _ = ∑ a ∈ Finset.univ.filter (fun a => P (f a)), X a := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : P (f a) <;> simp [h]

/-! ### Independent product distributions -/

/-- Independent product of two (sub-)distributions.

`prod X Y` is the distribution on `A × B` obtained by sampling `a ~ X` and
`b ~ Y` independently and returning `(a,b)`. The weight is `|X| * |Y|`. -/
def prod (X : Distribution A) (Y : Distribution B) : Distribution (A × B) :=
  X.sum (fun a wa => Y.sum (fun b wb => Finsupp.single (a, b) (wa * wb)))

-- Independent products and `iidPow` are all support-based: no `Fintype`/`Nonempty` on the
-- carriers. (Theorems would otherwise inherit them from the section `variable`s; `omit` sheds them
-- for the whole block, restored at `end` for the `Fintype`-using lemmas below, e.g. `mass_eq_sum`.)
section
omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]

theorem prod_apply (X : Distribution A) (Y : Distribution B) (a : A) (b : B) :
    prod X Y (a, b) = X a * Y b := by
  classical
  -- Push evaluation inside the nested sums and discharge each sum via `Finsupp.sum_eq_single`.
  simp [prod, Finsupp.sum_apply]
  let g : A → ℝ → ℝ :=
    fun a' wa => Y.sum (fun b' wb => (Finsupp.single (a', b') (wa * wb)) (a, b))
  change X.sum g = X a * Y b
  have hX : X.sum g = g a (X a) := by
    refine Finsupp.sum_eq_single a (f := X) (g := g) ?_ ?_
    · intro a' _hne0 hne
      simp [g, hne]
    · intro _
      simp [g]
  have hY : Y.sum (fun b' wb => if b' = b then X a * wb else 0) = X a * Y b := by
    simpa using
      (Finsupp.sum_eq_single b (f := Y)
        (g := fun b' wb => if b' = b then X a * wb else 0)
        (h₀ := by
          intro b' _hne0 hne
          simp [hne])
        (h₁ := by
          intro _
          simp))
  calc
    X.sum g = g a (X a) := hX
    _ = Y.sum (fun b' wb => if b' = b then X a * wb else 0) := by
      simp [g, Finsupp.single_apply]
    _ = X a * Y b := hY

/-- An independent product is supported on the rectangle of the component
supports: a pair carries mass only if both of its coordinates do. -/
theorem support_prod_subset (X : Distribution A) (Y : Distribution B) :
    (prod X Y).support ⊆ X.support ×ˢ Y.support := fun p hp =>
  have hne : X p.1 * Y p.2 ≠ 0 :=
    prod_apply X Y p.1 p.2 ▸ Finsupp.mem_support_iff.mp hp
  Finset.mem_product.mpr
    ⟨Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hne),
     Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hne)⟩

/-- The mass of an arbitrary event under an independent product as an iterated
finite-support sum.  The rectangle case is `mass_prod_and`; this unrestricted
form is useful when the event couples the two coordinates. -/
theorem mass_prod_eq_double_sum (X : Distribution A) (Y : Distribution B) (R : A × B → Prop) :
    (prod X Y).mass R =
      X.sum fun a wa => Y.sum fun b wb => if R (a, b) then wa * wb else 0 := by
  classical
  have key : ∀ p : A × B, prod X Y p = X p.1 * Y p.2 := fun p => prod_apply X Y p.1 p.2
  have hsub : (prod X Y).support ⊆ X.support ×ˢ Y.support := support_prod_subset X Y
  rw [mass, Finsupp.sum,
    Finset.sum_subset hsub fun p _ hp => by
      rw [show prod X Y p = 0 by simpa using hp]; simp,
    Finset.sum_product]
  simp only [Finsupp.sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [key (a, b)]

/-- A weighted sum over an independent product is an iterated weighted sum. -/
theorem sum_prod_mul (X : Distribution A) (Y : Distribution B) (f : A × B → ℝ) :
    (prod X Y).sum (fun p w => w * f p) =
      X.sum fun a wa => wa * Y.sum fun b wb => wb * f (a, b) := by
  classical
  have key : ∀ p : A × B, prod X Y p = X p.1 * Y p.2 := fun p => prod_apply X Y p.1 p.2
  have hsub : (prod X Y).support ⊆ X.support ×ˢ Y.support := support_prod_subset X Y
  rw [Finsupp.sum,
    Finset.sum_subset hsub fun p _ hp => by
      rw [show prod X Y p = 0 by simpa using hp]; simp,
    Finset.sum_product]
  simp only [Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [key (a, b)]
  ring

theorem weight_prod (X : Distribution A) (Y : Distribution B) :
    (prod X Y).weight = X.weight * Y.weight := by
  classical
  -- Support-based, so **no `Fintype` on the carriers**: sum the product mass over the finite
  -- `X.support ×ˢ Y.support` and split the double sum.
  have key : ∀ p : A × B, prod X Y p = X p.1 * Y p.2 := fun p => prod_apply X Y p.1 p.2
  have hsub : (prod X Y).support ⊆ X.support ×ˢ Y.support := fun p hp =>
    have hne : X p.1 * Y p.2 ≠ 0 := key p ▸ Finsupp.mem_support_iff.mp hp
    Finset.mem_product.mpr
      ⟨Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hne),
       Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hne)⟩
  calc (prod X Y).weight
      = ∑ p ∈ X.support ×ˢ Y.support, prod X Y p := by
        rw [weight, Finsupp.sum]
        exact Finset.sum_subset hsub fun p _ hp => by simpa using hp
    _ = ∑ p ∈ X.support ×ˢ Y.support, X p.1 * Y p.2 := Finset.sum_congr rfl fun p _ => key p
    _ = ∑ a ∈ X.support, ∑ b ∈ Y.support, X a * Y b := by rw [Finset.sum_product]
    _ = X.weight * Y.weight := by rw [← Finset.sum_mul_sum]; simp only [weight, Finsupp.sum]

/-- Independent products preserve non-negativity. -/
theorem NonNeg.prod {X : Distribution A} {Y : Distribution B} (hX : X.NonNeg) (hY : Y.NonNeg) :
    (Distribution.prod X Y).NonNeg := fun p => by
  rw [show p = (p.1, p.2) from rfl, prod_apply]
  exact mul_nonneg (hX p.1) (hY p.2)

/-- The product of two probability distributions is a probability distribution. -/
theorem prod_isProbDist (X : Distribution A) (Y : Distribution B)
    (hX : X.isProbDist) (hY : Y.isProbDist) : (prod X Y).isProbDist := by
  refine ⟨hX.nonNeg.prod hY.nonNeg, ?_⟩
  rw [weight_prod, hX.weight_eq, hY.weight_eq, mul_one]

/-- Independent products preserve the probability capability. -/
instance (X : Distribution A) (Y : Distribution B) [IsProbability X] [IsProbability Y] :
    IsProbability (prod X Y) :=
  ⟨(prod_isProbDist X Y (IsProbability.isProbDist X) (IsProbability.isProbDist Y)).1,
    (prod_isProbDist X Y (IsProbability.isProbDist X) (IsProbability.isProbDist Y)).2⟩

/-- The product of two probability distributions, as a `ProbDist` (CR18 Appendix A:
the joint distribution of two **independently selected** random variables). -/
noncomputable def prodProbDist (P : ProbDist A) (Q : ProbDist B) : ProbDist (A × B) :=
  ⟨prod P.val Q.val, prod_isProbDist P.val Q.val P.property Q.property⟩

@[simp] theorem prodProbDist_val (P : ProbDist A) (Q : ProbDist B) :
    (prodProbDist P Q).val = prod P.val Q.val := rfl

/-- CR18 **Definition 4.9** (finite part). The **q-fold i.i.d. power** `X^q` of a distribution:
`q` *independent* copies with *identical* marginal `X`, as one distribution over the `q`-tuples
`Fin q → A`. Its mass is the product of marginals `X^q(f) = ∏ i, X (f i)` — which is exactly
"the copies are independent" (product law) *and* "each has the same marginal `X`" (every factor is
`X`). (Maurer's countable power `⟨X⟩ = X^∞` is deliberately *not* formalized: by fn 24, `X^∞` is
uncountable and leaves the realm of discrete probability. No `Fintype A` is needed — the finite
support carries everything.) -/
noncomputable def iidPow (X : Distribution A) (q : ℕ) : Distribution (Fin q → A) :=
  Finsupp.onFinset (Fintype.piFinset fun _ => X.support) (fun f => ∏ i, X (f i))
    (fun _ h0 => Fintype.mem_piFinset.mpr fun i =>
      Finsupp.mem_support_iff.mpr fun hi => h0 (Finset.prod_eq_zero (Finset.mem_univ i) hi))

/-- The defining property of `X^q`: its mass is the product of the marginals (independence +
identical marginal `X`). -/
@[simp] theorem iidPow_apply (X : Distribution A) (q : ℕ) (f : Fin q → A) :
    iidPow X q f = ∏ i, X (f i) := by rw [iidPow]; exact Finsupp.onFinset_apply

/-- The weight of `X^q` is the `q`-th power of the weight: `|X^q| = |X|^q`. -/
theorem iidPow_weight (X : Distribution A) (q : ℕ) : (iidPow X q).weight = X.weight ^ q := by
  have hsub : (iidPow X q).support ⊆ Fintype.piFinset fun _ : Fin q => X.support :=
    fun f hf => Fintype.mem_piFinset.mpr fun i => Finsupp.mem_support_iff.mpr fun hi =>
      (iidPow_apply X q f ▸ Finsupp.mem_support_iff.mp hf) (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  have hX : ∀ _ : Fin q, ∑ a ∈ X.support, X a = X.weight := fun _ => by rw [weight, Finsupp.sum]
  calc (iidPow X q).weight
      = ∑ f ∈ Fintype.piFinset fun _ : Fin q => X.support, iidPow X q f := by
        rw [weight, Finsupp.sum]
        exact Finset.sum_subset hsub fun f _ hf => by simpa using hf
    _ = ∑ f ∈ Fintype.piFinset fun _ : Fin q => X.support, ∏ i, X (f i) := by simp_rw [iidPow_apply]
    _ = ∏ _i : Fin q, ∑ a ∈ X.support, X a := (Finset.prod_univ_sum _ _).symm
    _ = X.weight ^ q := by
        rw [Finset.prod_congr rfl fun i _ => hX i, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]

/-- `X^q` is a probability distribution whenever `X` is (CR18 Def 4.9: `X^q` is again a random
variable) — the n-ary analogue of `prod_isProbDist`. -/
theorem iidPow_isProbDist {X : Distribution A} (hX : X.isProbDist) (q : ℕ) : (iidPow X q).isProbDist := by
  refine ⟨fun f => ?_, ?_⟩
  · rw [iidPow_apply]
    exact Finset.prod_nonneg fun i _ => hX.nonNeg (f i)
  · rw [iidPow_weight, hX.weight_eq, one_pow]

/-- CR18 **Definition 4.10** (finite part). The **q-fold clone power** `X^[q]` of a distribution:
`q` *clones* `X₁ = ⋯ = X_q` — the *same* value in every coordinate — each with marginal `X`. It is
the pushforward (`fTransform`) of `X` along the **diagonal** `a ↦ (a,…,a)`, hence supported on the
constant tuples with the constant-`a` tuple carrying mass `X a` (`clonePow_apply`). Contrast `iidPow`
(independent copies): clones are *fully correlated*. (Example 4.11: clones of a uniform bit put mass
½ on each of `(0,…,0)` and `(1,…,1)`. The countable version is omitted, as for Def 4.9 fn 24.) -/
def clonePow (X : Distribution A) (q : ℕ) : Distribution (Fin q → A) :=
  fTransform (fun a _ => a) X

/-- `X^[q]` is supported on constant tuples: its mass at `g` is the `X`-mass of the values whose
clone tuple is `g` (so `0` unless `g` is constant, and `X a` at the constant-`a` tuple). -/
@[simp] theorem clonePow_apply (X : Distribution A) (q : ℕ) (g : Fin q → A) :
    clonePow X q g = X.mass (fun a => (fun _ => a) = g) := fTransform_apply_eq_mass _ X g

end

omit [Nonempty A] in
/-- `mass` as a `Fintype` sum: `X.mass P = ∑ a, (if P a then X a else 0)`. -/
theorem mass_eq_sum (X : Distribution A) (P : A → Prop) :
    X.mass P = ∑ a, if P a then X a else 0 := by
  rw [Distribution.mass]
  exact Finsupp.sum_fintype _ _ (fun _ => by simp only [ite_self])

/-- Uniform event mass as a cardinality ratio. -/
theorem uniform_mass_eq_card_filter (P : A → Prop) [DecidablePred P] :
    (uniform A).mass P =
      (((Finset.univ : Finset A).filter P).card : ℝ) /
        (Fintype.card A : ℝ) := by
  rw [mass_eq_sum]
  simp_rw [uniform_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- **Uniform-mass product law from a counting identity**: if `#P · |B| = #Q · #E` then
`mass P = mass Q · mass E` over the uniform distributions.  The algebraic endgame of balanced-fiber
(re-randomisation) counting arguments: prove the count, read off the product law. -/
theorem uniform_mass_eq_mass_mul_mass_of_card_mul_eq {A B : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (P E : A → Prop) (Q : B → Prop) [DecidablePred P] [DecidablePred E] [DecidablePred Q]
    (hcard : (Finset.univ.filter P).card * Fintype.card B
      = (Finset.univ.filter Q).card * (Finset.univ.filter E).card) :
    (uniform A).mass P = (uniform B).mass Q * (uniform A).mass E := by
  have hB : ((Fintype.card B : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h : ((Finset.univ.filter P).card : ℝ) * (Fintype.card B : ℝ)
      = ((Finset.univ.filter Q).card : ℝ) * ((Finset.univ.filter E).card : ℝ) := by
    exact_mod_cast hcard
  calc (uniform A).mass P
      = (((Finset.univ.filter P).card : ℝ) * (Fintype.card B : ℝ))
          / ((Fintype.card B : ℝ) * (Fintype.card A : ℝ)) := by
        rw [uniform_mass_eq_card_filter, mul_comm ((Fintype.card B : ℝ)),
          mul_div_mul_right _ _ hB]
    _ = (uniform B).mass Q * (uniform A).mass E := by
        rw [uniform_mass_eq_card_filter, uniform_mass_eq_card_filter, div_mul_div_comm, h]

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] in
/-- **Independence of the two coordinates of a product distribution**: under
`prod P Q`, the first coordinate and any predicate on the second are independent —
the joint mass factors as the product of the marginals.

`Fintype`-free: summed over the finite support `P.support ×ˢ Q.support`, not the whole type, so it
applies to the `DDS`/`DDE` carriers (which must **not** be `Fintype`). This is what lets the
transcript distribution / Lemma 3.2 (`transcriptDist`) drop its `[Fintype Ω]`. -/
theorem mass_prod_and (P : Distribution A) (Q : Distribution B) (R₁ : A → Prop) (R₂ : B → Prop) :
    (prod P Q).mass (fun ab => R₁ ab.1 ∧ R₂ ab.2) = P.mass R₁ * Q.mass R₂ := by
  classical
  have key : ∀ p : A × B, prod P Q p = P p.1 * Q p.2 := fun p => prod_apply P Q p.1 p.2
  have hsub : (prod P Q).support ⊆ P.support ×ˢ Q.support := fun p hp =>
    have hne : P p.1 * Q p.2 ≠ 0 := key p ▸ Finsupp.mem_support_iff.mp hp
    Finset.mem_product.mpr
      ⟨Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hne),
       Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hne)⟩
  have hPmass : P.mass R₁ = ∑ a ∈ P.support, (if R₁ a then P a else 0) := rfl
  have hQmass : Q.mass R₂ = ∑ b ∈ Q.support, (if R₂ b then Q b else 0) := rfl
  have hmass : (prod P Q).mass (fun ab => R₁ ab.1 ∧ R₂ ab.2)
      = ∑ p ∈ (prod P Q).support, (if R₁ p.1 ∧ R₂ p.2 then prod P Q p else 0) := by
    rw [mass, Finsupp.sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : R₁ p.1 ∧ R₂ p.2 <;> simp [h]
  rw [hmass, hPmass, hQmass]
  calc ∑ p ∈ (prod P Q).support, (if R₁ p.1 ∧ R₂ p.2 then prod P Q p else 0)
      = ∑ p ∈ P.support ×ˢ Q.support, (if R₁ p.1 ∧ R₂ p.2 then prod P Q p else 0) := by
        refine Finset.sum_subset hsub fun p _ hp => ?_
        rw [show prod P Q p = 0 by simpa using hp]; simp
    _ = ∑ a ∈ P.support, ∑ b ∈ Q.support, (if R₁ a ∧ R₂ b then P a * Q b else 0) := by
        rw [Finset.sum_product]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [key (a, b)]
    _ = (∑ a ∈ P.support, (if R₁ a then P a else 0))
          * (∑ b ∈ Q.support, (if R₂ b then Q b else 0)) := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        by_cases h1 : R₁ a <;> by_cases h2 : R₂ b <;> simp [h1, h2]

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] in
/-- The mass of the singleton event `· = a` is just the weight `X a`. -/
theorem mass_singleton (X : Distribution A) (a : A) : X.mass (fun b => b = a) = X a := by
  classical
  unfold mass
  rw [Finsupp.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
  simp

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] in
/-- **CR18 Def A.4 marginal** on the first coordinate of a product distribution:
`P_X(x) = ∑_y P_{XY}(x,y)`, here `(prod P Q).mass (R ∘ fst) = P.mass R · weight Q`. -/
theorem mass_prod_fst (P : Distribution A) (Q : Distribution B) (R : A → Prop) :
    (prod P Q).mass (fun ab => R ab.1) = P.mass R * Q.weight := by
  rw [show (fun ab : A × B => R ab.1) = (fun ab => R ab.1 ∧ (fun _ : B => True) ab.2) from by
        funext; simp,
     mass_prod_and P Q R (fun _ => True), mass_true]

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] in
/-- **CR18 Def A.4 marginal** on the second coordinate of a product distribution. -/
theorem mass_prod_snd (P : Distribution A) (Q : Distribution B) (R : B → Prop) :
    (prod P Q).mass (fun ab => R ab.2) = P.weight * Q.mass R := by
  rw [show (fun ab : A × B => R ab.2) = (fun ab => (fun _ : A => True) ab.1 ∧ R ab.2) from by
        funext; simp,
     mass_prod_and P Q (fun _ => True) R, mass_true]

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] in
/-- Projecting an independent product onto its first coordinate recovers the
first factor, scaled by the total weight of the discarded factor.  At
`|Q| = 1` — the intended reading, where the second factor is a probability
distribution — the scaling is trivial (`one_smul`); the general form is what
an optimal coupling needs, whose off-diagonal factors carry the transported
mass rather than weight one. -/
theorem fTransform_fst_prod (P : Distribution A) (Q : Distribution B) :
    fTransform Prod.fst (prod P Q) = Q.weight • P := by
  ext a
  rw [fTransform_apply_eq_mass, Finsupp.smul_apply, smul_eq_mul]
  calc
    (prod P Q).mass (fun pair => pair.1 = a) =
        P.mass (fun x => x = a) * Q.weight := by
      simpa using mass_prod_fst P Q (fun x => x = a)
    _ = Q.weight * P a := by rw [mass_singleton, mul_comm]

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] in
/-- Projecting an independent product onto its second coordinate recovers the
second factor, scaled by the total weight of the discarded factor. -/
theorem fTransform_snd_prod (P : Distribution A) (Q : Distribution B) :
    fTransform Prod.snd (prod P Q) = P.weight • Q := by
  ext b
  rw [fTransform_apply_eq_mass, Finsupp.smul_apply, smul_eq_mul]
  calc
    (prod P Q).mass (fun pair => pair.2 = b) =
        P.weight * Q.mass (fun y => y = b) := by
      simpa using mass_prod_snd P Q (fun y => y = b)
    _ = P.weight * Q b := by rw [mass_singleton]

theorem prod_uniform :
    prod (uniform A) (uniform B) = uniform (A × B) := by
  classical
  ext p
  rcases p with ⟨a, b⟩
  -- Both sides assign constant mass `1/|A| * 1/|B| = 1/|A×B|` to each pair.
  simp [prod_apply, uniform, Fintype.card_prod, div_eq_mul_inv, mul_comm]

-- Basic properties

omit [Fintype A] [Nonempty A] in
/-- The weight equals the Finsupp.sum with identity.  (`rfl`; needs no `Fintype`/`Nonempty` — those
are section-variable leaks, omitted so callers over arbitrary carriers, e.g. `Distribution gs.Game`, can use
it without spurious `Nonempty` obligations.) -/
theorem weight_eq_finsupp_sum (X : Distribution A) :
    X.weight = X.sum (fun _ w => w) := by
  rfl

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [Fintype C] [Nonempty C] in
/-- Composing two f-transformations equals the f-transformation of the composition.

This is the pushforward functoriality law: `f_*(g_*(X)) = (f ∘ g)_*(X)`. -/
theorem fTransform_comp
    (g : B → C) (f : A → B) (X : Distribution A) :
    fTransform g (fTransform f X) = fTransform (g ∘ f) X := by
  show Finsupp.mapDomain g (Finsupp.mapDomain f X) = Finsupp.mapDomain (g ∘ f) X
  rw [Finsupp.mapDomain_comp]

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [Fintype C] [Nonempty C] in
/-- **The law of a stripped random variable.**  Let `aug` and `plain` be two
random variables on the same sample space.  If stripping `aug` recovers
`plain` pointwise, then stripping the law of `aug` recovers the law of
`plain`.

All randomness, including fresh augmentation coins, belongs in the source
law `X`; no product observation carrier or transcript-specific construction
is involved. -/
theorem fTransform_comp_eq_of_pointwise
    (strip : B → C) (aug : A → B) (plain : A → C) (X : Distribution A)
    (h : ∀ a, strip (aug a) = plain a) :
    fTransform strip (fTransform aug X) = fTransform plain X := by
  rw [fTransform_comp]
  exact congrArg (fun observation => fTransform observation X) (funext h)

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [Fintype C] [Nonempty C] in
/-- The pushforward is additive: it is `Finsupp.mapDomain`, a linear map, and
mixtures therefore survive to the image.  Stated for a `Finset` sum, which is
the form a decomposition over a finite support takes. -/
theorem fTransform_sum {A B ι : Type*} (f : A → B) (t : Finset ι)
    (Z : ι → Distribution A) :
    fTransform f (∑ i ∈ t, Z i) = ∑ i ∈ t, fTransform f (Z i) :=
  map_sum (Finsupp.mapDomain.addMonoidHom f) Z t

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [Fintype C] [Nonempty C] in
/-- The binary face of `fTransform_sum`: the pushforward of a sum of two
distributions is the sum of the pushforwards. -/
theorem fTransform_add {A B : Type*} (f : A → B) (Z W : Distribution A) :
    fTransform f (Z + W) = fTransform f Z + fTransform f W :=
  map_add (Finsupp.mapDomain.addMonoidHom f) Z W

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [Fintype C] [Nonempty C] in
/-- The pushforward commutes with scaling: mass is moved, not rescaled. -/
theorem fTransform_smul {A B : Type*} (f : A → B) (c : ℝ)
    (Z : Distribution A) : fTransform f (c • Z) = c • fTransform f Z :=
  Finsupp.mapDomain_smul c Z

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [Fintype C] [Nonempty C] in
/-- Pushing a distribution forward by the identity map
does not change it. -/
@[simp]
theorem fTransform_id {A : Type*} (X : Distribution A) :
    fTransform id X = X := by
  ext a
  simpa using fTransform_injective_apply X id Function.injective_id a

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [Fintype C] [Nonempty C] in
/-- Adding a deterministic terminal component and then
forgetting it by first projection recovers the original distribution.

This is the distribution-level conservative-extension law used by extended
transcript arguments: constant terminal side information carries no observable
mass once projected away. -/
@[simp]
theorem fTransform_fst_const_pair {A U : Type*} (X : Distribution A) (u : U) :
    fTransform (fun p : A × U => p.1) (fTransform (fun a : A => (a, u)) X) = X := by
  calc
    fTransform (fun p : A × U => p.1) (fTransform (fun a : A => (a, u)) X)
        = fTransform id X :=
          fTransform_comp_eq_of_pointwise _ _ id X fun _ => rfl
    _ = X := fTransform_id X

section ProductUniform

variable {A' B' : Type*}
variable [Fintype A'] [Nonempty A'] [Fintype B'] [Nonempty B']

/-- An equivalence pushes the uniform distribution to uniform.

Generalizes `fTransform_bijection_uniform` to maps between different types:
if `e : A ≃ B` is an equivalence, then the pushforward of `uniform A`
through `e` is `uniform B`. -/
theorem fTransform_equiv_uniform (e : A' ≃ B') :
    fTransform e (uniform A') = uniform B' := by
  classical
  apply fTransform_uniform_eq_uniform_of_card_fiber_mul e
  intro b
  have h_filter : (Finset.univ.filter (fun a => e a = b)).card = 1 := by
    rw [show (Finset.univ.filter (fun a => e a = b)) = {e.symm b} from by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact e.eq_symm_apply.symm]
    exact Finset.card_singleton _
  rw [h_filter, one_mul]
  exact (Fintype.card_congr e).symm

variable (A' B')

end ProductUniform

/-! ### Independent products under pushforward -/

/-- **`prod` is a bifunctor for pushforward**: pushing an independent
product forward coordinatewise is the independent product of the
pushforwards. -/
theorem fTransform_prod {A B A' B' : Type*} (f : A → A') (g : B → B')
    (X : Distribution A) (Y : Distribution B) :
    fTransform (Prod.map f g) (prod X Y) = prod (fTransform f X) (fTransform g Y) := by
  ext p
  obtain ⟨a, b⟩ := p
  rw [fTransform_apply_eq_mass, prod_apply, fTransform_apply_eq_mass,
    fTransform_apply_eq_mass, ← mass_prod_and X Y (fun x => f x = a) (fun y => g y = b)]
  exact mass_congr _ fun q => by simp [Prod.map, Prod.ext_iff]

/-- Pushing only the second factor forward is a pushforward of the product. -/
theorem fTransform_prod_right {A B B' : Type*} (X : Distribution A) (g : B → B')
    (Y : Distribution B) :
    prod X (fTransform g Y) = fTransform (Prod.map id g) (prod X Y) := by
  rw [fTransform_prod, fTransform_id]

/-- Pushing only the first factor forward is a pushforward of the product. -/
theorem fTransform_prod_left {A A' B : Type*} (f : A → A') (X : Distribution A)
    (Y : Distribution B) :
    prod (fTransform f X) Y = fTransform (Prod.map f id) (prod X Y) := by
  rw [fTransform_prod, fTransform_id]

/-- **Symmetry of the independent product**: exchanging the two coordinates
exchanges the two factors. -/
theorem fTransform_swap_prod {A B : Type*} (X : Distribution A) (Y : Distribution B) :
    fTransform Prod.swap (prod X Y) = prod Y X := by
  ext p
  obtain ⟨b, a⟩ := p
  calc fTransform (Prod.swap : A × B → B × A) (prod X Y) (b, a)
      = prod X Y (a, b) :=
        fTransform_injective_apply (prod X Y) Prod.swap Prod.swap_injective (a, b)
    _ = X a * Y b := prod_apply X Y a b
    _ = Y b * X a := mul_comm _ _
    _ = prod Y X (b, a) := (prod_apply Y X b a).symm

/-- **Associativity of the independent product**: reassociating the sample
reassociates the factors. -/
theorem fTransform_assoc_prod {A B C : Type*} (X : Distribution A) (Y : Distribution B)
    (Z : Distribution C) :
    fTransform (fun p : A × B × C => ((p.1, p.2.1), p.2.2)) (prod X (prod Y Z)) =
      prod (prod X Y) Z := by
  have hinj : Function.Injective (fun p : A × B × C => ((p.1, p.2.1), p.2.2)) := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simpa [Prod.ext_iff, and_assoc] using h
  ext p
  obtain ⟨⟨a, b⟩, c⟩ := p
  calc fTransform (fun p : A × B × C => ((p.1, p.2.1), p.2.2)) (prod X (prod Y Z)) ((a, b), c)
      = prod X (prod Y Z) (a, b, c) :=
        fTransform_injective_apply (prod X (prod Y Z)) _ hinj (a, b, c)
    _ = X a * (Y b * Z c) := by rw [prod_apply, prod_apply]
    _ = X a * Y b * Z c := (mul_assoc _ _ _).symm
    _ = prod (prod X Y) Z ((a, b), c) := by rw [prod_apply, prod_apply]

/-- A fixed first coordinate is a pushforward of the second law. -/
theorem prod_single_left {A B : Type*} (a : A) (Y : Distribution B) :
    prod (Finsupp.single a 1) Y = fTransform (fun b => (a, b)) Y := by
  classical
  rw [prod, Finsupp.sum_single_index (by
    simp only [zero_mul, Finsupp.single_zero, Finsupp.sum, Finset.sum_const_zero])]
  simp only [one_mul]
  rfl

/-- A fixed second coordinate is a pushforward of the first law. -/
theorem prod_single_right {A B : Type*} (X : Distribution A) (b : B) :
    prod X (Finsupp.single b 1) = fTransform (fun a => (a, b)) X := by
  rw [← fTransform_swap_prod, prod_single_left, fTransform_comp]
  rfl

/-! ### Fibering, filtering, and finite sums -/

/-- **Fibering an event mass over the values of a statistic**: if `V` covers
the image of `g` on the support, the mass of `P` splits into the masses of `P`
on the fibers `g = v`. -/
theorem mass_eq_sum_mass_fiber {A B : Type*} (μ : Distribution A)
    (P : A → Prop) (g : A → B) (V : Finset B)
    (hV : ∀ a ∈ μ.support, g a ∈ V) :
    μ.mass P = ∑ v ∈ V, μ.mass fun a => P a ∧ g a = v := by
  unfold mass
  simp only [Finsupp.sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  refine Eq.symm (Eq.trans (Finset.sum_eq_single_of_mem (g a) (hV a ha) ?_) ?_)
  · intro v _ hv
    exact if_neg fun hc => hv (hc.2.symm)
  · by_cases hP : P a <;> simp [hP]

/-- The weight of a finite sum of laws is the sum of their weights. -/
theorem weight_finset_sum {A ι : Type*} (t : Finset ι)
    (Rf : ι → Distribution A) :
    (∑ i ∈ t, Rf i).weight = ∑ i ∈ t, (Rf i).weight := by
  rw [weight_eq_finsupp_sum,
    ← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  exact Finset.sum_congr rfl fun i _ => (weight_eq_finsupp_sum _).symm

/-- A finite probabilistic choice of normalized laws is normalized. -/
theorem isProbDist_sum_smul
    {I A : Type*} (indices : Finset I) (weights : I → ℝ) (laws : I → Distribution A)
    (nonnegative : ∀ i ∈ indices, 0 ≤ weights i)
    (total : ∑ i ∈ indices, weights i = 1)
    (probability : ∀ i ∈ indices, (laws i).isProbDist) :
    (∑ i ∈ indices, weights i • laws i).isProbDist := by
  constructor
  · intro a
    simp only [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]
    exact Finset.sum_nonneg fun i hi => mul_nonneg (nonnegative i hi) ((probability i hi).1 a)
  · rw [weight_finset_sum]
    have weighted (i : I) : (weights i • laws i).weight = weights i * (laws i).weight := by
      unfold weight
      rw [Finsupp.sum_smul_index fun _ => rfl]
      unfold Finsupp.sum
      rw [Finset.mul_sum]
    simp only [weighted]
    calc
      _ = ∑ i ∈ indices, weights i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [(probability i hi).2, mul_one]
      _ = 1 := total

/-- The pushforward of the zero law is the zero law. -/
@[simp]
theorem fTransform_zero {A B : Type*} (f : A → B) :
    fTransform f (0 : Distribution A) = 0 :=
  Finsupp.mapDomain_zero

/-! ### Weights, products and independent products -/

section Products

variable {A : Type*}

/-- Weight is homogeneous: `|c · X| = c · |X|`.  Signed layer. -/
theorem weight_smul (c : ℝ) (X : Distribution A) : (c • X).weight = c * X.weight := by
  unfold weight
  rw [Finsupp.sum_smul_index fun _ => rfl]
  unfold Finsupp.sum
  rw [Finset.mul_sum]

/-- Weight is additive. -/
theorem weight_add (X Y : Distribution A) :
    (X + Y).weight = X.weight + Y.weight :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

/-- The weight of a point mass is its mass. -/
@[simp]
theorem weight_single (a : A) (c : ℝ) :
    weight (Finsupp.single a c : Distribution A) = c := by
  unfold weight
  exact Finsupp.sum_single_index rfl

theorem mass_single (a : A) (c : ℝ) (P : A → Prop) :
    mass (Finsupp.single a c : Distribution A) P = if P a then c else 0 := by
  unfold mass
  exact Finsupp.sum_single_index (ite_self 0)

theorem mass_prod_eq_sum {A' B' : Type} (P : Distribution A') (Q : Distribution B')
    (C : A' → B' → Prop) :
    (Distribution.prod P Q).mass (fun p => C p.1 p.2) = P.sum fun a w => w * Q.mass (C a) := by
  rw [Distribution.mass_prod_eq_double_sum]
  refine Finsupp.sum_congr fun a _ => ?_
  unfold Distribution.mass
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun b _ => ?_
  split_ifs <;> simp

theorem mass_prod_eq_sum_right {A' B' : Type} (P : Distribution A') (Q : Distribution B')
    (C : A' → B' → Prop) :
    (Distribution.prod P Q).mass (fun p => C p.1 p.2) = Q.sum fun b w => w * P.mass (fun a => C a b) := by
  rw [← mass_prod_eq_sum Q P (fun b a => C a b), ← Distribution.fTransform_swap_prod,
    Distribution.mass_fTransform]
  rfl

theorem fTransform_prod_assoc {A B C D : Type} (f : (A × B) × C → D) (P : Distribution A)
    (Q : Distribution B) (R : Distribution C) :
    Distribution.fTransform f (Distribution.prod (Distribution.prod P Q) R) =
      Distribution.fTransform (fun p => f ((p.1, p.2.1), p.2.2)) (Distribution.prod P (Distribution.prod Q R)) := by
  rw [← Distribution.fTransform_assoc_prod, Distribution.fTransform_comp]
  rfl

/-- Regrouping two independent pairs as the pairs of their first and of their second
components. -/
theorem independent_product_middle {A B C D : Type}
    (P : Distribution A) (Q : Distribution B) (R : Distribution C) (S : Distribution D) :
    Distribution.fTransform (fun p : (A × B) × (C × D) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      (Distribution.prod (Distribution.prod P Q) (Distribution.prod R S)) =
      Distribution.prod (Distribution.prod P R) (Distribution.prod Q S) := by
  have hi : Function.Injective (fun p : (A × B) × (C × D) => ((p.1.1, p.2.1), (p.1.2, p.2.2))) := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ he
    simp only [Prod.mk.injEq] at he ⊢
    exact ⟨⟨he.1.1, he.2.1⟩, ⟨he.1.2, he.2.2⟩⟩
  ext ⟨⟨a, c⟩, ⟨b, d⟩⟩
  rw [show ((a, c), (b, d)) =
      (fun p : (A × B) × (C × D) => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ((a, b), (c, d)) from rfl,
    Distribution.fTransform_injective_apply _ _ hi]
  simp only [Distribution.prod_apply]
  ring

/-! ### The independent product of a finite family -/

/-- The independent product of finitely many finitely supported laws:
`(⨂ᵢ μᵢ)(f) = ∏ᵢ μᵢ(f i)`.  This is `Distribution.iidPow` with the factors
allowed to differ, and it is what the `n`-ary maximal coupling glues onto the
diagonal. -/
noncomputable def pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Distribution A) : Distribution (ι → A) :=
  Finsupp.onFinset (Fintype.piFinset fun i => (μ i).support)
    (fun f => ∏ i, μ i (f i))
    (fun _f hf => Fintype.mem_piFinset.mpr fun i =>
      Finsupp.mem_support_iff.mpr fun h0 =>
        hf (Finset.prod_eq_zero (Finset.mem_univ i) h0))

@[simp]
theorem pi_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → Distribution A) (f : ι → A) :
    pi μ f = ∏ i, μ i (f i) := by
  rw [pi]; exact Finsupp.onFinset_apply

/-- An independent product of non-negative factors is non-negative. -/
theorem pi_nonNeg {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : ι → Distribution A}
    (h : ∀ i, (μ i).NonNeg) :
    (pi μ).NonNeg := fun f => by
  rw [pi_apply]
  exact Finset.prod_nonneg fun i _ => h i (f i)

/-- The total mass of independent finite distributions is the product of their masses. -/
theorem weight_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → Distribution A) :
    (pi μ).weight = ∏ i, (μ i).weight := by
  classical
  rw [weight_eq_finsupp_sum]
  rw [Finsupp.sum_of_support_subset (pi μ)
    (s := Fintype.piFinset fun i => (μ i).support)
    Finsupp.support_onFinset_subset _ (fun _ _ => rfl)]
  simp only [pi_apply, weight_eq_finsupp_sum, Finsupp.sum]
  exact (Finset.prod_univ_sum _ _).symm

/-- Independent probability distributions form a probability distribution. -/
theorem pi_isProbDist {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : ι → Distribution A}
    (h : ∀ i, (μ i).isProbDist) : (pi μ).isProbDist :=
  ⟨pi_nonNeg fun i => (h i).1, by
    rw [weight_pi]
    exact Finset.prod_eq_one fun i _ => (h i).2⟩

/-- Independent normalized distributions form a normalized distribution. -/
instance {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → Distribution A)
    [h : ∀ i, IsProbability (μ i)] : IsProbability (pi μ) where
  nonNeg := pi_nonNeg fun i => IsProbability.nonNeg
  weight_eq_one := by simp only [weight_pi, IsProbability.weight_eq_one, Finset.prod_const_one]

/-! ### Marginal bookkeeping -/

/-- Coordinate marginals are additive in the joint law. -/
theorem marginalAt_add {ι : Type*} {T : ι → Type*}
    (F G : Distribution ((i : ι) → T i)) (j : ι) :
    marginalAt (F + G) j = marginalAt F j + marginalAt G j :=
  Finsupp.sum_add_index' (fun _ => Finsupp.single_zero _)
    (fun x b₁ b₂ => Finsupp.single_add (x j) b₁ b₂)

/-- Coordinate marginals commute with scaling. -/
theorem marginalAt_smul {ι : Type*} {T : ι → Type*}
    (c : ℝ) (F : Distribution ((i : ι) → T i)) (j : ι) :
    marginalAt (c • F) j = c • marginalAt F j := by
  unfold marginalAt
  rw [Finsupp.sum_smul_index (fun _ => Finsupp.single_zero _), Finsupp.smul_sum]
  exact Finsupp.sum_congr fun x _ => by
    rw [Finsupp.smul_single, smul_eq_mul]

/-- The coordinate marginal of an independent product: the chosen factor,
scaled by the total weights of all the other factors. -/
theorem marginalAt_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → Distribution A) (i : ι) :
    marginalAt (pi μ) i
      = (∏ j ∈ Finset.univ.erase i, (μ j).weight) • μ i := by
  classical
  refine Finsupp.ext fun b => ?_
  rw [marginalAt_apply, Finsupp.smul_apply, smul_eq_mul, mass]
  rw [Finsupp.sum_of_support_subset (pi μ)
    (s := Fintype.piFinset fun j => (μ j).support)
    Finsupp.support_onFinset_subset _
    (fun f _ => by simp only [ite_self])]
  have hgate : ∀ f ∈ Fintype.piFinset fun j => (μ j).support,
      (if f i = b then pi μ f else 0)
        = ∏ j, if j = i then (if f j = b then μ j (f j) else 0)
            else μ j (f j) := by
    intro f _
    by_cases hf : f i = b
    · rw [if_pos hf, pi_apply]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hj : j = i
      · subst hj
        rw [if_pos rfl, if_pos hf]
      · rw [if_neg hj]
    · rw [if_neg hf]
      refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
      rw [if_pos rfl, if_neg hf]
  have hfubini :
      (∑ f ∈ Fintype.piFinset fun j => (μ j).support,
        ∏ j, if j = i then (if f j = b then μ j (f j) else 0)
            else μ j (f j))
      = ∏ j, ∑ a ∈ (μ j).support,
          if j = i then (if a = b then μ j a else 0) else μ j a :=
    (Finset.prod_univ_sum _ fun j a =>
      if j = i then (if a = b then μ j a else 0) else μ j a).symm
  rw [Finset.sum_congr rfl hgate, hfubini,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have hifactor :
      (∑ a ∈ (μ i).support,
          if i = i then (if a = b then μ i a else 0) else μ i a)
        = μ i b := by
    have hred : ∀ a ∈ (μ i).support,
        (if i = i then (if a = b then μ i a else 0) else μ i a)
          = (if a = b then μ i a else 0) := fun a _ => if_pos rfl
    rw [Finset.sum_congr rfl hred,
      Finset.sum_ite_eq' (μ i).support b (fun a => μ i a)]
    split
    · rfl
    · exact (Finsupp.notMem_support_iff.mp ‹_›).symm
  have hother : ∀ j ∈ Finset.univ.erase i,
      (∑ a ∈ (μ j).support,
          if j = i then (if a = b then μ j a else 0) else μ j a)
        = (μ j).weight := by
    intro j hj
    rw [weight_eq_finsupp_sum, Finsupp.sum]
    exact Finset.sum_congr rfl fun a _ => if_neg (Finset.ne_of_mem_erase hj)
  rw [hifactor, Finset.prod_congr rfl hother, mul_comm]

/-- Under an independent product, an event not depending on coordinate `i` is
independent of the value at `i`. -/
theorem mass_pi_and_eq {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
    (μ : ι → Distribution A) (hμ : ∀ j, (μ j).weight = 1) (i : ι) (a : A)
    (ev : (ι → A) → Prop) (hev : ∀ f a', ev (Function.update f i a') ↔ ev f) :
    (pi μ).mass (fun f => ev f ∧ f i = a) = (pi μ).mass ev * μ i a := by
  classical
  -- The factor of the other coordinates, together with the event.
  let G : (ι → A) → ℝ := fun f => if ev f then ∏ j : {j // j ≠ i}, μ j (f j) else 0
  have hG : ∀ f a', G (Function.update f i a') = G f := by
    intro f a'
    simp only [G, hev]
    congr 1
    exact Finset.prod_congr rfl fun j _ => by rw [Function.update_of_ne j.2]
  have split : ∀ f : ι → A, (∏ j, μ j (f j)) = μ i (f i) * ∏ j : {j // j ≠ i}, μ j (f j) :=
    fun f => Fintype.prod_eq_mul_prod_subtype_ne (fun j => μ j (f j)) i
  -- The fibres over different values at `i` carry the same total.
  let K : A → ℝ := fun a' => ∑ f : ι → A, if f i = a' then G f else 0
  have hK : ∀ a', K a' = K a := by
    intro a'
    let e : (ι → A) ≃ (ι → A) :=
      { toFun := fun f => Function.update f i (Equiv.swap a a' (f i))
        invFun := fun f => Function.update f i (Equiv.swap a a' (f i))
        left_inv := fun f => by
          funext j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_of_ne hj]
        right_inv := fun f => by
          funext j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_of_ne hj] }
    refine Fintype.sum_equiv e _ _ fun f => ?_
    simp only [e, Equiv.coe_fn_mk, Function.update_self, hG]
    by_cases hf : f i = a'
    · simp [hf]
    · have : Equiv.swap a a' (f i) ≠ a := by
        intro h
        apply hf
        simpa using congrArg (Equiv.swap a a') h
      simp [hf, this]
  have lhs : (pi μ).mass (fun f => ev f ∧ f i = a) = μ i a * K a := by
    rw [mass_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    by_cases hf : f i = a
    · by_cases he : ev f
      · simp [hf, he, pi_apply, split f, G]
      · simp [hf, he, G]
    · simp [hf]
  have rhs : (pi μ).mass ev = K a := by
    have : (pi μ).mass ev = ∑ a', μ i a' * K a' := by
      rw [mass_eq_sum]
      simp only [K, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [Finset.sum_eq_single (f i)]
      · by_cases he : ev f
        · simp [he, pi_apply, split f, G]
        · simp [he, G]
      · intro a' _ ha'
        simp [Ne.symm ha']
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [this]
    simp only [hK]
    rw [← Finset.sum_mul, ← weight_eq_sum, hμ, one_mul]
  rw [lhs, rhs, mul_comm]

/-- **Independent samples, truncated**: the first `k'` of `k` independent samples from a law of
weight one are `k'` independent samples. -/
theorem fTransform_pi_castLE [Fintype A] [DecidableEq A] (μ : Distribution A) (hμ : μ.weight = 1)
    {k' k : ℕ} (h : k' ≤ k) :
    fTransform (fun t : Fin k → A => fun i : Fin k' => t (Fin.castLE h i))
        (pi fun _ : Fin k => μ) = pi fun _ : Fin k' => μ := by
  classical
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  ext f
  rw [fTransform_apply_eq_mass, mass_eq_sum, pi_apply]
  rw [← (Fin.appendEquiv k' d).sum_comp]
  have htrunc : ∀ (u : Fin k' → A) (v : Fin d → A),
      (fun i : Fin k' => Fin.append u v (Fin.castLE h i)) = u := fun u v =>
    funext fun i => Fin.append_left u v i
  simp only [Fin.appendEquiv, Equiv.coe_fn_mk, htrunc, pi_apply, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single f]
  · simp only [if_true]
    rw [← Finset.mul_sum, ← Fintype.prod_sum]
    have : ∑ a, μ a = 1 := by rw [← weight_eq_sum]; exact hμ
    simp [this]
  · intro u _ hu
    simp [hu]
  · simp

end Products

end Distribution

end Probability
