import Probability.Distribution
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Fibers of uniform random functions

Counting facts about functions `X → Y` under the uniform distribution, used for
collision bounds.

## Main definitions

* `walkSite`: the point a walk visits, given its parent map, step functions and
  start
* `multiShift u δ f`: `f` shifted by `δ s` at the points `u s`

## Main results

* `card_function_fiber_finset`, `card_function_fiber_multipoint`,
  `card_function_fiber_index`: the number of functions with prescribed values
* `fTransform_eval_uniform_eq_uniform`, `uniform_mass_eval_eq`: evaluations of
  a uniform random function are uniform and independent
* `uniform_mass_walk_eval_eq`, `uniform_mass_coord_determined_le`,
  `uniform_mass_walk_repeat_le`: lazy sampling along a walk
* `card_filter_shift`, `card_filter_shift_univ`: re-randomization fibers
-/

noncomputable section

open scoped BigOperators NNReal

namespace Probability

namespace Counting

/-! ## Function fibers -/

/-- The number of functions agreeing with a prescribed map on a finite input
subset.

This is the shared finite-set function-fiber count used by transcript
normalization arguments. -/
theorem card_function_fiber_finset {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (S : Finset X) (g : S → Y) :
    (Finset.univ.filter (fun f : X → Y => ∀ x : S, f x.1 = g x)).card =
      Fintype.card Y ^ (Fintype.card X - S.card) := by
  classical
  rw [show Fintype.card Y ^ (Fintype.card X - S.card) = Fintype.card (↥Sᶜ → Y) from by
    rw [Fintype.card_fun, Fintype.card_coe, Finset.card_compl]]
  refine Finset.card_bij (fun f _ => fun ⟨x, hx⟩ => f x) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro f₁ hf₁ f₂ hf₂ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf₁ hf₂
    ext x
    by_cases hx : x ∈ S
    · rw [hf₁ ⟨x, hx⟩, hf₂ ⟨x, hx⟩]
    · exact congr_fun h ⟨x, Finset.mem_compl.mpr hx⟩
  · intro h _
    refine Exists.intro
      (fun x => if hx : x ∈ S then g ⟨x, hx⟩ else h ⟨x, Finset.mem_compl.mpr hx⟩) ?_
    refine Exists.intro ?_ ?_
    · rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_univ _
      · intro x
        simp [x.2]
    · ext x
      simp [Finset.mem_compl.mp x.2]

/-- The number of functions matching a prescribed output tuple on an injective
input tuple is `|Y|^(|X|-q)`. -/
theorem card_function_fiber_multipoint {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {q : ℕ} (xs : Fin q → X) (ys : Fin q → Y)
    (hxs : Function.Injective xs) :
    ((Finset.univ : Finset (X → Y)).filter
        (fun f : X → Y => (fun i : Fin q => f (xs i)) = ys)).card =
      Fintype.card Y ^ (Fintype.card X - q) := by
  classical
  set S : Finset X := Finset.univ.image xs
  have hS_card : S.card = q := by
    rw [Finset.card_image_of_injective _ hxs, Finset.card_fin]
  let C : Finset X := Finset.univ \ S
  rw [show Fintype.card Y ^ (Fintype.card X - q) = Fintype.card (C → Y) from by
    have hC_card : C.card = Fintype.card X - S.card := by
      exact Finset.card_sdiff_of_subset (by intro x _; exact Finset.mem_univ x)
    rw [Fintype.card_fun, Fintype.card_coe, hC_card, hS_card]]
  refine Finset.card_bij (fun f _ => fun ⟨x, hx⟩ => f x)
    (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro f₁ hf₁ f₂ hf₂ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf₁ hf₂
    ext x
    by_cases hx : x ∈ S
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      rw [congr_fun hf₁ i, congr_fun hf₂ i]
    · exact congr_fun h ⟨x, by simp [C, hx]⟩
  · intro g _
    have h_ext : ∀ x ∈ S, ∃! i : Fin q, xs i = x := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i, rfl, fun j hj => hxs hj⟩
    refine ⟨fun x =>
        if hx : x ∈ S then ys ((h_ext x hx).choose)
        else g ⟨x, by simp [C, hx]⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      ext i
      have h_mem : xs i ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ i)
      show dite (xs i ∈ S) _ _ = ys i
      rw [dif_pos h_mem]
      have hcs := (h_ext (xs i) h_mem).choose_spec
      congr 1
      exact hxs hcs.1
    · ext ⟨x, hx⟩
      show dite (x ∈ S) _ _ = g ⟨x, hx⟩
      rw [dif_neg ((Finset.mem_sdiff.mp hx).2)]

/-! ## The uniform random function: marginals, joint marginals, and freshness -/

/-- **The fiber of a uniform random function over a
prescribed value tuple at distinct points**, at an arbitrary finite index type:
`card_function_fiber_multipoint` transported along `Fintype.equivFin`. -/
theorem card_function_fiber_index {X Y ι : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Fintype ι] (xs : ι → X) (ys : ι → Y)
    (hxs : Function.Injective xs) :
    ((Finset.univ : Finset (X → Y)).filter
        (fun f : X → Y => (fun i => f (xs i)) = ys)).card
      = Fintype.card Y ^ (Fintype.card X - Fintype.card ι) := by
  classical
  set e := Fintype.equivFin ι with he
  have hxs' : Function.Injective (fun k => xs (e.symm k)) :=
    hxs.comp e.symm.injective
  have hpred : ∀ f : X → Y,
      ((fun i => f (xs i)) = ys)
        ↔ ((fun k => f (xs (e.symm k))) = fun k => ys (e.symm k)) := by
    intro f
    constructor
    · intro h; funext k; exact congrFun h (e.symm k)
    · intro h; funext i
      have := congrFun h (e i)
      simpa using this
  rw [Finset.filter_congr (fun f _ => by rw [hpred f]),
    card_function_fiber_multipoint (fun k => xs (e.symm k))
      (fun k => ys (e.symm k)) hxs']

/-- **Joint marginals of a uniform random function at
distinct points are uniform.**  Pushing the uniform law on `𝒳 → 𝒴` forward
along evaluation at an injective family of points is the uniform law on value
tuples: this is independence of the values at distinct points, in the form this
carrier can state it. -/
theorem fTransform_eval_uniform_eq_uniform {X Y ι : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype ι] [DecidableEq ι]
    (xs : ι → X) (hxs : Function.Injective xs) :
    Distribution.fTransform (fun f : X → Y => fun i => f (xs i))
        (Distribution.uniform (X → Y))
      = Distribution.uniform (ι → Y) := by
  classical
  refine Distribution.fTransform_uniform_eq_uniform_of_card_fiber_mul _ fun ys => ?_
  have hcard : Fintype.card ι ≤ Fintype.card X := Fintype.card_le_of_injective xs hxs
  rw [card_function_fiber_index xs ys hxs, Fintype.card_fun, Fintype.card_fun,
    ← pow_add]
  congr 1
  omega

/-- **The mass of a prescribed value tuple at distinct
points**: `(1/|𝒴|)^{|ι|}`, whatever the tuple.  The mass reading of
`fTransform_eval_uniform_eq_uniform`, and the form a transcript-law computation
consumes. -/
theorem uniform_mass_eval_eq {X Y ι : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype ι] [DecidableEq ι]
    (xs : ι → X) (hxs : Function.Injective xs) (ys : ι → Y) :
    (Distribution.uniform (X → Y)).mass (fun f => (fun i => f (xs i)) = ys)
      = (1 / (Fintype.card Y : ℝ)) ^ Fintype.card ι := by
  have h := congrArg (fun d : Distribution (ι → Y) => d ys)
    (fTransform_eval_uniform_eq_uniform (X := X) (Y := Y) xs hxs)
  simp only [Distribution.fTransform_apply_eq_mass, Distribution.uniform_apply] at h
  rw [h, Fintype.card_fun, div_pow, one_pow]
  push_cast
  ring

/-! ## Lazy sampling along a walk on a uniform random function -/

/-- The input consumed at site `t` when the walk is replayed in the **lazy
world**: against a tuple `y` of recorded outputs rather than against a
function.  `par t = none` marks a site that starts from the public initial
state `x₀`. -/
def walkSite {ι X : Type*} (par : ι → Option ι) (g : ι → X → X) (x₀ : X)
    (y : ι → X) (t : ι) : X :=
  g t ((par t).elim x₀ y)

/-- **A walk always replays itself.**  Run the lazy walk
on the very outputs `f` produced, and it reproduces `f`'s own site inputs.
This needs no hypothesis on the walk at all — it is the recursion read
outwards. -/
theorem walkSite_of_eval {ι X : Type*}
    (par : ι → Option ι) (g : ι → X → X) (x₀ : X)
    (inp : (X → X) → ι → X)
    (hinp : ∀ f t, inp f t = g t ((par t).elim x₀ (fun h => f (inp f h))))
    (f : X → X) :
    inp f = walkSite par g x₀ (fun t => f (inp f t)) := by
  funext t
  rw [hinp f t]
  rfl

/-- **A walk is pinned by a consistent tuple**: if `f`
answers `y t` at every lazily replayed site input, then `f`'s own site inputs
*are* the replayed ones.  The converse direction of `walkSite_of_eval`, and the
one that needs the parent relation to be well-founded — supplied here as a
`rank` that strictly decreases towards the parent. -/
theorem eq_walkSite_of_eval_eq {ι X : Type*}
    (par : ι → Option ι) (g : ι → X → X) (x₀ : X) (rank : ι → ℕ)
    (hrank : ∀ t h, par t = some h → rank h < rank t)
    (inp : (X → X) → ι → X)
    (hinp : ∀ f t, inp f t = g t ((par t).elim x₀ (fun h => f (inp f h))))
    {f : X → X} {y : ι → X}
    (hf : ∀ t, f (walkSite par g x₀ y t) = y t) :
    inp f = walkSite par g x₀ y := by
  have key : ∀ n : ℕ, ∀ t : ι, rank t ≤ n → inp f t = walkSite par g x₀ y t := by
    intro n
    induction n with
    | zero =>
      intro t ht
      rw [hinp f t]
      rcases hp : par t with _ | h
      · simp [walkSite, hp]
      · exact absurd (hrank t h hp) (by omega)
    | succ n ih =>
      intro t ht
      rw [hinp f t]
      rcases hp : par t with _ | h
      · simp [walkSite, hp]
      · have hh : rank h ≤ n := by have := hrank t h hp; omega
        simp only [hp, Option.elim, walkSite]
        rw [ih h hh, hf h]
  exact funext fun t => key (rank t) t le_rfl

/-- **The law of the walk's evaluations, until the first
repeat.**  At a tuple `y` whose replayed walk visits pairwise distinct site
inputs, the uniform random function returns exactly `y` with probability
`(1/|𝒳|)^{|ι|}` — the law of `|ι|` independent uniform draws.

This is the lazy-sampling statement.  It is false without the repeat-freeness
hypothesis: at a tuple whose replay repeats an input the two directions of
`walkSite_of_eval` still pin the fiber, but the fiber is the one of a *smaller*
set of distinct evaluation points, so its mass is larger (or zero). -/
theorem uniform_mass_walk_eval_eq {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype X] [DecidableEq X] [Nonempty X]
    (par : ι → Option ι) (g : ι → X → X) (x₀ : X) (rank : ι → ℕ)
    (hrank : ∀ t h, par t = some h → rank h < rank t)
    (inp : (X → X) → ι → X)
    (hinp : ∀ f t, inp f t = g t ((par t).elim x₀ (fun h => f (inp f h))))
    {y : ι → X} (hy : Function.Injective (walkSite par g x₀ y)) :
    (Distribution.uniform (X → X)).mass (fun f => (fun t => f (inp f t)) = y)
      = (1 / (Fintype.card X : ℝ)) ^ Fintype.card ι := by
  have hev : ∀ f : X → X,
      ((fun t => f (inp f t)) = y) ↔ ((fun t => f (walkSite par g x₀ y t)) = y) := by
    intro f
    constructor
    · intro h
      have hw : inp f = walkSite par g x₀ y := by
        rw [walkSite_of_eval par g x₀ inp hinp f, h]
      rw [← hw]; exact h
    · intro h
      have hw : inp f = walkSite par g x₀ y :=
        eq_walkSite_of_eval_eq par g x₀ rank hrank inp hinp (congrFun h)
      rw [hw]; exact h
  rw [Distribution.mass_congr _ hev]
  exact uniform_mass_eval_eq (walkSite par g x₀ y) hy y

/-- **The repeat-free region has the same mass in both
worlds.**  The probability that a uniform random function drives the walk
without a repeat equals the probability that `|ι|` independent uniform draws
replay it without a repeat.  Only the repeat-free region transports — which is
enough, because the birthday argument takes the complement afterwards. -/
theorem uniform_mass_walk_injective_eq {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype X] [DecidableEq X] [Nonempty X]
    (par : ι → Option ι) (g : ι → X → X) (x₀ : X) (rank : ι → ℕ)
    (hrank : ∀ t h, par t = some h → rank h < rank t)
    (inp : (X → X) → ι → X)
    (hinp : ∀ f t, inp f t = g t ((par t).elim x₀ (fun h => f (inp f h)))) :
    (Distribution.uniform (X → X)).mass (fun f => Function.Injective (inp f))
      = (Distribution.uniform (ι → X)).mass
          (fun y => Function.Injective (walkSite par g x₀ y)) := by
  classical
  have h1 : (Distribution.uniform (X → X)).mass (fun f => Function.Injective (inp f))
      = (Distribution.fTransform (fun f : X → X => fun t => f (inp f t))
          (Distribution.uniform (X → X))).mass
          (fun y => Function.Injective (walkSite par g x₀ y)) := by
    rw [Distribution.mass_fTransform]
    refine Distribution.mass_congr _ fun f => ?_
    rw [← walkSite_of_eval par g x₀ inp hinp f]
  rw [h1,
    Distribution.mass_eq_sum_of_support_subset _ (Finset.subset_univ _),
    Distribution.mass_eq_sum_of_support_subset _ (Finset.subset_univ _)]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hinj : Function.Injective (walkSite par g x₀ y) := (Finset.mem_filter.mp hy).2
  rw [Distribution.fTransform_apply_eq_mass, Distribution.uniform_apply,
    uniform_mass_walk_eval_eq par g x₀ rank hrank inp hinp hinj,
    Fintype.card_fun, div_pow, one_pow]
  push_cast
  ring

/-- **One coordinate determined is one factor lost.**  If
an event on uniform tuples pins the value at coordinate `c` — through an
injective `u` — against a quantity `v` that never reads coordinate `c`, its
probability is at most `1/|𝒳|`.

This is the elementary counting behind every step of a birthday argument, in
the form the walk consumes: `u` is the step at the site being added and `v` is
the input already sitting at the site it might hit. -/
theorem uniform_mass_coord_determined_le {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype X] [DecidableEq X] [Nonempty X]
    (c : ι) (u : X → X) (hu : Function.Injective u) (v : (ι → X) → X)
    (hv : ∀ y z : ι → X, (∀ i, i ≠ c → y i = z i) → v y = v z) :
    (Distribution.uniform (ι → X)).mass (fun y => u (y c) = v y)
      ≤ 1 / (Fintype.card X : ℝ) := by
  classical
  have hXpos : (0 : ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨c⟩
  have hsub : Fintype.card {i : ι // i ≠ c} = Fintype.card ι - 1 := by
    rw [Fintype.card_subtype_compl (p := fun i : ι => i = c), Fintype.card_subtype_eq]
  have hcard : ((Finset.univ : Finset (ι → X)).filter (fun y => u (y c) = v y)).card
      ≤ Fintype.card X ^ (Fintype.card ι - 1) := by
    have hle := Finset.card_le_card_of_injOn
      (f := fun (y : ι → X) => fun i : {i : ι // i ≠ c} => y i.1)
      (s := (Finset.univ : Finset (ι → X)).filter (fun y => u (y c) = v y))
      (t := (Finset.univ : Finset ({i : ι // i ≠ c} → X)))
      (fun y _ => Finset.mem_univ _) ?_
    · rw [Finset.card_univ, Fintype.card_fun, hsub] at hle
      exact hle
    · intro y hy z hz hyz
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hy hz
      have hoff : ∀ i, i ≠ c → y i = z i := fun i hi => congrFun hyz ⟨i, hi⟩
      have hc : y c = z c := hu (by rw [hy.2, hv y z hoff, ← hz.2])
      funext i
      by_cases hi : i = c
      · subst hi; exact hc
      · exact hoff i hi
  rw [Distribution.uniform_mass_eq_card_filter, Fintype.card_fun]
  push_cast
  rw [div_le_div_iff₀ (by positivity) hXpos]
  have hpow : (Fintype.card X : ℝ) ^ Fintype.card ι
      = (Fintype.card X : ℝ) ^ (Fintype.card ι - 1) * (Fintype.card X : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [one_mul, hpow]
  have hcast : (((Finset.univ : Finset (ι → X)).filter (fun y => u (y c) = v y)).card : ℝ)
      ≤ (Fintype.card X : ℝ) ^ (Fintype.card ι - 1) := by
    exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_right hcast hXpos.le

/-- **One step of the birthday argument.**  In the lazy
world two distinct sites collide with probability at most `1/|𝒳|`.

The case analysis is the whole point, and both branches are genuinely
different.  If the two sites share a parent they read the *same* state, and
`hsib` makes the collision outright impossible — this is the branch that covers
two sites starting from the fixed `x₀`, whose inputs carry no randomness at
all.  Otherwise one of the two reads a state that the other does not, and
`uniform_mass_coord_determined_le` charges the step `1/|𝒳|`; note this runs in
*either* direction, so a deterministic site colliding with a randomized one is
charged just as a continuation step is. -/
theorem uniform_mass_walkSite_eq_le {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype X] [DecidableEq X] [Nonempty X]
    (par : ι → Option ι) (g : ι → X → X) (x₀ : X)
    (hg : ∀ t, Function.Injective (g t))
    (hsib : ∀ t t', t ≠ t' → par t = par t' → ∀ x : X, g t x ≠ g t' x)
    {t t' : ι} (htt : t ≠ t') :
    (Distribution.uniform (ι → X)).mass
        (fun y => walkSite par g x₀ y t = walkSite par g x₀ y t')
      ≤ 1 / (Fintype.card X : ℝ) := by
  classical
  have hXpos : (0 : ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  by_cases hpar : par t = par t'
  · have hz : (Distribution.uniform (ι → X)).mass
        (fun y => walkSite par g x₀ y t = walkSite par g x₀ y t') = 0 :=
      Distribution.mass_eq_zero_of_forall_not _ fun y hy =>
        hsib t t' htt hpar ((par t').elim x₀ y)
          (by simpa only [walkSite, hpar] using hy)
    rw [hz]
    positivity
  · rcases hp : par t with _ | c
    · rcases hp' : par t' with _ | c'
      · exact absurd (by rw [hp, hp']) hpar
      · refine le_of_le_of_eq ?_ rfl
        have hdet := uniform_mass_coord_determined_le (ι := ι) (X := X) c' (g t')
          (hg t') (fun y => walkSite par g x₀ y t) ?_
        · refine le_trans (le_of_eq ?_) hdet
          refine Distribution.mass_congr _ fun y => ?_
          simp [walkSite, hp, hp', eq_comm]
        · intro y z hyz
          simp [walkSite, hp]
    · have hdet := uniform_mass_coord_determined_le (ι := ι) (X := X) c (g t)
        (hg t) (fun y => walkSite par g x₀ y t') ?_
      · refine le_trans (le_of_eq ?_) hdet
        refine Distribution.mass_congr _ fun y => ?_
        simp [walkSite, hp]
      · intro y z hyz
        rcases hp' : par t' with _ | c'
        · simp [walkSite, hp']
        · have hne : c' ≠ c := by
            intro h
            exact hpar (by rw [hp, hp', h])
          simp [walkSite, hp', hyz c' hne]

/-- **The birthday bound for a walk, on a set of sites.**
The union bound run one site at a time: adding a site to `s` either repeats a
collision already inside `s`, or hits one of its `|s|` inputs, and the second
costs `|s|/|𝒳|`.

The induction is on the *set of sites*, not on a global statement, because
"repeat-free so far" is what makes the next step's charge legitimate; the
telescoping `∑_{k<|s|} k/|𝒳|` is the birthday bound's arithmetic. -/
theorem uniform_mass_walkSite_not_injOn_le {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype X] [DecidableEq X] [Nonempty X]
    (par : ι → Option ι) (g : ι → X → X) (x₀ : X)
    (hg : ∀ t, Function.Injective (g t))
    (hsib : ∀ t t', t ≠ t' → par t = par t' → ∀ x : X, g t x ≠ g t' x)
    (s : Finset ι) :
    (Distribution.uniform (ι → X)).mass
        (fun y => ¬ Set.InjOn (walkSite par g x₀ y) ↑s)
      ≤ (s.card : ℝ) * ((s.card : ℝ) - 1) / (2 * Fintype.card X) := by
  classical
  have hXpos : (0 : ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  induction s using Finset.induction_on with
  | empty =>
    have hz : (Distribution.uniform (ι → X)).mass
        (fun y => ¬ Set.InjOn (walkSite par g x₀ y) ↑(∅ : Finset ι)) = 0 :=
      Distribution.mass_eq_zero_of_forall_not _ (by simp)
    rw [hz]
    simp
  | insert a s ha ih =>
    have hstep : ∀ y : ι → X,
        (¬ Set.InjOn (walkSite par g x₀ y) ↑(insert a s)) →
          ((¬ Set.InjOn (walkSite par g x₀ y) ↑s) ∨
            ∃ t ∈ s, walkSite par g x₀ y t = walkSite par g x₀ y a) := by
      intro y hy
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      refine hy fun u hu v hv huv => ?_
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hu hv
      rcases hu with rfl | hu
      · rcases hv with rfl | hv
        · rfl
        · exact absurd huv.symm (h2 v hv)
      · rcases hv with rfl | hv
        · exact absurd huv (h2 u hu)
        · exact h1 (by simpa using hu) (by simpa using hv) huv
    have hsum : (Distribution.uniform (ι → X)).mass
        (fun y => ∃ t ∈ s, walkSite par g x₀ y t = walkSite par g x₀ y a)
          ≤ (s.card : ℝ) / (Fintype.card X : ℝ) := by
      refine le_trans (Distribution.mass_exists_le Distribution.uniform_nonNeg s _) ?_
      refine le_trans (Finset.sum_le_sum (fun t ht =>
        uniform_mass_walkSite_eq_le par g x₀ hg hsib
          (fun h => ha (h ▸ ht)))) ?_
      rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    have hcards : ((insert a s).card : ℝ) = (s.card : ℝ) + 1 := by
      rw [Finset.card_insert_of_notMem ha]
      push_cast
      ring
    refine le_trans (le_trans (Distribution.mass_mono Distribution.uniform_nonNeg hstep)
      (Distribution.mass_or_le Distribution.uniform_nonNeg _ _)) ?_
    rw [hcards]
    refine le_trans (add_le_add ih hsum) (le_of_eq ?_)
    field_simp
    ring

/-- **The lazy-sampling birthday bound for a walk.**  A
uniform random function drives the walk into a repeated site input with
probability at most `|ι|(|ι|−1)/2|𝒳|` — the birthday bound for `|ι|` uniform
draws from `𝒳` (`birthday_bound`'s right-hand side at `q := |ι|`).

The two hypotheses on the walk are the two halves of injectivity of the step:
`hg` says a uniform state gives a uniform input, and `hsib` says two distinct
sites reading the same state cannot agree.  `hrank` says the parent relation is
well-founded, which is what lets a tuple of outputs replay the walk. -/
theorem uniform_mass_walk_repeat_le {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype X] [DecidableEq X] [Nonempty X]
    (par : ι → Option ι) (g : ι → X → X) (x₀ : X) (rank : ι → ℕ)
    (hrank : ∀ t h, par t = some h → rank h < rank t)
    (hg : ∀ t, Function.Injective (g t))
    (hsib : ∀ t t', t ≠ t' → par t = par t' → ∀ x : X, g t x ≠ g t' x)
    (inp : (X → X) → ι → X)
    (hinp : ∀ f t, inp f t = g t ((par t).elim x₀ (fun h => f (inp f h)))) :
    (Distribution.uniform (X → X)).mass (fun f => ¬ Function.Injective (inp f))
      ≤ (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1)
          / (2 * Fintype.card X) := by
  classical
  have hcompl := Distribution.mass_add_compl (Distribution.uniform (X → X))
    (fun f => Function.Injective (inp f))
  have hcompl' := Distribution.mass_add_compl (Distribution.uniform (ι → X))
    (fun y => Function.Injective (walkSite par g x₀ y))
  rw [Distribution.weight_uniform] at hcompl hcompl'
  have hkey := uniform_mass_walk_injective_eq par g x₀ rank hrank inp hinp
  have heq : (Distribution.uniform (X → X)).mass (fun f => ¬ Function.Injective (inp f))
      = (Distribution.uniform (ι → X)).mass
        (fun y => ¬ Function.Injective (walkSite par g x₀ y)) := by
    rw [hkey] at hcompl
    linarith
  rw [heq]
  have hB := uniform_mass_walkSite_not_injOn_le par g x₀ hg hsib (Finset.univ : Finset ι)
  rw [Finset.card_univ] at hB
  refine le_trans (le_of_eq ?_) hB
  refine Distribution.mass_congr _ fun y => ?_
  rw [Finset.coe_univ, Set.injOn_univ]

/-! ## Re-randomisation fibers -/

/-- **Multi-point additive shift** — the generic re-randomisation gadget: translate `f : X → X` by
`δ s` at each site `u s`.  Away from the sites nothing changes; at an injectively-placed site exactly
`δ s` is added; shifts over the same site family compose additively and vanish at `δ = 0` — precisely
the free-action package `card_filter_shift` consumes. -/
def multiShift {ι D A : Type*} [Fintype ι] [DecidableEq D] [AddCommMonoid A]
    (u : ι → D) (δ : ι → A) (f : D → A) : D → A :=
  fun x => f x + ∑ s, if u s = x then δ s else 0

theorem multiShift_apply_of_ne {ι D A : Type*} [Fintype ι] [DecidableEq D]
    [AddCommMonoid A] {u : ι → D} (δ : ι → A) (f : D → A) {x : D}
    (h : ∀ s, u s ≠ x) :
    multiShift u δ f x = f x := by
  rw [multiShift, Finset.sum_eq_zero fun s _ => if_neg (h s), add_zero]

theorem multiShift_apply_site {ι D A : Type*} [Fintype ι] [DecidableEq D]
    [AddCommMonoid A] {u : ι → D} (δ : ι → A) (f : D → A)
    (hu : Function.Injective u) (s₀ : ι) :
    multiShift u δ f (u s₀) = f (u s₀) + δ s₀ := by
  rw [multiShift]
  congr 1
  rw [Finset.sum_eq_single s₀ (fun s _ hs => if_neg fun hc => hs (hu hc))
    (fun hns => absurd (Finset.mem_univ s₀) hns), if_pos rfl]

theorem multiShift_zero {ι D A : Type*} [Fintype ι] [DecidableEq D]
    [AddCommMonoid A] (u : ι → D) (f : D → A) :
    multiShift u 0 f = f := by
  funext x; simp [multiShift]

/-- Shifts over the same site family compose additively. -/
theorem multiShift_multiShift {ι D A : Type*} [Fintype ι] [DecidableEq D]
    [AddCommMonoid A] (u : ι → D) (δ δ' : ι → A) (f : D → A) :
    multiShift u δ' (multiShift u δ f) = multiShift u (δ + δ') f := by
  funext x
  show (f x + ∑ s, if u s = x then δ s else 0) + (∑ s, if u s = x then δ' s else 0)
    = f x + ∑ s, if u s = x then (δ + δ') s else 0
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun s _ => by by_cases h : u s = x <;> simp [h]

/-- **Generic balanced-fiber count.** A free, `φ`-equivariant action of a finite additive group `A`
on a finite set `G` makes every `φ`-fiber the same size: `|fiber| · |A| = |G|`.  This is the shared
counting principle behind re-randomisation arguments (e.g. the CBC-MAC's joint-MAC count and its
birthday per-pair count). -/
theorem card_filter_shift {F A : Type*} [Fintype F] [DecidableEq F]
    [AddCommGroup A] [Fintype A] [DecidableEq A]
    (G : Finset F) (φ : F → A) (act : A → F → F)
    (hmem : ∀ δ, ∀ f ∈ G, act δ f ∈ G)
    (hφ : ∀ δ, ∀ f ∈ G, φ (act δ f) = φ f + δ)
    (hcomp : ∀ δ δ', ∀ f ∈ G, act δ' (act δ f) = act (δ + δ') f)
    (hzero : ∀ f ∈ G, act 0 f = f) (c : A) :
    (G.filter (fun f => φ f = c)).card * Fintype.card A = G.card := by
  classical
  have hbij : ∀ c' : A,
      (G.filter (fun f => φ f = c')).card = (G.filter (fun f => φ f = c)).card := by
    intro c'
    refine Finset.card_bij' (fun f _ => act (c - c') f) (fun g _ => act (c' - c) g) ?_ ?_ ?_ ?_
    · intro f hf
      rw [Finset.mem_filter] at hf ⊢
      exact ⟨hmem _ _ hf.1, by rw [hφ _ _ hf.1, hf.2]; abel⟩
    · intro g hg
      rw [Finset.mem_filter] at hg ⊢
      exact ⟨hmem _ _ hg.1, by rw [hφ _ _ hg.1, hg.2]; abel⟩
    · intro f hf
      rw [Finset.mem_filter] at hf
      show act (c' - c) (act (c - c') f) = f
      rw [hcomp _ _ _ hf.1, show c - c' + (c' - c) = (0 : A) by abel, hzero _ hf.1]
    · intro g hg
      rw [Finset.mem_filter] at hg
      show act (c - c') (act (c' - c) g) = g
      rw [hcomp _ _ _ hg.1, show c' - c + (c - c') = (0 : A) by abel, hzero _ hg.1]
  calc (G.filter (fun f => φ f = c)).card * Fintype.card A
      = ∑ c' : A, (G.filter (fun f => φ f = c')).card := by
        rw [Finset.sum_congr rfl fun c' _ => hbij c', Finset.sum_const, Finset.card_univ,
          smul_eq_mul, mul_comm]
    _ = G.card := (Finset.card_eq_sum_card_fiberwise fun f _ => Finset.mem_univ (φ f)).symm

/-- **Predicate form of `card_filter_shift`** over `univ`: a free, `φ`-equivariant `A`-action on the
`Good` subtype balances the `φ`-fibers within it.  Phrased on the predicate `Good` so consumers avoid
`Finset`-membership plumbing. -/
theorem card_filter_shift_univ {F A : Type*} [Fintype F] [DecidableEq F]
    [AddCommGroup A] [Fintype A] [DecidableEq A]
    (Good : F → Prop) [DecidablePred Good] (φ : F → A) (act : A → F → F)
    (hmem : ∀ δ f, Good f → Good (act δ f))
    (hφ : ∀ δ f, Good f → φ (act δ f) = φ f + δ)
    (hcomp : ∀ δ δ' f, Good f → act δ' (act δ f) = act (δ + δ') f)
    (hzero : ∀ f, Good f → act 0 f = f) (c : A) :
    (Finset.univ.filter (fun f => φ f = c ∧ Good f)).card * Fintype.card A
      = (Finset.univ.filter Good).card := by
  have hgood : ∀ f, f ∈ Finset.univ.filter Good ↔ Good f := by
    intro f; simp
  have key := card_filter_shift (Finset.univ.filter Good) φ act
    (fun δ f hf => (hgood _).mpr (hmem δ f ((hgood f).mp hf)))
    (fun δ f hf => hφ δ f ((hgood f).mp hf))
    (fun δ δ' f hf => hcomp δ δ' f ((hgood f).mp hf))
    (fun f hf => hzero f ((hgood f).mp hf)) c
  rw [Finset.filter_filter] at key
  rw [← key]
  congr 2
  ext f
  simp [and_comm]

end Counting

end Probability
