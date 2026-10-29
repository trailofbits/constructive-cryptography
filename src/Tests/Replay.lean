import Probability.Replay

/-!
# Adaptive replay and public table constraints

Tests of `Probability.Replay` on a two-query adaptive replay of a Boolean table
`F : Option Bool → Bool`, with outputs indexed by `I = Option Unit` and one public entry
`F (some false) = false`, indexed by `J = Unit`.

```text
query none:      F(none)        ⇒ b
query some ():   F(some b)      ⇒ c        output y = (b, c)
public ():       F(some false)  = false
```

The replay sites `none` and `some b` avoid the public site `some false` exactly when `b = true`.
Off that event the factorization fails: at `y = (false, false)` the second replay site is the
public site, so only two entries are constrained, with mass `1/4` rather than `(1/2)^3 = 1/8`.
-/

namespace Probability.Tests.Replay

open Counting

/-- **The adaptive replay** on a table `F`: `evaluate F none = F none` and
`evaluate F (some ()) = F (some (F none))`; the first reply chooses the second query. -/
def evaluate (table : Option Bool → Bool) : Option Unit → Bool
  | none => table none
  | some () => table (some (table none))

/-- **The query sites of an output tuple** `y`: `site y none = none` and
`site y (some ()) = some (y none)`, the coordinates `evaluate` reads when its replies are `y`. -/
def site (value : Option Unit → Bool) : Option Unit → Option Bool
  | none => none
  | some () => some (value none)

/-- **The replay is pinned by its output tuple**:
`evaluate F = y ↔ F none = y none ∧ F (some (y none)) = y (some ())`. Once `F none = y none`,
the second query `some (F none)` is the site `some (y none)`. -/
lemma pinned (table : Option Bool → Bool) (value : Option Unit → Bool) :
    evaluate table = value ↔ ∀ i, table (site value i) = value i := by
  constructor
  -- (→) The first output gives `F none = y none`, which turns the second query into its site.
  · intro h i
    have hfirst : table none = value none := congrFun h none
    cases i with
    | none => exact hfirst
    | some u =>
      cases u
      simpa only [site, evaluate, hfirst] using congrFun h (some ())
  -- (←) The site equation at `none` gives `F none = y none`, and then the second output.
  · intro h
    have hfirst : table none = value none := h none
    funext i
    cases i with
    | none => exact hfirst
    | some u =>
      cases u
      simpa only [evaluate, hfirst, site] using h (some ())

/-- **Joint injectivity on the good event**: if `y none = true`, the replay sites `none` and
`some true` and the public site `some false` are distinct. -/
lemma distinct (value : Option Unit → Bool) (h : value none = true) :
    Function.Injective (Sum.elim (site value) (fun _ : Unit => some false)) := by
  simp only [Function.Injective, Sum.forall, Sum.elim_inl, site, h, Option.forall, Sum.elim_inr,
    Sum.inl.injEq, reduceCtorEq, imp_false, forall_const, and_self,
    not_false_eq_true, Option.some.injEq, Bool.true_eq_false, Bool.false_eq_true]

/-- **The first law** at `y = (true, true)` with `F (some false) = false`: the three distinct
entries `none`, `some true` and `some false` give mass `(1/2)^(2 + 1) = 1/8`. -/
example : (Distribution.uniform (Option Bool → Bool)).mass
      (fun f => evaluate f = (fun _ => true) ∧ f (some false) = false) = 1 / 8 := by
  -- `|I| = |Option Unit| = 2`, `|J| = |Unit| = 1`; evaluate the cardinalities on both sides.
  have h := uniform_mass_replay_public_eq site evaluate pinned (fun _ : Unit => some false)
    (fun _ => false) (fun _ => true) (distinct _ rfl)
  norm_num at h ⊢
  exact h

/-- **The second law** with `Good y := y none = true` and any `Event`:
`Pr_F[F none = true ∧ Event (evaluate F) ∧ F (some false) = false]`
`= 𝒰(Option Unit → Bool)[y none = true ∧ Event y] · 1/2`. -/
example (Event : (Option Unit → Bool) → Prop) :
    (Distribution.uniform (Option Bool → Bool)).mass
        (fun f => evaluate f none = true ∧ Event (evaluate f) ∧ f (some false) = false) =
      (Distribution.uniform (Option Unit → Bool)).mass
        (fun value => value none = true ∧ Event value) * (1 / 2) := by
  -- `distinct` is the joint injectivity on `Good`; `(1/|Bool|)^|Unit| = 1/2`.
  have h := uniform_replay_public_good_factor site evaluate pinned
    (fun _ : Unit => some false) (fun _ => false) (fun value => value none = true) Event distinct
  norm_num at h ⊢
  exact h

/-- **Joint injectivity fails off the good event**: at `y none = false` the second site
`some (y none) = some false` is the public site. At `y = (false, false)` the two constraints
share the entry `F (some false)`; the next example computes its mass. -/
example : ¬ Function.Injective
    (Sum.elim (site (fun _ => false)) (fun _ : Unit => some false)) := by
  -- `inl (some ())` and `inr ()` both map to `some false`, yet are different indices.
  intro h
  have he := h (a₁ := Sum.inl (some ())) (a₂ := Sum.inr ()) rfl
  cases he

/-- **The actual mass off the good event**: at `y = (false, false)` the second replay site
`some (y none) = some false` is the public site, so
`Pr_F[evaluate F = y ∧ F (some false) = false] = Pr_F[F none = false ∧ F (some false) = false]`
`= (1/2)^2 = 1/4`, not the independent `(1/2)^(2 + 1) = 1/8`. -/
example : (Distribution.uniform (Option Bool → Bool)).mass
    (fun f => evaluate f = (fun _ => false) ∧ f (some false) = false) = 1 / 4 := by
  -- The two distinct constrained entries: `xs none = none`, `xs (some ()) = some false`.
  let xs : Option Unit → Option Bool := fun i => i.map (fun _ => false)
  -- `xs` is injective, since `none ≠ some false`.
  have hx : Function.Injective xs := by
    intro i j h
    cases i <;> cases j <;> first | rfl | cases h
  -- By `pinned`, the event is `F none = false ∧ F (some false) = false`: the second replay
  -- equation and the public equation are the same, so the event is the fiber `F ∘ xs = y`.
  have he : (fun f : Option Bool → Bool =>
      evaluate f = (fun _ => false) ∧ f (some false) = false) =
      (fun f => (fun i => f (xs i)) = (fun _ => false)) := by
    funext f
    apply propext
    rw [pinned, funext_iff]
    simp only [site, Option.forall, forall_const, and_self_right, Option.map_none, Option.map_some,
      xs]
  -- `uniform_mass_eval_eq` at the two sites: `(1/|Bool|)^|Option Unit| = (1/2)^2 = 1/4`.
  rw [he, uniform_mass_eval_eq xs hx]
  norm_num

#print axioms Probability.Counting.uniform_replay_public_good_factor

end Probability.Tests.Replay
