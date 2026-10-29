import Probability.Counting

/-!
# Adaptive replay against fixed public table entries

A uniform function table `F ←$ (X → Y)` is read by an adaptive replay, with output tuple
`evaluate F : I → Y`, and constrained at `|J|` fixed public entries
`F (publicSite j) = publicValue j`. When the replay sites of an output tuple `y` and the public
sites are distinct, the replay and the public entries are `|I| + |J|` independent uniform
evaluations of `F`.

```text
                 F ←$ (X → Y)
replay:   site y i      ──F──▶ y i              (i : I, the site may depend on y)
public:   publicSite j  ──F──▶ publicValue j    (j : J, fixed)
joint:    Sum.elim (site y) publicSite : I ⊕ J → X   injective
```

The declarations are universe-polymorphic, but `X`, `Y`, `I` and `J` are finite: `F` is a
finite table and `y` a finite tuple.

## Main results

* `uniform_mass_replay_public_eq`:
  `Pr[evaluate F = y ∧ F ∘ publicSite = publicValue] = (1/|Y|)^(|I| + |J|)`
* `uniform_replay_public_good_factor`:
  `Pr[(Good ∧ Event)(evaluate F) ∧ F ∘ publicSite = publicValue]`
  `= 𝒰(I → Y)[Good ∧ Event] · (1/|Y|)^|J|`

Both are derived from `uniform_mass_eval_eq` (`Probability.Counting`) in the table model of
MauRen16, printed p. 6.
-/

namespace Probability.Counting

open Classical in
/-- **A pinned replay with distinct public entries** has the mass of `|I| + |J|` independent
uniform evaluations:
`Pr_F[evaluate F = value ∧ ∀ j, F (publicSite j) = publicValue j] = (1/|Y|)^(|I| + |J|)`.

* `evaluate F : I → Y` is the output tuple of the replay on the table `F`.
* `site y i : X` is the coordinate the replay queries at `i` when its replies are `y`.
* `pinned`: `evaluate F = y ↔ ∀ i, F (site y i) = y i`. The consumer proves this of its own
  evaluator; this library does not derive it from a query order or a causality model.
* `publicSite j` and `publicValue j` are fixed, independent of `F` and of the replay.
* `hinj`: `Sum.elim (site value) publicSite : I ⊕ J → X` is injective; the replay sites are
  pairwise distinct, the public sites are pairwise distinct, and no replay site is public.

The event is then the single fiber `F ∘ Sum.elim (site value) publicSite =
Sum.elim value publicValue` of `uniform_mass_eval_eq`, in the table model of MauRen16, printed
p. 6: "a uniformly chosen function table F … that can be accessed by giving as input a value x
and receiving as output the value F (x)". -/
lemma uniform_mass_replay_public_eq {X Y I J : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    [Fintype I] [Fintype J]
    (site : (I → Y) → I → X) (evaluate : (X → Y) → I → Y)
    (pinned : ∀ f y, evaluate f = y ↔ ∀ i, f (site y i) = y i)
    (publicSite : J → X) (publicValue : J → Y) (value : I → Y)
    (hinj : Function.Injective (Sum.elim (site value) publicSite)) :
    (Distribution.uniform (X → Y)).mass
        (fun f => evaluate f = value ∧ ∀ j, f (publicSite j) = publicValue j) =
      (1 / (Fintype.card Y : ℝ)) ^ (Fintype.card I + Fintype.card J) := by
  classical
  -- Joint fiber at the distinct sites `I ⊕ J`:
  -- `Pr[F ∘ Sum.elim (site value) publicSite = Sum.elim value publicValue] = (1/|Y|)^|I ⊕ J|`.
  have he := uniform_mass_eval_eq (Sum.elim (site value) publicSite) hinj
    (Sum.elim value publicValue)
  -- `|I ⊕ J| = |I| + |J|`.
  rw [Fintype.card_sum] at he
  -- The events agree: by `pinned`, `evaluate F = value` is `∀ i, F (site value i) = value i`,
  -- the `inl` half of the joint fiber; the public entries are its `inr` half.
  refine (Distribution.mass_congr _ fun f => ?_).trans he
  rw [pinned]
  constructor
  -- (→) Glue the replay and public equations into one equation on `I ⊕ J`.
  · rintro ⟨hi, hj⟩
    funext i
    cases i with
    | inl i => exact hi i
    | inr j => exact hj j
  -- (←) Restrict the joint equation to `inl i` and `inr j`.
  · intro h
    exact ⟨fun i => congrFun h (.inl i), fun j => congrFun h (.inr j)⟩

open Classical in
/-- **The good part of a pinned replay factors against fixed public entries**:
`Pr_F[Good (evaluate F) ∧ Event (evaluate F) ∧ ∀ j, F (publicSite j) = publicValue j]`
`= 𝒰(I → Y)[Good ∧ Event] · (1/|Y|)^|J|`.

`evaluate`, `site`, `pinned`, `publicSite` and `publicValue` are as in
`uniform_mass_replay_public_eq`; `Event` is any further predicate on the output tuple, and the
joint injectivity `hinj` is required only for output tuples in `Good`. The left side is summed
over the output fibers `evaluate F = y`; each fiber with `Good y ∧ Event y` has mass
`(1/|Y|)^(|I| + |J|) = 𝒰(I → Y)(y) · (1/|Y|)^|J|`, so the public cost `(1/|Y|)^|J|` factors
against the uniform output tuple law. Nothing is claimed on `¬ Good`, where a replay site may
be a public site. A derived consequence of `uniform_mass_eval_eq` in the table model of
MauRen16, printed p. 6. -/
lemma uniform_replay_public_good_factor {X Y I J : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    [Fintype I] [Fintype J]
    (site : (I → Y) → I → X) (evaluate : (X → Y) → I → Y)
    (pinned : ∀ f y, evaluate f = y ↔ ∀ i, f (site y i) = y i)
    (publicSite : J → X) (publicValue : J → Y)
    (Good Event : (I → Y) → Prop)
    (hinj : ∀ value, Good value → Function.Injective (Sum.elim (site value) publicSite)) :
    (Distribution.uniform (X → Y)).mass
        (fun f => Good (evaluate f) ∧ Event (evaluate f) ∧
          ∀ j, f (publicSite j) = publicValue j) =
      (Distribution.uniform (I → Y)).mass (fun value => Good value ∧ Event value) *
        (1 / (Fintype.card Y : ℝ)) ^ Fintype.card J := by
  classical
  -- Fiber the left side over the output tuple: `Pr[E] = ∑ y, Pr[E ∧ evaluate F = y]`.
  rw [Distribution.mass_eq_sum_mass_fiber _ _ evaluate Finset.univ (fun _ _ => Finset.mem_univ _)]
  -- Expand the right side: `∑ y, (if Good y ∧ Event y then 𝒰(I → Y)(y) else 0) · (1/|Y|)^|J|`.
  conv_rhs => rw [Distribution.mass_eq_sum, Finset.sum_mul]
  -- Compare the two sums fiber by fiber.
  apply Finset.sum_congr rfl
  intro value _
  by_cases hg : Good value ∧ Event value
  · rw [if_pos hg]
    -- A good fiber: the replay and public sites are distinct, so the first law applies.
    have he := uniform_mass_replay_public_eq site evaluate pinned publicSite publicValue value
      (hinj value hg.1)
    -- On `evaluate F = value`, `Good` and `Event` already hold; drop them from the fiber.
    have hm : (Distribution.uniform (X → Y)).mass
        (fun f => (Good (evaluate f) ∧ Event (evaluate f) ∧
          ∀ j, f (publicSite j) = publicValue j) ∧ evaluate f = value) =
        (Distribution.uniform (X → Y)).mass
          (fun f => evaluate f = value ∧ ∀ j, f (publicSite j) = publicValue j) := by
      apply Distribution.mass_congr
      intro f
      constructor
      · rintro ⟨⟨_, _, hf⟩, he⟩
        exact ⟨he, hf⟩
      · rintro ⟨he, hf⟩
        exact ⟨he.symm ▸ ⟨hg.1, hg.2, hf⟩, he⟩
    -- `(1/|Y|)^(|I| + |J|) = 1/|Y|^|I| · (1/|Y|)^|J| = 𝒰(I → Y)(value) · (1/|Y|)^|J|`.
    rw [hm, he, Distribution.uniform_apply, Fintype.card_fun, Nat.cast_pow, pow_add,
      div_pow, one_pow]
  -- Any other fiber is empty on both sides, since `evaluate F = value` would give
  -- `Good value ∧ Event value`; no injectivity is used here.
  · rw [if_neg hg, zero_mul]
    apply Distribution.mass_eq_zero_of_forall_not
    rintro f ⟨⟨hgood, hevent, _⟩, he⟩
    exact hg (he ▸ ⟨hgood, hevent⟩)

end Probability.Counting
