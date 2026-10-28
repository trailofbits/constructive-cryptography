import Probability.Counting

/-!
# Adaptive replay and independent public table constraints

`uniform_mass_replay_public_eq` counts a pinned adaptive output tuple together with public
values at distinct coordinates. `uniform_replay_public_good_factor` sums these fibers over
an explicit good event. The `pinned` equivalence is the consumer's proof that its evaluator
really queries those sites; it cannot be replaced by an informal causality claim.

These are finite-fiber consequences of `uniform_mass_eval_eq`. Jost's resource algebra
imposes no independence of revealed coordinates; independence here follows solely from
the uniform function law and the stated injectivity. No claim is made on the bad event.
-/

namespace Probability.Counting

open Classical in
/-- A replay pinned by its output tuple has the usual uniform-function fiber whenever its
sites, together with fixed public sites, are distinct. The replay can depend on prior outputs. -/
lemma uniform_mass_replay_public_eq {X Y I J : Type}
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
  -- The pinned evaluator event is a single joint table fiber.
  have he := uniform_mass_eval_eq (Sum.elim (site value) publicSite) hinj
    (Sum.elim value publicValue)
  rw [Fintype.card_sum] at he
  -- Combine private replay sites and public sites through the explicit sum injection.
  refine (Distribution.mass_congr _ fun f => ?_).trans he
  rw [pinned]
  constructor
  · rintro ⟨hi, hj⟩
    funext i
    cases i with
    | inl i => exact hi i
    | inr j => exact hj j
  · intro h
    exact ⟨fun i => congrFun h (.inl i), fun j => congrFun h (.inr j)⟩

open Classical in
/-- The good part of a causal reveal is independent of every fixed public table constraint.
This factors only the proved distinct-site event; it makes no independence claim on bad runs. -/
lemma uniform_replay_public_good_factor {X Y I J : Type}
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
  -- Partition the event by the complete replay output tuple.
  rw [Distribution.mass_eq_sum_mass_fiber _ _ evaluate Finset.univ (fun _ _ => Finset.mem_univ _)]
  conv_rhs => rw [Distribution.mass_eq_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro value _
  by_cases hg : Good value ∧ Event value
  · rw [if_pos hg]
    -- On the good part, all constrained coordinates are distinct.
    have he := uniform_mass_replay_public_eq site evaluate pinned publicSite publicValue value
      (hinj value hg.1)
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
    rw [hm, he, Distribution.uniform_apply, Fintype.card_fun, Nat.cast_pow, pow_add,
      div_pow, one_pow]
  -- Every other fiber contributes zero.
  · rw [if_neg hg, zero_mul]
    apply Distribution.mass_eq_zero_of_forall_not
    rintro f ⟨⟨hgood, hevent, _⟩, he⟩
    exact hg (he ▸ ⟨hgood, hevent⟩)

end Probability.Counting
