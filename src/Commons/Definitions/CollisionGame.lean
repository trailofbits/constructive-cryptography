module

public import Commons.Definitions.Ideal
public import RandomSystems.Typed.AutomatonGame

/-!
# Collisions in a uniform random function

`URF.collisionGame A` monitors equal replies at distinct inputs to the same port of `URF A`.
One uniform function is retained at each port; the hidden event becomes true at the first
such pair and stays true. Different ports are tested separately. Repeated inputs alone do not
set the event. In [1, §4.4.3, p. 137], the permutation challenger tests for such a collision
before replacing a repeated output. With the same default draws, its first firing agrees
with the first collision in the function challenger, which has the URF transcript law.
The source bounds this event by collisions among all of its presampled default replies.

`URF.collisionGame_unsetMBOs_eq` identifies the all-unset transcript law with URF mass
restricted to collision-free replies. This supplies the cumulative law for the adaptive
bound in `Commons.Definitions.CollisionBound`.
`URF.collisionGame_unsetProbability` gives the probability that its condition remains false.
`URF.collisionGame_visible` proves that hiding the event gives exactly `URF A`, preserving
its declared domain and arbitrary adaptive interactions. The game uses
`TypedGame.ofAutomaton`; its state update retains the sampled functions unchanged.

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace Commons.URF

open SystemAlgebra Probability Probability.Distribution

-- `A` supplies ports, finite alphabets and the selected query domain.
variable (A : Interface)

/-- Two distinct queries at one port in `xs` have equal replies under `f`.
[1, §4.4.3, p. 137] tests “if yᵢ ∈ {y₁, . . . , yᵢ₋₁}” only at a fresh input. -/
def Collision
    -- `f` is the retained function at each port; `xs` records tagged inputs.
    (f : ∀ i, A.X i → A.Y i) (xs : List (Σ i, A.X i)) : Prop :=
  ∃ i x x', (⟨i, x⟩ : Σ i, A.X i) ∈ xs ∧ ⟨i, x'⟩ ∈ xs ∧ x ≠ x' ∧ f i x = f i x'

/-- A collision persists when more queries are added. -/
lemma Collision.mono
    -- `f` supplies replies; `hxs` includes every tested query of `xs` in `ys`.
    {f : ∀ i, A.X i → A.Y i} {xs ys : List (Σ i, A.X i)}
    (hxs : xs ⊆ ys) (h : Collision A f xs) : Collision A f ys := by
  obtain ⟨i, x, x', hx, hx', hne, he⟩ := h
  exact ⟨i, x, x', hxs hx, hxs hx', hne, he⟩

open Classical in
/-- On `A.domain`, retain `f ← 𝒰[∀ i, A.X i → A.Y i]` and answer `i(x)` with `f i x`.
The hidden bit records `Collision A f xs` on the queries so far. -/
noncomputable def collisionGame
    -- Each reply type is inhabited so that its uniform law is normalized.
    [∀ i, Nonempty (A.Y i)] : TypedGame A :=
  TypedGame.ofAutomaton A (fun (f : ∀ i, A.X i → A.Y i) i x => (f, f i x))
    𝒰[∀ i, A.X i → A.Y i]
    (fun f => ⟨Collision A f, fun _ _ hp => Collision.mono A hp.subset⟩)

/-- A collision is failure of injectivity of the tagged reply function on tested inputs.
Equal tagged replies have the same port, so this is precisely the per-port event. -/
lemma Collision.iff_not_injOn
    -- `f` supplies retained replies; `xs` contains the tested tagged inputs.
    (f : ∀ i, A.X i → A.Y i) (xs : List (Σ i, A.X i)) :
    Collision A f xs ↔ ¬ Set.InjOn (fun x : Σ i, A.X i => (⟨x.1, f x.1 x.2⟩ : Σ i, A.Y i))
      {x | x ∈ xs} := by
  -- Tagged equality identifies both the common port and its two reply values.
  constructor
  · rintro ⟨i, x, y, hx, hy, hne, he⟩ hi
    exact hne (eq_of_heq (Sigma.mk.inj_iff.mp (hi hx hy (congrArg (Sigma.mk i) he))).2)
  · intro hn
    unfold Set.InjOn at hn
    push Not at hn
    obtain ⟨⟨i, x⟩, hx, ⟨j, y⟩, hy, he, hne⟩ := hn
    have hij := congrArg Sigma.fst he
    change i = j at hij
    subst j
    exact ⟨i, x, y, hx, hy, fun h => hne (congrArg (Sigma.mk i) h),
      eq_of_heq (Sigma.mk.inj_iff.mp he).2⟩

open Classical in
/-- A transcript whose equal replies came from identical inputs keeps its URF mass with every
MBO unset; any other transcript has mass zero. -/
lemma collisionGame_unsetMBOs_eq [∀ i, Nonempty (A.Y i)]
    -- `h` is a visible transcript on the original interface, including unadmitted histories.
    (h : List ((Σ i, A.X i) × Σ i, A.Y i)) :
    (collisionGame A).1.1 (unsetMBOs h) =
      if (∀ a ∈ h, ∀ b ∈ h, a.2 = b.2 → a.1 = b.1) then (Commons.URF A).1 h else 0 := by
  classical
  -- Pull back the unset event to the one retained family of functions.
  rw [collisionGame, TypedGame.ofAutomaton_mass_unsetMBOs]
  swap
  · rintro f _ ⟨i, x, x', hx, _⟩
    exact List.not_mem_nil hx
  have he (f : ∀ i, A.X i → A.Y i) :
      filterDom A.domain (automatonSystem (fun f i x => (f, f i x)) f) =
        (DDS.ofFunction A.domain A.nonempty_prefix
          (fun x => (⟨x.1, f x.1 x.2⟩ : Σ i, A.Y i))).1 :=
    Interface.automatonDDS_eq_ofFunction A id f
  simp only [he]
  have hc (f : ∀ i, A.X i → A.Y i)
      (hr : Replies (DDS.ofFunction A.domain A.nonempty_prefix
        (fun x => (⟨x.1, f x.1 x.2⟩ : Σ i, A.Y i))).1
        (h.map Prod.fst) (h.map Prod.snd)) :
      ¬ Collision A f (h.map Prod.fst) ↔
        ∀ a ∈ h, ∀ b ∈ h, a.2 = b.2 → a.1 = b.1 := by
    rw [Collision.iff_not_injOn, not_not]
    -- Since `f` answers `h`, injectivity on tested inputs says that equal recorded replies
    -- came from identical inputs.
    have hh := (DDS.replies_ofFunction_iff _ _ _ _ _).mp hr |>.2
    rw [List.map_map] at hh
    have replies z (hz : z ∈ h) := ((List.map_eq_map_iff.mp hh) z hz).symm
    constructor
    · intro hi a ha b hb he
      exact hi (List.mem_map.mpr ⟨a, ha, rfl⟩) (List.mem_map.mpr ⟨b, hb, rfl⟩)
        ((replies a ha).trans (he.trans (replies b hb).symm))
    · intro hg x hx y hy he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
      exact hg a ha b hb ((replies a ha).symm.trans (he.trans (replies b hb)))
  -- The transcript alone determines whether any function answering it has a collision.
  by_cases good : ∀ a ∈ h, ∀ b ∈ h, a.2 = b.2 → a.1 = b.1
  · rw [ite_eq_left good, Commons.URF, TypedSystem.sample_ofFunction_mass,
      behaviorMass, mass_fTransform]
    exact mass_congr _ fun f => ⟨And.left, fun hr => ⟨hr, (hc f hr).mpr good⟩⟩
  · rw [ite_eq_right good]
    exact mass_eq_zero_of_forall_not _ fun f hf => good ((hc f hf.1).mp hf.2)

open Classical in
/-- On admitted queries, the MBO stays unset exactly when the retained functions have no
collision among distinct inputs at any one port. -/
lemma collisionGame_unsetProbability [∀ i, Nonempty (A.Y i)]
    -- `xs` is the chosen admitted query list, including any repeated inputs.
    {xs : List (Σ i, A.X i)} (hxs : A.domain xs) :
    (collisionGame A).1.1.unsetProbability xs =
      1 - (Distribution.uniform (∀ i, A.X i → A.Y i)).mass (fun f => Collision A f xs) := by
  rw [collisionGame, TypedGame.ofAutomaton_unsetProbability _ _ _ _ hxs]
  rfl

/-- Hiding the collision bit gives the URF on the same interface and domain. -/
lemma collisionGame_visible [∀ i, Nonempty (A.Y i)] :
    (collisionGame A).visible = Commons.URF A := by
  rw [collisionGame, TypedGame.visible_ofAutomaton, TypedSystem.ofAutomaton_eq_sample]
  rfl

end Commons.URF
