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

`URF.collisionGame_unsetProbability` gives the probability of its hidden condition.
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
