/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.UpperLower.Closure
import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.Order.Birkhoff
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Lattice.Prod
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Event algebras: an orthogonal axis (GegMau26, ePrint 2026/1071)

§2, **Definition 1**:

> "An event algebra `(E; ⪯, ∧, ∨, ∸, ⊤, ⊥)` is a bounded lattice with an
> additional binary operation `∸`, satisfying the following for any
> `a, b, c ∈ E`:
>
>   `a ∸ a = ⊥`                              (E1)
>   `(a ∸ b) ∨ a = a`                        (E2)
>   `(a ∸ b) ∨ b = a ∨ b`                    (E3)
>   `(a ∨ b) ∸ c = (a ∸ c) ∨ (b ∸ c)`        (E4)
>   `(a ∸ b) ∧ (b ∸ a) = ⊥`                  (E5)"

> "Event algebras lie strictly between bounded distributive lattices and
> Boolean algebras."

§2.1, on what the axioms mean:

> "The axioms of Definition 1 capture natural and intuitive properties of
> the event concept: (E1) states that no event can occur without itself.
> (E2) is equivalent to stating that `a ∸ b` can't occur without `a`.
> The remaining axioms can be described similarly.  Note that (E5)
> captures that it can't be simultaneously the case that `a` occurred
> without `b` and vice versa, which implies that at any point in the
> development, the order in which the events have occurred so far is
> linear."

Following the plan's binding decision (§3.4), the base E1–E4 (their
`DualHeytingAlgebra`) is **not** re-axiomatized: their Lemma 1(iii)
`a ≤ b ⊔ c ↔ a ∸ b ≤ c` is mathlib's defining axiom `sdiff_le_iff`, so a
dual Heyting lattice *is* a `CoheytingAlgebra` (the bridge is
`GeneralizedCoheytingAlgebra.ofE1E2E3E4` below), and only E5 is a new
axiom: `EventAlgebra := CoheytingAlgebra + E5`.

## Dictionary (GegMau26 App. F.3 ↔ mathlib)

Their Lean development — App. F.3, "Lean Code for the Formal Verification
of Lemma 4", whose `DualHeytingAlgebra` class is E1–E4 — maps onto
`GeneralizedCoheytingAlgebra` as follows.  Everything on the right is
inherited for free.

**The Corollary 1 rows follow App. F.3's numbering, which is *not* the
body's.** The paper numbers Corollary 1 one way in §2.2 and another way
in its own Lean appendix; the two are cyclically shifted:

| item  | §2.2 (body)                        | App. F.3 (Lean code)               |
|-------|------------------------------------|------------------------------------|
| (i)   | `a ∸ b = ⊥ ⟺ a ⪯ b`                | `a ∸ b ⪯ ((a ⊓ c) ∸ b) ⊔ (a ∸ c)`  |
| (ii)  | `a ∸ b ⪯ ((a ⊓ c) ∸ b) ⊔ (a ∸ c)`  | `a ∸ b ⪯ (a ∸ c) ⊔ (c ∸ b)`        |
| (iii) | `a ∸ b ⪯ (a ∸ c) ⊔ (c ∸ b)`        | `a ∸ b = ⊥ ⟺ a ⪯ b`                |

This table is against App. F.3, as its heading says.  A reader checking a
Corollary 1 row against §2.2 of the paper will find it displaced by one;
that is the paper's discrepancy, not a transcription error here.  The
Lemma 1 rows are unaffected — body and appendix agree there.

| GegMau26            | mathlib                                        |
|---------------------|------------------------------------------------|
| E1                  | `sdiff_self`                                   |
| E2                  | `sdiff_le` (via `sup_eq_right`)                |
| E3                  | `sdiff_sup_self`                               |
| E4                  | `sup_sdiff`                                    |
| Lemma 1(i)          | `sdiff_le`                                     |
| Lemma 1(ii)         | `sdiff_le_sdiff_right`                         |
| Lemma 1(iii)        | `sdiff_le_iff` (the defining axiom)            |
| Lemma 1(iv)         | `sdiff_le_sdiff_left`                          |
| Lemma 1(v)          | `inf_sup_sdiff_eq` (below)                     |
| Lemma 1(vii)        | `sdiff_inf`                                    |
| Lemma 2 / distrib.  | `GeneralizedCoheytingAlgebra.toDistribLattice` |
| Lemma 11            | `sdiff_sdiff`                                  |
| Corollary 1(i)      | `sdiff_le_inf_sdiff_sup_sdiff` (below)         |
| Corollary 1(ii)     | `sdiff_triangle`                               |
| Corollary 1(iii)    | `sdiff_eq_bot_iff`                             |
| Lemma 8 (Boolean ⊆) | the `BooleanAlgebra` instance below            |

New content (needs E5): Lemma 1(vi) = `inf_sdiff_distrib` (J1),
Lemma 1(viii) = `sdiff_sup_distrib` (J2), Lemma 12 = the
`EventAlgebra.ofInfSdiffDistrib` / `EventAlgebra.ofSdiffSupDistrib`
constructors.  The UEI machinery (their Lemmas 3, 4, 15) is in
`AbstractCryptography.EventAlgebra`; the forest development below implements
Theorems 1 and 2, while Theorem 3 motivates the infinite-chain generalization in
`ForestOrder`.  The `LatticeValuation` definition takes up the paper's
future-work proposal; every valuation lemma after that definition is
project-local (plan §4, P4).

## References

* [B. Gegier, U. Maurer, *Event Algebras and Applications to
  Cryptography*, ePrint 2026/1071][GegMau26], §2, App. F.3.
-/

namespace AbstractCryptography

variable {α : Type*}

/-! ### The two paper lemmas at E1–E4 level that mathlib lacks -/

section GeneralizedCoheyting

variable [GeneralizedCoheytingAlgebra α]

/-- **Lemma 1(v)**: "`a = (a ∧ b) ∨ (a ∸ b)`".

"(v) expresses a form of case distinction for events, stating that for
any events `a` and `b`, if `a` occurs, either `a` occurred without `b`,
or `b` must have occurred as well." (§2.2) -/
theorem inf_sup_sdiff_eq (a b : α) : a ⊓ b ⊔ a \ b = a := by
  refine le_antisymm (sup_le inf_le_left sdiff_le) ?_
  have h : a = a ⊓ b ⊔ a ⊓ (a \ b) := by
    rw [← inf_sup_left, inf_eq_left.mpr le_sup_sdiff]
  rw [inf_eq_right.mpr sdiff_le] at h
  exact h.le

/-- **Corollary 1(ii)** in the body's numbering, **Corollary 1(i)** in
App. F.3's (`corollary_1_i`) — see the header's table; the paper numbers
these two differently in the two places.  The statement, unambiguously:

  `a ∸ b ⪯ ((a ∧ c) ∸ b) ∨ (a ∸ c)` -/
theorem sdiff_le_inf_sdiff_sup_sdiff (a b c : α) : a \ b ≤ (a ⊓ c) \ b ⊔ a \ c := by
  calc a \ b = (a ⊓ c ⊔ a \ c) \ b := by rw [inf_sup_sdiff_eq]
    _ = (a ⊓ c) \ b ⊔ (a \ c) \ b := sup_sdiff
    _ ≤ (a ⊓ c) \ b ⊔ a \ c := sup_le_sup_left sdiff_le _

end GeneralizedCoheyting

/-- **Ours**: the bridge discharging the header's claim that E1–E4 need
no re-axiomatization.  A lattice with `⊥` and a difference satisfying
E1–E4 — the paper's `DualHeytingAlgebra` (App. F.3), i.e. "a bounded
lattice satisfying (E1) up to (E4)" (Thm 3) — is a generalized co-Heyting
algebra.  Together with the reverse direction (E1–E4 are theorems in any
`GeneralizedCoheytingAlgebra`, per the dictionary above), this is the
equivalence of their base axiomatization with mathlib's.

The proof is their **Lemma 1(iii)**, "`a ⪯ b ∨ c ⟺ a ∸ b ⪯ c`" — which
in mathlib is not a lemma but the *defining* axiom `sdiff_le_iff`.  §2.2:
"(iii) gives a characterization of `∸` in terms of the order relation `⪯`
and `∨`." -/
@[reducible]
def GeneralizedCoheytingAlgebra.ofE1E2E3E4 [Lattice α] [OrderBot α] [SDiff α]
    (E1 : ∀ a : α, a \ a = ⊥)
    (E2 : ∀ a b : α, a \ b ⊔ a = a)
    (E3 : ∀ a b : α, a ⊔ b = a \ b ⊔ b)
    (E4 : ∀ a b c : α, (a ⊔ b) \ c = a \ c ⊔ b \ c) :
    GeneralizedCoheytingAlgebra α :=
  { ‹Lattice α›, ‹OrderBot α›, ‹SDiff α› with
    sdiff_le_iff := fun a b c => by
      constructor
      · intro h
        calc a ≤ a ⊔ b := le_sup_left
          _ = a \ b ⊔ b := E3 a b
          _ ≤ c ⊔ b := sup_le_sup_right h b
          _ = b ⊔ c := sup_comm ..
      · intro h
        calc a \ b ≤ a \ b ⊔ (b ⊔ c) \ b := le_sup_left
          _ = (a ⊔ (b ⊔ c)) \ b := (E4 ..).symm
          _ = (b ⊔ c) \ b := by rw [sup_eq_right.mpr h]
          _ = b \ b ⊔ c \ b := E4 ..
          _ = c \ b := by rw [E1, bot_sup_eq]
          _ ≤ c := le_sup_left.trans_eq (E2 c b) }

/-! ### The event algebra: E5 -/

/-- **Definition 1**: "An event algebra `(E; ⪯, ∧, ∨, ∸, ⊤, ⊥)` is a
bounded lattice with an additional binary operation `∸`, satisfying the
following for any `a, b, c ∈ E`: … `(a ∸ b) ∧ (b ∸ a) = ⊥`  (E5)".

E1–E4 are subsumed by `CoheytingAlgebra` (see the header), so only E5 is
a new axiom here.  §2.1 on E5: "(E5) captures that it can't be
simultaneously the case that `a` occurred without `b` and vice versa,
which implies that at any point in the development, the order in which
the events have occurred so far is linear."  (The paper gives E5 no
name.)

Fig. 11, "The relation of event algebras relative to other types of
algebras.  Arrows should be read as 'is a (proper) special case of'":

  `Boolean Algebra → Event Algebra → Dual Heyting Algebra →
   Bounded Distributive Lattice` -/
class EventAlgebra (α : Type*) extends CoheytingAlgebra α where
  /-- E5: `(a ∸ b) ∧ (b ∸ a) = ⊥`. -/
  sdiff_inf_sdiff (a b : α) : a \ b ⊓ b \ a = ⊥

export EventAlgebra (sdiff_inf_sdiff)

/-- App. B.2, **Lemma 8**: "Every Boolean algebra `(L; ⪯, ∧, ∨, ¯, ⊤, ⊥)`
is an event algebra, where `∸` is defined as `a ∸ b := a ∧ b̄`."

This is what carries UEIs into probability: "but every Boolean algebra,
in particular every σ-algebra, is an event algebra" (§2). -/
instance (priority := 100) [BooleanAlgebra α] : EventAlgebra α :=
  { (inferInstance : CoheytingAlgebra α) with
    sdiff_inf_sdiff := fun _ _ => disjoint_sdiff_sdiff.eq_bot }

section EventAlgebra

variable [EventAlgebra α]

/-- **Lemma 1(vi)**: "`(a ∧ b) ∸ c = (a ∸ c) ∧ (b ∸ c)`" — the identity
Lemma 12 calls **(J1)**.

Needs E5.  §2.2: "(vi) to (viii) together with (E4) show how `∸`
distributes over `∧` and `∨`."  (The `⪯` direction holds in any
co-Heyting algebra; equality is equivalent to E5 — that converse is
Lemma 12, `EventAlgebra.ofInfSdiffDistrib`.) -/
theorem inf_sdiff_distrib (a b c : α) : (a ⊓ b) \ c = a \ c ⊓ b \ c := by
  refine le_antisymm
    (le_inf (sdiff_le_sdiff_right inf_le_left) (sdiff_le_sdiff_right inf_le_right)) ?_
  calc a \ c ⊓ b \ c
      = (a ⊓ b ⊔ a \ b) \ c ⊓ (b ⊓ a ⊔ b \ a) \ c := by
        rw [inf_sup_sdiff_eq, inf_sup_sdiff_eq]
    _ = ((a ⊓ b) \ c ⊔ (a \ b) \ c) ⊓ ((a ⊓ b) \ c ⊔ (b \ a) \ c) := by
        rw [sup_sdiff, sup_sdiff, inf_comm b a]
    _ = (a ⊓ b) \ c ⊔ (a \ b) \ c ⊓ (b \ a) \ c := (sup_inf_left ..).symm
    _ ≤ (a ⊓ b) \ c ⊔ a \ b ⊓ b \ a := sup_le_sup_left (inf_le_inf sdiff_le sdiff_le) _
    _ = (a ⊓ b) \ c := by rw [sdiff_inf_sdiff, sup_bot_eq]

/-- **Lemma 1(viii)**: "`a ∸ (b ∨ c) = (a ∸ b) ∧ (a ∸ c)`" — the identity
Lemma 12 calls **(J2)**.

Needs E5; again `⪯` is co-Heyting and equality is equivalent to E5
(Lemma 12, `EventAlgebra.ofSdiffSupDistrib`). -/
theorem sdiff_sup_distrib (a b c : α) : a \ (b ⊔ c) = a \ b ⊓ a \ c := by
  refine le_antisymm
    (le_inf (sdiff_le_sdiff_left le_sup_left) (sdiff_le_sdiff_left le_sup_right)) ?_
  calc a \ b ⊓ a \ c
      ≤ (a ⊔ c) \ b ⊓ (a ⊔ b) \ c :=
        inf_le_inf (sdiff_le_sdiff_right le_sup_left) (sdiff_le_sdiff_right le_sup_left)
    _ = (a \ c ⊔ c) \ b ⊓ (a \ b ⊔ b) \ c := by
        rw [sdiff_sup_self c a, sdiff_sup_self b a]
    _ = (a \ (c ⊔ b) ⊔ c \ b) ⊓ (a \ (b ⊔ c) ⊔ b \ c) := by
        rw [sup_sdiff, sup_sdiff, sdiff_sdiff, sdiff_sdiff]
    _ = (a \ (b ⊔ c) ⊔ c \ b) ⊓ (a \ (b ⊔ c) ⊔ b \ c) := by rw [sup_comm c b]
    _ = a \ (b ⊔ c) ⊔ c \ b ⊓ b \ c := (sup_inf_left ..).symm
    _ = a \ (b ⊔ c) := by rw [sdiff_inf_sdiff, sup_bot_eq]

end EventAlgebra

/-! ### Lemma 12: J1 or J2 imply E5 (constructors)

**Lemma 12**: "Any lattice `E` satisfying (E1) - (E4) in which one of the
following identities holds is an event algebra:

  `(a ∧ b) ∸ c = (a ∸ c) ∧ (b ∸ c)`      (J1)
  `a ∸ (b ∨ c) = (a ∸ b) ∧ (a ∸ c)`      (J2)"

"*Proof.* We only have to prove that (E5) is satisfied."
-/

/-- **Lemma 12**, the (J1) half: a lattice satisfying E1–E4 in which
`(a ∧ b) ∸ c = (a ∸ c) ∧ (b ∸ c)` holds is an event algebra.  Mathlib
`ofSDiff`-style non-instance constructor. -/
@[reducible]
def EventAlgebra.ofInfSdiffDistrib [CoheytingAlgebra α]
    (J1 : ∀ a b c : α, (a ⊓ b) \ c = a \ c ⊓ b \ c) : EventAlgebra α where
  sdiff_inf_sdiff a b := by
    calc a \ b ⊓ b \ a = a \ (a ⊓ b) ⊓ b \ (a ⊓ b) := by
          rw [sdiff_inf, sdiff_inf, sdiff_self, sdiff_self, bot_sup_eq, sup_bot_eq]
      _ = (a ⊓ b) \ (a ⊓ b) := (J1 ..).symm
      _ = ⊥ := sdiff_self

/-- **Lemma 12**, the (J2) half: a lattice satisfying E1–E4 in which
`a ∸ (b ∨ c) = (a ∸ b) ∧ (a ∸ c)` holds is an event algebra. -/
@[reducible]
def EventAlgebra.ofSdiffSupDistrib [CoheytingAlgebra α]
    (J2 : ∀ a b c : α, a \ (b ⊔ c) = a \ b ⊓ a \ c) : EventAlgebra α where
  sdiff_inf_sdiff a b := by
    calc a \ b ⊓ b \ a = (a ⊔ b) \ b ⊓ (a ⊔ b) \ a := by
          rw [sup_sdiff_right_self, sup_sdiff_left_self]
      _ = (a ⊔ b) \ (b ⊔ a) := (J2 ..).symm
      _ = ⊥ := by rw [sup_comm b a, sdiff_self]

end AbstractCryptography

/-!
# The forest representation of event algebras (GegMau26 §3, Thms 1–2)

Event algebras are exactly the algebras of down-sets of *forests*.  The
two directions, quoted:

**Theorem 1**: "For any forest poset (see Definition 9) `(P ; ⪯)`, the set
`(Dn(P) ; ⊆, ∪, ∩, ∸_P, P, ∅)` is an event algebra, where
`A ∸_P B := (A \ B)↓`."

> "Conversely, Theorem 2 is a consequence of a result due to Birkhoff
> [27] and shows that every event algebra can naturally be interpreted as
> a tree (or forest) capturing the dynamic development aspect of the
> algebra:"

**Theorem 2**: "For any finite event algebra `E`, `Ji(E)` (see
Definition 10) is a forest poset and we have `E ≅ Dn(Ji(E))`."

Dictionary: their `Dn(P)` is mathlib's `LowerSet P`; their `Ji(E)`
(**Definition 10**, "join-irreducible") is mathlib's `SupIrred`; their
`(·)↓` is `lowerClosure`; their `{x}↑` is `Set.Ici x`.

* `ForestOrder P` — **Definition 9**: "We call a poset `(P ; ⪯)` a
  *forest poset* if every principal up-set of `P` is a finite chain."
  The **finiteness is deliberately dropped** from the class: it is used
  only for the *finite* representation theorem (Thm 2), and Thm 3 states
  the correspondence "allowing principal up-sets to be infinite chains".
  Mathlib-style it would be a separate `Fintype`/`WellFounded` mixin.
* `LowerSet.sdiff_eq_lowerClosure` — Theorem 1's difference
  `A ∸_P B := (A \ B)↓`, on the down-sets of *any* preorder.  The paper's
  App. B.1 proof notes the same: "Note that so far we have not used that
  `P` is a forest.  That is, we have shown that the down-sets on any
  poset are a dual Heyting algebra."
* `instEventAlgebraLowerSet` — **Theorem 1**.  Exactly as in the paper,
  the forest property is used only for E5.
* `forestOrder_supIrred` — the structural half of **Theorem 2**, "`Ji(E)`
  … is a forest poset".
* `EventAlgebra.orderIsoLowerSetSupIrred` — **Theorem 2**'s "`E ≅
  Dn(Ji(E))`", which the paper attributes to Birkhoff; here it *is*
  mathlib's Birkhoff representation `OrderIso.lowerSetSupIrred`, plus
  `forestOrder_supIrred`.  An order isomorphism suffices to transport the
  event algebra structure because of **Lemma 10**: "`∸` is uniquely
  defined in every event algebra."

## References

* [B. Gegier, U. Maurer, *Event Algebras and Applications to
  Cryptography*, ePrint 2026/1071][GegMau26], §3 (Def 9, Def 10,
  Thms 1–2, Lemma 10), App. B.1.
* Mathlib, `Order/Birkhoff.lean` (`OrderIso.lowerSetSupIrred`).
-/

namespace AbstractCryptography

variable {P α : Type*}

/-- **Definition 9**: "We call a poset `(P ; ⪯)` a *forest poset* if
every principal up-set of `P` is a finite chain."

The **finiteness of the chains is not required here** — see the header.
It is needed only for Theorem 2 (which is anyway stated for *finite*
event algebras), and Theorem 3 gives the correspondence "allowing
principal up-sets to be infinite chains". -/
class ForestOrder (P : Type*) [PartialOrder P] : Prop where
  isChain_Ici (a : P) : IsChain (· ≤ ·) (Set.Ici a)

/-- Def 9 in the form the E5 proof uses it — App. B.1: "Since `y, z ∈
{x}↑` and `P` is a forest poset, we must have either `y ≤ z` or
`z ≤ y`." -/
theorem ForestOrder.le_or_le [PartialOrder P] [ForestOrder P] {x a b : P}
    (ha : x ≤ a) (hb : x ≤ b) : a ≤ b ∨ b ≤ a := by
  rcases eq_or_ne a b with rfl | hab
  · exact Or.inl le_rfl
  · exact ForestOrder.isChain_Ici x ha hb hab

section LowerSet

variable [Preorder P]

/-- **Theorem 1**'s difference, "`A ∸_P B := (A \ B)↓`", agreeing with
mathlib's co-Heyting difference on `LowerSet P`.

No forest structure needed — App. B.1, after verifying E1–E4: "Note that
so far we have not used that `P` is a forest.  That is, we have shown
that the down-sets on any poset are a dual Heyting algebra."  The forest
property enters only at E5. -/
theorem LowerSet.sdiff_eq_lowerClosure (A B : LowerSet P) :
    A \ B = lowerClosure ((A : Set P) \ (B : Set P)) := by
  refine le_antisymm ?_ ?_
  · rw [sdiff_le_iff]
    intro x hxA
    refine LowerSet.mem_sup_iff.mpr ?_
    by_cases hxB : x ∈ B
    · exact Or.inl hxB
    · exact Or.inr (subset_lowerClosure ⟨hxA, hxB⟩)
  · rw [lowerClosure_le]
    rintro x ⟨hxA, hxB⟩
    have hx : x ∈ B ⊔ A \ B := LowerSet.coe_subset_coe.mpr le_sup_sdiff hxA
    rcases LowerSet.mem_sup_iff.mp hx with h | h
    · exact absurd h hxB
    · exact h

end LowerSet

/-- **Theorem 1**: "For any forest poset (see Definition 9) `(P ; ⪯)`,
the set `(Dn(P) ; ⊆, ∪, ∩, ∸_P, P, ∅)` is an event algebra, where
`A ∸_P B := (A \ B)↓`."

Only E5 uses the forest property.  The proof below is App. B.1's, which
reads in full:

> "(E5): We need to prove `(A ∸_P B) ∩ (B ∸_P A) = ∅`.  Assume towards
> contradiction that `x ∈ (A ∸_P B) ∩ (B ∸_P A) = (A \ B)↓ ∩ (B \ A)↓`.
> There must be `y, z` satisfying `x ⪯ y`, `y ∈ A`, `y ∉ B` as well as
> `x ⪯ z`, `z ∈ B`, `z ∉ A`.  Since `y, z ∈ {x}↑` and `P` is a forest
> poset, we must have either `y ≤ z` or `z ≤ y`.  If `y ≤ z` then
> `z ∈ B`, `y ∉ B` contradicts `B ∈ Dn(P)`.  Similarly, if `z ≤ y` then
> `y ∈ A`, `z ∉ A` contradicts `A ∈ Dn(P)`." -/
instance [PartialOrder P] [ForestOrder P] : EventAlgebra (LowerSet P) :=
  { (inferInstance : CoheytingAlgebra (LowerSet P)) with
    sdiff_inf_sdiff := fun A B => by
      rw [LowerSet.sdiff_eq_lowerClosure, LowerSet.sdiff_eq_lowerClosure]
      refine le_bot_iff.mp ?_
      intro x hx
      obtain ⟨hxAB, hxBA⟩ := LowerSet.mem_inf_iff.mp hx
      obtain ⟨a, ⟨haA, haB⟩, hxa⟩ := mem_lowerClosure.mp hxAB
      obtain ⟨b, ⟨hbB, hbA⟩, hxb⟩ := mem_lowerClosure.mp hxBA
      rcases ForestOrder.le_or_le hxa hxb with h | h
      · exact (haB (B.lower h hbB)).elim
      · exact (hbA (A.lower h haA)).elim }

/-- The structural half of **Theorem 2**: "For any finite event algebra
`E`, `Ji(E)` (see Definition 10) is a forest poset".

Their `Ji(E)` is mathlib's `SupIrred` — **Definition 10**: "An element
`a` of a lattice `(L; ⪯)` is *join-irreducible* if for all `B ⊆ L :
a = ⋁_{b∈B}` implies `a ∈ B`, i.e., `a` cannot be represented as the join
of different elements.  Denote by `Ji(L)` the set of join-irreducible
elements of `L`."  (Mathlib's `SupIrred` is the binary form; the two
agree on the finite lattices Thm 2 is about.)

Finiteness is not needed for *this* half: E5 alone gives the forest.  If
`a ⪯ b, c` with `b, c` join-irreducible and incomparable, then `b = b ∸ c`
and `c = c ∸ b` by join-irreducibility of the Lemma 1(v) splittings, so
`b ∧ c = ⊥` by E5, forcing the join-irreducible `a ⪯ ⊥` — absurd. -/
instance forestOrder_supIrred [EventAlgebra α] :
    ForestOrder {a : α // SupIrred a} where
  isChain_Ici a b hb c hc hbc := by
    by_contra h
    rw [not_or] at h
    obtain ⟨hbc', hcb'⟩ := h
    have hb' : (b : α) \ (c : α) = (b : α) :=
      (b.2.2 (inf_sup_sdiff_eq (b : α) (c : α))).resolve_left
        fun hEq => hbc' (Subtype.coe_le_coe.mp (inf_eq_left.mp hEq))
    have hc' : (c : α) \ (b : α) = (c : α) :=
      (c.2.2 (inf_sup_sdiff_eq (c : α) (b : α))).resolve_left
        fun hEq => hcb' (Subtype.coe_le_coe.mp (inf_eq_left.mp hEq))
    have hbot : (b : α) ⊓ (c : α) = ⊥ :=
      calc (b : α) ⊓ (c : α) = (b : α) \ (c : α) ⊓ ((c : α) \ (b : α)) := by rw [hb', hc']
        _ = ⊥ := sdiff_inf_sdiff (b : α) (c : α)
    have hab : (a : α) ≤ (b : α) ⊓ (c : α) :=
      le_inf (Subtype.coe_le_coe.mpr hb) (Subtype.coe_le_coe.mpr hc)
    rw [hbot] at hab
    exact a.2.ne_bot (le_bot_iff.mp hab)

/-- **Theorem 2**: "For any finite event algebra `E`, `Ji(E)` (see
Definition 10) is a forest poset and we have

  `E ≅ Dn(Ji(E))`."

This is the `≅` half; the target carries its event algebra structure by
Theorem 1, via `forestOrder_supIrred`.  The paper: "Conversely, Theorem 2
is a consequence of a result due to Birkhoff [27] and shows that every
event algebra can naturally be interpreted as a tree (or forest)
capturing the dynamic development aspect of the algebra" — and that
Birkhoff result is exactly mathlib's `OrderIso.lowerSetSupIrred`, so
there is nothing left to prove.

An *order* isomorphism is enough to make this an isomorphism of event
algebras: `⊔`, `⊓`, `⊥`, `⊤` are order-determined, and so is `∸`, by
**Lemma 10** — "`∸` is uniquely defined in every event algebra." -/
noncomputable def EventAlgebra.orderIsoLowerSetSupIrred
    [EventAlgebra α] [Fintype α] [@DecidablePred α SupIrred] :
    α ≃o LowerSet {a : α // SupIrred a} :=
  OrderIso.lowerSetSupIrred

end AbstractCryptography

/-!
# Universal event inequalities (GegMau26 §3.2, §4.2, App. F.3)

A *universal event inequality* (UEI) is a term inequality valid in every
event algebra.  §3.3:

> "UEIs hold in any event algebra (and for any choice of parameter sets
> and parameterized events).  To use this statement for a concrete
> (discrete-step) model, one must only verify that the axioms hold (for
> example, by verifying that the model defines a forest and using
> Theorem 1).  This is the precise sense in which the statements we prove
> are model-independent."

The two UEIs formalized here live in **different sections** — Lemma 3 in
§3, Lemma 4 in §4 — and their proofs are deferred to §E.3 ("Proofs for
Section 3") and §F.2 ("Proofs for Section 4") respectively.  Both are
formally verified in the paper's own Lean appendix, §F.3 ("Lean Code for
the Formal Verification of Lemma 4", which states: "The following allows
to formally verify Lemmas 3 and 4 (and the lemmas in Section 2) in
mathlib (Lean)").

The abbreviation both lemmas are stated in, §3.2, eq. (1) — "the
following term (which we will use later) expresses that `Fₓ` does not
precede `Eₓ` for some `x` in a parameter set `X` and two parameterized
events `E, F`":

  `nPre^X_{E,F} := ⋁ₓ (Eₓ ∸ Fₓ)`

Notably, both hold in any *generalized co-Heyting* algebra — E5 is not
needed — matching their Lean code, whose `lemma_3` and `lemma_4` assume
only `[DualHeytingAlgebra δ]`.

* `finsetSup_sdiff` — their `finset_sup_sdiff`, "a finite join version of
  (E4)".  Mathlib's `Finset.sup_sdiff_right` states this only for
  `GeneralizedBooleanAlgebra`; this is the co-Heyting generalization
  (upstream candidate).
* `uei_trans` — **Lemma 3** (§3.2), which their Lean code names
  "transitivity of authentication".
* `uei_two_step` — **Lemma 4** (§4.2), the headline UEI, the one App. F.3
  exists to verify.

Their helper `finset_sup_product` is mathlib's `Finset.sup_product_left`
(their proof is literally `rw [Finset.sup_product_left]`), and their
`lemma_15` is the `≤` direction of mathlib's `Finset.sup_sup`.

## References

* [B. Gegier, U. Maurer, *Event Algebras and Applications to
  Cryptography*, ePrint 2026/1071][GegMau26], §3.2, §4.2, App. F.3.
-/

namespace AbstractCryptography

variable {α ι κ : Type*} [GeneralizedCoheytingAlgebra α]

/-- App. F.3, `finset_sup_sdiff` — "This is a finite join version of
(E4)":

  `(⋁_{x∈s} f x) ∸ a = ⋁_{x∈s} (f x ∸ a)`

Co-Heyting generalization of mathlib's `Finset.sup_sdiff_right`, which
requires `GeneralizedBooleanAlgebra`. -/
theorem finsetSup_sdiff (s : Finset ι) (f : ι → α) (a : α) :
    s.sup f \ a = s.sup fun i => f i \ a := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => rw [Finset.sup_cons, Finset.sup_cons, sup_sdiff, ih]

/-- §3.2, **Lemma 3** — "a concrete example of a universal event
inequality (which is proved in Section E.3)":

> "For any event algebra `E`, any sets `X`, any `E, F, G : X → E`, we
> have
>
>   `nPre^X_{E,G} ⪯ nPre^X_{E,F} ∨ nPre^X_{F,G}`"

Unfolding `nPre` (§3.2 eq. (1)), that is

  `⋁ₓ (Eₓ ∸ Gₓ) ⪯ ⋁ₓ (Eₓ ∸ Fₓ) ∨ ⋁ₓ (Fₓ ∸ Gₓ)`

App. F.3 names it `lemma_3` and glosses it "transitivity of
authentication"; §3.5, "Authentication and Authentication Amplification",
supplies that narrative: "We present a narrative in which the term
`nPre^X_{E,F}` and Lemma 3 have cryptographic meaning." -/
theorem uei_trans (s : Finset ι) (E F G : ι → α) :
    (s.sup fun x => E x \ G x)
      ≤ (s.sup fun x => E x \ F x) ⊔ s.sup fun x => F x \ G x :=
  Finset.sup_le fun x hx =>
    (sdiff_triangle (E x) (F x) (G x)).trans
      (sup_le_sup (Finset.le_sup (f := fun x => E x \ F x) hx)
        (Finset.le_sup (f := fun x => F x \ G x) hx))

/-- §4.2, **Lemma 4** — "We first prove an abstract event inequality that
relates events of the structure introduced above.  Proofs are deferred to
Section F.2."

> "For any event algebra `E`, any finite sets `X, Y`, any `E, F : X → E`,
> `G, H : X × Y → E` we have
>
>   `nPre^X_{E,F} ⪯ pnPre^{X,Y}_{G,H} ∨ P1^{X,Y}_{H,F} ∨ P2^{X,Y}_{E,G}`
>
> where `P1^{X,Y}_{H,F} := ⋁_{x,y} (H_{x,y} ∸ Fₓ)` and
> `P2^{X,Y}_{E,G} := ⋁ₓ (Eₓ ∸ ⋁_{y′} G_{x,y′})`."

`pnPre` is §4.1 eq. (3), "the abstract event capturing the structure of
forgery events … (for sets `X, Y`, and 2-argument parameterized events
`E_{x,y}` and `F_{x,y}`)":

  `pnPre^{X,Y}_{E,F} := ⋁_{x,y} (E_{x,y} ∸ ⋁_{y′} F_{x,y′})`

The `⊔` association below follows App. F.3's `lemma_4` (`… ⊔ … ⊔ …`, left
associated), which is why `P2` — the `nPre`-through-`G` term — appears
first. -/
theorem uei_two_step (sX : Finset ι) (sY : Finset κ)
    (E F : ι → α) (G H : ι → κ → α) :
    (sX.sup fun x => E x \ F x)
      ≤ ((sX.sup fun x => E x \ sY.sup (G x))
          ⊔ (sX ×ˢ sY).sup fun p => G p.1 p.2 \ sY.sup (H p.1))
          ⊔ (sX ×ˢ sY).sup fun p => H p.1 p.2 \ F p.1 := by
  refine Finset.sup_le fun x hx => ?_
  -- one `sdiff_triangle` through `⨆ y, G x y`, then one through `⨆ y, H x y`
  have hG : sY.sup (G x) \ F x
      ≤ (sY.sup fun y => G x y \ sY.sup (H x)) ⊔ sY.sup (H x) \ F x := by
    rw [finsetSup_sdiff]
    exact Finset.sup_le fun y hy =>
      (sdiff_triangle (G x y) (sY.sup (H x)) (F x)).trans
        (sup_le_sup (Finset.le_sup (f := fun y => G x y \ sY.sup (H x)) hy) le_rfl)
  have h2 : (sY.sup fun y => G x y \ sY.sup (H x))
      ≤ (sX ×ˢ sY).sup fun p => G p.1 p.2 \ sY.sup (H p.1) :=
    Finset.sup_le fun y hy =>
      Finset.le_sup (b := (x, y)) (f := fun p => G p.1 p.2 \ sY.sup (H p.1))
        (Finset.mem_product.mpr ⟨hx, hy⟩)
  have h3 : sY.sup (H x) \ F x ≤ (sX ×ˢ sY).sup fun p => H p.1 p.2 \ F p.1 := by
    rw [finsetSup_sdiff]
    exact Finset.sup_le fun y hy =>
      Finset.le_sup (b := (x, y)) (f := fun p => H p.1 p.2 \ F p.1)
        (Finset.mem_product.mpr ⟨hx, hy⟩)
  calc E x \ F x
      ≤ E x \ sY.sup (G x) ⊔ sY.sup (G x) \ F x := sdiff_triangle ..
    _ ≤ E x \ sY.sup (G x)
        ⊔ (((sX ×ˢ sY).sup fun p => G p.1 p.2 \ sY.sup (H p.1))
            ⊔ (sX ×ˢ sY).sup fun p => H p.1 p.2 \ F p.1) :=
        sup_le_sup_left (hG.trans (sup_le_sup h2 h3)) _
    _ ≤ _ := by
        rw [← sup_assoc]
        exact sup_le_sup_right
          (sup_le_sup_right (Finset.le_sup (f := fun x => E x \ sY.sup (G x)) hx) _) _

end AbstractCryptography

/-!
# Lattice valuations and the UEI → probability transfer (plan P4)

Event algebras are probability-free; probability enters at the end, and
the paper says how.  §4.9:

> "Every σ-algebra is an event algebra (see Section B.2).  Therefore,
> UEIs hold also in every σ-algebra that contains the corresponding
> events, in particular, in any random experiment between an adversary
> and a game.  This means that statements involving an adversary's
> success probability follow directly: If, for example, we have
> `e ⪯ f ∨ g`, then `Pr(e) ≤ Pr(f) + Pr(g)` follows by the union bound,
> no matter how the random experiment is defined (that is, how the
> probability measure `P` is defined).  We emphasize that no independence
> assumptions (for example, between the adversary's and game's
> randomness) need to be made."

The *valuation* generalizing that is **future work in the paper**, not a
developed notion — §5 ("Conclusions and Future Work"), item 3, "Beyond
Event Algebras":

> "σ-algebras are event algebras, and UEIs yield corresponding
> probability-theoretic statements via the union bound.  A more ambitious
> goal is to generalize probability theory itself from σ-algebras to
> general event algebras.  A promising starting point is the notion of
> lattice valuations, functions `m : E → ℝ≥0` satisfying `m(⊥) = 0`,
> `m(⊤) = 1`, monotonicity, and modularity
> (`m(a) + m(b) = m(a ∧ b) + m(a ∨ b)`).  Restricted to σ-algebras,
> lattice valuations coincide with probability measures, but on general
> event algebras, they form a strictly richer class of quantitative
> tools."

This file takes up that starting point.  It is a genuine mathlib gap
(plan §4, upstream candidate): mathlib has `MeasureTheory.AddContent` for
set semirings but nothing for abstract lattices.

* `LatticeValuation α R` — the paper's four conditions minus
  normalization: `m ⊥ = 0`, monotone, modular.  **Two deviations from the
  quoted definition, both deliberate**: `m(⊤) = 1` is left as a separate
  hypothesis where needed (as mathlib does for measures — it is what
  distinguishes a probability measure from a content, and the UEI
  transfer never needs it), and the codomain is any ordered additive
  monoid rather than `ℝ≥0`.
* `sup_le_add` — finite subadditivity: the union bound, abstractly.
* `le_add_of_le_sup` — the **UEI transfer**, i.e. §4.9's "if, for
  example, we have `e ⪯ f ∨ g`, then `Pr(e) ≤ Pr(f) + Pr(g)`", for an
  arbitrary valuation in place of `Pr`.
* `finsetSup_le_sum` — subadditivity over a `Finset`-indexed join,
  `m (⋁_{i∈s} f i) ≤ ∑_{i∈s} m (f i)`.
* `le_sum_of_le_finsetSup` — the `Finset`-indexed transfer, which is the
  shape the UEIs of `AbstractCryptography.EventAlgebra` (Lemmas 3 and 4,
  both stated over `Finset.sup`) actually need:
  `e ⪯ ⋁_{i∈s} f i ⟹ m e ≤ ∑_{i∈s} m (f i)`.

Everything here past the `LatticeValuation` definition is **ours** — the
paper proposes the notion and stops.  The bridge to
`MeasureTheory.AddContent`/transcript-cylinder algebras is instantiation
material (plan §3.5, P4), deferred.

## References

* [B. Gegier, U. Maurer, *Event Algebras and Applications to
  Cryptography*, ePrint 2026/1071][GegMau26], §4.9, §5 (item 3).
-/

namespace AbstractCryptography

variable {α R : Type*}

/-- GegMau26 §5, item 3, on generalizing probability theory beyond
σ-algebras: "A promising starting point is the notion of *lattice
valuations*, functions `m : E → ℝ≥0` satisfying `m(⊥) = 0`, `m(⊤) = 1`,
monotonicity, and modularity (`m(a) + m(b) = m(a ∧ b) + m(a ∨ b)`).
Restricted to σ-algebras, lattice valuations coincide with probability
measures, but on general event algebras, they form a strictly richer
class of quantitative tools."

Deviations from that definition, deliberate (see the header):
normalization `m ⊤ = 1` is not a field, and the codomain is any ordered
additive monoid, not `ℝ≥0`. -/
structure LatticeValuation (α R : Type*) [Lattice α] [OrderBot α]
    [AddCommMonoid R] [PartialOrder R] where
  /-- The underlying map. -/
  toFun : α → R
  /-- "`m(⊥) = 0`". -/
  map_bot : toFun ⊥ = 0
  /-- "monotonicity". -/
  mono : Monotone toFun
  /-- "modularity (`m(a) + m(b) = m(a ∧ b) + m(a ∨ b)`)". -/
  modular (a b : α) : toFun (a ⊔ b) + toFun (a ⊓ b) = toFun a + toFun b

namespace LatticeValuation

variable [Lattice α] [OrderBot α] [AddCommMonoid R] [PartialOrder R]

instance : CoeFun (LatticeValuation α R) fun _ => α → R := ⟨toFun⟩

variable (m : LatticeValuation α R)

theorem nonneg (a : α) : 0 ≤ m a := m.map_bot ▸ m.mono bot_le

variable [IsOrderedAddMonoid R]

/-- **Ours**: finite subadditivity, `m (a ⊔ b) ≤ m a + m b` — the union
bound at an arbitrary valuation.  Modularity plus `m ≥ 0` (which is
`map_bot` and `mono`); the paper does not derive it. -/
theorem sup_le_add (a b : α) : m (a ⊔ b) ≤ m a + m b :=
  calc m (a ⊔ b) = m (a ⊔ b) + 0 := (add_zero _).symm
    _ ≤ m (a ⊔ b) + m (a ⊓ b) := add_le_add le_rfl (m.nonneg _)
    _ = m a + m b := m.modular a b

/-- The UEI → probability transfer.  GegMau26 §4.9: "If, for example, we
have `e ⪯ f ∨ g`, then `Pr(e) ≤ Pr(f) + Pr(g)` follows by the union
bound, no matter how the random experiment is defined (that is, how the
probability measure `P` is defined).  We emphasize that no independence
assumptions (for example, between the adversary's and game's randomness)
need to be made."

Stated here for an arbitrary valuation `m` in place of `Pr`; the paper's
own reading (§2, Fig. 11's surrounding text) is the σ-algebra case, via
Lemma 8. -/
theorem le_add_of_le_sup {e f g : α} (h : e ≤ f ⊔ g) : m e ≤ m f + m g :=
  (m.mono h).trans (m.sup_le_add f g)

/-- **Ours**: `sup_le_add` iterated over a `Finset`,
`m (⋁_{i∈s} f i) ≤ ∑_{i∈s} m (f i)`. -/
theorem finsetSup_le_sum {ι : Type*} (s : Finset ι) (f : ι → α) :
    m (s.sup f) ≤ ∑ i ∈ s, m (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [m.map_bot]
  | cons i s hi ih =>
    rw [Finset.sup_cons, Finset.sum_cons]
    exact (m.sup_le_add _ _).trans (add_le_add le_rfl ih)

/-- **Ours**: the `Finset`-indexed UEI transfer, `e ⪯ ⋁_{i∈s} f i ⟹
m e ≤ ∑_{i∈s} m (f i)`.

This is the form the paper's UEIs are actually shaped for — Lemmas 3 and
4 are both stated over joins indexed by parameter sets (`nPre^X_{E,F} :=
⋁ₓ (Eₓ ∸ Fₓ)`), so applying this to `uei_trans` / `uei_two_step` is what
turns each into a probability estimate. -/
theorem le_sum_of_le_finsetSup {ι : Type*} {s : Finset ι} {e : α} {f : ι → α}
    (h : e ≤ s.sup f) : m e ≤ ∑ i ∈ s, m (f i) :=
  (m.mono h).trans (m.finsetSup_le_sum s f)

end LatticeValuation

end AbstractCryptography
