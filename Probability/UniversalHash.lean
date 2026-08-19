/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Probability.Distribution

/-!
# Almost-universal hashing

The one universality notion for keyed hash families, at the L2 level of the
probability tower (`DESIGN.md` §12): a bound on the probability that two
*distinct* messages are related in the output, over a random key.

## The definition, and why this shape

`IsAlmostUniversalFor H keyDist Φ len δ` reads

  `∀ m ≠ m',  Pr_{k ← keyDist} [ Φ (H k m) (H k m') ] ≤ δ (max (len m) (len m'))`.

Three parameters carry the generality that the specialized notions in this
tree each dropped, and each is forced by a caller that could not be stated
without it:

* **`δ` depends on the input length.**  This is Maurer's `δ`-almost universal
  hash (CR18 lecture notes Definition 6.2, printed p. 129): `δ : ℕ → ℝ⁺` and
  the bound is `δ(max(|y|,|y'|))`.  The source's own footnote records that this
  is *more general* than the literature's length-independent definition.  The
  domain-extension corollary (Corollary 6.4, printed p. 130 — a `δ`-AUH
  followed by a random function constructs a long-input random function with
  error `½r²δ(ℓ)`) quantifies over the length cap `ℓ`, so it cannot even be
  stated against a scalar `ε`.
* **`Φ` is the relation on digests**, not hard-wired to equality.  Equality is
  almost-universality; `fun x y => x - y = g` for every offset `g` is
  almost-XOR-universality, which is what the POLYVAL-class hash of HCTR2 §3.2
  provides and what a Carter–Wegman-style analysis consumes.  Only the pair
  event changes between the two, so only it is a parameter.
* **`keyDist` is an arbitrary key law.**  The sources say "uniformly selected
  key", which is `Distribution.uniform K`; nothing in the union bound needs it, and
  the seeded condition-C games in this tree carry an arbitrary seed law.

`len` is a length function on the message type rather than a literal bit
length: the source's domain is `𝒴 ⊆ {0,1}*`, i.e. an arbitrary sub-domain
carrying a notion of size, and in Lean that sub-domain is the message type
itself.

## The specializations

| notion | source | here |
| --- | --- | --- |
| `δ`-almost universal | CR18 Definition 6.2 | `IsAlmostUniversal` (`Φ := Eq`) |
| `ε`-universal, scalar | Boneh–Shoup Definition 7.4 | `IsEpsUniversal` (`δ` constant) |
| 2-universal | CR18 Definition 7.2 | `Is2Universal` (`ε := 1/|X|`) |
| `δ`-almost-XOR-universal | HCTR2 §3.2 Property 2 | `IsAlmostXorUniversal` |

CR18 Definition 7.2 is introduced there as "a special case of the concept of
`δ`-AUH functions", and that is exactly how it is obtained here.

## The union bound

`mass_exists_ne_le_choose_two_mul` is the one collision-probability estimate
every caller wants: on `n ≤ q` queries whose lengths are capped by `ℓ`, some
pair of *distinct* queried messages collides with probability at most
`C(q,2)·δ(ℓ)`.  `mass_exists_mem_list_le_choose_two_mul` is its `List` form,
which is the shape an adaptive condition-C game's fixed-schedule leaf hands
you.

UPSTREAM-CANDIDATE: mathlib has no universal-hashing notion.
-/

open scoped BigOperators NNReal

namespace Probability

universe u v w

variable {K : Type u} {M : Type v} {X : Type w}

/-! ## The definition -/

/-- **`δ`-almost `Φ`-universal keyed hash family.**  For any two distinct
messages, the probability under a random key that their digests stand in the
relation `Φ` is at most `δ` evaluated at the larger of the two lengths.

The equality instance is Maurer's `δ`-almost universal hash function (CR18
lecture notes Definition 6.2): `Pr(H_K(y) = H_K(y')) ≤ δ(max(|y|,|y'|))` for
distinct `y, y'` and a uniformly selected key.  See the module docstring for
why each of `Φ`, `len` and `keyDist` is a parameter.

Nothing here is assumed about `δ` — not monotonicity, not that it is a
probability.  The lemmas that need `Monotone δ` (to replace both lengths by a
cap) ask for it individually. -/
def IsAlmostUniversalFor (H : K → M → X) (keyDist : Distribution K) (Φ : X → X → Prop)
    (len : M → ℕ) (δ : ℕ → NNReal) : Prop :=
  ∀ m m' : M, m ≠ m' →
    keyDist.mass (fun k => Φ (H k m) (H k m')) ≤ δ (max (len m) (len m'))

/-- **`δ`-almost universal hash function** (CR18 lecture notes Definition 6.2,
printed p. 129): the collision instance `Φ := Eq` of `IsAlmostUniversalFor`. -/
abbrev IsAlmostUniversal (H : K → M → X) (keyDist : Distribution K) (len : M → ℕ)
    (δ : ℕ → NNReal) : Prop :=
  IsAlmostUniversalFor H keyDist Eq len δ

/-- **`ε`-universal hash function** (Boneh–Shoup Definition 7.4 with Attack
Game 7.1): the length-independent instance, `δ` constant.  This is the scalar
notion, and it is `IsAlmostUniversal` at a constant `δ` for *any* length
function — see `isEpsUniversal_iff_isAlmostUniversal_const`. -/
abbrev IsEpsUniversal (H : K → M → X) (keyDist : Distribution K) (ε : NNReal) : Prop :=
  IsAlmostUniversal H keyDist (fun _ => 0) (fun _ => ε)

/-- **A 2-universal (Carter–Wegman "universal") class** (CR18 lecture notes
Definition 7.2, printed p. 139): distinct messages collide with probability at
most `1/|X|` under a uniformly chosen member of the class.  The source
introduces it as "a special case of the concept of `δ`-AUH functions", which
is how it is obtained here: `IsEpsUniversal` at `ε = 1/|X|`. -/
abbrev Is2Universal [Fintype X] (H : K → M → X) (keyDist : Distribution K) : Prop :=
  IsEpsUniversal H keyDist (1 / (Fintype.card X : NNReal))

/-- **`δ`-almost-XOR-universal hash family** (HCTR2 §3.2, Property 2 of
`H_h̄`): for distinct messages the digest *difference* hits every fixed target
`g` with probability at most `δ`, not merely the target `0`.  Over a field of
characteristic two — the setting of every AXU hash in this tree — `x - y` is
`x + y`, so this is the paper's `Pr[H(m₁) ⊕ H(m₂) = g] ≤ δ`. -/
abbrev IsAlmostXorUniversal [AddGroup X] (H : K → M → X) (keyDist : Distribution K)
    (len : M → ℕ) (δ : ℕ → NNReal) : Prop :=
  ∀ g : X, IsAlmostUniversalFor H keyDist (fun x y => x - y = g) len δ

/-! ## Relations between the specializations -/

/-- The scalar notion is the constant-`δ` almost-universal notion, at any
length function at all: a constant bound does not read the length. -/
theorem isEpsUniversal_iff_isAlmostUniversal_const (H : K → M → X)
    (keyDist : Distribution K) (ε : NNReal) (len : M → ℕ) :
    IsEpsUniversal H keyDist ε ↔ IsAlmostUniversal H keyDist len (fun _ => ε) :=
  Iff.rfl

/-- 2-universality is the scalar notion at `ε = 1/|X|`. -/
theorem is2Universal_iff_isEpsUniversal [Fintype X] (H : K → M → X)
    (keyDist : Distribution K) :
    Is2Universal H keyDist ↔
      IsEpsUniversal H keyDist (1 / (Fintype.card X : NNReal)) :=
  Iff.rfl

/-- **Almost-XOR-universal implies almost-universal**: the collision event is
the difference event at target `0`. -/
theorem IsAlmostXorUniversal.isAlmostUniversal [AddGroup X] {H : K → M → X}
    {keyDist : Distribution K} {len : M → ℕ} {δ : ℕ → NNReal}
    (hAXU : IsAlmostXorUniversal H keyDist len δ) :
    IsAlmostUniversal H keyDist len δ := fun m m' hne => by
  simpa only [sub_eq_zero] using hAXU 0 m m' hne

namespace IsAlmostUniversalFor

variable {H : K → M → X} {keyDist : Distribution K} {Φ : X → X → Prop} {len : M → ℕ}
  {δ δ' : ℕ → NNReal}

/-- Universality at a pointwise larger bound. -/
theorem mono (hAU : IsAlmostUniversalFor H keyDist Φ len δ) (hδ : δ ≤ δ') :
    IsAlmostUniversalFor H keyDist Φ len δ' := fun m m' hne =>
  (hAU m m' hne).trans (by exact_mod_cast hδ _)

/-- The defining bound with both lengths replaced by a common cap `ℓ`.  This
is where `Monotone δ` is needed, and the only place: the definition itself
reads `δ` at the exact larger length. -/
theorem mass_le_of_len_le (hAU : IsAlmostUniversalFor H keyDist Φ len δ)
    (hδ : Monotone δ) {m m' : M} (hne : m ≠ m') {ℓ : ℕ} (hm : len m ≤ ℓ)
    (hm' : len m' ≤ ℓ) :
    keyDist.mass (fun k => Φ (H k m) (H k m')) ≤ δ ℓ :=
  (hAU m m' hne).trans (by exact_mod_cast hδ (max_le hm hm'))

/-! ### The union bound over a set of message pairs -/

/-- **Union bound over an indexed family of distinct message pairs**, at the
exact per-pair lengths. -/
theorem mass_exists_mem_le_sum (hAU : IsAlmostUniversalFor H keyDist Φ len δ)
    (hkey : keyDist.NonNeg) {ι : Type*} (s : Finset ι) (f : ι → M × M)
    (hne : ∀ i ∈ s, (f i).1 ≠ (f i).2) :
    keyDist.mass (fun k => ∃ i ∈ s, Φ (H k (f i).1) (H k (f i).2))
      ≤ ∑ i ∈ s, (δ (max (len (f i).1) (len (f i).2)) : ℝ) :=
  (Distribution.mass_exists_le hkey s _).trans
    (Finset.sum_le_sum fun i hi => hAU _ _ (hne i hi))

/-- **Union bound at a common length cap**: `|s|` pairs, each within the cap
`ℓ`, cost `|s|·δ(ℓ)`. -/
theorem mass_exists_mem_le_card_mul (hAU : IsAlmostUniversalFor H keyDist Φ len δ)
    (hkey : keyDist.NonNeg) (hδ : Monotone δ) {ι : Type*} (s : Finset ι)
    (f : ι → M × M) (hne : ∀ i ∈ s, (f i).1 ≠ (f i).2) {ℓ : ℕ}
    (hlen : ∀ i ∈ s, len (f i).1 ≤ ℓ ∧ len (f i).2 ≤ ℓ) :
    keyDist.mass (fun k => ∃ i ∈ s, Φ (H k (f i).1) (H k (f i).2))
      ≤ (s.card : ℝ) * δ ℓ := by
  refine (hAU.mass_exists_mem_le_sum hkey s f hne).trans ?_
  refine (Finset.sum_le_sum (g := fun _ => (δ ℓ : ℝ)) fun i hi => ?_).trans_eq ?_
  · exact_mod_cast hδ (max_le (hlen i hi).1 (hlen i hi).2)
  · rw [Finset.sum_const, nsmul_eq_mul]

/-! ### The collision bound on a query vector -/

/-- Ordered index pairs of `Fin n` number `C(n,2)`.

UPSTREAM-CANDIDATE: the strict lower triangle of a square index set. -/
theorem card_filter_lt_eq_choose_two (n : ℕ) :
    ((Finset.univ : Finset (Fin n × Fin n)).filter
      (fun p => p.1.val < p.2.val)).card = Nat.choose n 2 := by
  classical
  rw [← Fintype.card_subtype (fun p : Fin n × Fin n => p.1.val < p.2.val)]
  let e : {p : Fin n × Fin n // p.1.val < p.2.val} ≃
      Sigma (fun j : Fin n => Fin j.val) :=
    { toFun := fun x => ⟨x.1.2, ⟨x.1.1.val, x.2⟩⟩
      invFun := fun x => ⟨(⟨x.2.1, Nat.lt_trans x.2.2 x.1.2⟩, x.1), x.2.2⟩
      left_inv := by
        intro x
        rcases x with ⟨⟨i, j⟩, hij⟩
        simp
      right_inv := by
        intro x
        rcases x with ⟨j, i⟩
        simp }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_eq_sum_range (f := fun m : ℕ => m)] at ih ⊢
      rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ]
      simp [Nat.add_comm]

/-- **The collision bound on a query vector.**  Among `n ≤ q` queried messages
of length at most `ℓ`, the probability that some two *distinct* ones are
`Φ`-related is at most `C(q,2)·δ(ℓ)`.

`Φ` is only asked to be symmetric, which is what lets each unordered pair be
charged once — an asymmetric relation would pay the ordered count `n(n-1)`. -/
theorem mass_exists_ne_le_choose_two_mul
    (hAU : IsAlmostUniversalFor H keyDist Φ len δ) (hkey : keyDist.NonNeg)
    (hsymm : ∀ x y : X, Φ x y → Φ y x) (hδ : Monotone δ) {n : ℕ} (ms : Fin n → M)
    {ℓ q : ℕ} (hlen : ∀ i, len (ms i) ≤ ℓ) (hq : n ≤ q) :
    keyDist.mass
        (fun k => ∃ i j : Fin n, ms i ≠ ms j ∧ Φ (H k (ms i)) (H k (ms j)))
      ≤ (Nat.choose q 2 : ℝ) * δ ℓ := by
  classical
  set s : Finset (Fin n × Fin n) :=
    (Finset.univ : Finset (Fin n × Fin n)).filter
      (fun p => p.1.val < p.2.val ∧ ms p.1 ≠ ms p.2) with hs
  have hcard : (s.card : ℝ) ≤ (Nat.choose q 2 : ℝ) := by
    have hsub : s ⊆ (Finset.univ : Finset (Fin n × Fin n)).filter
        (fun p => p.1.val < p.2.val) := by
      intro p hp
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp.1
    have := (Finset.card_le_card hsub).trans_eq (card_filter_lt_eq_choose_two n)
    exact_mod_cast this.trans (Nat.choose_le_choose 2 hq)
  calc
    keyDist.mass
        (fun k => ∃ i j : Fin n, ms i ≠ ms j ∧ Φ (H k (ms i)) (H k (ms j)))
        ≤ keyDist.mass
            (fun k => ∃ p ∈ s, Φ (H k (ms p.1)) (H k (ms p.2))) := by
          refine Distribution.mass_mono hkey ?_
          rintro k ⟨i, j, hij, hΦ⟩
          rcases lt_trichotomy i.val j.val with hlt | heq | hgt
          · refine ⟨(i, j), ?_, hΦ⟩
            simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hlt, hij⟩
          · exact absurd (congrArg ms (Fin.ext heq)) hij
          · refine ⟨(j, i), ?_, hsymm _ _ hΦ⟩
            simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hgt, hij.symm⟩
    _ ≤ (s.card : ℝ) * δ ℓ :=
        hAU.mass_exists_mem_le_card_mul hkey hδ s (fun p => (ms p.1, ms p.2))
          (fun p hp => ((Finset.mem_filter.mp hp).2).2)
          (fun p _ => ⟨hlen p.1, hlen p.2⟩)
    _ ≤ (Nat.choose q 2 : ℝ) * δ ℓ := by
        exact mul_le_mul_of_nonneg_right hcard (NNReal.coe_nonneg _)

/-- **The collision bound on a query list.**  Distinct messages of a list of
length at most `q`, each of length at most `ℓ`, collide with probability at
most `C(q,2)·δ(ℓ)`.

The event is literally the one an adaptive condition-C game's fixed-schedule
leaf presents (`RandomSystems.CR18.seededHashCollision`, stated on a `List`),
so this discharges such a leaf by `exact`. -/
theorem mass_exists_mem_list_le_choose_two_mul
    (hAU : IsAlmostUniversal H keyDist len δ) (hkey : keyDist.NonNeg)
    (hδ : Monotone δ) (l : List M) {ℓ q : ℕ} (hlen : ∀ m ∈ l, len m ≤ ℓ)
    (hq : l.length ≤ q) :
    keyDist.mass (fun k => ∃ x ∈ l, ∃ y ∈ l, x ≠ y ∧ H k x = H k y)
      ≤ (Nat.choose q 2 : ℝ) * δ ℓ := by
  classical
  refine le_trans (Distribution.mass_mono hkey
    (Q := fun k => ∃ i j : Fin l.length,
      l.get i ≠ l.get j ∧ H k (l.get i) = H k (l.get j)) ?_)
    (hAU.mass_exists_ne_le_choose_two_mul hkey (fun _ _ h => h.symm) hδ l.get
      (fun i => hlen _ (l.get_mem i)) hq)
  rintro k ⟨x, hx, y, hy, hxy, hH⟩
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hx
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hy
  exact ⟨i, j, hxy, hH⟩

end IsAlmostUniversalFor

end Probability
