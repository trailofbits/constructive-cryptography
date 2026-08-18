/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.Behaviour
import RandomSystems.System.Relabel

/-!
# Random games (Lanzenberger §2.3.3, Definitions 2.20–2.25)

Lanzenberger, *A Theory of Random Systems, Games, and Hardness Amplification*
(Diss. ETH 29554), §2.3.3, printed pp. 16–17.  Every definition is quoted in
the docstring that renders it and was checked against the printed page.

## The condition: an upper set of histories

**Definition 2.20** (printed p. 17): "A *monotone condition* (or MC) for an
`(𝒳,𝒴)`-DDS `s` is a monotone predicate `A : 𝒳* → {0,1}`", where footnote 7
reads "by *monotone* we mean that if `A(t) = 1` then `A(t|t') = 1` for any
extension `t|t'` of `t`".

The carrier is the *upper set*: `MonotoneCondition X` is an upward-closed set
of histories in the prefix order.  Monotonicity is then not a side condition
carried alongside a predicate but the closure property of the object itself,
which is what makes the algebra work — conditions form a **complete lattice**
(`⊔` is the union, the bad-event union every technique takes; `⨆ i, A i` is
the union over a family, which is what a `q`-query union bound sums and what a
CR18 multigame carries), and they pull back along prefix-monotone maps on
histories (`comap`), which is how a condition on a sub-history becomes a
condition on the whole.

The thesis's own `{0,1}`-predicate form is kept as a **certified view**:
`boolEquiv : MonotoneCondition X ≃ BoolCondition X` is an equivalence, not an
analogy, and `toPred`/`ofPred` with their round trips are its two halves.

Mathlib's `UpperSet` is not used: it needs a `Preorder (List X)` instance, and
the prefix order is *not* one in mathlib — `Mathlib/Data/List/Infix.lean:184`
registers only `IsPartialOrder (List α) (· <+: ·)`, a relation-level instance,
while the `LE (List α)` slot is taken by the lexicographic order
(`Mathlib/Data/List/Lex.lean:147`).  Registering a prefix `Preorder` on
`List X` would collide there, so the carrier is the subtype
`{s : Set (List X) // IsPrefixUpperSet s}` — FLAGGED as the fallback rendering
(PHI-SPEC R10 refinement).  Its order is *inclusion* (`Subtype.partialOrder`
over `Set`), so `⊔` is the union; mathlib's `UpperSet` reverses the inclusion
order, and this file deliberately does not.

## The game: the pair is primitive

**Definition 2.20**: "A deterministic discrete `(𝒳,𝒴)`-game (or an
`(𝒳,𝒴)`-DDG) is a pair `(s, A)`, denoted by `s^A`."  **Definition 2.22**: "A
probabilistic discrete `(𝒳,𝒴)`-game (or an `(𝒳,𝒴)`-PDG) is a distribution over
`(𝒳,𝒴)`-DDG."

So `DDG X Y = DDS X Y × MonotoneCondition X` and `PDG X Y = Distribution (DDG
X Y)`: the probabilistic game is a *joint* law over (system, condition) pairs.
That is what makes Remark 2.24's adjoining expressible — the condition sampled
with a deterministic system may depend on that system, which is the content of
`p^A_{Aᵢ|XⁱYⁱAᵢ₋₁}` conditioning on the outputs.  A law over pairs is not a
pair of laws, and it is not a law of systems at a paired output alphabet.

The `(𝒳, 𝒴 × {0,1})` presentation (Maurer13b Definition 9; the form CR18 and
the quarry take as primitive) is a **derived view**, built here as
`toBitSystem` with an inverse on monotone-bit systems and both round-trip
equalities.

## Remark 2.23 holds by construction

**Remark 2.23**: "In general, an environment does not observe the monotone
condition.  This matters in the probabilistic case, where being able to
observe the MC may reveal information about the system's internal state that
would not be observable just from the system's outputs."

An environment here is `System.DDE.Total Y X = List (Option Y) → Option X`
(CR18 Definitions 3.6/3.7, the tree's total presentation).  Its argument type
mentions the output alphabet only: no term of the environment's type can read
a condition, and Definition 2.25's supremum quantifies over exactly that type.
Blindness is not a hypothesis, a converter, or a predicate on environments —
it is the type of the environment.  §6 proves the corresponding statement for
the *derived* bit view, where the bit is a real output and blindness has
content: the environment meets the bit view through
`System.relabel id Prod.fst`, an existing generator of the trivial-converter
monoid, and its entire interaction record erases to the plain one.

## Definition 2.21 on the total presentation (the one carrier delta)

**Definition 2.21**: "The transcript of an `(𝒳,𝒴)`-DDG `s^A` under
`(𝒴,𝒳)`-DDE `e` … is the pair `(t, A(t'))`, where `t = tr(s,e)` … and
`t' ∈ 𝒳*` is `t` projected to the inputs."

The thesis interacts through *compatible* environments, which never query
outside the domain, so `t` projected to the inputs is the input history the
system processed.  This carrier interacts through the `⊥`-completion (Rulings
R1/R2): a query outside the domain is answered `none` and deleted from the
system-side history (CR18 Definition 3.3).  The condition is therefore
evaluated at `answeredQueries t = keptPrefix s (t↓ₓ)`
(`System.DDE.Total.answeredQueries_transcript`) — the input history the system
actually processed, which is the thesis's `t'` whenever no query is refused.
`keptPrefix` is itself prefix-monotone
(`MonotoneCondition.prefixMonotoneMap_keptPrefix`), so this is a `comap` of
the condition and not an ad-hoc evaluation rule.  The quarry makes
the same reading (`Q:RandomSystems/GameWinnability.lean:31`).
-/

namespace RandomSystems

namespace System

noncomputable section

open Classical

universe u u' v

variable {X : Type u} {X' : Type u'} {Y : Type v}

/-! ## Definition 2.20: monotone conditions -/

/-- Lanzenberger **Definition 2.20**, footnote 7, as a closure property of a
set of histories: "if `A(t) = 1` then `A(t|t') = 1` for any extension `t|t'`
of `t`" — the set of satisfying histories is upward closed in the prefix
order. -/
def IsPrefixUpperSet (s : Set (List X)) : Prop :=
  ∀ ⦃t t' : List X⦄, t <+: t' → t ∈ s → t' ∈ s

/-- Lanzenberger **Definition 2.20**: "A *monotone condition* (or MC) for an
`(𝒳,𝒴)`-DDS `s` is a monotone predicate `A : 𝒳* → {0,1}`."

Rendered as the upper set of histories at which the condition holds.  The
condition is an *input* object — it reads the query history and nothing else —
and it is attached to a system only by Definition 2.20's pair, never bundled
into it.  See the module docstring for why this is the subtype and not
mathlib's `UpperSet` (FLAGGED fallback). -/
abbrev MonotoneCondition (X : Type u) : Type u :=
  {s : Set (List X) // IsPrefixUpperSet s}

/-- Conditions are closed under union: the disjunction of two bad events is a
bad event. -/
theorem IsPrefixUpperSet.union {s t : Set (List X)} (hs : IsPrefixUpperSet s)
    (ht : IsPrefixUpperSet t) : IsPrefixUpperSet (s ∪ t) := by
  rintro l l' hpre (h | h)
  · exact Or.inl (hs hpre h)
  · exact Or.inr (ht hpre h)

/-- Conditions are closed under intersection. -/
theorem IsPrefixUpperSet.inter {s t : Set (List X)} (hs : IsPrefixUpperSet s)
    (ht : IsPrefixUpperSet t) : IsPrefixUpperSet (s ∩ t) :=
  fun _ _ hpre h => ⟨hs hpre h.1, ht hpre h.2⟩

/-- Conditions are closed under arbitrary unions: the bad event "one of these
happened", over a family of any size. -/
theorem IsPrefixUpperSet.sUnion {S : Set (Set (List X))}
    (hS : ∀ s ∈ S, IsPrefixUpperSet s) : IsPrefixUpperSet (⋃₀ S) := by
  rintro t t' hpre ⟨s, hs, hts⟩
  exact ⟨s, hs, hS s hs hpre hts⟩

/-- Conditions are closed under arbitrary intersections. -/
theorem IsPrefixUpperSet.sInter {S : Set (Set (List X))}
    (hS : ∀ s ∈ S, IsPrefixUpperSet s) : IsPrefixUpperSet (⋂₀ S) :=
  fun _ _ hpre h s hs => hS s hs hpre (h s hs)

namespace MonotoneCondition

theorem upward (A : MonotoneCondition X) {t t' : List X} (h : t <+: t')
    (ht : t ∈ A.1) : t' ∈ A.1 :=
  A.2 h ht

/-! ### The complete lattice of conditions

Conditions are closed under arbitrary unions and intersections, so they
inherit `Set`'s order — **inclusion** — as a complete lattice.  The join is
the union: the disjunction of bad events, which is the operation every union
bound and every bad-event decomposition uses, and the indexed form `⨆ i, A i`
is the union over a family — a `q`-query union bound, or the family of
conditions a CR18 multigame carries. -/

instance : Lattice (MonotoneCondition X) :=
  Subtype.lattice (fun ⦃_ _⦄ hs ht => hs.union ht) fun ⦃_ _⦄ hs ht => hs.inter ht

@[simp] theorem coe_sup (A B : MonotoneCondition X) :
    (A ⊔ B).1 = A.1 ∪ B.1 := rfl

@[simp] theorem coe_inf (A B : MonotoneCondition X) :
    (A ⊓ B).1 = A.1 ∩ B.1 := rfl

/-- The never-won condition — the thesis's unnamed always-losing system `V` in
the alternative proof of Theorem 2.37 (printed p. 26), which the quarry coins
`zeroMBO` (`Q:RandomSystems/GameWinnability.lean:356`).  Here it is simply the
bottom of the lattice. -/
instance : OrderBot (MonotoneCondition X) where
  bot := ⟨∅, fun _ _ _ h => absurd h (Set.notMem_empty _)⟩
  bot_le _ := Set.empty_subset _

/-- The condition already satisfied at the empty history: won before the
interaction begins.  Definition 2.20 admits it — `A` is a predicate on all of
`𝒳*` and monotonicity permits `A([]) = 1` — and §4 records that the bit-output
view cannot express it. -/
instance : OrderTop (MonotoneCondition X) where
  top := ⟨Set.univ, fun _ _ _ _ => trivial⟩
  le_top _ := Set.subset_univ _

@[simp] theorem coe_bot : (⊥ : MonotoneCondition X).1 = (∅ : Set (List X)) := rfl

@[simp] theorem coe_top :
    (⊤ : MonotoneCondition X).1 = (Set.univ : Set (List X)) := rfl

/-- The complete lattice: arbitrary joins are unions and arbitrary meets are
intersections, extending the finite operations above rather than replacing
them (`coe_sup`, `coe_inf`, `coe_bot`, `coe_top` are still `rfl`). -/
instance : CompleteLattice (MonotoneCondition X) where
  __ := (inferInstance : Lattice (MonotoneCondition X))
  __ := (inferInstance : OrderBot (MonotoneCondition X))
  __ := (inferInstance : OrderTop (MonotoneCondition X))
  sSup S := ⟨⋃₀ (Subtype.val '' S),
    IsPrefixUpperSet.sUnion (by rintro s ⟨A, -, rfl⟩; exact A.2)⟩
  sInf S := ⟨⋂₀ (Subtype.val '' S),
    IsPrefixUpperSet.sInter (by rintro s ⟨A, -, rfl⟩; exact A.2)⟩
  isLUB_sSup S := by
    constructor
    · intro A hA l hl
      exact ⟨A.1, ⟨A, hA, rfl⟩, hl⟩
    · rintro B hB l ⟨s, ⟨A, hA, rfl⟩, hl⟩
      exact hB hA hl
  isGLB_sInf S := by
    constructor
    · intro A hA l hl
      exact hl A.1 ⟨A, hA, rfl⟩
    · rintro B hB l hl s ⟨A, hA, rfl⟩
      exact hB hA hl

@[simp] theorem mem_sSup {S : Set (MonotoneCondition X)} {l : List X} :
    l ∈ (sSup S).1 ↔ ∃ A ∈ S, l ∈ A.1 := by
  constructor
  · rintro ⟨s, ⟨A, hA, rfl⟩, hl⟩
    exact ⟨A, hA, hl⟩
  · rintro ⟨A, hA, hl⟩
    exact ⟨A.1, ⟨A, hA, rfl⟩, hl⟩

@[simp] theorem mem_sInf {S : Set (MonotoneCondition X)} {l : List X} :
    l ∈ (sInf S).1 ↔ ∀ A ∈ S, l ∈ A.1 := by
  constructor
  · exact fun hl A hA => hl A.1 ⟨A, hA, rfl⟩
  · rintro hl s ⟨A, hA, rfl⟩
    exact hl A hA

/-- The bad-event union over a family, which is what a union bound sums. -/
@[simp] theorem mem_iSup {ι : Sort*} {A : ι → MonotoneCondition X}
    {l : List X} : l ∈ (⨆ i, A i).1 ↔ ∃ i, l ∈ (A i).1 := by
  rw [iSup, mem_sSup]
  simp

@[simp] theorem mem_iInf {ι : Sort*} {A : ι → MonotoneCondition X}
    {l : List X} : l ∈ (⨅ i, A i).1 ↔ ∀ i, l ∈ (A i).1 := by
  rw [iInf, mem_sInf]
  simp

/-! ### The thesis's `{0,1}`-predicate view, certified -/

/-- Lanzenberger **Definition 2.20**'s monotonicity clause on a `{0,1}`-valued
predicate: "if `A(t) = 1` then `A(t|t') = 1` for any extension `t|t'` of
`t`". -/
def PrefixMonotone (A : List X → Bool) : Prop :=
  ∀ ⦃t t' : List X⦄, t <+: t' → A t = true → A t' = true

/-- Lanzenberger **Definition 2.20** verbatim: the monotone predicate
`A : 𝒳* → {0,1}`.  `boolEquiv` certifies that this is the same object as the
upper-set carrier. -/
abbrev BoolCondition (X : Type u) : Type u :=
  {A : List X → Bool // PrefixMonotone A}

/-- The `{0,1}`-predicate view of a condition (classical: membership in an
arbitrary upper set is not decidable). -/
def toPred (A : MonotoneCondition X) : List X → Bool :=
  fun l => decide (l ∈ A.1)

@[simp] theorem toPred_eq_true {A : MonotoneCondition X} {l : List X} :
    toPred A l = true ↔ l ∈ A.1 :=
  decide_eq_true_iff

/-- The condition presented by a monotone `{0,1}`-predicate. -/
def ofPred (A : List X → Bool) (hA : PrefixMonotone A) : MonotoneCondition X :=
  ⟨{l | A l = true}, fun _ _ hpre h => hA hpre h⟩

@[simp] theorem mem_ofPred {A : List X → Bool} {hA : PrefixMonotone A}
    {l : List X} : l ∈ (ofPred A hA).1 ↔ A l = true :=
  Iff.rfl

theorem prefixMonotone_toPred (A : MonotoneCondition X) :
    PrefixMonotone (toPred A) := by
  intro t t' hpre ht
  rw [toPred_eq_true] at ht ⊢
  exact A.upward hpre ht

/-- Round trip, one way: reading a condition as a predicate and back is the
identity. -/
@[simp] theorem ofPred_toPred (A : MonotoneCondition X) :
    ofPred (toPred A) (prefixMonotone_toPred A) = A := by
  refine Subtype.ext (Set.ext fun l => ?_)
  simp

/-- Round trip, the other way: presenting a monotone predicate as a condition
and reading it back is the identity. -/
@[simp] theorem toPred_ofPred (A : List X → Bool) (hA : PrefixMonotone A) :
    toPred (ofPred A hA) = A := by
  funext l
  by_cases h : A l = true <;> simp [toPred, ofPred, h]

/-- **The certified thesis equivalence.**  Definition 2.20's monotone
predicate `A : 𝒳* → {0,1}` and the upper set of histories satisfying it are
the same object; the upper set is the carrier, the predicate is the view. -/
def boolEquiv : MonotoneCondition X ≃ BoolCondition X where
  toFun A := ⟨toPred A, prefixMonotone_toPred A⟩
  invFun A := ofPred A.1 A.2
  left_inv A := ofPred_toPred A
  right_inv A := Subtype.ext (toPred_ofPred A.1 A.2)

/-! ### Pulling a condition back along a history map

A condition on one history alphabet becomes a condition on another by
substitution, provided the substitution preserves the prefix order.  This is
the composability the upper-set carrier was chosen for: the two maps the tree
already uses to relate histories — the interface projection `historyAt` and
CR18's deletion pass `keptPrefix` — both qualify. -/

/-- A history map preserves the prefix order. -/
def PrefixMonotoneMap (f : List X → List X') : Prop :=
  ∀ ⦃t t' : List X⦄, t <+: t' → f t <+: f t'

/-- Substitution of histories, pulling a condition back.  `comap f hf A` is
"`A` holds of the substituted history". -/
def comap (f : List X → List X') (hf : PrefixMonotoneMap f)
    (A : MonotoneCondition X') : MonotoneCondition X :=
  ⟨f ⁻¹' A.1, fun _ _ hpre h => A.upward (hf hpre) h⟩

@[simp] theorem mem_comap {f : List X → List X'} {hf : PrefixMonotoneMap f}
    {A : MonotoneCondition X'} {l : List X} :
    l ∈ (comap f hf A).1 ↔ f l ∈ A.1 :=
  Iff.rfl

/-- Pulling back is a lattice homomorphism: it commutes with the bad-event
union … -/
@[simp] theorem comap_sup (f : List X → List X') (hf : PrefixMonotoneMap f)
    (A B : MonotoneCondition X') :
    comap f hf (A ⊔ B) = comap f hf A ⊔ comap f hf B :=
  Subtype.ext (Set.preimage_union)

/-- … and with the intersection. -/
@[simp] theorem comap_inf (f : List X → List X') (hf : PrefixMonotoneMap f)
    (A B : MonotoneCondition X') :
    comap f hf (A ⊓ B) = comap f hf A ⊓ comap f hf B :=
  Subtype.ext (Set.preimage_inter)

theorem comap_mono (f : List X → List X') (hf : PrefixMonotoneMap f)
    {A B : MonotoneCondition X'} (hAB : A ≤ B) :
    comap f hf A ≤ comap f hf B :=
  fun _ h => hAB h

/-- **Receipt**: the interface projection qualifies.  A component owning the
queries in `c` sees `historyAt c`, and `historyAt_append` makes it
prefix-monotone, so any condition on a component's own history is a condition
on the whole history. -/
theorem prefixMonotoneMap_historyAt (c : Set X) :
    PrefixMonotoneMap (historyAt c) := by
  rintro t _ ⟨w, rfl⟩
  exact ⟨historyAt c w, (historyAt_append c t w).symm⟩

/-- **Receipt**: CR18 Definition 3.3's deletion pass qualifies
(`keptPrefix_mono`).  This is the map Definition 2.21 evaluates the condition
along on this carrier (module docstring), so that evaluation is a `comap`. -/
theorem prefixMonotoneMap_keptPrefix (S : DDS X Y) :
    PrefixMonotoneMap (keptPrefix S) :=
  fun _ _ hpre => keptPrefix_mono S hpre

end MonotoneCondition

/-! ## Definition 2.20: deterministic games -/

/-- Lanzenberger **Definition 2.20**: "A *deterministic discrete
`(𝒳,𝒴)`-game* (or an `(𝒳,𝒴)`-DDG) is a pair `(s, A)`, denoted by `s^A`."

The pair is the primitive object (PHI-SPEC R10); the `(𝒳, 𝒴 × {0,1})` form is
the derived view of §4. -/
abbrev DDG (X : Type u) (Y : Type v) : Type (max u v) :=
  DDS X Y × MonotoneCondition X

/-! ## Definition 2.21: the transcript of a game -/

/-- Lanzenberger **Definition 2.21**: "The transcript of an `(𝒳,𝒴)`-DDG `s^A`
under `(𝒴,𝒳)`-DDE `e`, denoted by `tr(s^A, e)`, is the pair `(t, A(t'))`,
where `t = tr(s,e)` is the transcript of `s` under `e` … and `t' ∈ 𝒳*` is `t`
projected to the inputs."

Stated over the tree's total presentation at interaction length `n`: `t` is
`System.DDE.Total.transcript`, and `t'` is `answeredQueries t`, the input
history the system processed (module docstring).  The second component is the
thesis's `{0,1}` value, i.e. the condition read through `toPred`. -/
def gameTranscript (g : DDG X Y) (e : DDE.Total Y X) (n : ℕ) :
    List (X × Option Y) × Bool :=
  (DDE.Total.transcript g.1 e n,
    MonotoneCondition.toPred g.2 (answeredQueries (DDE.Total.transcript g.1 e n)))

@[simp] theorem gameTranscript_fst (g : DDG X Y) (e : DDE.Total Y X) (n : ℕ) :
    (gameTranscript g e n).1 = DDE.Total.transcript g.1 e n := rfl

/-- Lanzenberger **Definition 2.25**'s winning transcripts `𝒯_w`: "the
transcripts ending with `(·, 1)`" — the Definition 2.21 pair whose second
component is `1`.  A winner wins the game when the condition occurs during the
interaction (printed p. 17). -/
def Won (g : DDG X Y) (e : DDE.Total Y X) (n : ℕ) : Prop :=
  answeredQueries (DDE.Total.transcript g.1 e n) ∈ g.2.1

theorem won_iff_gameTranscript (g : DDG X Y) (e : DDE.Total Y X) (n : ℕ) :
    Won g e n ↔ (gameTranscript g e n).2 = true :=
  MonotoneCondition.toPred_eq_true.symm

/-- Winning is monotone along the interaction: Definition 2.20's upward
closure, transported by `DDE.Total.answeredQueries_prefix`.  This is why
Definition 2.25's "ends with `(·,1)`" and the `∃`-form "some prefix of the
interaction satisfies the condition" describe the same event
(`exists_won_iff`) — the reading the quarry had to choose by hand
(`Q:RandomSystems/GameWinnability.lean:105`). -/
theorem Won.mono {g : DDG X Y} {e : DDE.Total Y X} {m n : ℕ} (hmn : m ≤ n)
    (h : Won g e m) : Won g e n :=
  g.2.upward (DDE.Total.answeredQueries_prefix g.1 e hmn) h

theorem exists_won_iff (g : DDG X Y) (e : DDE.Total Y X) (n : ℕ) :
    (∃ m ≤ n, Won g e m) ↔ Won g e n :=
  ⟨fun ⟨_, hmn, h⟩ => h.mono hmn, fun h => ⟨n, le_rfl, h⟩⟩

@[simp] theorem not_won_bot (s : DDS X Y) (e : DDE.Total Y X) (n : ℕ) :
    ¬ Won (s, ⊥) e n :=
  Set.notMem_empty _

@[simp] theorem won_top (s : DDS X Y) (e : DDE.Total Y X) (n : ℕ) :
    Won (s, ⊤) e n :=
  trivial

/-! ## The derived bit-output view (Maurer13b Definition 9)

Maurer13b Definition 9 — the form CR18 and the quarry take as primitive
(`Q:RandomSystems/PDS.lean:3045`) — presents a game as a system at the output
alphabet `𝒴 × {0,1}` whose bit is monotone.  Here that is a *view* of
Definition 2.20's pair, with an inverse and both round-trip equalities.

The view is faithful exactly on `DomainSupported` conditions, and the round
trip shows why: a bit is shown only where the system answers, so a condition
already satisfied at the empty history — legitimate under Definition 2.20, and
the lattice's `⊤` — has no bit to be read off.  That is the exact
expressiveness gap between the pair and the bit form. -/

/-- Maurer13b Definition 9, derived from Definition 2.20's pair: the same
system, answering `(y, A(l))` where it answered `y`.  Domains are untouched. -/
def toBitSystem (g : DDG X Y) : DDS X (Y × Bool) :=
  ⟨fun l => (g.1.1 l).map fun y => (y, MonotoneCondition.toPred g.2 l),
    ⟨fun h => g.1.2.1 h, fun hpre hne hdom => g.1.2.2 hpre hne hdom⟩⟩

@[simp] theorem dom_toBitSystem (g : DDG X Y) : dom (toBitSystem g) = dom g.1 :=
  rfl

@[simp] theorem output_toBitSystem (g : DDG X Y) (l : List X)
    (h : l ∈ dom (toBitSystem g)) :
    output (toBitSystem g) l h =
      (output g.1 l h, MonotoneCondition.toPred g.2 l) :=
  rfl

@[simp] theorem keptPrefix_toBitSystem (g : DDG X Y) :
    keptPrefix (toBitSystem g) = keptPrefix g.1 :=
  rfl

/-- Maurer13b Definition 9's monotonicity clause on one deterministic system:
the bit, once shown as `1`, is shown as `1` on every extension the system
answers.  (The quarry imposes the same clause support-wise and calls it
`MonotoneMBO`, `Q:RandomSystems/PDS.lean:3101`.) -/
def MonotoneBit (t : DDS X (Y × Bool)) : Prop :=
  ∀ ⦃l₁ l₂ : List X⦄, l₁ <+: l₂ → ∀ (h₁ : l₁ ∈ dom t) (h₂ : l₂ ∈ dom t),
    (output t l₁ h₁).2 = true → (output t l₂ h₂).2 = true

/-- The bit view of a Definition 2.20 game has a monotone bit: Definition
2.20's upward closure, read at the histories the system answers. -/
theorem monotoneBit_toBitSystem (g : DDG X Y) : MonotoneBit (toBitSystem g) := by
  intro l₁ l₂ hpre _ _ hbit
  rw [output_toBitSystem, MonotoneCondition.toPred_eq_true] at hbit ⊢
  exact g.2.upward hpre hbit

/-- The inverse of the bit view: the system is the bit-hiding relabelling
(`relabel id Prod.fst`, an existing generator of the trivial-converter
monoid), and the condition is "some answered prefix has already shown the bit
`1`". -/
def ofBitSystem (t : DDS X (Y × Bool)) : DDG X Y :=
  (relabel id Prod.fst t,
    ⟨{l | ∃ l' : List X, l' <+: l ∧ ∃ h : l' ∈ dom t, (output t l' h).2 = true},
      by
        rintro l₁ l₂ hpre ⟨l', hl', hmem⟩
        exact ⟨l', hl'.trans hpre, hmem⟩⟩)

@[simp] theorem ofBitSystem_fst (t : DDS X (Y × Bool)) :
    (ofBitSystem t).1 = relabel id Prod.fst t := rfl

@[simp] theorem mem_ofBitSystem_snd (t : DDS X (Y × Bool)) (l : List X) :
    l ∈ (ofBitSystem t).2.1 ↔
      ∃ l' : List X, l' <+: l ∧ ∃ h : l' ∈ dom t, (output t l' h).2 = true :=
  Iff.rfl

@[simp] theorem dom_relabel_fst (t : DDS X (Y × Bool)) :
    dom (relabel id Prod.fst t) = dom t := by
  ext l
  rw [mem_dom_relabel, List.map_id]

theorem raw_relabel_fst (t : DDS X (Y × Bool)) (l : List X) :
    (relabel id Prod.fst t).1 l = (t.1 l).map Prod.fst := by
  show (t.1 (l.map id)).map Prod.fst = _
  rw [List.map_id]

/-- The bit-hiding relabelling undoes the bit view on the nose: this is the
deterministic half of the forgetting law of §5, through an existing generator
of the converter monoid rather than a new primitive. -/
@[simp] theorem relabel_fst_toBitSystem (g : DDG X Y) :
    relabel id Prod.fst (toBitSystem g) = g.1 := by
  refine Subtype.ext (funext fun l => ?_)
  rw [raw_relabel_fst]
  show ((g.1.1 l).map fun y => (y, MonotoneCondition.toPred g.2 l)).map Prod.fst
    = g.1.1 l
  rw [Part.map_map]
  exact Part.ext' Iff.rfl fun _ _ => rfl

/-- COINAGE, flagged: the condition is *supported by the domain* when every
history satisfying it has a prefix that the system answers and that already
satisfies it.  This is exactly the class on which the bit view is faithful
(`ofBitSystem_toBitSystem`), and `domainSupported_ofBitSystem` shows the
reconstruction always lands in it. -/
def DomainSupported (g : DDG X Y) : Prop :=
  ∀ l ∈ g.2.1, ∃ l' : List X, l' <+: l ∧ l' ∈ dom g.1 ∧ l' ∈ g.2.1

/-- What the bit view cannot express: a domain-supported condition is false at
the empty history, because the empty history is in no DDS domain (Definition
2.9).  A Definition 2.20 game whose condition holds at `[]` — `⊤`, say:
already won before the interaction starts — is outside the image of the bit
view. -/
theorem not_mem_nil_of_domainSupported {g : DDG X Y} (h : DomainSupported g) :
    [] ∉ g.2.1 := by
  intro hnil
  obtain ⟨l', hl', hmem, -⟩ := h [] hnil
  exact empty_not_mem g.1 (by rwa [List.prefix_nil.mp hl'] at hmem)

theorem domainSupported_ofBitSystem (t : DDS X (Y × Bool)) :
    DomainSupported (ofBitSystem t) := by
  intro l hl
  obtain ⟨l', hl', hmem, hbit⟩ := (mem_ofBitSystem_snd t l).mp hl
  exact ⟨l', hl', by rw [ofBitSystem_fst, dom_relabel_fst]; exact hmem,
    (mem_ofBitSystem_snd t l').mpr ⟨l', List.prefix_rfl, hmem, hbit⟩⟩

/-- **Round trip, one way**: on a monotone-bit system the view is inverted
exactly.  Monotonicity is what makes "some answered prefix showed `1`" the bit
shown here. -/
theorem toBitSystem_ofBitSystem {t : DDS X (Y × Bool)} (ht : MonotoneBit t) :
    toBitSystem (ofBitSystem t) = t := by
  refine Subtype.ext (funext fun l => ?_)
  show ((ofBitSystem t).1.1 l).map
      (fun y => (y, MonotoneCondition.toPred (ofBitSystem t).2 l)) = t.1 l
  rw [ofBitSystem_fst, raw_relabel_fst, Part.map_map]
  refine Part.ext' Iff.rfl fun _ h₂ => ?_
  have hmem : l ∈ dom t := h₂
  have hbit : l ∈ (ofBitSystem t).2.1 ↔ ((t.1 l).get h₂).2 = true :=
    ⟨fun ⟨_, hl', hl'mem, hl'bit⟩ => ht hl' hl'mem hmem hl'bit,
      fun h => ⟨l, List.prefix_rfl, hmem, h⟩⟩
  show ((t.1 l).get h₂ |>.1, MonotoneCondition.toPred (ofBitSystem t).2 l)
    = (t.1 l).get h₂
  rcases hcase : ((t.1 l).get h₂).2 with _ | _
  · have : MonotoneCondition.toPred (ofBitSystem t).2 l = false := by
      simp only [MonotoneCondition.toPred, decide_eq_false_iff_not]
      exact fun h => by simp [hbit.mp h] at hcase
    rw [this, ← hcase]
  · have : MonotoneCondition.toPred (ofBitSystem t).2 l = true := by
      rw [MonotoneCondition.toPred_eq_true]
      exact hbit.mpr hcase
    rw [this, ← hcase]

/-- **Round trip, the other way**: on a domain-supported condition the pair is
recovered exactly.  `DomainSupported` is not decoration — without it the
reconstructed condition is the upward closure of the bits actually shown,
which differs from the original precisely off the domain. -/
theorem ofBitSystem_toBitSystem {g : DDG X Y} (hg : DomainSupported g) :
    ofBitSystem (toBitSystem g) = g := by
  refine Prod.ext (relabel_fst_toBitSystem g) (Subtype.ext (Set.ext fun l => ?_))
  rw [mem_ofBitSystem_snd]
  refine ⟨fun ⟨l', hl', hl'mem, hl'bit⟩ => g.2.upward hl' ?_, fun h => ?_⟩
  · rw [output_toBitSystem, MonotoneCondition.toPred_eq_true] at hl'bit
    exact hl'bit
  · obtain ⟨l', hl', hl'mem, hl'bit⟩ := hg l h
    refine ⟨l', hl', hl'mem, ?_⟩
    rw [output_toBitSystem, MonotoneCondition.toPred_eq_true]
    exact hl'bit

/-! ## Remark 2.23 for the derived view: the bit is hidden by relabelling

On Definition 2.20's pair, Remark 2.23 is the type of the environment (module
docstring).  On the *derived* bit view the bit is a real output, so blindness
has content, and CR18 Definition 4.20's rendering is the right one: the
environment meets the system through a trivial converter that blocks what it
may not see.  Here that converter is `relabel id Prod.fst` — an existing
generator of the trivial-converter monoid with its own receipts
(`answer_relabel`, `exists_absorb_relabel`) — and no `IsBlind` predicate on
environments is introduced.

The two statements below are the honest content:

* `mapOutputs_transcript_toBitSystem` — the environment's entire record of an
  interaction with the bit view erases to its record of the interaction with
  the plain system.  Nothing the bit does reaches the environment.
* `winningMass_eq_mass_lastBit_toBitLaw` — Definition 2.25's winning
  probability is unchanged when it is read off the bit view through that
  converter, on the conditions the bit view can express. -/

/-- The environment for a `Y'`-system induced by an environment for the
`Y`-system it relabels to: the environment side of `relabel id g`.  At
`g = Prod.fst` it is the environment of Remark 2.23 for the bit view — it
receives the answers with the bit erased. -/
def DDE.Total.relabelOut {Y' : Type v} (g : Y' → Y) (e : DDE.Total Y X) :
    DDE.Total Y' X :=
  fun ys => e (ys.map (Option.map g))

/-- The record erasure matching `DDE.Total.relabelOut`: translate every answer,
keeping the refusals refusals. -/
def mapOutputs {Y' : Type v} (g : Y' → Y) (t : List (X × Option Y')) :
    List (X × Option Y) :=
  t.map fun p => (p.1, p.2.map g)

@[simp] theorem mapOutputs_nil {Y' : Type v} (g : Y' → Y) :
    mapOutputs (X := X) g [] = [] := rfl

@[simp] theorem mapOutputs_append {Y' : Type v} (g : Y' → Y)
    (t : List (X × Option Y')) (p : X × Option Y') :
    mapOutputs g (t ++ [p]) = mapOutputs g t ++ [(p.1, p.2.map g)] := by
  simp [mapOutputs]

@[simp] theorem transcriptOutputs_mapOutputs {Y' : Type v} (g : Y' → Y)
    (t : List (X × Option Y')) :
    (mapOutputs g t)↓ᵧ = t↓ᵧ.map (Option.map g) := by
  simp [mapOutputs, transcriptOutputs, List.map_map, Function.comp_def]

@[simp] theorem transcriptInputs_mapOutputs {Y' : Type v} (g : Y' → Y)
    (t : List (X × Option Y')) : (mapOutputs g t)↓ₓ = t↓ₓ := by
  simp [mapOutputs, transcriptInputs, List.map_map, Function.comp_def]

@[simp] theorem answeredQueries_mapOutputs {Y' : Type v} (g : Y' → Y)
    (t : List (X × Option Y')) :
    answeredQueries (mapOutputs g t) = answeredQueries t := by
  induction t with
  | nil => rfl
  | cons p t ih => rcases p with ⟨_, _ | _⟩ <;> simp [mapOutputs, answeredQueries] at ih ⊢ <;> simp [ih]

/-- **A relabelling is absorbed by the environment, concretely.**  Interacting
with `relabel id g S` is interacting with `S` through the induced environment
and erasing the record.  (`exists_absorb_relabel` states the same absorption
existentially; this is the explicit witness, which is what a statement about
*what the environment sees* needs.) -/
theorem transcript_relabel_id {Y' : Type v} (g : Y' → Y) (S : DDS X Y')
    (e : DDE.Total Y X) (n : ℕ) :
    DDE.Total.transcript (relabel id g S) e n =
      mapOutputs g (DDE.Total.transcript S (DDE.Total.relabelOut g e) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hstep : e (DDE.Total.transcript (relabel id g S) e n)↓ᵧ =
          DDE.Total.relabelOut g e
            (DDE.Total.transcript S (DDE.Total.relabelOut g e) n)↓ᵧ := by
        rw [ih, transcriptOutputs_mapOutputs]
        rfl
      rcases hx : DDE.Total.relabelOut g e
          (DDE.Total.transcript S (DDE.Total.relabelOut g e) n)↓ᵧ with _ | x
      · rw [DDE.Total.transcript_succ_of_stop _ _ (hstep.trans hx),
          DDE.Total.transcript_succ_of_stop _ _ hx]
        exact ih
      · rw [DDE.Total.transcript_succ_of_query _ _ (hstep.trans hx),
          DDE.Total.transcript_succ_of_query _ _ hx, mapOutputs_append, ih,
          transcriptInputs_mapOutputs, answer_relabel, List.map_id]
        rfl

/-- **Remark 2.23 for the bit view.**  The environment's whole record of an
interaction with the bit view, met through the bit-erasing converter, is its
record of the interaction with the plain system.  The bit reaches nothing. -/
theorem mapOutputs_transcript_toBitSystem (g : DDG X Y) (e : DDE.Total Y X)
    (n : ℕ) :
    mapOutputs Prod.fst (DDE.Total.transcript (toBitSystem g)
        (DDE.Total.relabelOut Prod.fst e) n) =
      DDE.Total.transcript g.1 e n := by
  rw [← transcript_relabel_id, relabel_fst_toBitSystem]

@[simp] theorem answeredQueries_transcript_toBitSystem (g : DDG X Y)
    (e : DDE.Total Y X) (n : ℕ) :
    answeredQueries (DDE.Total.transcript (toBitSystem g)
        (DDE.Total.relabelOut Prod.fst e) n) =
      answeredQueries (DDE.Total.transcript g.1 e n) := by
  rw [← mapOutputs_transcript_toBitSystem g e n, answeredQueries_mapOutputs]

/-- Definition 2.25's test on the derived view, reading only the record: the
last bit the system showed.  `none` when the system has answered nothing. -/
def lastBit (t : List (X × Option (Y × Bool))) : Option Bool :=
  (answeredEntries t).getLast?.map fun p => p.2.2

@[simp] theorem lastBit_nil : lastBit ([] : List (X × Option (Y × Bool))) = none :=
  rfl

/-- The bit view answers where the system answers, and shows the condition at
the history the system processed. -/
theorem answer_toBitSystem (g : DDG X Y) (l : List X) (x : X) :
    answer (toBitSystem g) l x =
      (answer g.1 l x).map fun y =>
        (y, MonotoneCondition.toPred g.2 (keptPrefix g.1 l ++ [x])) := by
  rw [answer_eq, answer_eq]
  by_cases h : keptPrefix g.1 l ++ [x] ∈ dom g.1
  · rw [dif_pos (show keptPrefix (toBitSystem g) l ++ [x] ∈ dom (toBitSystem g)
      from h), dif_pos h]
    rfl
  · rw [dif_neg (show ¬ keptPrefix (toBitSystem g) l ++ [x] ∈ dom (toBitSystem g)
      from h), dif_neg h]
    rfl

/-- **The winning test transported to the bit view.**  The last bit shown in
the blinded interaction with the bit view is the condition evaluated at the
history the system processed — and `none` exactly when the system has answered
nothing.  The `none` case is where Definition 2.20's `A([]) = 1` lives: the
bit view has no place to show it, which is `DomainSupported` again. -/
theorem lastBit_transcript_toBitSystem (g : DDG X Y) (e : DDE.Total Y X)
    (n : ℕ) :
    lastBit (DDE.Total.transcript (toBitSystem g)
        (DDE.Total.relabelOut Prod.fst e) n) =
      if answeredQueries (DDE.Total.transcript g.1 e n) = [] then none
      else some (MonotoneCondition.toPred g.2
        (answeredQueries (DDE.Total.transcript g.1 e n))) := by
  induction n with
  | zero => simp [lastBit, DDE.Total.transcript, answeredQueries, answeredEntries]
  | succ n ih =>
      have hstep : DDE.Total.relabelOut Prod.fst e
          (DDE.Total.transcript (toBitSystem g)
            (DDE.Total.relabelOut Prod.fst e) n)↓ᵧ =
          e (DDE.Total.transcript g.1 e n)↓ᵧ := by
        rw [← mapOutputs_transcript_toBitSystem g e n,
          transcriptOutputs_mapOutputs]
        rfl
      have hinputs : (DDE.Total.transcript (toBitSystem g)
          (DDE.Total.relabelOut Prod.fst e) n)↓ₓ =
          (DDE.Total.transcript g.1 e n)↓ₓ := by
        rw [← mapOutputs_transcript_toBitSystem g e n,
          transcriptInputs_mapOutputs]
      have hkept : keptPrefix g.1 (DDE.Total.transcript g.1 e n)↓ₓ =
          answeredQueries (DDE.Total.transcript g.1 e n) :=
        (DDE.Total.answeredQueries_transcript g.1 e n).symm
      rcases hx : e (DDE.Total.transcript g.1 e n)↓ᵧ with _ | x
      · rw [DDE.Total.transcript_succ_of_stop _ _ (hstep.trans hx),
          DDE.Total.transcript_succ_of_stop _ _ hx]
        exact ih
      · rw [DDE.Total.transcript_succ_of_query _ _ (hstep.trans hx),
          DDE.Total.transcript_succ_of_query _ _ hx, hinputs,
          answer_toBitSystem, hkept]
        rcases hans : answer g.1 (DDE.Total.transcript g.1 e n)↓ₓ x with _ | y
        · simpa [lastBit] using ih
        · simp [lastBit]

end

end System

/-! ## Definition 2.22: probabilistic games -/

noncomputable section

open Classical

open Probability (Distribution)

universe u v

variable {X : Type u} {Y : Type v}

/-- Lanzenberger **Definition 2.22**: "A *probabilistic discrete
`(𝒳,𝒴)`-game* (or an `(𝒳,𝒴)`-PDG) is a distribution over `(𝒳,𝒴)`-DDG."

The distribution is over Definition 2.20's *pairs*, so the system and the
condition are jointly distributed; §5's `adjoin` is the constructor that
builds such a joint law from a system law and a per-atom condition. -/
abbrev PDG (X : Type u) (Y : Type v) : Type (max u v) :=
  Distribution (System.DDG X Y)

namespace PDG

/-- The Definition 2.21 observable at the law level: the distribution of the
game transcript `tr(S^A, e)` after `n` environment moves.  Definition 2.25's
`ν` is a function of this law alone (`winningMass_eq_mass_gameTrLaw`). -/
def gameTrLaw (e : System.DDE.Total Y X) (n : ℕ) (G : PDG X Y) :
    Distribution (List (X × Option Y) × Bool) :=
  Distribution.fTransform (fun g => System.gameTranscript g e n) G

/-- The mass of Definition 2.25's winning transcripts in one environment at
one interaction length: `Pr^{tr(S^A)}(tr(S^A,e) ∈ 𝒯_w)`. -/
def winningMass (e : System.DDE.Total Y X) (n : ℕ) (G : PDG X Y) : ℝ :=
  G.mass fun g => System.Won g e n

/-- Winning is an observable of the Definition 2.21 transcript law: the
winning mass reads only `gameTrLaw`, never the presentation. -/
theorem winningMass_eq_mass_gameTrLaw (e : System.DDE.Total Y X) (n : ℕ)
    (G : PDG X Y) :
    winningMass e n G = (gameTrLaw e n G).mass fun t => t.2 = true := by
  rw [gameTrLaw, Distribution.mass_fTransform]
  exact Distribution.mass_congr _ fun g => System.won_iff_gameTranscript g e n

/-- Lanzenberger **Definition 2.25**: "For a random `(𝒳,𝒴)`-game `S^A`, we
define the supremum winning probability of `S^A` by
`ν(S^A) := sup_e Pr^{tr S^A}(tr(S^A,e) ∈ 𝒯_w)`, where `𝒯_w` denotes the set of
all winning transcripts, i.e., the transcripts ending with `(·,1)`."

The supremum is over *deterministic* environments — the thesis's own remark
before Definition 2.25: "This is sufficient, since in an information-theoretic
setting, one can always fix the randomness of a probabilistic environment to
be optimal."  On the tree's total presentation the environment is
`System.DDE.Total`, and the interaction length is a second index of the
supremum rather than a stopping hypothesis, exactly as in `advFullyDefined`
(Ruling R4).  **The index type is the whole content of Remark 2.23**: an
environment is a function of the output history alone, so no environment in
the supremum can observe the condition. -/
def supWinProb (G : PDG X Y) : ℝ :=
  ⨆ p : System.DDE.Total Y X × ℕ, winningMass p.1 p.2 G

/-- Lanzenberger Definition 2.25 notation: `ν(G)` is the supremum winning
probability. -/
scoped notation "ν(" G ")" => supWinProb G

theorem winningMass_nonneg {G : PDG X Y} (hG : G.NonNeg)
    (e : System.DDE.Total Y X) (n : ℕ) : 0 ≤ winningMass e n G :=
  hG.mass_nonneg _

theorem winningMass_le_weight {G : PDG X Y} (hG : G.NonNeg)
    (e : System.DDE.Total Y X) (n : ℕ) : winningMass e n G ≤ G.weight :=
  Distribution.mass_le_weight hG _

/-- The winning masses are bounded above by the weight, so Definition 2.25's
supremum is a genuine least upper bound.  Non-negativity is the hypothesis
that makes it one: on the signed carrier a supremum of masses need not be
bounded, the same phenomenon the thesis's `ω` guards against with its own
`NonNeg` conjunct. -/
theorem bddAbove_range_winningMass {G : PDG X Y} (hG : G.NonNeg) :
    BddAbove (Set.range fun p : System.DDE.Total Y X × ℕ =>
      winningMass p.1 p.2 G) := by
  refine ⟨G.weight, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact winningMass_le_weight hG p.1 p.2

/-- Definition 2.25's defining property, upper half. -/
theorem winningMass_le_supWinProb {G : PDG X Y} (hG : G.NonNeg)
    (e : System.DDE.Total Y X) (n : ℕ) : winningMass e n G ≤ supWinProb G :=
  le_ciSup (bddAbove_range_winningMass hG) (e, n)

/-- Definition 2.25's defining property, lower half. -/
theorem supWinProb_le_of_forall {G : PDG X Y} {c : ℝ}
    (h : ∀ (e : System.DDE.Total Y X) (n : ℕ), winningMass e n G ≤ c) :
    supWinProb G ≤ c :=
  ciSup_le fun p => h p.1 p.2

theorem supWinProb_nonneg {G : PDG X Y} (hG : G.NonNeg) : 0 ≤ supWinProb G :=
  le_trans (winningMass_nonneg hG (fun _ => none) 0)
    (winningMass_le_supWinProb hG (fun _ => none) 0)

theorem supWinProb_le_weight {G : PDG X Y} (hG : G.NonNeg) :
    supWinProb G ≤ G.weight :=
  supWinProb_le_of_forall fun e n => winningMass_le_weight hG e n

/-! ## The bit view at the law level -/

/-- The Maurer13b Definition 9 view of a probabilistic game: the pushforward
of the law along `toBitSystem`. -/
def toBitLaw (G : PDG X Y) : PDS X (Y × Bool) :=
  Distribution.fTransform System.toBitSystem G

/-- The inverse view at the law level. -/
def ofBitLaw (T : PDS X (Y × Bool)) : PDG X Y :=
  Distribution.fTransform System.ofBitSystem T

/-- The bit view of a game law lands in the monotone-bit class. -/
theorem monotoneBit_of_mem_support_toBitLaw (G : PDG X Y)
    {t : System.DDS X (Y × Bool)} (ht : t ∈ (toBitLaw G).support) :
    System.MonotoneBit t := by
  obtain ⟨g, -, rfl⟩ := Distribution.mem_support_fTransform _ G ht
  exact System.monotoneBit_toBitSystem g

/-- **Definition 2.25 is invariant under the bit-hiding view.**  The winning
probability read off the derived bit view — through the trivial converter that
erases the bit, by the test `lastBit … = some true` that reads only the
interaction record — is the winning probability of the game.

The hypothesis is exactly the expressiveness gap of §4: a condition already
satisfied at the empty history has no bit to be shown, so the bit view can
only report the conditions the domain supports
(`System.not_mem_nil_of_domainSupported` gives it for every domain-supported
game).  This is the one *contentful* blindness statement here; on Definition
2.20's pair, Remark 2.23 is the type of the environment and needs no
theorem. -/
theorem winningMass_eq_mass_lastBit_toBitLaw {G : PDG X Y}
    (hG : ∀ g ∈ G.support, [] ∉ g.2.1) (e : System.DDE.Total Y X) (n : ℕ) :
    winningMass e n G =
      (toBitLaw G).mass fun t =>
        System.lastBit (System.DDE.Total.transcript t
          (System.DDE.Total.relabelOut Prod.fst e) n) = some true := by
  rw [toBitLaw, Distribution.mass_fTransform, winningMass]
  refine Distribution.mass_congr_of_support G fun g hg => ?_
  rw [System.lastBit_transcript_toBitSystem]
  by_cases hnil : System.answeredQueries
      (System.DDE.Total.transcript g.1 e n) = []
  · rw [if_pos hnil]
    exact ⟨fun hwon => absurd (hnil ▸ hwon) (hG g hg), fun h => by simp at h⟩
  · rw [if_neg hnil]
    rw [show (some (System.MonotoneCondition.toPred g.2
        (System.answeredQueries (System.DDE.Total.transcript g.1 e n)))
          = some true) ↔ _ from Option.some_inj]
    exact System.MonotoneCondition.toPred_eq_true.symm

/-- **Round trip at the law level**, one way. -/
theorem ofBitLaw_toBitLaw {G : PDG X Y}
    (hG : ∀ g ∈ G.support, System.DomainSupported g) :
    ofBitLaw (toBitLaw G) = G := by
  rw [ofBitLaw, toBitLaw, Distribution.fTransform_fTransform]
  refine (Distribution.fTransform_congr (g := id) G ?_).trans
    (Distribution.fTransform_id G)
  exact fun g hg => System.ofBitSystem_toBitSystem (hG g hg)

/-- **Round trip at the law level**, the other way. -/
theorem toBitLaw_ofBitLaw {T : PDS X (Y × Bool)}
    (hT : ∀ t ∈ T.support, System.MonotoneBit t) :
    toBitLaw (ofBitLaw T) = T := by
  rw [toBitLaw, ofBitLaw, Distribution.fTransform_fTransform]
  refine (Distribution.fTransform_congr (g := id) T ?_).trans
    (Distribution.fTransform_id T)
  exact fun t ht => System.toBitSystem_ofBitSystem (hT t ht)

/-! ## Remark 2.24: adjoining a condition to a system -/

/-- Dropping the condition: the system law underlying a game.  This is the
forgetful map whose sections `adjoin` builds. -/
def forget (G : PDG X Y) : PDS X Y :=
  Distribution.fTransform Prod.fst G

@[simp] theorem weight_forget (G : PDG X Y) : (forget G).weight = G.weight :=
  Distribution.weight_fTransform _ G

theorem nonNeg_forget {G : PDG X Y} (hG : G.NonNeg) : (forget G).NonNeg :=
  hG.fTransform _

/-- Forgetting the condition of the pushforward `s ↦ (s, A s)` returns the
system law on the nose — the computation behind the forgetting law. -/
theorem forget_pair_fTransform (S : PDS X Y)
    (A : System.DDS X Y → System.MonotoneCondition X) :
    forget (Distribution.fTransform (fun s => (s, A s)) S) = S := by
  rw [forget, Distribution.fTransform_fTransform]
  exact Distribution.fTransform_id S

end PDG

namespace PDS

/-- Lanzenberger **Definition 2.20** attaches a condition to a system — "a
monotone condition (or MC) **for** an `(𝒳,𝒴)`-DDS `s`" — and **Remark 2.24**
does it at the law level: "An MC `A`, specified by distributions
`p^A_{Aᵢ|XⁱYⁱAᵢ₋₁}`, can be *adjoined* to a random system, i.e., given
distributions `p^S_{Yᵢ|XⁱYⁱ⁻¹}` it induces distributions
`p^{S^A}_{YᵢAᵢ|XⁱYⁱ⁻¹,Aᵢ₋₁}`."

`GamesFor S` is the type of games for `S`: those whose underlying behaviour is
`S`.  Membership *is* the forgetting law — dropping the condition returns `S`
— and it is stated against the equivalence class (Lanzenberger Definition
2.17, `PDS.equivalent`), not against a representative, so which presentation a
construction happens to produce is the user's discharge obligation and not a
modeling wrinkle.  Definition 2.20's other obligation, monotonicity, lives in
`MonotoneCondition` itself.  There are therefore no proof fields anywhere in
this development: the two obligations are the two subtypes. -/
def GamesFor (S : PDS X Y) : Type (max u v) :=
  {G : PDG X Y // equivalent (PDG.forget G) S}

namespace GamesFor

/-- The forgetting law, as carried by membership. -/
theorem equivalent_forget {S : PDS X Y} (G : GamesFor S) :
    equivalent (PDG.forget G.1) S :=
  G.2

/-- The forgetting law at the quotient: a game for `S` forgets to `S`'s
behaviour (Lanzenberger Notation 2.19). -/
theorem toBehaviour_forget {S : PDS X Y} (G : GamesFor S) :
    toBehaviour (PDG.forget G.1) = toBehaviour S :=
  toBehaviour_eq_iff.mpr G.2

/-- A game for `S` carries `S`'s weight — the first consequence of the
forgetting law, and the hypothesis every symmetry statement about `Adv⊥`
needs. -/
theorem weight_eq {S : PDS X Y} (G : GamesFor S) : G.1.weight = S.weight := by
  rw [← PDG.weight_forget]
  exact weight_eq_of_equivalent G.2

end GamesFor

/-- **Remark 2.24's constructor**: adjoining to `S` the condition `A s` chosen
per deterministic atom `s`.  The result is a game *for* `S`; the joint law is
the pushforward of `S` along `s ↦ (s, A s)`, so the condition is correlated
with the system exactly as `A`'s dependence on `s` prescribes — which is what
Remark 2.24's conditioning on `XⁱYⁱ` amounts to on this carrier.

The two obligations are discharged by construction: monotonicity because `A`
lands in `MonotoneCondition`, and the forgetting law because the second
component of the subtype is proved here, on the nose rather than up to
equivalence. -/
def adjoin (S : PDS X Y) (A : System.DDS X Y → System.MonotoneCondition X) :
    GamesFor S :=
  ⟨Distribution.fTransform (fun s => (s, A s)) S,
    by rw [PDG.forget_pair_fTransform]; exact equivalent_refl S⟩

@[simp] theorem coe_adjoin (S : PDS X Y)
    (A : System.DDS X Y → System.MonotoneCondition X) :
    (adjoin S A).1 = Distribution.fTransform (fun s => (s, A s)) S :=
  rfl

/-- The forgetting law for `adjoin`, in its strongest form: an equality of
laws, not merely of behaviours. -/
@[simp] theorem forget_adjoin (S : PDS X Y)
    (A : System.DDS X Y → System.MonotoneCondition X) :
    PDG.forget (adjoin S A).1 = S :=
  PDG.forget_pair_fTransform S A

theorem nonNeg_adjoin {S : PDS X Y} (hS : S.NonNeg)
    (A : System.DDS X Y → System.MonotoneCondition X) :
    (adjoin S A).1.NonNeg :=
  hS.fTransform _

/-- Definition 2.25's winning mass of an adjoined game, computed: the mass of
the deterministic systems whose own answered history triggers their own
condition. -/
theorem winningMass_adjoin (S : PDS X Y)
    (A : System.DDS X Y → System.MonotoneCondition X)
    (e : System.DDE.Total Y X) (n : ℕ) :
    PDG.winningMass e n (adjoin S A).1 =
      S.mass fun s => System.answeredQueries (System.DDE.Total.transcript s e n)
        ∈ (A s).1 :=
  Distribution.mass_fTransform _ S _

/-! ### Worked receipt: the never-won and the already-won poles

Adjoining the bottom condition forgets to the original system and is never
won; adjoining the top condition forgets to it too and is always won.  The
first is the thesis's always-losing `V` (printed p. 26) obtained as a
constructor call rather than as a separate object; together they show the
forgetting law is genuinely independent of the condition adjoined. -/

@[simp] theorem forget_adjoin_bot (S : PDS X Y) :
    PDG.forget (adjoin S fun _ => ⊥).1 = S :=
  forget_adjoin S _

@[simp] theorem winningMass_adjoin_bot (S : PDS X Y)
    (e : System.DDE.Total Y X) (n : ℕ) :
    PDG.winningMass e n (adjoin S fun _ => ⊥).1 = 0 := by
  rw [winningMass_adjoin]
  exact Distribution.mass_eq_zero_of_forall_not S fun _ => Set.notMem_empty _

@[simp] theorem supWinProb_adjoin_bot (S : PDS X Y) :
    PDG.supWinProb (adjoin S fun _ => ⊥).1 = 0 := by
  have h : ∀ p : System.DDE.Total Y X × ℕ,
      PDG.winningMass p.1 p.2 (adjoin S fun _ => ⊥).1 = 0 :=
    fun p => winningMass_adjoin_bot S p.1 p.2
  calc (⨆ p : System.DDE.Total Y X × ℕ,
        PDG.winningMass p.1 p.2 (adjoin S fun _ => ⊥).1)
      = ⨆ _ : System.DDE.Total Y X × ℕ, (0 : ℝ) := iSup_congr h
    _ = 0 := ciSup_const

@[simp] theorem forget_adjoin_top (S : PDS X Y) :
    PDG.forget (adjoin S fun _ => ⊤).1 = S :=
  forget_adjoin S _

@[simp] theorem winningMass_adjoin_top (S : PDS X Y)
    (e : System.DDE.Total Y X) (n : ℕ) :
    PDG.winningMass e n (adjoin S fun _ => ⊤).1 = S.weight := by
  rw [winningMass_adjoin]
  exact Distribution.mass_true S

end PDS

end

end RandomSystems
