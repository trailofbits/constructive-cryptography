import ConstructiveCryptography.DSL

/-!
# Procedures on parallel outside interfaces

Named `outside` components `a : A`, `b : B` give the ordered tensor `A q₁ ⊗ B q₂` with the
budget tuple `(q₁, q₂)`; three give `A q₁ ⊗ (B q₂ ⊗ C q₃)`. Each history projection respects its
own budget, while state and initial samples belong to the whole component:

* `Store : TypedSystem (Reading r ⊗ Writing w)` keeps one bit, written at `write` and read at
  `read`;
* `Forward : Reading r ⊗ Writing w ⟶ Cell (Forward.bound * (r + w))` sends both requests to one
  cell, and `Forward • EmptyCell` is attached at the tuple budget;
* `SharedBit : TypedSystem (Reading l ⊗ (Reading m ⊗ Reading r))` returns one initial draw at
  all three components.

The per-port (`perPort`) and exact-cost (`exact`) typings, the scalar budget of one component and
the rejected declarations are checked as well.
-/

open SystemAlgebra SystemAlgebra.DSL Probability
open CategoryTheory MonoidalCategory

noncomputable section
namespace DSLTests.ParallelOutside

-- `Reading q`: at most `q` queries `get()`, each answered by a `Bool`.
-- `Writing q`: at most `q` queries `put(b)`, `b : Bool`, each answered by `()`.
interface Reading
  get() → Bool

interface Writing
  put(b : Bool) → Unit

-- `Cell q`: both operations on one interface, at most `q` queries in total.
interface Cell
  get() → Bool
  put(b : Bool) → Unit

-- `Store` on `Reading r ⊗ Writing w` retains one bit `value`, initially `false`:
-- `write.put(b) ⇒ ()` sets `value ≔ b`, and `read.get() ⇒ value` leaves it unchanged.
-- Both ports act on the same state; the tensor only describes the outside interface.
--
--                         ┌─ Store ─────────────┐
--   read.get() ⇒ value ───┤  value : Bool       │
--   write.put(b) ⇒ () ────┤  (initially false)  │
--                         └─────────────────────┘
--   Reading r ⊗ Writing w: `read.get` has label `.inl .get`, `write.put` has `.inr .put`.
system Store
  outside read : Reading
  outside write : Writing
  initialize
    value ← false
  on read.get() → Bool
    return value
  on write.put(b : Bool) → Unit
    value ← b
    return ()

-- The budget tuple `(r, w)` selects `Reading r ⊗ Writing w`.
example (r w : ℕ) : Store.outer (r, w) = Reading r ⊗ Writing w := rfl

example (r w : ℕ) : TypedSystem (Reading r ⊗ Writing w) := Store (budget := (r, w))

-- One budget `q` on the tagged labels gives each component its per-port budget.
example (q : Reading.Port ⊕ Writing.Port → ℕ) :
    TypedSystem (Reading.perPort (fun i => q (.inl i)) ⊗
      Writing.perPort (fun i => q (.inr i))) := Store.perPort (budget := q)

/-- `put(true), get()` lies in the domain of `Reading 1 ⊗ Writing 1`: its `read` projection
`[get()]` and its `write` projection `[put(true)]` each have length `1 ≤ 1`. -/
lemma store_admits_write_read :
    (Store.outer (1, 1)).domain [⟨.inr .put, true⟩, ⟨.inl .get, ()⟩] := by
  -- Unfold the parallel domain and compute both projections of the history.
  simp only [Store.outer, Interface.tensor, Interface.parallelDomain, parallelInputs,
    List.map_cons, List.map_nil, sumAlphabet, Equiv.coe_fn_symm_mk,
    restrict_cons_self, restrict_cons_ne (by simp : (none : Option Unit) ≠ some ()),
    restrict_cons_ne (by simp : (some () : Option Unit) ≠ none), restrict_nil]
  -- The history is nonempty, and each projection is nonempty with length within its budget.
  exact ⟨by simp, Or.inr ⟨by simp, le_rfl⟩, Or.inr ⟨by simp, le_rfl⟩⟩

/-- `get(), get()` lies outside `Reading 1 ⊗ Writing 4`: its `read` projection has length
`2 > 1`, although the total `2` is within `1 + 4`. Budgets are per component, not pooled. -/
lemma store_rejects_two_reads :
    ¬ (Store.outer (1, 4)).domain [⟨.inl .get, ()⟩, ⟨.inl .get, ()⟩] := by
  intro h
  -- The condition on the `read` projection, here both queries.
  have hr := h.2.1
  simp only [List.map_cons, List.map_nil, sumAlphabet, Equiv.coe_fn_symm_mk,
    restrict_cons_self, restrict_nil] at hr
  -- The projection is not empty, and its length `2` exceeds the budget `1`.
  rcases hr with he | ⟨_, hl⟩
  · exact List.cons_ne_nil _ _ he
  · change 2 ≤ 1 at hl
    omega

/-- The write is observed through the other component: from `value = false`, `write.put(b)`
moves to `value = b`, and `read.get()` then replies `b` and keeps `value = b`. -/
lemma store_read_after_write (b : Bool) :
    Store.step (Store.step false (.inr .put) b).1 (.inl .get) () = (b, b) := rfl

/-- At budgets `(1, 1)`, the interleaved transcript `write.put(true) ⇒ ()`, `read.get() ⇒ true`
has probability one. -/
lemma store_write_read :
    (Store (budget := (1, 1))).1
      [(⟨.inr .put, true⟩, ⟨.inr .put, ()⟩), (⟨.inl .get, ()⟩, ⟨.inl .get, true⟩)] = 1 := by
  -- `Store` is the automaton started in the single state `false`: the mass is one exactly when
  -- the deterministic system, restricted to the domain, gives these replies.
  rw [Store, TypedSystem.ofAutomaton_mass]
  refine (Distribution.mass_single _ _ _).trans (if_pos ?_)
  simp only [List.map_cons, List.map_nil]
  -- The queries lie in the domain (`store_admits_write_read`), so the restriction is inactive.
  apply (replies_filterDom_iff (Store.outer (1, 1)).nonempty_prefix.2 _
    (fun _ => store_admits_write_read)).mpr
  change Replies _ ([] ++ [(⟨.inr .put, true⟩ : Sigma (Store.outer (1, 1)).X)] ++
    [⟨.inl .get, ()⟩]) ([] ++ [(⟨.inr .put, ()⟩ : Sigma (Store.outer (1, 1)).Y)] ++
    [⟨.inl .get, true⟩])
  -- Check the replies one query at a time.
  refine replies_snoc.mpr ⟨replies_snoc.mpr ⟨replies_nil _, ?_⟩, ?_⟩
  -- From the initial state, `put(true)` replies `()`.
  · rw [automatonSystem_snoc, stateAfter_nil]
  -- After `put(true)` the state is `true`, and `get()` replies `true`.
  · rw [automatonSystem_snoc, stateAfter_snoc, stateAfter_nil]
    rfl

-- `Forward : Reading r ⊗ Writing w ⟶ Cell (Forward.bound * (r + w))`, stateless:
-- `read.get()` calls `cell.get() ⇒ b` and replies `b`; `write.put(b)` calls `cell.put(b) ⇒ u`
-- and replies `u`. One inside call per invocation, so `Forward.bound = 1`.
converter Forward
  outside read : Reading
  outside write : Writing
  inside cell : Cell
  on read.get() → Bool
    b ← cell.get()
    return b
  on write.put(b : Bool) → Unit
    u ← cell.put(b)
    return u

example : Forward.bound = 1 := rfl

-- The inside allowance is the bound times the total outside bound `r + w`.
example (r w : ℕ) : Reading r ⊗ Writing w ⟶ Cell (Forward.bound * (r + w)) :=
  Forward (budget := (r, w))

-- Per-port budgets outside; the inside allowance is the bound times their aggregate.
example (q : Reading.Port ⊕ Writing.Port → ℕ) :
    Reading.perPort (fun i => q (.inl i)) ⊗ Writing.perPort (fun i => q (.inr i)) ⟶
      Cell (Forward.bound * ((∑ i, q (.inl i)) + ∑ i, q (.inr i))) :=
  Forward.perPort (budget := q)

-- Exact cost: tuple query budgets `(r, w)` outside, and the scalar work budget `work` inside.
example (r w work : ℕ) := Forward.exact (queries := (r, w)) (budget := work)

-- `EmptyCell : TypedSystem (Cell q)`, stateless: `get() ⇒ false` and `put(b) ⇒ ()`.
system EmptyCell : Cell
  on get() → Bool
    return false
  on put(_b : Bool) → Unit
    return ()

-- `Forward • EmptyCell` takes its outside interface, and so its tuple budget, from `Forward`.
system Forwarded ≔ Forward • EmptyCell

example (r w : ℕ) : TypedSystem (Reading r ⊗ Writing w) :=
  Forwarded (budget := (r, w))

-- `SharedBit` on `Reading l ⊗ (Reading m ⊗ Reading r)` draws `bit ←$ 𝒰[Bool]` once, at its
-- first invocation, and every `get() ⇒ bit` replies with that retained draw:
--
--                       ┌─ SharedBit ─────────┐
--   left.get() ⇒ bit ───┤                     │
--   middle.get() ⇒ bit ─┤  bit ←$ 𝒰[Bool]     │   one draw, retained
--   right.get() ⇒ bit ──┤                     │
--                       └─────────────────────┘
--   labels `.inl .get`, `.inr (.inl .get)`, `.inr (.inr .get)`.
-- Three one-port components composed with `∥` would instead make three independent draws.
system SharedBit
  outside left : Reading
  outside middle : Reading
  outside right : Reading
  initialize
    bit ←$ 𝒰[Bool]
  on left.get() → Bool
    return bit
  on middle.get() → Bool
    return bit
  on right.get() → Bool
    return bit

-- Three components nest to the right, with the budget tuple `(l, m, r)`.
example (l m r : ℕ) :
    TypedSystem (Reading l ⊗ (Reading m ⊗ Reading r)) := SharedBit (budget := (l, m, r))

/-- With stored `bit = b`, `left.get()` replies `b` at once, keeping the state and making no
source call. -/
lemma sharedBit_left_retains (b : Bool) :
    SharedBit.body (some b) (.inl .get) () [] = .inl (some b, b) := rfl

/-- `middle.get()` replies with the same stored `b`, without a source call. -/
lemma sharedBit_middle_retains (b : Bool) :
    SharedBit.body (some b) (.inr (.inl .get)) () [] = .inl (some b, b) := rfl

/-- `right.get()` replies with the same stored `b`, without a source call. -/
lemma sharedBit_right_retains (b : Bool) :
    SharedBit.body (some b) (.inr (.inr .get)) () [] = .inl (some b, b) := rfl

-- `SingleReader : TypedSystem (Reading q)`, `get() ⇒ false`: one named component keeps the
-- scalar budget and the interface's own labels, with no tensor tag.
system SingleReader
  outside read : (Reading)
  on read.get() → Bool
    return false

example (q : ℕ) : TypedSystem (Reading q) := SingleReader (budget := q)

example (q : Reading.Port → ℕ) : TypedSystem (Reading.perPort q) :=
  SingleReader.perPort (budget := q)

-- `RepeatedRead : Cell q ⊗ Reading r ⟶ Reading (RepeatedRead.bound * (q + r))`, stateless:
-- `cell.get()` calls `source.get()` twice and replies the last answer, `cell.put(b) ⇒ ()` calls
-- nothing, and `extra.get()` forwards one `source.get()`. The loop gives an inferred bound.
converter RepeatedRead
  outside cell : Cell
  outside extra : Reading
  inside source : Reading
  on cell.get() → Bool
    result ← false
    for _i ∈ [(), ()]
      result ← source.get()
    return result
  on cell.put(_b : Bool) → Unit
    return ()
  on extra.get() → Bool
    result ← source.get()
    return result

example (q r : ℕ) : Cell q ⊗ Reading r ⟶ Reading (RepeatedRead.bound * (q + r)) :=
  RepeatedRead (budget := (q, r))

-- Rejected: an annotation and named components; a repeated component name; a procedure whose
-- prefix names no component, or no prefix at all.
/-- error: Use either an interface annotation or named outside components. -/
#guard_msgs in
system AmbiguousOutside : Reading
  outside read : Reading
  on read.get() → Bool
    return false

/-- error: Duplicate outside component. -/
#guard_msgs in
system DuplicateOutside
  outside read : Reading
  outside read : Reading
  on read.get() → Bool
    return false

/-- error: Unknown outside component in procedure name. -/
#guard_msgs in
system UnknownOutside
  outside read : Reading
  on other.get() → Bool
    return false

/-- error: Unknown outside component in procedure name. -/
#guard_msgs in
system UnqualifiedOutside
  outside read : Reading
  on get() → Bool
    return false

#print axioms Store
#print axioms Forward
#print axioms Forward.exact
#print axioms Forward.perPort
#print axioms RepeatedRead
#print axioms SharedBit

end DSLTests.ParallelOutside
