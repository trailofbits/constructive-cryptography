/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import RandomSystems.System.DiscreteSystem
import RandomSystems.PartialFunction

/-!
# Deterministic discrete converters (CR18 §3.4.2, Definitions 3.8–3.9)

A converter is a discrete system at another signature: Definition 3.8 reads
"a deterministic discrete converter converting an `(X,Y)`-DDS into a
`(U,V)`-DDS is just a DDS over the converter alphabets", so the converter half
of the theory needs no carrier of its own.

Two presentations reach that object, each by a realization theorem.  This
module holds both and the map between them.

* `DDC`, Definition 3.8 itself, together with Definition 3.9's application.
* `ProtocolFn` — the converter as a single partial history function
  `ν : List U × List (Option Y) →. (X ⊕ V)`, "after outer inputs `u^k` and
  inner answers `y^l`, the converter's next move is an inner query `inl x` or
  an outer answer `inr v`".  The converter's own past outputs are
  recomputable, so nothing else is data, and round boundaries are derived from
  `ν` itself.  Memory classes are invariance *predicates* on `ν`, never part of
  the type.
* `toDDC` — the canonical Definition 3.8 object of a protocol function,
  defined on protocol traces only.  Its realization theorem, `apply_toDDC`,
  lives with serial composition in `RandomSystems.Converter.Cascade`.

Converter identity is trace equality, `ν* = ν'*`: `Reach ν` is the trace tree,
the pairs `ν` can actually be consulted at; undefinedness inside the tree is
honest partiality, values off the tree are junk; `normalize` erases the junk
and `TraceEquiv` compares normal forms.

Definition 3.8's closing clause — "there is a finite upper bound on the number
of consecutive outputs of the form `(in, x)`" — is kept as the predicate
`AnswersWithin`, and `IsDDC` is that together with `AnswersInY`.  It is never
baked into a driver; see `RandomSystems.PartialFunction` for the finite
unrolling the drivers use instead.
-/


namespace RandomSystems

universe u v w z

namespace Converter

open scoped System

/-! ### CR18 §3.4.2 / Definition 3.8 -/

variable {U : Type u} {V : Type w} {X : Type z} {Y : Type v}

/-- Converter-side labels. -/
inductive InLabel : Type where
  | inside
  | outside

scoped infixr:30 " ∪ₜ " => Sum

/-- CR18 Definition 3.8: a deterministic discrete converter converting an
`(X,Y)`-DDS into a `(U,V)`-DDS is just a DDS over the converter alphabets. -/
abbrev DDC (U : Type u) (V : Type w) (X : Type z) (Y : Type v) :
    Type (max (max u v) (max w z)) :=
  System.DDS
    ((InLabel × U) ∪ₜ (InLabel × Option Y))
    ((InLabel × V) ∪ₜ (InLabel × X))

/-! ### CR18 §3.4.2 / Definition 3.9 -/

namespace DDC

/-! #### Function-native realization of CR18 Definition 3.9

Maurer (Def 3.9) describes `αs` purely by *connection rules* and then notes:
"We do not give a completely formal definition of the application of a converter
to a system. Formally, one would have to show that the described object `αs` is
indeed a `(U,V)`-DDS. Intuitively, this is obvious."

We realize `αs` as exactly that missing object — a partial function (Def 3.2),
built by *function composition*, with no operational driver. The inner
converter/system interaction is the **least fixed point** of a single connection
step (`PFun.fix`); the outer round structure is ordinary structural recursion on
the outside input history. Maurer's two connection rules then *are* the
fixed-point lemmas `PFun.fix_stop` (output `(out,v)`) and `PFun.fix_fwd_eq`
(query `(in,x)`), recorded below as `resolve_out` and `resolve_in`.

Per Def 3.8 a converter has "a finite upper bound on the number of consecutive
`(in,x)` outputs". We keep that as a *predicate* on converters (a property, never
part of the converter's type); a converter without it still yields a partial
`αs`, undefined exactly where the inner loop never reaches an `(out,v)`. -/

/-- The converter-input alphabet `U ∪ (Y ∪ {⊥})` of CR18 Def 3.8. -/
abbrev CIn (U : Type u) (Y : Type v) : Type (max u v) :=
  (InLabel × U) ∪ₜ (InLabel × Option Y)

/-- The converter-output alphabet `({out} × V) ∪ ({in} × X)` of CR18 Def 3.8. -/
abbrev COut (V : Type w) (X : Type z) : Type (max w z) :=
  (InLabel × V) ∪ₜ (InLabel × X)

/-- CR18 Def 3.9, one connection step over the hidden
`(converter-history, system-history)` state:
* `α` outputs `(out, v)` ⟹ stop with `v` (histories unchanged);
* `α` outputs `(in, x)` ⟹ feed `x` to `s⊥` and continue with the answer;
* otherwise (α undefined, or an off-interface label) ⟹ undefined. -/
noncomputable def connStep (α : DDC U V X Y) (S : System.DDS X Y) :
    (List (CIn U Y) × List X) →.
      (V × (List (CIn U Y) × List X)) ⊕ (List (CIn U Y) × List X) :=
  fun st =>
    (α.1 st.1).bind fun o =>
      match o with
      | Sum.inl (InLabel.outside, v) => Part.some (Sum.inl (v, st))
      | Sum.inr (InLabel.inside, x) =>
          Part.some (Sum.inr
            (st.1 ++ [Sum.inr (InLabel.inside,
                System.output (S⊥) (st.2 ++ [x])
                  (by rw [System.dom_fullyDefined]; simp))],
             st.2 ++ [x]))
      | _ => Part.none

/-- CR18 Def 3.9 inner resolution: the least fixed point of `connStep`. A genuine
partial function `(history) →. V`, undefined exactly when the inner loop never
reaches an `(out, v)`. -/
noncomputable def resolve (α : DDC U V X Y) (S : System.DDS X Y) :
    (List (CIn U Y) × List X) →. (V × (List (CIn U Y) × List X)) :=
  (connStep α S).fix

/-- CR18 Def 3.9 **output rule**, which is exactly `PFun.fix_stop`: when `α`
outputs `(out, v)` on the current converter history, the inner resolution returns
`v` with the histories unchanged. -/
theorem resolve_out (α : DDC U V X Y) (S : System.DDS X Y)
    {c : List (CIn U Y)} {xs : List X} {v : V}
    (h : Sum.inl (InLabel.outside, v) ∈ α.1 c) :
    (v, (c, xs)) ∈ resolve α S (c, xs) := by
  refine PFun.fix_stop (f := connStep α S) ?_
  refine Part.mem_bind_iff.mpr ⟨_, h, ?_⟩
  simp

/-- CR18 Def 3.9 **query rule**, which is exactly `PFun.fix_fwd_eq`: when `α`
outputs `(in, x)`, the inner resolution continues from the converter history
extended by `s⊥`'s answer to `x`. -/
theorem resolve_in (α : DDC U V X Y) (S : System.DDS X Y)
    {c : List (CIn U Y)} {xs : List X} {x : X}
    (h : Sum.inr (InLabel.inside, x) ∈ α.1 c) :
    resolve α S (c, xs) =
      resolve α S
        (c ++ [Sum.inr (InLabel.inside,
            System.output (S⊥) (xs ++ [x])
              (by rw [System.dom_fullyDefined]; simp))], xs ++ [x]) := by
  refine PFun.fix_fwd_eq (f := connStep α S) ?_
  refine Part.mem_bind_iff.mpr ⟨_, h, ?_⟩
  simp

/-- CR18 Def 3.9 outer iteration: feed the outside inputs `us` to the converter
one after another, threading the hidden histories through `resolve`, and collect
the outside outputs. This is ordinary structural recursion on `us`; the only
fixed point is the inner `resolve`. -/
noncomputable def driveFrom (α : DDC U V X Y) (S : System.DDS X Y) :
    (List (CIn U Y) × List X) → List U →. (List V × (List (CIn U Y) × List X))
  | st, [] => Part.some ([], st)
  | st, u :: rest =>
      (resolve α S (st.1 ++ [Sum.inl (InLabel.outside, u)], st.2)).bind
        fun r => (driveFrom α S r.2 rest).map fun rr => (r.1 :: rr.1, rr.2)

/-- The applied system as a raw partial function `List U →. V`: replay the whole
interaction from empty histories and return the output of the last round. -/
noncomputable def applyRaw (α : DDC U V X Y) (S : System.DDS X Y) :
    System.Raw U V :=
  fun us => (driveFrom α S ([], []) us).bind fun r =>
    match r.1.getLast? with
    | some v => Part.some v
    | none => Part.none

/-- Each completed round produces exactly one outside output. -/
theorem driveFrom_length (α : DDC U V X Y) (S : System.DDS X Y)
    (st : List (CIn U Y) × List X) (us : List U)
    {r : List V × (List (CIn U Y) × List X)} (h : r ∈ driveFrom α S st us) :
    r.1.length = us.length := by
  induction us generalizing st r with
  | nil =>
      simp only [driveFrom, Part.mem_some_iff] at h
      subst h; simp
  | cons u rest ih =>
      simp only [driveFrom, Part.mem_bind_iff, Part.mem_map_iff] at h
      obtain ⟨r', _hr', rr, hrr, rfl⟩ := h
      simp [ih r'.2 hrr]

/-- The outer iteration splits over a concatenation of outside histories: drive
the prefix, then drive the suffix from the resulting state. -/
theorem driveFrom_append (α : DDC U V X Y) (S : System.DDS X Y)
    (st : List (CIn U Y) × List X) (a b : List U) :
    driveFrom α S st (a ++ b) =
      (driveFrom α S st a).bind fun ra =>
        (driveFrom α S ra.2 b).map fun rb => (ra.1 ++ rb.1, rb.2) := by
  induction a generalizing st with
  | nil =>
      simp only [List.nil_append, driveFrom, Part.bind_some]
      refine (Part.map_id' ?_ _).symm
      intro rb; rfl
  | cons u rest ih =>
      simp only [List.cons_append, driveFrom, ih, Part.bind_assoc, Part.bind_map,
        Part.map_bind, Part.map_map, Function.comp_def, List.cons_append]

/-- CR18 Definition 3.9: the applied converter `αs`, realized as the partial
function `applyRaw α S`. The `Valid` proof (Maurer's "one would have to show αs
is a `(U,V)`-DDS") is discharged from the structural driver lemmas. -/
noncomputable def apply (α : DDC U V X Y) (S : System.DDS X Y) :
    System.DDS U V :=
  ⟨applyRaw α S, by
    refine ⟨?_, ?_⟩
    · -- the empty outside history produces no output
      rw [PFun.mem_dom]
      rintro ⟨v, hv⟩
      simp [applyRaw, driveFrom] at hv
    · -- domain is closed under nonempty prefixes
      intro l₁ l₂ hpre hne hdom
      obtain ⟨suf, rfl⟩ := hpre
      rw [PFun.mem_dom] at hdom
      obtain ⟨v, hv⟩ := hdom
      simp only [applyRaw, Part.mem_bind_iff] at hv
      obtain ⟨r, hr, _hvr⟩ := hv
      rw [driveFrom_append, Part.mem_bind_iff] at hr
      obtain ⟨ra, hra, _hr2⟩ := hr
      have hlen : ra.1.length = l₁.length := driveFrom_length α S ([], []) l₁ hra
      have hne1 : ra.1 ≠ [] := by
        intro hnil
        apply hne
        apply List.eq_nil_of_length_eq_zero
        rw [← hlen, hnil, List.length_nil]
      rw [PFun.mem_dom]
      refine ⟨ra.1.getLast hne1, ?_⟩
      simp only [applyRaw, Part.mem_bind_iff]
      refine ⟨ra, hra, ?_⟩
      rw [List.getLast?_eq_some_getLast hne1]
      exact Part.mem_some _⟩

/-- The applied system is exactly the raw partial function `applyRaw`. -/
@[simp]
theorem apply_toPFun (α : DDC U V X Y) (S : System.DDS X Y) :
    (apply α S).1 = applyRaw α S := rfl

/-- Membership characterization of `αs`: the outside history `us` yields `v`
exactly when replaying it produces a final output list ending in `v`. This is
the function-native replacement for the old `ApplicationGraph` relation. -/
theorem mem_apply_iff (α : DDC U V X Y) (S : System.DDS X Y)
    (us : List U) (v : V) :
    v ∈ applyRaw α S us ↔
      ∃ r ∈ driveFrom α S ([], []) us, r.1.getLast? = some v := by
  simp only [applyRaw, Part.mem_bind_iff]
  refine exists_congr fun r => and_congr_right fun _ => ?_
  cases r.1.getLast? with
  | none => simp
  | some w => simp [Part.mem_some_iff, eq_comm]

/-- CR18 Definition 3.9 notation: `α ·ᶜ S` is the DDS obtained by applying
the deterministic converter `α` to the DDS `S`.

The subscript distinguishes converter application from cascade notation `⊲`
and probabilistic converter composition notation `·ₚ`. -/
scoped notation:70 α " ·ᶜ " S => apply α S

/-! ### One connection step (CR18 Definition 3.9), by membership -/


theorem connStep_mem_inl (α : DDC U V X Y) (S : System.DDS X Y)
    (st : List (CIn U Y) × List X) (b : V × (List (CIn U Y) × List X)) :
    Sum.inl b ∈ connStep α S st ↔
      Sum.inl (InLabel.outside, b.1) ∈ α.1 st.1 ∧ b.2 = st := by
  rw [connStep, Part.mem_bind_iff]
  constructor
  · rintro ⟨o, ho, hb⟩
    rcases o with ⟨lbl, v0⟩ | ⟨lbl, x0⟩ <;> cases lbl <;> simp_all
  · rintro ⟨hmem, hst⟩
    exact ⟨Sum.inl (InLabel.outside, b.1), hmem, by rw [← hst]; cases b; simp⟩

theorem connStep_mem_inr (α : DDC U V X Y) (S : System.DDS X Y)
    (st st' : List (CIn U Y) × List X) :
    Sum.inr st' ∈ connStep α S st ↔
      ∃ x, Sum.inr (InLabel.inside, x) ∈ α.1 st.1 ∧
        st' = (st.1 ++ [Sum.inr (InLabel.inside,
            System.output (S⊥) (st.2 ++ [x])
              (by rw [System.dom_fullyDefined]; simp))],
          st.2 ++ [x]) := by
  rw [connStep, Part.mem_bind_iff]
  constructor
  · rintro ⟨o, ho, hst'⟩
    rcases o with ⟨lbl, v0⟩ | ⟨lbl, x0⟩ <;> cases lbl <;>
      simp only [Part.mem_some_iff, Part.notMem_none, reduceCtorEq,
        Sum.inr.injEq] at hst'
    exact ⟨x0, ho, hst'⟩
  · rintro ⟨x, hmem, rfl⟩
    exact ⟨Sum.inr (InLabel.inside, x), hmem, by simp⟩


/-- A converter's next move, in the Definition 3.8 output alphabet: an inner
query is tagged `inside`, an outer answer `outside`.  This is the canonical
injection `X ⊕ V → COut V X` that every presentation of a converter lands in. -/
def moveOf (m : X ⊕ V) : COut V X :=
  match m with
  | Sum.inl x => Sum.inr (InLabel.inside, x)
  | Sum.inr v => Sum.inl (InLabel.outside, v)

@[simp] theorem moveOf_inl (x : X) :
    moveOf (Sum.inl x : X ⊕ V) = Sum.inr (InLabel.inside, x) := rfl

@[simp] theorem moveOf_inr (v : V) :
    moveOf (Sum.inr v : X ⊕ V) = Sum.inl (InLabel.outside, v) := rfl

end DDC

/-! ### CR18 §3.4.3: filters -/

/-- CR18 §3.4.3: a filter is a converter from `(X,Y)` systems to `(X,Y)`
systems. -/
abbrev Filter (X : Type z) (Y : Type v) : Type (max z v) :=
  DDC X Y X Y

namespace Filter

/-- Applying a filter to a DDS is the converter application from Definition 3.9,
specialized to filters. -/
noncomputable abbrev apply (φ : Filter X Y) (S : System.DDS X Y) :
    System.DDS X Y :=
  DDC.apply φ S

end Filter

def queryLimitOutputFrom (q : Nat) :
    Nat → Bool →
    List (((InLabel × X) ∪ₜ (InLabel × Option Y))) →
    Option (((InLabel × Y) ∪ₜ (InLabel × X)))
  | used, true, Sum.inl (InLabel.outside, x) :: rest =>
      if used < q then
        match rest with
        | [] => some (Sum.inr (InLabel.inside, x))
        | _ :: _ => queryLimitOutputFrom q (used + 1) false rest
      else
        none
  | used, false, Sum.inr (InLabel.inside, some y) :: rest =>
      match rest with
      | [] => some (Sum.inl (InLabel.outside, y))
      | _ :: _ => queryLimitOutputFrom q used true rest
  | _, _, _ => none

theorem queryLimitOutputFrom_prefix (q : Nat) :
    ∀ (l t : List (((InLabel × X) ∪ₜ (InLabel × Option Y)))) (used : Nat)
      (ready : Bool),
      l ≠ [] →
      (queryLimitOutputFrom (X := X) (Y := Y) q used ready (l ++ t)).isSome →
      (queryLimitOutputFrom (X := X) (Y := Y) q used ready l).isSome := by
  intro l
  induction l with
  | nil =>
      intro t used ready hne _
      exact False.elim (hne rfl)
  | cons a rest ih =>
      intro t used ready _ hsome
      cases ready
      · cases a with
        | inl p =>
            cases p with
            | mk side x =>
                cases side <;> simp [queryLimitOutputFrom] at hsome ⊢
        | inr p =>
            cases p with
            | mk side oy =>
                cases side <;> cases oy <;> simp [queryLimitOutputFrom] at hsome ⊢
                · cases rest with
                  | nil => simp
                  | cons b rest =>
                      exact ih t used true (by simp) hsome
      · cases a with
        | inl p =>
            cases p with
            | mk side x =>
                cases side
                · simp [queryLimitOutputFrom] at hsome ⊢
                · by_cases hlt : used < q
                  · simp [queryLimitOutputFrom, hlt] at hsome ⊢
                    cases rest with
                    | nil => simp
                    | cons b rest =>
                        exact ih t (used + 1) false (by simp) hsome
                  · simp [queryLimitOutputFrom, hlt] at hsome
        | inr p =>
            cases p with
            | mk side oy =>
                cases side <;> cases oy <;> simp [queryLimitOutputFrom] at hsome ⊢

/-- CR18 Definition 3.10: `[q]` restricts access to at most `q` queries.

As a DDC, `[q]` forwards the first `q` outside inputs to the inside system and
relays defined inside replies back outside. On the `(q+1)`-st outside input it
is undefined. -/
def queryLimit (q : Nat) : Filter X Y :=
  ⟨(fun l : List (((InLabel × X) ∪ₜ (InLabel × Option Y))) =>
      (⟨(queryLimitOutputFrom (X := X) (Y := Y) q 0 true l).isSome,
        fun h => (queryLimitOutputFrom (X := X) (Y := Y) q 0 true l).get h⟩ :
        Part (((InLabel × Y) ∪ₜ (InLabel × X))))),
    ⟨by simp [queryLimitOutputFrom], by
      intro l₁ l₂ hp hne hdom
      rcases hp with ⟨t, rfl⟩
      exact queryLimitOutputFrom_prefix (X := X) (Y := Y) q l₁ t 0 true hne hdom⟩⟩

/-- Alternating converter-side history produced by completed `[q]ᶠ` rounds.

UPSTREAM-CANDIDATE: trace normal form for proving that the operational query-limit converter realizes
the canonical DDS-level `System.filterQueries`. -/
def queryLimitTrace : List (X × Y) → List (DDC.CIn X Y)
  | [] => []
  | (x, y) :: t =>
      Sum.inl (InLabel.outside, x) :: Sum.inr (InLabel.inside, some y) :: queryLimitTrace t

theorem queryLimitTrace_append_single (t : List (X × Y)) (x : X) (y : Y) :
    queryLimitTrace (t ++ [(x, y)]) =
      queryLimitTrace t ++ [Sum.inl (InLabel.outside, x), Sum.inr (InLabel.inside, some y)] := by
  induction t with
  | nil => simp [queryLimitTrace]
  | cons p t ih =>
      cases p with
      | mk x0 y0 => simp [queryLimitTrace, ih]

theorem queryLimitOutputFrom_trace_query_from
    (q used : Nat) (t : List (X × Y)) (x : X) :
    queryLimitOutputFrom (X := X) (Y := Y) q used true
        (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)]) =
      if used + t.length < q then some (Sum.inr (InLabel.inside, x)) else none := by
  induction t generalizing used with
  | nil => by_cases h : used < q <;> simp [queryLimitTrace, queryLimitOutputFrom, h]
  | cons p t ih =>
      cases p with
      | mk x0 y0 =>
          by_cases h : used < q
          · have hne : queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)] ≠ [] := by simp
            cases hrest : queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)] with
            | nil => exact False.elim (hne hrest)
            | cons head tail =>
                have hrec := ih (used + 1)
                rw [hrest] at hrec
                simpa [queryLimitTrace, queryLimitOutputFrom, h, hrest, Nat.add_assoc,
                  Nat.add_left_comm, Nat.add_comm] using hrec
          · simp [queryLimitTrace, queryLimitOutputFrom, h]
            omega

theorem queryLimitOutputFrom_trace_query (q : Nat) (t : List (X × Y)) (x : X) :
    queryLimitOutputFrom (X := X) (Y := Y) q 0 true
        (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)]) =
      if t.length < q then some (Sum.inr (InLabel.inside, x)) else none := by
  simpa using queryLimitOutputFrom_trace_query_from (X := X) (Y := Y) q 0 t x

theorem queryLimitOutputFrom_trace_reply_from
    (q used : Nat) (t : List (X × Y)) (x : X) (y : Y) :
    queryLimitOutputFrom (X := X) (Y := Y) q used true
        (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
          Sum.inr (InLabel.inside, some y)]) =
      if used + t.length < q then some (Sum.inl (InLabel.outside, y)) else none := by
  induction t generalizing used with
  | nil => by_cases h : used < q <;> simp [queryLimitTrace, queryLimitOutputFrom, h]
  | cons p t ih =>
      cases p with
      | mk x0 y0 =>
          by_cases h : used < q
          · have hne :
              queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
                Sum.inr (InLabel.inside, some y)] ≠ [] := by simp
            cases hrest :
                queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
                  Sum.inr (InLabel.inside, some y)] with
            | nil => exact False.elim (hne hrest)
            | cons head tail =>
                have hrec := ih (used + 1)
                rw [hrest] at hrec
                simpa [queryLimitTrace, queryLimitOutputFrom, h, hrest, Nat.add_assoc,
                  Nat.add_left_comm, Nat.add_comm] using hrec
          · simp [queryLimitTrace, queryLimitOutputFrom, h]
            omega

theorem queryLimitOutputFrom_trace_reply
    (q : Nat) (t : List (X × Y)) (x : X) (y : Y) :
    queryLimitOutputFrom (X := X) (Y := Y) q 0 true
        (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
          Sum.inr (InLabel.inside, some y)]) =
      if t.length < q then some (Sum.inl (InLabel.outside, y)) else none := by
  simpa using queryLimitOutputFrom_trace_reply_from (X := X) (Y := Y) q 0 t x y

theorem queryLimitOutputFrom_trace_reply_none_from
    (q used : Nat) (t : List (X × Y)) (x : X) :
    queryLimitOutputFrom (X := X) (Y := Y) q used true
        (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
          Sum.inr (InLabel.inside, none)]) = none := by
  induction t generalizing used with
  | nil => by_cases h : used < q <;> simp [queryLimitTrace, queryLimitOutputFrom, h]
  | cons p t ih =>
      cases p with
      | mk x0 y0 =>
          by_cases h : used < q
          · have hne :
              queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
                Sum.inr (InLabel.inside, none)] ≠ [] := by simp
            cases hrest :
                queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
                  Sum.inr (InLabel.inside, none)] with
            | nil => exact False.elim (hne hrest)
            | cons head tail =>
                have hrec := ih (used + 1)
                rw [hrest] at hrec
                simpa [queryLimitTrace, queryLimitOutputFrom, h, hrest, Nat.add_assoc,
                  Nat.add_left_comm, Nat.add_comm] using hrec
          · simp [queryLimitTrace, queryLimitOutputFrom, h]

theorem queryLimit_trace_query_mem_iff
    (q : Nat) (t : List (X × Y)) (x : X)
    (o : ((InLabel × Y) ∪ₜ (InLabel × X))) :
    o ∈ (queryLimit q : Filter X Y).1
        (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)]) ↔
      t.length < q ∧ o = Sum.inr (InLabel.inside, x) := by
  change o ∈
      (⟨(queryLimitOutputFrom (X := X) (Y := Y) q 0 true
          (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)])).isSome,
        fun h => (queryLimitOutputFrom (X := X) (Y := Y) q 0 true
          (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)])).get h⟩ :
        Part ((InLabel × Y) ∪ₜ (InLabel × X))) ↔
      t.length < q ∧ o = Sum.inr (InLabel.inside, x)
  rw [queryLimitOutputFrom_trace_query]
  by_cases h : t.length < q <;> simp [h, eq_comm]

theorem queryLimit_trace_reply_mem_iff
    (q : Nat) (t : List (X × Y)) (x : X) (y : Y)
    (o : ((InLabel × Y) ∪ₜ (InLabel × X))) :
    o ∈ (queryLimit q : Filter X Y).1
        (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
          Sum.inr (InLabel.inside, some y)]) ↔
      t.length < q ∧ o = Sum.inl (InLabel.outside, y) := by
  change o ∈
      (⟨(queryLimitOutputFrom (X := X) (Y := Y) q 0 true
          (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
            Sum.inr (InLabel.inside, some y)])).isSome,
        fun h => (queryLimitOutputFrom (X := X) (Y := Y) q 0 true
          (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
            Sum.inr (InLabel.inside, some y)])).get h⟩ :
        Part ((InLabel × Y) ∪ₜ (InLabel × X))) ↔
      t.length < q ∧ o = Sum.inl (InLabel.outside, y)
  rw [queryLimitOutputFrom_trace_reply]
  by_cases h : t.length < q <;> simp [h, eq_comm]

theorem queryLimit_trace_reply_none_not_mem
    (q : Nat) (t : List (X × Y)) (x : X)
    (o : ((InLabel × Y) ∪ₜ (InLabel × X))) :
    o ∉ (queryLimit q : Filter X Y).1
        (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
          Sum.inr (InLabel.inside, none)]) := by
  change o ∉
      (⟨(queryLimitOutputFrom (X := X) (Y := Y) q 0 true
          (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
            Sum.inr (InLabel.inside, none)])).isSome,
        fun h => (queryLimitOutputFrom (X := X) (Y := Y) q 0 true
          (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
            Sum.inr (InLabel.inside, none)])).get h⟩ :
        Part ((InLabel × Y) ∪ₜ (InLabel × X)))
  rw [queryLimitOutputFrom_trace_reply_none_from]
  simp

-- UPSTREAM-CANDIDATE: generic `fullyDefined`/`keptPrefix` API for CR18 Def 3.3.
theorem output_fullyDefined_append_keptPrefix_of_mem
    (S : System.DDS X Y) (l : List X) (x : X)
    (hnext : System.keptPrefix S l ++ [x] ∈ System.dom S) :
    System.output S⊥ (l ++ [x]) (by
      rw [System.dom_fullyDefined]
      simp) =
      some (System.output S (System.keptPrefix S l ++ [x]) hnext) := by
  rw [System.output_fullyDefined]
  have hdrop : (l ++ [x]).dropLast = l := by simp
  have hlast : (l ++ [x]).getLast (by simp) = x := by simp
  rw [hdrop, hlast]
  dsimp
  have hnextRaw : System.keptPrefix S l ++ [x] ∈ PFun.Dom S.1 := by
    simpa [System.dom, System.toPFun] using hnext
  rw [dif_pos hnextRaw]

theorem queryLimit_resolve_round_mem_imp
    (q : Nat) (S : System.DDS X Y) (t : List (X × Y)) (xs : List X) (x : X)
    {r : Y × (List (DDC.CIn X Y) × List X)}
    (hr : r ∈ DDC.resolve (queryLimit q : Filter X Y) S
        (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)], xs)) :
    ∃ y, t.length < q ∧
      System.output S⊥ (xs ++ [x])
        (by rw [System.dom_fullyDefined]; simp) = some y ∧
      r = (y, (queryLimitTrace (t ++ [(x, y)]), xs ++ [x])) := by
  rw [DDC.resolve, PFun.mem_fix_iff] at hr
  rcases hr with hstop | hstep
  · rw [DDC.connStep, Part.mem_bind_iff] at hstop
    obtain ⟨o, ho, hsum⟩ := hstop
    rw [queryLimit_trace_query_mem_iff] at ho
    obtain ⟨_, rfl⟩ := ho
    simp at hsum
  · obtain ⟨a', hconn, hrec⟩ := hstep
    rw [DDC.connStep, Part.mem_bind_iff] at hconn
    obtain ⟨o, ho, hsum⟩ := hconn
    rw [queryLimit_trace_query_mem_iff] at ho
    obtain ⟨hbudget, rfl⟩ := ho
    simp at hsum
    subst a'
    rw [PFun.mem_fix_iff] at hrec
    rcases hrec with hstop2 | hstep2
    · rw [DDC.connStep, Part.mem_bind_iff] at hstop2
      obtain ⟨o, ho, hsum2⟩ := hstop2
      simp at ho
      split at ho
      · rename_i hcand
        rw [queryLimit_trace_reply_mem_iff] at ho
        obtain ⟨_, rfl⟩ := ho
        simp at hsum2
        subst r
        have hcand' : System.keptPrefix S xs ++ [x] ∈ System.dom S := by
          simpa [System.dom, List.dropLast_concat, List.getLast_concat] using hcand
        refine ⟨System.output S (System.keptPrefix S xs ++ [x]) hcand',
          hbudget, ?_, ?_⟩
        · exact output_fullyDefined_append_keptPrefix_of_mem S xs x hcand'
        · have hcand'' : System.keptPrefix S xs ++ [x] ∈ System.dom S := by
            simpa [System.dom, List.dropLast_concat, List.getLast_concat] using hcand
          have houtEq :
              System.output S (System.keptPrefix S xs ++ [x]) hcand'' =
                System.output S (System.keptPrefix S xs ++ [x]) hcand' := by
            exact System.output_congr S rfl hcand'' hcand'
          rw [dif_pos hcand]
          apply Prod.ext
          · exact System.output_congr S rfl _ hcand'
          · apply Prod.ext
            · rw [queryLimitTrace_append_single]
            · rfl
      · exact False.elim (queryLimit_trace_reply_none_not_mem q t x o ho)
    · obtain ⟨a', hconn2, _hrec2⟩ := hstep2
      rw [DDC.connStep, Part.mem_bind_iff] at hconn2
      obtain ⟨o, ho, hsum2⟩ := hconn2
      simp at ho
      split at ho
      · rw [queryLimit_trace_reply_mem_iff] at ho
        obtain ⟨_, rfl⟩ := ho
        simp at hsum2
      · exact False.elim (queryLimit_trace_reply_none_not_mem q t x o ho)

theorem queryLimit_resolve_round
    (q : Nat) (S : System.DDS X Y) (t : List (X × Y)) (xs : List X) (x : X) (y : Y)
    (hbudget : t.length < q)
    (hout : System.output S⊥ (xs ++ [x]) (by
        rw [System.dom_fullyDefined]
        simp) = some y) :
    (y, (queryLimitTrace (t ++ [(x, y)]), xs ++ [x])) ∈
      DDC.resolve (queryLimit q : Filter X Y) S
        (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)], xs) := by
  have hquery : Sum.inr (InLabel.inside, x) ∈
      (queryLimit q : Filter X Y).1 (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)]) := by
    simp [queryLimit, queryLimitOutputFrom_trace_query, hbudget]
  rw [DDC.resolve_in (queryLimit q : Filter X Y) S hquery]
  simpa [hout, queryLimitTrace_append_single, List.append_assoc] using
    (DDC.resolve_out (queryLimit q : Filter X Y) S
      (c := queryLimitTrace t ++ [Sum.inl (InLabel.outside, x),
        Sum.inr (InLabel.inside, some y)])
      (xs := xs ++ [x])
      (v := y)
      (by
        simp [queryLimit, queryLimitOutputFrom_trace_reply, hbudget]))

theorem queryLimit_driveFrom_suffix_apply
    (q : Nat) (S : System.DDS X Y) :
    ∀ (rest pref : List X) (t : List (X × Y))
      (_ : t.length = pref.length)
      (_ : pref ∈ System.dom S ∨ pref = [])
      (hfull : pref ++ rest ∈ System.dom S)
      (_ : pref.length + rest.length ≤ q)
      (_ : rest ≠ []),
      ∃ r ∈ DDC.driveFrom (queryLimit q : Filter X Y) S (queryLimitTrace t, pref) rest,
        r.1.getLast? = some (System.output S (pref ++ rest) hfull) := by
  intro rest
  induction rest with
  | nil =>
      intro _pref _t _htlen _hpref _hfull _hbudget hne
      exact False.elim (hne rfl)
  | cons x rest ih =>
      intro pref t htlen hpref hfull hbudget _hne
      have hnext : pref ++ [x] ∈ System.dom S := by
        exact System.prefix_closed S (by simp) (by simp) hfull
      have hbudgetRound : t.length < q := by
        rw [htlen]
        simp at hbudget
        omega
      let y := System.output S (pref ++ [x]) hnext
      have hout : System.output S⊥ (pref ++ [x]) (by
          rw [System.dom_fullyDefined]
          simp) = some y := by
        exact System.output_fullyDefined_append_of_mem S pref x hpref hnext
      have hround : (y, (queryLimitTrace (t ++ [(x, y)]), pref ++ [x])) ∈
          DDC.resolve (queryLimit q : Filter X Y) S
            (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)], pref) := by
        exact queryLimit_resolve_round q S t pref x y hbudgetRound hout
      cases rest with
      | nil =>
          refine ⟨([y], (queryLimitTrace (t ++ [(x, y)]), pref ++ [x])), ?_, ?_⟩
          · simp only [DDC.driveFrom, Part.mem_bind_iff, Part.mem_map_iff]
            refine ⟨(y, (queryLimitTrace (t ++ [(x, y)]), pref ++ [x])), hround,
              ([], (queryLimitTrace (t ++ [(x, y)]), pref ++ [x])), ?_, ?_⟩
            · simp
            · rfl
          · simp [y]
      | cons x' rest' =>
          have htlen' : (t ++ [(x, y)]).length = (pref ++ [x]).length := by
            simp [htlen]
          have hpref' : pref ++ [x] ∈ System.dom S ∨ pref ++ [x] = [] := Or.inl hnext
          have hfull' : (pref ++ [x]) ++ x' :: rest' ∈ System.dom S := by
            simpa [List.append_assoc] using hfull
          have hbudget' : (pref ++ [x]).length + (x' :: rest').length ≤ q := by
            simp at hbudget ⊢
            omega
          obtain ⟨rtail, htail, hlast⟩ :=
            ih (pref ++ [x]) (t ++ [(x, y)]) htlen' hpref' hfull' hbudget' (by simp)
          have hlast' :
              rtail.1.getLast? = some (System.output S (pref ++ x :: x' :: rest') hfull) := by
            rw [hlast]
            congr 1
            exact System.output_congr S (by simp [List.append_assoc]) hfull' hfull
          refine ⟨(y :: rtail.1, rtail.2), ?_, ?_⟩
          · change (y :: rtail.1, rtail.2) ∈
              (DDC.resolve (queryLimit q) S
                (queryLimitTrace t ++ [Sum.inl (InLabel.outside, x)], pref)).bind
                (fun r => (DDC.driveFrom (queryLimit q) S r.2 (x' :: rest')).map
                  fun rr => (r.1 :: rr.1, rr.2))
            refine Part.mem_bind_iff.mpr
              ⟨(y, (queryLimitTrace (t ++ [(x, y)]), pref ++ [x])), hround, ?_⟩
            rw [Part.mem_map_iff]
            exact ⟨rtail, htail, rfl⟩
          · cases hys : rtail.1 with
            | nil => simp [hys] at hlast'
            | cons y0 ys => simpa [hys] using hlast'

theorem queryLimit_driveFrom_suffix_apply_mem_imp
    (q : Nat) (S : System.DDS X Y) :
    ∀ (rest pref : List X) (t : List (X × Y))
      (_ : t.length = pref.length)
      (_ : pref ∈ System.dom S ∨ pref = [])
      {r : List Y × (List (DDC.CIn X Y) × List X)} {y : Y},
      r ∈ DDC.driveFrom (queryLimit q : Filter X Y) S (queryLimitTrace t, pref) rest →
      r.1.getLast? = some y →
      ∃ hfull : pref ++ rest ∈ System.dom S,
        pref.length + rest.length ≤ q ∧
          y = System.output S (pref ++ rest) hfull := by
  intro rest
  induction rest with
  | nil =>
      intro pref t htlen hpref r y hr hlast
      simp [DDC.driveFrom] at hr
      subst r
      simp at hlast
  | cons x rest ih =>
      intro pref t htlen hpref r y hr hlast
      simp only [DDC.driveFrom, Part.mem_bind_iff, Part.mem_map_iff] at hr
      obtain ⟨rround, hround, rtail, htail, rfl⟩ := hr
      obtain ⟨y0, hbudgetRound, houtFD, hroundEq⟩ :=
        queryLimit_resolve_round_mem_imp q S t pref x hround
      subst rround
      obtain ⟨hnext, houtS⟩ :=
        System.mem_of_output_fullyDefined_append_eq_some S pref x hpref houtFD
      cases rest with
      | nil =>
          simp [DDC.driveFrom] at htail
          subst rtail
          simp at hlast
          refine ⟨by simpa using hnext, ?_, ?_⟩
          · rw [htlen] at hbudgetRound
            simp at hbudgetRound ⊢
            omega
          · rw [← hlast, ← houtS]
      | cons x' rest' =>
          have htailLast : rtail.1.getLast? = some y := by
            have hlenTail :=
              DDC.driveFrom_length (queryLimit q : Filter X Y) S
                (queryLimitTrace (t ++ [(x, y0)]), pref ++ [x]) (x' :: rest') htail
            cases hys : rtail.1 with
            | nil => simp [hys] at hlenTail
            | cons y1 ys => simpa [hys] using hlast
          have htlen' : (t ++ [(x, y0)]).length = (pref ++ [x]).length := by
            simp [htlen]
          have hpref' : pref ++ [x] ∈ System.dom S ∨ pref ++ [x] = [] := Or.inl hnext
          obtain ⟨hfull', hbudget', houtFinal⟩ :=
            ih (pref ++ [x]) (t ++ [(x, y0)]) htlen' hpref' htail htailLast
          let hfull : pref ++ x :: x' :: rest' ∈ System.dom S := by
            simpa [List.append_assoc] using hfull'
          refine ⟨hfull, ?_, ?_⟩
          · simp at hbudget' ⊢
            omega
          · rw [houtFinal]
            exact System.output_congr S (by simp [List.append_assoc]) hfull' hfull

theorem queryLimit_applyRaw_mem_of_dom
    (q : Nat) (S : System.DDS X Y) {l : List X}
    (hdom : l ∈ System.dom S) (hbudget : l.length ≤ q) :
    System.output S l hdom ∈ DDC.applyRaw (queryLimit q : Filter X Y) S l := by
  have hne : l ≠ [] := by
    intro hl
    exact System.empty_not_mem S (by simpa [hl] using hdom)
  obtain ⟨r, hr, hlast⟩ :=
    queryLimit_driveFrom_suffix_apply q S l [] [] rfl (Or.inr rfl) hdom
      (by simpa using hbudget) hne
  exact (DDC.mem_apply_iff (queryLimit q : Filter X Y) S l (System.output S l hdom)).mpr
    ⟨r, hr, hlast⟩

theorem queryLimit_applyRaw_mem_iff
    (q : Nat) (S : System.DDS X Y) (l : List X) (y : Y) :
    y ∈ DDC.applyRaw (queryLimit q : Filter X Y) S l ↔
      ∃ hdom : l ∈ System.dom S,
        l.length ≤ q ∧ System.output S l hdom = y := by
  constructor
  · intro hy
    obtain ⟨r, hr, hlast⟩ :=
      (DDC.mem_apply_iff (queryLimit q : Filter X Y) S l y).mp hy
    obtain ⟨hdom, hbudget, hout⟩ :=
      queryLimit_driveFrom_suffix_apply_mem_imp q S l [] [] rfl (Or.inr rfl) hr hlast
    exact ⟨hdom, by simpa using hbudget, hout.symm⟩
  · rintro ⟨hdom, hbudget, hout⟩
    rw [← hout]
    exact queryLimit_applyRaw_mem_of_dom q S hdom hbudget

/-- CR18 notation for Definition 3.10. Use `([q]ᶠ) S` for `[q]S`. -/
scoped notation "[" q "]ᶠ" => queryLimit q

/-- Explicit query-count filter notation. This is an alias for `[q]ᶠ`; the
double brackets avoid confusion with Lean list notation when reading code. -/
scoped notation "⟦" q "⟧ᶠ" => queryLimit q

@[simp]
theorem queryCountFilter_notation (q : Nat) :
    (⟦q⟧ᶠ : Filter X Y) = ([q]ᶠ : Filter X Y) :=
  rfl

/-- CR18 §3.4.3 / Definition 3.10: the DDS obtained by applying the query
filter `[q]` is the canonical DDS-level restriction `System.filterQueries q`.
The converter object is `[q]ᶠ`; this name records its induced action on systems. -/
abbrev queryLimitApply (q : Nat) (S : System.DDS X Y) : System.DDS X Y :=
  System.filterQueries q S

/-- The converter-facing `[q]` action and the canonical DDS-level query filter are
the same operation. -/
@[simp] theorem queryLimitApply_eq_filterQueries (q : Nat) (S : System.DDS X Y) :
    queryLimitApply q S = System.filterQueries q S :=
  rfl

/-- CR18 Definition 3.10, operational form: applying the query-limit converter `[q]ᶠ`
to a DDS realizes the canonical DDS-level query restriction. -/
@[simp] theorem queryLimit_filter_apply_eq_filterQueries
    (q : Nat) (S : System.DDS X Y) :
    Filter.apply (queryLimit q : Filter X Y) S = System.filterQueries q S := by
  apply Subtype.ext
  funext l
  apply Part.ext'
  · constructor
    · intro hleft
      have hleftMem :
          ((Filter.apply (queryLimit q : Filter X Y) S).1 l).get hleft ∈
            DDC.applyRaw (queryLimit q : Filter X Y) S l := by
        simpa [Filter.apply, DDC.apply_toPFun] using
          (Part.get_mem hleft)
      obtain ⟨hdom, hbudget, _hout⟩ :=
        (queryLimit_applyRaw_mem_iff q S l
          (((Filter.apply (queryLimit q : Filter X Y) S).1 l).get hleft)).mp hleftMem
      exact ⟨hdom, hbudget⟩
    · intro hright
      have hdom : l ∈ System.dom S := hright.1
      have hbudget : l.length ≤ q := hright.2
      change (DDC.applyRaw (queryLimit q : Filter X Y) S l).Dom
      rw [Part.dom_iff_mem]
      exact ⟨System.output S l hdom, by
        exact queryLimit_applyRaw_mem_of_dom q S hdom hbudget⟩
  · intro h₁ h₂
    have hleftMem :
        ((Filter.apply (queryLimit q : Filter X Y) S).1 l).get h₁ ∈
          DDC.applyRaw (queryLimit q : Filter X Y) S l := by
      simpa [Filter.apply, DDC.apply_toPFun] using
        (Part.get_mem h₁)
    obtain ⟨hdom, _hbudget, houtLeft⟩ :=
      (queryLimit_applyRaw_mem_iff q S l
        (((Filter.apply (queryLimit q : Filter X Y) S).1 l).get h₁)).mp hleftMem
    have hrightDom : l ∈ System.dom (System.filterQueries q S) := h₂
    have hrightBase : l ∈ System.dom S :=
      ((System.mem_dom_filterQueries q S l).mp hrightDom).1
    calc
      ((Filter.apply (queryLimit q : Filter X Y) S).1 l).get h₁
          = System.output S l hdom := houtLeft.symm
      _ = System.output S l hrightBase := System.output_congr S rfl hdom hrightBase
      _ = ((System.filterQueries q S).1 l).get h₂ := by
            rfl

@[simp]
theorem queryLimitApply_dom (q : Nat) (S : System.DDS X Y) (l : List X) :
    l ∈ System.dom (queryLimitApply q S) ↔
      l ∈ System.dom S ∧ l.length ≤ q :=
  System.mem_dom_filterQueries q S l

@[simp]
theorem queryLimitApply_output (q : Nat) (S : System.DDS X Y)
    (l : List X) (h : l ∈ System.dom (queryLimitApply q S)) :
    System.output (queryLimitApply q S) l h =
      System.output S l ((queryLimitApply_dom q S l).mp h).1 :=
  rfl

/-- CR18 Definition 3.10: `[q]S` is undefined on every DDS input history with
more than `q` queries. -/
theorem queryLimitApply_undefined_of_length_gt (q : Nat) (S : System.DDS X Y)
    {l : List X} (hlen : q < l.length) :
    l ∉ System.dom (queryLimitApply q S) := by
  intro h
  exact (not_le_of_gt hlen) ((queryLimitApply_dom q S l).mp h).2

/-- CR18 Definition 3.10, paper-facing form: `[q]S` is undefined at the
`(q+1)`-st query. -/
theorem queryLimitApply_undefined_at_query_succ (q : Nat) (S : System.DDS X Y)
    {l : List X} (hlen : l.length = q + 1) :
    l ∉ System.dom (queryLimitApply q S) := by
  apply queryLimitApply_undefined_of_length_gt q S
  omega

theorem queryLimit_first_query_output (q : Nat) (x : X) (h : 0 < q) :
    System.output (([q]ᶠ : Filter X Y)) [Sum.inl (InLabel.outside, x)]
      (by
        change (queryLimitOutputFrom (X := X) (Y := Y) q 0 true
          [Sum.inl (InLabel.outside, x)]).isSome
        simp [queryLimitOutputFrom, h]) =
      Sum.inr (InLabel.inside, x) :=
  by simp [System.output, queryLimit, queryLimitOutputFrom, h]

theorem queryLimit_first_query_undefined (x : X) :
    [Sum.inl (InLabel.outside, x)] ∉
      System.dom (([0]ᶠ : Filter X Y)) := by
  change ¬ (queryLimitOutputFrom (X := X) (Y := Y) 0 0 true
    [Sum.inl (InLabel.outside, x)]).isSome
  simp [queryLimitOutputFrom]

theorem queryLimit_reply_output (q : Nat) (x : X) (y : Y) (h : 0 < q) :
    System.output (([q]ᶠ : Filter X Y))
      [Sum.inl (InLabel.outside, x), Sum.inr (InLabel.inside, some y)]
      (by
        change (queryLimitOutputFrom (X := X) (Y := Y) q 0 true
          [Sum.inl (InLabel.outside, x), Sum.inr (InLabel.inside, some y)]).isSome
        simp [queryLimitOutputFrom, h]) =
      Sum.inl (InLabel.outside, y) :=
  by simp [System.output, queryLimit, queryLimitOutputFrom, h]

end Converter

/-! ### CR18 §3.4.4 / Definition 3.11: cascade -/

namespace System

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- Internal construction for CR18 Definition 3.11: the list
`[S(x₁), S(x₁,x₂), ..., S(x₁,...,xₖ)]`. The paper names its entries `yⱼ`;
the public API below exposes only cascade itself. -/
def cascadeMiddle (S : DDS X Y) (l : List X) (h : l ∈ dom S) : List Y :=
  (List.finRange l.length).map fun j =>
    output S (l.take (j.val + 1)) (by
      have hprefix : l.take (j.val + 1) <+: l := List.take_prefix (j.val + 1) l
      have hle : j.val + 1 ≤ l.length := Nat.succ_le_of_lt j.isLt
      have hne : l.take (j.val + 1) ≠ [] := by
        intro hnil
        have hlen : (l.take (j.val + 1)).length = j.val + 1 := by
          rw [List.length_take, Nat.min_eq_left hle]
        simp [hnil] at hlen
      exact prefix_closed S hprefix hne h)

@[simp]
theorem cascadeMiddle_length (S : DDS X Y) (l : List X) (h : l ∈ dom S) :
    (cascadeMiddle S l h).length = l.length := by
  simp [cascadeMiddle]

theorem cascadeMiddle_getElem (S : DDS X Y) (l : List X) (h : l ∈ dom S)
    (j : Nat) (hj : j < (cascadeMiddle S l h).length) :
    (cascadeMiddle S l h)[j] =
      output S (l.take (j + 1))
        (prefix_closed S (List.take_prefix (j + 1) l)
          (by
            have hjl : j < l.length := by simpa [cascadeMiddle] using hj
            have hlen : (l.take (j + 1)).length = j + 1 := by
              rw [List.length_take, Nat.min_eq_left (by omega)]
            intro hnil
            simp [hnil] at hlen) h) := by
  simp only [cascadeMiddle, List.getElem_map, List.getElem_finRange, Fin.cast_mk]

theorem cascadeMiddle_congr (S : DDS X Y) {l₁ l₂ : List X} (hl : l₁ = l₂)
    (h₁ : l₁ ∈ dom S) (h₂ : l₂ ∈ dom S) :
    cascadeMiddle S l₁ h₁ = cascadeMiddle S l₂ h₂ := by
  subst hl
  apply List.ext_getElem
  · simp
  · intro j hj₁ hj₂
    rw [cascadeMiddle_getElem S l₁ h₁ j hj₁]

theorem cascadeMiddle_prefix (S : DDS X Y) {l₁ l₂ : List X}
    (h₁ : l₁ ∈ dom S) (h₂ : l₂ ∈ dom S) (hp : l₁ <+: l₂) :
    cascadeMiddle S l₁ h₁ <+: cascadeMiddle S l₂ h₂ := by
  have hlen : l₁.length ≤ l₂.length := hp.length_le
  refine List.prefix_iff_eq_take.2 ?_
  apply List.ext_getElem
  · rw [cascadeMiddle_length, List.length_take, cascadeMiddle_length, Nat.min_eq_left hlen]
  · intro j hj1 hj2
    have hj1' : j < l₁.length := by
      have : j < (cascadeMiddle S l₁ h₁).length := hj1
      rwa [cascadeMiddle_length] at this
    have hj2' : j < l₂.length := by omega
    rw [cascadeMiddle_getElem S l₁ h₁ j hj1]
    rw [List.getElem_take]
    rw [cascadeMiddle_getElem S l₂ h₂ j (by rw [cascadeMiddle_length]; exact hj2')]
    have htake : l₁.take (j + 1) = l₂.take (j + 1) := by
      have hpt : l₁.take (j + 1) <+: l₂.take (j + 1) := hp.take (j + 1)
      have hlen1 : (l₁.take (j + 1)).length = j + 1 := by
        rw [List.length_take]
        omega
      have hlen2 : (l₂.take (j + 1)).length = j + 1 := by
        rw [List.length_take]
        omega
      exact List.IsPrefix.eq_of_length_le hpt (by rw [hlen1, hlen2])
    exact output_congr S htake _ _

theorem cascadeMiddle_ne_nil (S : DDS X Y) (l : List X) (h : l ∈ dom S) :
    cascadeMiddle S l h ≠ [] := by
  intro hnil
  have hlen : (cascadeMiddle S l h).length = 0 := by simp [hnil]
  rw [cascadeMiddle_length] at hlen
  have hl : l = [] := List.length_eq_zero_iff.mp hlen
  exact empty_not_mem S (by simpa [hl] using h)

/-- CR18 Definition 3.11: native DDS-level cascade. -/
noncomputable def cascade (S : DDS X Y) (T : DDS Y Z) : DDS X Z :=
  ⟨(fun l : List X =>
      (⟨∃ hS : l ∈ dom S, cascadeMiddle S l hS ∈ dom T,
        fun h =>
          output T (cascadeMiddle S l (Classical.choose h))
            (Classical.choose_spec h)⟩ : Part Z)),
    ⟨by
      intro h
      rcases h with ⟨hS, _⟩
      exact empty_not_mem S hS,
    by
      intro l₁ l₂ hp hne hdom
      rcases hdom with ⟨hS₂, hT₂⟩
      let hS₁ : l₁ ∈ dom S := prefix_closed S hp hne hS₂
      exact ⟨hS₁,
        prefix_closed T (cascadeMiddle_prefix S hS₁ hS₂ hp)
          (cascadeMiddle_ne_nil S l₁ hS₁) hT₂⟩⟩⟩

/-- PFun-native CR18 cascade notation. The subscript avoids colliding with the
existing compatibility-layer `⊲` notation. -/
scoped infixl:70 " ⊲ₚ " => cascade

/-! ### CR18 §3.4.5 / Definition 3.12: output-combine -/

variable {Y' : Type v}

/-- CR18 Definition 3.12: combine the outputs of two `(X,Y)` DDSs.

The combined DDS is defined exactly where both systems are defined, and on such
a history returns `op (S l) (T l)`. -/
def combine (op : Y' → Y' → Y') (S T : DDS X Y') : DDS X Y' :=
  ⟨(fun l : List X =>
      (⟨l ∈ dom S ∧ l ∈ dom T,
        fun h => op (output S l h.1) (output T l h.2)⟩ : Part Y')),
    ⟨by
      intro h
      exact empty_not_mem S h.1,
    by
      intro l₁ l₂ hp hne hdom
      exact ⟨prefix_closed S hp hne hdom.1,
        prefix_closed T hp hne hdom.2⟩⟩⟩

/-- PFun-native CR18 output-combine notation. The operation is explicit because
Lean has no ambient meaning for Maurer's schematic `⋆`. -/
scoped notation:70 S:71 " ⋆ₚ[" op "] " T:70 => combine op S T

@[simp]
theorem combine_dom (op : Y' → Y' → Y') (S T : DDS X Y') (l : List X) :
    l ∈ dom (combine op S T) ↔ l ∈ dom S ∧ l ∈ dom T :=
  Iff.rfl

@[simp]
theorem combine_output (op : Y' → Y' → Y') (S T : DDS X Y')
    (l : List X) (h : l ∈ dom (combine op S T)) :
    output (combine op S T) l h =
      op (output S l ((combine_dom op S T l).mp h).1)
        (output T l ((combine_dom op S T l).mp h).2) :=
  rfl

end System

namespace Converter

variable {X : Type z} {Y : Type v} {Z : Type w}

namespace Cascade

/-- One local prefix phase of the CR18 `casc` converter. -/
def stepOutput?
    : List (((InLabel × X) ∪ₜ (InLabel × Option (Y ∪ₜ Z)))) →
      Option (((InLabel × Z) ∪ₜ (InLabel × (X ∪ₜ Y))))
  | [] => none
  | Sum.inl (InLabel.outside, x) :: rest =>
      match rest with
      | [] => some (Sum.inr (InLabel.inside, Sum.inl x))
      | Sum.inr (InLabel.inside, some (Sum.inl y)) :: rest' =>
          match rest' with
          | [] => some (Sum.inr (InLabel.inside, Sum.inr y))
          | Sum.inr (InLabel.inside, some (Sum.inr z)) :: rest'' =>
              match rest'' with
              | [] => some (Sum.inl (InLabel.outside, z))
              | Sum.inl (InLabel.outside, _) :: _ => stepOutput? rest''
              | _ => none
          | _ => none
      | _ => none
  | _ => none

/-- Accepted converter histories for `casc`: every nonempty prefix is in the
right phase of the three-step protocol. -/
def Valid (l : List (((InLabel × X) ∪ₜ (InLabel × Option (Y ∪ₜ Z))))) : Prop :=
  l ≠ [] ∧ ∀ p, p ≠ [] → p <+: l → (stepOutput? p).isSome

theorem valid_prefix
    {l₁ l₂ : List (((InLabel × X) ∪ₜ (InLabel × Option (Y ∪ₜ Z))))}
    (hp : l₁ <+: l₂) (hne : l₁ ≠ []) (h : Valid l₂) :
    Valid l₁ := by
  exact ⟨hne, fun p hpne hpp => h.2 p hpne (List.IsPrefix.trans hpp hp)⟩

def roundsTrace :
    List (X × Y × Z) →
      List (((InLabel × X) ∪ₜ (InLabel × Option (Y ∪ₜ Z))))
  | [] => []
  | (x, y, z) :: r =>
      Sum.inl (InLabel.outside, x) ::
      Sum.inr (InLabel.inside, some (Sum.inl y)) ::
      Sum.inr (InLabel.inside, some (Sum.inr z)) ::
      roundsTrace r

def roundsInner : List (X × Y × Z) → List (X ∪ₜ Y)
  | [] => []
  | (x, y, _) :: r => Sum.inl x :: Sum.inr y :: roundsInner r

def roundsInputs (r : List (X × Y × Z)) : List X :=
  r.map fun p => p.1

def roundsMiddle (r : List (X × Y × Z)) : List Y :=
  r.map fun p => p.2.1

def roundsOutputs (r : List (X × Y × Z)) : List Z :=
  r.map fun p => p.2.2

theorem roundsTrace_append (r₁ r₂ : List (X × Y × Z)) :
    roundsTrace (r₁ ++ r₂) = roundsTrace r₁ ++ roundsTrace r₂ := by
  induction r₁ with
  | nil => rfl
  | cons p r ih =>
      obtain ⟨x, y, z⟩ := p
      simp [roundsTrace, ih]

theorem roundsInner_append (r₁ r₂ : List (X × Y × Z)) :
    roundsInner (r₁ ++ r₂) = roundsInner r₁ ++ roundsInner r₂ := by
  induction r₁ with
  | nil => rfl
  | cons p r ih =>
      obtain ⟨x, y, z⟩ := p
      simp [roundsInner, ih]

theorem roundsInputs_append (r₁ r₂ : List (X × Y × Z)) :
    roundsInputs (r₁ ++ r₂) = roundsInputs r₁ ++ roundsInputs r₂ := by
  simp [roundsInputs, List.map_append]

theorem roundsMiddle_append (r₁ r₂ : List (X × Y × Z)) :
    roundsMiddle (r₁ ++ r₂) = roundsMiddle r₁ ++ roundsMiddle r₂ := by
  simp [roundsMiddle, List.map_append]

theorem roundsOutputs_append (r₁ r₂ : List (X × Y × Z)) :
    roundsOutputs (r₁ ++ r₂) = roundsOutputs r₁ ++ roundsOutputs r₂ := by
  simp [roundsOutputs, List.map_append]

theorem stepOutput?_roundsTrace_append (r : List (X × Y × Z))
    {x : X}
    {tail : List (((InLabel × X) ∪ₜ (InLabel × Option (Y ∪ₜ Z))))}
    (htail : tail.head? = some (Sum.inl (InLabel.outside, x))) :
    stepOutput? (X := X) (Y := Y) (Z := Z) (roundsTrace r ++ tail) =
      stepOutput? (X := X) (Y := Y) (Z := Z) tail := by
  induction r with
  | nil =>
      simp [roundsTrace]
  | cons p r ih =>
      obtain ⟨a, b, c⟩ := p
      obtain ⟨x', rest', heq⟩ :
          ∃ (x' : X)
            (rest' : List (((InLabel × X) ∪ₜ (InLabel × Option (Y ∪ₜ Z))))),
            roundsTrace r ++ tail = Sum.inl (InLabel.outside, x') :: rest' := by
        cases r with
        | nil =>
            cases tail with
            | nil =>
                simp at htail
            | cons i tl =>
                have hi : i = Sum.inl (InLabel.outside, x) := by
                  simpa using htail
                exact ⟨x, tl, by simp [roundsTrace, hi]⟩
        | cons q r' =>
            obtain ⟨a', b', c'⟩ := q
            exact ⟨a',
              Sum.inr (InLabel.inside, some (Sum.inl b')) ::
              Sum.inr (InLabel.inside, some (Sum.inr c')) ::
              (roundsTrace r' ++ tail), by simp [roundsTrace]⟩
      rw [show roundsTrace ((a, b, c) :: r) ++ tail =
          Sum.inl (InLabel.outside, a) ::
          Sum.inr (InLabel.inside, some (Sum.inl b)) ::
          Sum.inr (InLabel.inside, some (Sum.inr c)) ::
          (roundsTrace r ++ tail) from by simp [roundsTrace], heq]
      rw [show stepOutput? (X := X) (Y := Y) (Z := Z)
            (Sum.inl (InLabel.outside, a) ::
            Sum.inr (InLabel.inside, some (Sum.inl b)) ::
            Sum.inr (InLabel.inside, some (Sum.inr c)) ::
            Sum.inl (InLabel.outside, x') :: rest') =
          stepOutput? (X := X) (Y := Y) (Z := Z)
            (Sum.inl (InLabel.outside, x') :: rest') from by
        simp [stepOutput?]]
      rw [← heq]
      exact ih

end Cascade

/-- CR18 Definition 3.11: the deterministic converter `casc`, with outside
interface `(X,Z)` and inner parallel access to `(X,Y)` and `(Y,Z)` systems. -/
def cascadeConverter : DDC X Z (X ∪ₜ Y) (Y ∪ₜ Z) :=
  ⟨(fun l : List (((InLabel × X) ∪ₜ (InLabel × Option (Y ∪ₜ Z)))) =>
      (⟨Cascade.Valid l,
        fun h => (Cascade.stepOutput? l).get (h.2 l h.1 (List.prefix_refl l))⟩ :
        Part (((InLabel × Z) ∪ₜ (InLabel × (X ∪ₜ Y)))))),
    ⟨by simp [Cascade.Valid], by
      intro l₁ l₂ hp hne hdom
      exact Cascade.valid_prefix hp hne hdom⟩⟩

/-- CR18 notation for the `casc` converter. -/
scoped notation "cascᶜ" => cascadeConverter

/-- Projection of the inner parallel-access history to the left system. -/
def cascadeLeftHistory (l : List (X ∪ₜ Y)) : List X :=
  l.filterMap fun q =>
    match q with
    | Sum.inl x => some x
    | Sum.inr _ => none

/-- Projection of the inner parallel-access history to the right system. -/
def cascadeRightHistory (l : List (X ∪ₜ Y)) : List Y :=
  l.filterMap fun q =>
    match q with
    | Sum.inl _ => none
    | Sum.inr y => some y

theorem cascadeLeftHistory_append (l₁ l₂ : List (X ∪ₜ Y)) :
    cascadeLeftHistory (l₁ ++ l₂) =
      cascadeLeftHistory l₁ ++ cascadeLeftHistory l₂ :=
  List.filterMap_append

theorem cascadeRightHistory_append (l₁ l₂ : List (X ∪ₜ Y)) :
    cascadeRightHistory (l₁ ++ l₂) =
      cascadeRightHistory l₁ ++ cascadeRightHistory l₂ :=
  List.filterMap_append

theorem cascadeLeftHistory_roundsInner (r : List (X × Y × Z)) :
    cascadeLeftHistory (Cascade.roundsInner r) = Cascade.roundsInputs r := by
  induction r with
  | nil => rfl
  | cons p r ih =>
      obtain ⟨x, y, z⟩ := p
      simp [Cascade.roundsInner, Cascade.roundsInputs, cascadeLeftHistory]
      simpa [cascadeLeftHistory, Cascade.roundsInputs] using ih

theorem cascadeRightHistory_roundsInner (r : List (X × Y × Z)) :
    cascadeRightHistory (Cascade.roundsInner r) = Cascade.roundsMiddle r := by
  induction r with
  | nil => rfl
  | cons p r ih =>
      obtain ⟨x, y, z⟩ := p
      simp [Cascade.roundsInner, Cascade.roundsMiddle, cascadeRightHistory]
      simpa [cascadeRightHistory, Cascade.roundsMiddle] using ih

/-- Local domain condition for the inner DDS giving `casc` parallel access to
`S` and `T`. -/
def cascadeAccessStep (S : System.DDS X Y) (T : System.DDS Y Z)
    (p : List (X ∪ₜ Y)) : Prop :=
  match p.getLast? with
  | some (Sum.inl _) => cascadeLeftHistory p ∈ System.dom S
  | some (Sum.inr _) => cascadeRightHistory p ∈ System.dom T
  | none => False

/-- The single inner DDS representing parallel access to `S` and `T` for
`casc[S,T]`. -/
noncomputable def cascadeAccess (S : System.DDS X Y) (T : System.DDS Y Z) :
    System.DDS (X ∪ₜ Y) (Y ∪ₜ Z) :=
  ⟨(fun l : List (X ∪ₜ Y) =>
      (⟨l ≠ [] ∧ ∀ p, p ≠ [] → p <+: l → cascadeAccessStep S T p,
        fun h =>
          match hlast : l.getLast? with
          | some (Sum.inl _) =>
              Sum.inl (System.output S (cascadeLeftHistory l) (by
                simpa [cascadeAccessStep, hlast] using h.2 l h.1 (List.prefix_refl l)))
          | some (Sum.inr _) =>
              Sum.inr (System.output T (cascadeRightHistory l) (by
                simpa [cascadeAccessStep, hlast] using h.2 l h.1 (List.prefix_refl l)))
          | none =>
              False.elim (h.1 (List.getLast?_eq_none_iff.mp hlast))⟩ :
        Part (Y ∪ₜ Z))),
    ⟨by simp, by
      intro l₁ l₂ hp hne hdom
      exact ⟨hne, fun p hpne hpp => hdom.2 p hpne (List.IsPrefix.trans hpp hp)⟩⟩⟩

theorem cascadeAccess_dom_snoc (S : System.DDS X Y) (T : System.DDS Y Z)
    {p : List (X ∪ₜ Y)} {a : X ∪ₜ Y}
    (hp : p = [] ∨ p ∈ System.dom (cascadeAccess S T))
    (hstep : cascadeAccessStep S T (p ++ [a])) :
    p ++ [a] ∈ System.dom (cascadeAccess S T) := by
  refine ⟨by simp, ?_⟩
  intro q hqne hqpre
  rcases List.prefix_concat_iff.mp hqpre with hq | hq
  · subst hq
    exact hstep
  · rcases hp with rfl | hp
    · exact absurd (List.prefix_nil.mp hq) hqne
    · exact hp.2 q hqne hq

theorem cascadeAccess_output_inl (S : System.DDS X Y) (T : System.DDS Y Z)
    {p : List (X ∪ₜ Y)} (h : p ∈ System.dom (cascadeAccess S T)) {x : X}
    (hlast : p.getLast? = some (Sum.inl x))
    (hL : cascadeLeftHistory p ∈ System.dom S) :
    System.output (cascadeAccess S T) p h =
      Sum.inl (System.output S (cascadeLeftHistory p) hL) := by
  simp [cascadeAccess, System.output]
  split <;> rename_i heq
  · rfl
  · rw [hlast] at heq
    cases heq
  · rw [hlast] at heq
    cases heq

theorem cascadeAccess_output_inr (S : System.DDS X Y) (T : System.DDS Y Z)
    {p : List (X ∪ₜ Y)} (h : p ∈ System.dom (cascadeAccess S T)) {y : Y}
    (hlast : p.getLast? = some (Sum.inr y))
    (hR : cascadeRightHistory p ∈ System.dom T) :
    System.output (cascadeAccess S T) p h =
      Sum.inr (System.output T (cascadeRightHistory p) hR) := by
  simp [cascadeAccess, System.output]
  split <;> rename_i heq
  · rw [hlast] at heq
    cases heq
  · rfl
  · rw [hlast] at heq
    cases heq

/-- CR18 §3.4.4 converter-side construction: `casc[S,T]`.

At the paper-facing PFun layer, converter application is the mathematical
partial function induced by the converter. For the cascade converter this is
the native cascade partial function itself; the raw labeled-history converter
above is only a representation of the same converter, not the abstraction used
to state Definition 3.11. -/
noncomputable def cascadeViaConverter
    (S : System.DDS X Y) (T : System.DDS Y Z) : System.DDS X Z :=
  System.cascade S T

scoped notation "cascᶜ[" S "," T "]" => cascadeViaConverter S T

/-- CR18 Definition 3.11, DDS-level converter equation:
`casc[S,T] = S ⊲ T`.

NOTE: this is `rfl` only because `cascadeViaConverter` is *defined* as the
native cascade.  The honest converter equation — Def 3.9 application of the
actual Def 3.8 object — is `apply_cascadeStep` (`CascadeRealization.lean`):
`DDC.apply (ofStep cascadeStep) (cascadeAccess S T) = S ⊲ₚ T`. -/
theorem cascadeViaConverter_eq_cascade
    (S : System.DDS X Y) (T : System.DDS Y Z) :
    cascadeViaConverter S T = System.cascade S T := by
  rfl

/-! ### CR18 §3.4.5 / Definition 3.12: output-combine converter -/

namespace Combine

/-- One local prefix phase of the CR18 `comb⋆` converter. -/
def stepOutput? (op : Y → Y → Y) :
    List ((InLabel × X) ∪ₜ (InLabel × Option (Sigma (fun _ : Fin 2 => Y)))) →
      Option ((InLabel × Y) ∪ₜ (InLabel × Sigma (fun _ : Fin 2 => X)))
  | [] => none
  | Sum.inl (InLabel.outside, x) :: rest =>
      match rest with
      | [] => some (Sum.inr (InLabel.inside, ⟨(0 : Fin 2), x⟩))
      | Sum.inr (InLabel.inside, some ⟨i₁, y₁⟩) :: rest' =>
          if i₁ = (0 : Fin 2) then
            match rest' with
            | [] => some (Sum.inr (InLabel.inside, ⟨(1 : Fin 2), x⟩))
            | Sum.inr (InLabel.inside, some ⟨i₂, y₂⟩) :: rest'' =>
                if i₂ = (1 : Fin 2) then
                  match rest'' with
                  | [] => some (Sum.inl (InLabel.outside, op y₁ y₂))
                  | Sum.inl (InLabel.outside, _) :: _ => stepOutput? op rest''
                  | _ => none
                else
                  none
            | _ => none
          else
            none
      | _ => none
  | _ => none

/-- Accepted converter histories for `comb⋆`: every nonempty prefix is in the
right phase of the three-step protocol. -/
def Valid (op : Y → Y → Y)
    (l : List ((InLabel × X) ∪ₜ
      (InLabel × Option (Sigma (fun _ : Fin 2 => Y))))) :
    Prop :=
  (stepOutput? (X := X) op l).isSome

theorem valid_prefix (op : Y → Y → Y)
    {l₁ l₂ : List ((InLabel × X) ∪ₜ
      (InLabel × Option (Sigma (fun _ : Fin 2 => Y))))}
    (hp : l₁ <+: l₂) (hne : l₁ ≠ []) (h : Valid (X := X) op l₂) :
    Valid (X := X) op l₁ := by
  induction l₂ using stepOutput?.induct generalizing l₁ with
  | case1 =>
      exact absurd (List.prefix_nil.mp hp) hne
  | case2 x =>
      rcases List.prefix_cons_iff.mp hp with rfl | ⟨t, rfl, ht⟩
      · exact absurd rfl hne
      · obtain rfl := List.prefix_nil.mp ht
        simp [Valid, stepOutput?]
  | case3 x y₁ =>
      rcases List.prefix_cons_iff.mp hp with rfl | ⟨t, rfl, ht⟩
      · exact absurd rfl hne
      · rcases List.prefix_cons_iff.mp ht with rfl | ⟨t', rfl, ht'⟩
        · simp [Valid, stepOutput?]
        · obtain rfl := List.prefix_nil.mp ht'
          simp [Valid, stepOutput?]
  | case4 x y₁ y₂ =>
      rcases List.prefix_cons_iff.mp hp with rfl | ⟨t, rfl, ht⟩
      · exact absurd rfl hne
      · rcases List.prefix_cons_iff.mp ht with rfl | ⟨t', rfl, ht'⟩
        · simp [Valid, stepOutput?]
        · rcases List.prefix_cons_iff.mp ht' with rfl | ⟨t'', rfl, ht''⟩
          · simp [Valid, stepOutput?]
          · obtain rfl := List.prefix_nil.mp ht''
            simp [Valid, stepOutput?]
  | case5 x y₁ y₂ x' rest ih =>
      rcases List.prefix_cons_iff.mp hp with rfl | ⟨t, rfl, ht⟩
      · exact absurd rfl hne
      · rcases List.prefix_cons_iff.mp ht with rfl | ⟨t', rfl, ht'⟩
        · simp [Valid, stepOutput?]
        · rcases List.prefix_cons_iff.mp ht' with rfl | ⟨t'', rfl, ht''⟩
          · simp [Valid, stepOutput?]
          · by_cases htEmpty : t'' = []
            · subst t''
              simp [Valid, stepOutput?]
            · have hrest :
                Valid (X := X) op (Sum.inl (InLabel.outside, x') :: rest) := by
                simpa [Valid, stepOutput?] using h
              have htail : Valid (X := X) op t'' := ih ht'' htEmpty hrest
              rcases List.prefix_cons_iff.mp ht'' with rfl | ⟨tail, rfl, _⟩
              · exact False.elim (htEmpty rfl)
              · simpa [Valid, stepOutput?] using htail
  | case6 x y₁ y₂ y' rest =>
      simp [Valid, stepOutput?] at h
  | case7 x y₁ y₂ rest rest'' hne₂ =>
      simp [Valid, stepOutput?, hne₂] at h
  | case8 x y₁ i₂ y₂ =>
      simp [Valid, stepOutput?] at h
  | case9 x y₁ rest rest'' hne₁ =>
      exfalso
      fin_cases y₁
      · exact hne₁ rfl
      · have h10 : ¬ ((1 : Fin 2) = 0) := by decide
        cases rest'' with
        | nil =>
            simp [Valid, stepOutput?, h10] at h
        | cons head tail =>
            cases head with
            | inl p =>
                cases p
                simp [Valid, stepOutput?, h10] at h
            | inr p =>
                cases p
                rename_i side oy
                cases side <;> cases oy <;> simp [Valid, stepOutput?, h10] at h
  | case10 x i₁ y₁ =>
      simp [Valid, stepOutput?] at h
  | case11 i rest =>
      simp [Valid, stepOutput?] at h

def pair (S T : System.DDS X Y) :
    (i : Fin 2) → System.DDS ((fun _ : Fin 2 => X) i) ((fun _ : Fin 2 => Y) i) :=
  fun i => if i = (0 : Fin 2) then S else T

def roundsTrace :
    List (X × Y × Y) →
      List ((InLabel × X) ∪ₜ (InLabel × Option (Sigma (fun _ : Fin 2 => Y))))
  | [] => []
  | (x, y₁, y₂) :: r =>
      Sum.inl (InLabel.outside, x) ::
      Sum.inr (InLabel.inside, some ⟨(0 : Fin 2), y₁⟩) ::
      Sum.inr (InLabel.inside, some ⟨(1 : Fin 2), y₂⟩) ::
      roundsTrace r

def roundsInner :
    List (X × Y × Y) → List (Sigma (fun _ : Fin 2 => X))
  | [] => []
  | (x, _y₁, _y₂) :: r =>
      ⟨(0 : Fin 2), x⟩ :: ⟨(1 : Fin 2), x⟩ :: roundsInner r

def roundsInputs (r : List (X × Y × Y)) : List X :=
  r.map fun p => p.1

def roundsOutputs (op : Y → Y → Y) (r : List (X × Y × Y)) : List Y :=
  r.map fun p => op p.2.1 p.2.2

theorem roundsTrace_append (r₁ r₂ : List (X × Y × Y)) :
    roundsTrace (r₁ ++ r₂) = roundsTrace r₁ ++ roundsTrace r₂ := by
  induction r₁ with
  | nil => rfl
  | cons p r ih =>
      obtain ⟨x, y₁, y₂⟩ := p
      simp [roundsTrace, ih]

theorem roundsInner_append (r₁ r₂ : List (X × Y × Y)) :
    roundsInner (r₁ ++ r₂) = roundsInner r₁ ++ roundsInner r₂ := by
  induction r₁ with
  | nil => rfl
  | cons p r ih =>
      obtain ⟨x, y₁, y₂⟩ := p
      simp [roundsInner, ih]

theorem roundsInputs_append (r₁ r₂ : List (X × Y × Y)) :
    roundsInputs (r₁ ++ r₂) = roundsInputs r₁ ++ roundsInputs r₂ := by
  simp [roundsInputs, List.map_append]

theorem roundsOutputs_append (op : Y → Y → Y) (r₁ r₂ : List (X × Y × Y)) :
    roundsOutputs op (r₁ ++ r₂) = roundsOutputs op r₁ ++ roundsOutputs op r₂ := by
  simp [roundsOutputs, List.map_append]

theorem stepOutput?_roundsTrace_append (op : Y → Y → Y)
    (r : List (X × Y × Y))
    {x : X}
    {tail : List ((InLabel × X) ∪ₜ
      (InLabel × Option (Sigma (fun _ : Fin 2 => Y))))}
    (htail : tail.head? = some (Sum.inl (InLabel.outside, x))) :
    stepOutput? (X := X) op (roundsTrace r ++ tail) =
      stepOutput? (X := X) op tail := by
  induction r with
  | nil =>
      simp [roundsTrace]
  | cons p r ih =>
      obtain ⟨a, b, c⟩ := p
      obtain ⟨x', rest', heq⟩ :
          ∃ (x' : X)
            (rest' : List ((InLabel × X) ∪ₜ
              (InLabel × Option (Sigma (fun _ : Fin 2 => Y))))),
            roundsTrace r ++ tail = Sum.inl (InLabel.outside, x') :: rest' := by
        cases r with
        | nil =>
            cases tail with
            | nil =>
                simp at htail
            | cons i tl =>
                have hi : i = Sum.inl (InLabel.outside, x) := by
                  simpa using htail
                exact ⟨x, tl, by simp [roundsTrace, hi]⟩
        | cons q r' =>
            obtain ⟨a', b', c'⟩ := q
            exact ⟨a',
              Sum.inr (InLabel.inside, some ⟨(0 : Fin 2), b'⟩) ::
              Sum.inr (InLabel.inside, some ⟨(1 : Fin 2), c'⟩) ::
              (roundsTrace r' ++ tail), by simp [roundsTrace]⟩
      rw [show roundsTrace ((a, b, c) :: r) ++ tail =
          Sum.inl (InLabel.outside, a) ::
          Sum.inr (InLabel.inside, some ⟨(0 : Fin 2), b⟩) ::
          Sum.inr (InLabel.inside, some ⟨(1 : Fin 2), c⟩) ::
          (roundsTrace r ++ tail) from by simp [roundsTrace], heq]
      rw [show stepOutput? (X := X) op
            (Sum.inl (InLabel.outside, a) ::
            Sum.inr (InLabel.inside, some ⟨(0 : Fin 2), b⟩) ::
            Sum.inr (InLabel.inside, some ⟨(1 : Fin 2), c⟩) ::
            Sum.inl (InLabel.outside, x') :: rest') =
          stepOutput? (X := X) op
            (Sum.inl (InLabel.outside, x') :: rest') from by
        simp [stepOutput?]]
      rw [← heq]
      exact ih

theorem valid_roundsTrace_two_iff (op : Y → Y → Y)
    (r : List (X × Y × Y)) (x : X)
    (a : Option (Sigma (fun _ : Fin 2 => Y))) :
    Valid (X := X) op
        (roundsTrace r ++
          [Sum.inl (InLabel.outside, x), Sum.inr (InLabel.inside, a)]) ↔
      ∃ y₁ : Y, a = some (Sigma.mk (0 : Fin 2) y₁) := by
  rw [Valid, stepOutput?_roundsTrace_append op r rfl]
  cases a with
  | none =>
      simp [stepOutput?]
  | some s =>
      cases s with
      | mk i y₁ =>
          fin_cases i <;> simp [stepOutput?]

theorem valid_roundsTrace_three_iff (op : Y → Y → Y)
    (r : List (X × Y × Y)) (x : X) (y₁ : Y)
    (a : Option (Sigma (fun _ : Fin 2 => Y))) :
    Valid (X := X) op
        (roundsTrace r ++
          [Sum.inl (InLabel.outside, x),
           Sum.inr (InLabel.inside, some (Sigma.mk (0 : Fin 2) y₁)),
           Sum.inr (InLabel.inside, a)]) ↔
      ∃ y₂ : Y, a = some (Sigma.mk (1 : Fin 2) y₂) := by
  rw [Valid, stepOutput?_roundsTrace_append op r rfl]
  cases a with
  | none =>
      simp [stepOutput?]
  | some s =>
      cases s with
      | mk i y₂ =>
          fin_cases i <;> simp [stepOutput?]

theorem restrict_roundsInner_zero (r : List (X × Y × Y)) :
    System.restrict (Xs := fun _ : Fin 2 => X) (0 : Fin 2) (roundsInner r) =
      roundsInputs r := by
  induction r with
  | nil =>
      rfl
  | cons p r ih =>
      obtain ⟨x, y₁, y₂⟩ := p
      simp [roundsInner, roundsInputs, System.restrict]
      simpa [System.restrict, roundsInputs] using ih

theorem restrict_roundsInner_one (r : List (X × Y × Y)) :
    System.restrict (Xs := fun _ : Fin 2 => X) (1 : Fin 2) (roundsInner r) =
      roundsInputs r := by
  induction r with
  | nil =>
      rfl
  | cons p r ih =>
      obtain ⟨x, y₁, y₂⟩ := p
      simp [roundsInner, roundsInputs, System.restrict]
      simpa [System.restrict, roundsInputs] using ih

end Combine

/-- CR18 Definition 3.12: the deterministic converter `comb⋆`.

It has outside interface `(X,Y)` and inner parallel access to two `(X,Y)`
systems. On an outside input `x`, it queries the first inner system on `x`, then
the second inner system on `x`, then outputs `op y₁ y₂`. -/
def combineConverter (op : Y → Y → Y) :
    DDC X Y (Sigma (fun _ : Fin 2 => X)) (Sigma (fun _ : Fin 2 => Y)) :=
  ⟨(fun l : List ((InLabel × X) ∪ₜ
        (InLabel × Option (Sigma (fun _ : Fin 2 => Y)))) =>
      (⟨Combine.Valid (X := X) op l,
        fun h => (Combine.stepOutput? (X := X) op l).get
          h⟩ :
        Part ((InLabel × Y) ∪ₜ (InLabel × Sigma (fun _ : Fin 2 => X))))),
    ⟨by simp [Combine.Valid, Combine.stepOutput?], by
      intro l₁ l₂ hp hne hdom
      exact Combine.valid_prefix (X := X) op hp hne hdom⟩⟩

/-- CR18 notation for the `comb⋆` converter. -/
scoped notation "comb⋆ᶜ[" op "]" => combineConverter op

theorem combineConverter_output_two (op : Y → Y → Y)
    (r : List (X × Y × Y)) (x : X) (y₁ : Y)
    (hc :
      Combine.roundsTrace r ++
          [Sum.inl (InLabel.outside, x),
           Sum.inr (InLabel.inside, some (Sigma.mk (0 : Fin 2) y₁))] ∈
        System.dom (combineConverter (X := X) op :
          DDC X Y (Sigma (fun _ : Fin 2 => X)) (Sigma (fun _ : Fin 2 => Y)))) :
    System.output
        (combineConverter (X := X) op :
          DDC X Y (Sigma (fun _ : Fin 2 => X)) (Sigma (fun _ : Fin 2 => Y)))
        (Combine.roundsTrace r ++
          [Sum.inl (InLabel.outside, x),
           Sum.inr (InLabel.inside, some (Sigma.mk (0 : Fin 2) y₁))]) hc =
      Sum.inr (InLabel.inside, Sigma.mk (1 : Fin 2) x) := by
  change (Combine.stepOutput? (X := X) op _).get _ = _
  have hct :
      Combine.stepOutput? (X := X) op
          (Combine.roundsTrace r ++
            [Sum.inl (InLabel.outside, x),
             Sum.inr (InLabel.inside, some (Sigma.mk (0 : Fin 2) y₁))]) =
        some (Sum.inr (InLabel.inside, Sigma.mk (1 : Fin 2) x)) := by
    rw [Combine.stepOutput?_roundsTrace_append op r rfl]
    simp [Combine.stepOutput?]
  simp [hct]

theorem combineConverter_output_three (op : Y → Y → Y)
    (r : List (X × Y × Y)) (x : X) (y₁ y₂ : Y)
    (hc :
      Combine.roundsTrace r ++
          [Sum.inl (InLabel.outside, x),
           Sum.inr (InLabel.inside, some (Sigma.mk (0 : Fin 2) y₁)),
           Sum.inr (InLabel.inside, some (Sigma.mk (1 : Fin 2) y₂))] ∈
        System.dom (combineConverter (X := X) op :
          DDC X Y (Sigma (fun _ : Fin 2 => X)) (Sigma (fun _ : Fin 2 => Y)))) :
    System.output
        (combineConverter (X := X) op :
          DDC X Y (Sigma (fun _ : Fin 2 => X)) (Sigma (fun _ : Fin 2 => Y)))
        (Combine.roundsTrace r ++
          [Sum.inl (InLabel.outside, x),
           Sum.inr (InLabel.inside, some (Sigma.mk (0 : Fin 2) y₁)),
           Sum.inr (InLabel.inside, some (Sigma.mk (1 : Fin 2) y₂))]) hc =
      Sum.inl (InLabel.outside, op y₁ y₂) := by
  change (Combine.stepOutput? (X := X) op _).get _ = _
  have hct :
      Combine.stepOutput? (X := X) op
          (Combine.roundsTrace r ++
            [Sum.inl (InLabel.outside, x),
             Sum.inr (InLabel.inside, some (Sigma.mk (0 : Fin 2) y₁)),
             Sum.inr (InLabel.inside, some (Sigma.mk (1 : Fin 2) y₂))]) =
        some (Sum.inl (InLabel.outside, op y₁ y₂)) := by
    rw [Combine.stepOutput?_roundsTrace_append op r rfl]
    simp [Combine.stepOutput?]
  simp [hct]

/-- CR18 §3.4.5 converter-side construction: `comb⋆[S,T]`.

As with cascade, this is the semantic DDS-level application of the paper
converter, not the raw labeled-history interpreter. -/
noncomputable def combineViaConverter
    (op : Y → Y → Y) (S T : System.DDS X Y) : System.DDS X Y :=
  System.combine op S T

scoped notation "comb⋆ᶜ[" op "][" S "," T "]" => combineViaConverter op S T

/-- CR18 Definition 3.12, DDS-level converter equation:
`comb⋆[S,T] = S ⋆ T`.

NOTE: this is `rfl` only because `combineViaConverter` is *defined* as the
native combine.  The honest converter equation is `apply_combineStep`
(`CombineRealization.lean`):
`DDC.apply (ofStep (combineStep op)) [Combine.pair S T]ₚ = S ⋆ₚ[op] T`. -/
theorem combineViaConverter_eq_combine
    (op : Y → Y → Y) (S T : System.DDS X Y) :
    combineViaConverter op S T = System.combine op S T := by
  rfl

/-!
### CR18 Lemma 3.1: appending converters at distinct interfaces

This is the PFun-native, paper-facing attachment model.  A converter attached
at one interface is represented by the pure functions it induces on that
interface:

* `αin : X → Option X`, the partial input sent to the inner resource;
* `αout : X → Y → Y`, the outside output transformation after the resource
  answers.

Attaching at interface `i` is therefore just a coordinate-wise partial
translation of resource histories, followed by a last-output transformation at
interface `i`.  No trace language or driver loop is involved.
-/

section Attach

variable {P : Type u} [DecidableEq P]

/-- Entrywise input translation for attaching a converter at interface `i`. -/
def attachEntry (i : P) (αin : X → Option X) (e : P × X) : Option (P × X) :=
  if e.1 = i then
    (αin e.2).map fun x => (i, x)
  else
    some e

/-- Total form of `attachEntry`, used only for histories whose entries are
known to translate. -/
def attachEntryD (i : P) (αin : X → Option X) (e : P × X) : P × X :=
  (attachEntry i αin e).getD e

/-- A history is translatable at interface `i` when every `i`-entry is accepted
by the attached converter's input translation. -/
def attachDefined (i : P) (αin : X → Option X) (l : List (P × X)) : Prop :=
  ∀ e ∈ l, (attachEntry i αin e).isSome

/-- The resource history seen after attaching a converter at interface `i`. -/
def attachHistory (i : P) (αin : X → Option X) (l : List (P × X)) :
    List (P × X) :=
  l.map (attachEntryD i αin)

/-- The output transformation induced by an attached converter at the last
interface queried by the resource history. -/
def attachOutput (i : P) (αout : X → Y → Y) (l : List (P × X)) (y : Y) : Y :=
  match l.getLast? with
  | some (p, x) => if p = i then αout x y else y
  | none => y

@[simp]
theorem attachEntryD_fst (i : P) (αin : X → Option X) (e : P × X) :
    (attachEntryD i αin e).1 = e.1 := by
  unfold attachEntryD attachEntry
  by_cases he : e.1 = i
  · simp [he]
    cases αin e.2 <;> simp [he]
  · simp [he]

theorem attachEntryD_of_ne (i : P) (αin : X → Option X) {e : P × X}
    (he : e.1 ≠ i) :
    attachEntryD i αin e = e := by
  unfold attachEntryD attachEntry
  simp [he]

theorem attachEntryD_comm (i j : P) (hij : i ≠ j)
    (αin βin : X → Option X) (e : P × X) :
    attachEntryD i αin (attachEntryD j βin e) =
      attachEntryD j βin (attachEntryD i αin e) := by
  by_cases hei : e.1 = i
  · have hej : e.1 ≠ j := by
      intro h
      exact hij (hei.symm.trans h)
    rw [attachEntryD_of_ne j βin hej]
    have hnotj : (attachEntryD i αin e).1 ≠ j := by
      rw [attachEntryD_fst]
      exact hej
    rw [attachEntryD_of_ne j βin hnotj]
  · by_cases hej : e.1 = j
    · rw [attachEntryD_of_ne i αin hei]
      have hnoti : (attachEntryD j βin e).1 ≠ i := by
        rw [attachEntryD_fst]
        exact hei
      rw [attachEntryD_of_ne i αin hnoti]
    · simp [attachEntryD_of_ne i αin hei, attachEntryD_of_ne j βin hej]

theorem attachHistory_comm (i j : P) (hij : i ≠ j)
    (αin βin : X → Option X) (l : List (P × X)) :
    attachHistory i αin (attachHistory j βin l) =
      attachHistory j βin (attachHistory i αin l) := by
  simp [attachHistory, List.map_map, attachEntryD_comm i j hij αin βin]

theorem attachEntry_isSome_of_ne (i : P) (αin : X → Option X) {e : P × X}
    (he : e.1 ≠ i) :
    (attachEntry i αin e).isSome := by
  simp [attachEntry, he]

theorem attachEntry_isSome_attachEntryD (i j : P) (hij : i ≠ j)
    (αin βin : X → Option X) (e : P × X) :
    (attachEntry i αin (attachEntryD j βin e)).isSome =
      (attachEntry i αin e).isSome := by
  by_cases hei : e.1 = i
  · have hej : e.1 ≠ j := by
      intro h
      exact hij (hei.symm.trans h)
    rw [attachEntryD_of_ne j βin hej]
  · have htag : (attachEntryD j βin e).1 ≠ i := by
      rw [attachEntryD_fst]
      exact hei
    rw [attachEntry_isSome_of_ne i αin htag,
      attachEntry_isSome_of_ne i αin hei]

theorem attachDefined_history_iff (i j : P) (hij : i ≠ j)
    (αin βin : X → Option X) (l : List (P × X)) :
    attachDefined i αin (attachHistory j βin l) ↔
      attachDefined i αin l := by
  constructor
  · intro h e he
    have hmem : attachEntryD j βin e ∈ attachHistory j βin l := by
      simpa [attachHistory] using List.mem_map_of_mem he
    have := h (attachEntryD j βin e) hmem
    simpa [attachEntry_isSome_attachEntryD i j hij αin βin e] using this
  · intro h e he
    rcases List.mem_map.mp he with ⟨e₀, he₀, rfl⟩
    simpa [attachEntry_isSome_attachEntryD i j hij αin βin e₀] using h e₀ he₀

theorem attachOutput_history_eq (i j : P) (hij : i ≠ j)
    (αout : X → Y → Y) (βin : X → Option X) (l : List (P × X)) (y : Y) :
    attachOutput i αout (attachHistory j βin l) y =
      attachOutput i αout l y := by
  have hlast :
      (attachHistory j βin l).getLast? =
        l.getLast?.map (attachEntryD j βin) := by
    simp [attachHistory, List.getLast?_map]
  cases hl : l.getLast? with
  | none =>
      simp [attachOutput, hlast, hl]
  | some e =>
      rcases e with ⟨p, x⟩
      by_cases hpi : p = i
      · have hpj : i ≠ j := hij
        have hfix : attachEntryD j βin (i, x) = (i, x) :=
          attachEntryD_of_ne j βin hpj
        simp [attachOutput, hlast, hl, hpi, hfix]
      · have htag : (attachEntryD j βin (p, x)).1 ≠ i := by
          rw [attachEntryD_fst]
          exact hpi
        simp [attachOutput, hlast, hl, hpi]

theorem attachOutput_comm (i j : P) (hij : i ≠ j)
    (αin βin : X → Option X) (αout βout : X → Y → Y)
    (l : List (P × X)) (y : Y) :
    attachOutput i αout l
        (attachOutput j βout (attachHistory i αin l) y) =
      attachOutput j βout l
        (attachOutput i αout (attachHistory j βin l) y) := by
  rw [attachOutput_history_eq j i hij.symm βout αin,
    attachOutput_history_eq i j hij αout βin]
  cases hl : l.getLast? with
  | none =>
      simp [attachOutput, hl]
  | some e =>
      rcases e with ⟨p, x⟩
      by_cases hpi : p = i
      · simp [attachOutput, hl, hpi, hij]
      · by_cases hpj : p = j
        · simp [attachOutput, hl, hpj, hij.symm]
        · simp [attachOutput, hl, hpi, hpj]

/-- CR18 Definition 3.13, PFun-native semantic attachment at one interface. -/
noncomputable def attachAt (i : P) (αin : X → Option X) (αout : X → Y → Y)
    (S : System.Resource P X Y) : System.Resource P X Y :=
  ⟨(fun l : List (P × X) =>
      (⟨attachDefined i αin l ∧ attachHistory i αin l ∈ System.dom S,
        fun h =>
          attachOutput i αout l
            (System.output S (attachHistory i αin l) h.2)⟩ : Part Y)),
    ⟨by
      intro h
      exact System.empty_not_mem S h.2,
    by
      intro l₁ l₂ hprefix hne hdom
      refine ⟨?_, ?_⟩
      · intro e he
        exact hdom.1 e (hprefix.subset he)
      · exact System.prefix_closed S (hprefix.map (attachEntryD i αin)) (by
          intro hnil
          exact hne (List.map_eq_nil_iff.mp hnil)) hdom.2⟩⟩

@[simp]
theorem attachAt_dom_iff (i : P) (αin : X → Option X) (αout : X → Y → Y)
    (S : System.Resource P X Y) (l : List (P × X)) :
    l ∈ System.dom (attachAt i αin αout S) ↔
      attachDefined i αin l ∧ attachHistory i αin l ∈ System.dom S :=
  Iff.rfl

@[simp]
theorem attachAt_output (i : P) (αin : X → Option X) (αout : X → Y → Y)
    (S : System.Resource P X Y) (l : List (P × X))
    (h : l ∈ System.dom (attachAt i αin αout S)) :
    System.output (attachAt i αin αout S) l h =
      attachOutput i αout l
        (System.output S (attachHistory i αin l)
          ((attachAt_dom_iff i αin αout S l).mp h).2) :=
  rfl

theorem attachAt_mem_iff (i : P) (αin : X → Option X) (αout : X → Y → Y)
    (S : System.Resource P X Y) (l : List (P × X)) (y : Y) :
    y ∈ (↑(attachAt i αin αout S) : System.Raw (P × X) Y) l ↔
      attachDefined i αin l ∧
        ∃ hS : attachHistory i αin l ∈ System.dom S,
          attachOutput i αout l
            (System.output S (attachHistory i αin l) hS) = y := by
  constructor
  · rintro ⟨hdom, hout⟩
    exact ⟨hdom.1, hdom.2, hout⟩
  · rintro ⟨hdef, hS, hout⟩
    exact ⟨⟨hdef, hS⟩, hout⟩

/-- CR18 Lemma 3.1: appending converters at distinct interfaces commutes. -/
theorem attachAt_comm (i j : P) (hij : i ≠ j)
    (αin βin : X → Option X) (αout βout : X → Y → Y)
    (S : System.Resource P X Y) :
    attachAt i αin αout (attachAt j βin βout S) =
      attachAt j βin βout (attachAt i αin αout S) := by
  -- Functional equality of two partial functions: same domain, same value.
  -- The two memoryless operators commute because they act on disjoint
  -- interfaces (`i ≠ j`), reduced to the three algebraic facts below.
  apply Subtype.ext
  funext l
  apply Part.ext'
  · -- domains agree
    show l ∈ System.dom (attachAt i αin αout (attachAt j βin βout S)) ↔
        l ∈ System.dom (attachAt j βin βout (attachAt i αin αout S))
    simp only [attachAt_dom_iff, attachDefined_history_iff i j hij αin βin l,
      attachDefined_history_iff j i hij.symm βin αin l,
      attachHistory_comm i j hij αin βin l]
    tauto
  · -- values agree
    intro h₁ h₂
    have pL : attachHistory j βin (attachHistory i αin l) ∈ System.dom S :=
      ((attachAt_dom_iff j βin βout S (attachHistory i αin l)).mp
        ((attachAt_dom_iff i αin αout (attachAt j βin βout S) l).mp h₁).2).2
    have pR : attachHistory i αin (attachHistory j βin l) ∈ System.dom S :=
      ((attachAt_dom_iff i αin αout S (attachHistory j βin l)).mp
        ((attachAt_dom_iff j βin βout (attachAt i αin αout S) l).mp h₂).2).2
    show System.output (attachAt i αin αout (attachAt j βin βout S)) l h₁ =
        System.output (attachAt j βin βout (attachAt i αin αout S)) l h₂
    simp only [attachAt_output]
    rw [System.output_congr S (attachHistory_comm i j hij αin βin l).symm pL pR]
    exact attachOutput_comm i j hij αin βin αout βout l _

end Attach

/-! ### CR18 Definition 3.13 / Lemma 3.1 — general stateful interface attachment

The `Attach` section above models only *memoryless* interface converters (a pure
input map `αin` and output map `αout`, one inner query per outside query). Here
is the faithful general form: an arbitrary stateful `((X,Y),(X,Y))`-DDC `α`
attached at interface `i` of a `(P × X, Y)`-resource, exactly as CR18
Definition 3.13 describes — an `i`-query runs `α`, routing each of `α`'s inner
queries to interface `i` of the resource (via `s⊥`) and feeding the answers back
until `α` outputs; queries at other interfaces pass straight through. It is built
on the function-native `resolve`/`PFun.fix` machinery, with no driver loop. -/

namespace General

open DDC

variable {P : Type u} [DecidableEq P]

/-- CR18 Definition 3.13, one connection step of a general `((X,Y),(X,Y))`-DDC
`α` attached at interface `i`: read `α`'s next move; finish with its outside
output `y`, or route its inner query `x` to interface `i` of the resource (via
`s⊥`) and continue. State is `(α-history, resource-history)`.

Faithful to CR18 Definition 3.3: `α` always receives an answer (the `s⊥` value,
`some y` or `⊥ = none`), but the *recorded* resource history only retains the
query when `s` is actually defined on it — an undefined query is deleted from the
history (`keptPrefix`), so a later pass-through at another interface reads `s.1`
on a genuine element of `dom s`. -/
noncomputable def attachStep (i : P) (α : DDC X Y X Y)
    (s : System.Resource P X Y) :
    (List (CIn X Y) × List (P × X)) →.
      (Y × (List (CIn X Y) × List (P × X))) ⊕ (List (CIn X Y) × List (P × X)) :=
  fun st =>
    (α.1 st.1).bind fun o =>
      match o with
      | Sum.inl (InLabel.outside, y) => Part.some (Sum.inl (y, st))
      | Sum.inr (InLabel.inside, x) =>
          let ans : Option Y :=
            System.output (System.fullyDefined s) (st.2 ++ [(i, x)])
              (by rw [System.dom_fullyDefined]; simp)
          Part.some (Sum.inr
            (st.1 ++ [Sum.inr (InLabel.inside, ans)],
             match ans with
             | some _ => st.2 ++ [(i, x)]
             | none => st.2))
      | _ => Part.none

/-- The inner resolution of one `i`-round: least fixed point of `attachStep`. -/
noncomputable def attachResolve (i : P) (α : DDC X Y X Y)
    (s : System.Resource P X Y) :
    (List (CIn X Y) × List (P × X)) →. (Y × (List (CIn X Y) × List (P × X))) :=
  (attachStep i α s).fix

omit [DecidableEq P] in
/-- CR18 Def 3.13 output rule (= `PFun.fix_stop`): if `α` outputs `(out, y)`, the
`i`-round returns `y` with histories unchanged. -/
theorem attachResolve_out (i : P) (α : DDC X Y X Y) (s : System.Resource P X Y)
    {c : List (CIn X Y)} {rs : List (P × X)} {y : Y}
    (h : Sum.inl (InLabel.outside, y) ∈ α.1 c) :
    (y, (c, rs)) ∈ attachResolve i α s (c, rs) := by
  refine PFun.fix_stop (f := attachStep i α s) ?_
  refine Part.mem_bind_iff.mpr ⟨_, h, ?_⟩
  simp

omit [DecidableEq P] in
/-- CR18 Def 3.13 query rule (= `PFun.fix_fwd_eq`): if `α` outputs `(in, x)`, the
`i`-round continues with `α`'s history extended by `s⊥`'s answer; the resource
history is extended by `(i, x)` only when `s` is defined there (`keptPrefix`). -/
theorem attachResolve_in (i : P) (α : DDC X Y X Y) (s : System.Resource P X Y)
    {c : List (CIn X Y)} {rs : List (P × X)} {x : X}
    (h : Sum.inr (InLabel.inside, x) ∈ α.1 c) :
    attachResolve i α s (c, rs) =
      attachResolve i α s
        (c ++ [Sum.inr (InLabel.inside,
            System.output (System.fullyDefined s) (rs ++ [(i, x)])
              (by rw [System.dom_fullyDefined]; simp))],
          match System.output (System.fullyDefined s) (rs ++ [(i, x)])
              (by rw [System.dom_fullyDefined]; simp) with
          | some _ => rs ++ [(i, x)]
          | none => rs) := by
  refine PFun.fix_fwd_eq (f := attachStep i α s) ?_
  refine Part.mem_bind_iff.mpr ⟨_, h, ?_⟩
  simp

/-- Process one outside entry: an `i`-entry runs `α`'s round (`attachResolve`);
any other entry passes straight through to the resource. -/
noncomputable def attachEntryStep (i : P) (α : DDC X Y X Y)
    (s : System.Resource P X Y)
    (st : List (CIn X Y) × List (P × X)) (e : P × X) :
    Part (Y × (List (CIn X Y) × List (P × X))) :=
  if e.1 = i then
    attachResolve i α s (st.1 ++ [Sum.inl (InLabel.outside, e.2)], st.2)
  else
    (s.1 (st.2 ++ [e])).map fun y => (y, (st.1, st.2 ++ [e]))

/-- CR18 Definition 3.13 outer iteration: thread the `(α-history, resource-
history)` state through the outside history, collecting outputs. -/
noncomputable def attachDrive (i : P) (α : DDC X Y X Y)
    (s : System.Resource P X Y) :
    (List (CIn X Y) × List (P × X)) → List (P × X) →.
      (List Y × (List (CIn X Y) × List (P × X)))
  | st, [] => Part.some ([], st)
  | st, e :: rest =>
      (attachEntryStep i α s st e).bind fun r =>
        (attachDrive i α s r.2 rest).map fun rr => (r.1 :: rr.1, rr.2)

theorem attachDrive_length (i : P) (α : DDC X Y X Y)
    (s : System.Resource P X Y)
    (st : List (CIn X Y) × List (P × X)) (l : List (P × X))
    {r : List Y × (List (CIn X Y) × List (P × X))}
    (h : r ∈ attachDrive i α s st l) : r.1.length = l.length := by
  induction l generalizing st r with
  | nil => simp only [attachDrive, Part.mem_some_iff] at h; subst h; simp
  | cons e rest ih =>
      simp only [attachDrive, Part.mem_bind_iff, Part.mem_map_iff] at h
      obtain ⟨r', _hr', rr, hrr, rfl⟩ := h
      simp [ih r'.2 hrr]

theorem attachDrive_append (i : P) (α : DDC X Y X Y)
    (s : System.Resource P X Y)
    (st : List (CIn X Y) × List (P × X)) (a b : List (P × X)) :
    attachDrive i α s st (a ++ b) =
      (attachDrive i α s st a).bind fun ra =>
        (attachDrive i α s ra.2 b).map fun rb => (ra.1 ++ rb.1, rb.2) := by
  induction a generalizing st with
  | nil =>
      simp only [List.nil_append, attachDrive, Part.bind_some]
      refine (Part.map_id' ?_ _).symm
      intro rb; rfl
  | cons e rest ih =>
      simp only [List.cons_append, attachDrive, ih, Part.bind_assoc, Part.bind_map,
        Part.map_bind, Part.map_map, Function.comp_def, List.cons_append]

/-- The applied resource as a raw partial function: replay the whole interaction
and return the last entry's output. -/
noncomputable def attachRaw (i : P) (α : DDC X Y X Y)
    (s : System.Resource P X Y) : System.Raw (P × X) Y :=
  fun l => (attachDrive i α s ([], []) l).bind fun r =>
    match r.1.getLast? with
    | some y => Part.some y
    | none => Part.none

/-- CR18 Definition 3.13: a general stateful converter `α` attached at interface
`i` of a resource `s`. Faithful to Maurer's multi-query, stateful description;
`Valid` (Maurer's "one would have to show αⁱs is a `(P×X,Y)`-DDS") is discharged
from the structural driver lemmas. -/
noncomputable def attachAt (i : P) (α : DDC X Y X Y)
    (s : System.Resource P X Y) : System.Resource P X Y :=
  ⟨attachRaw i α s, by
    refine ⟨?_, ?_⟩
    · rw [PFun.mem_dom]; rintro ⟨v, hv⟩
      simp [attachRaw, attachDrive] at hv
    · intro l₁ l₂ hpre hne hdom
      obtain ⟨suf, rfl⟩ := hpre
      rw [PFun.mem_dom] at hdom
      obtain ⟨v, hv⟩ := hdom
      simp only [attachRaw, Part.mem_bind_iff] at hv
      obtain ⟨r, hr, _hvr⟩ := hv
      rw [attachDrive_append, Part.mem_bind_iff] at hr
      obtain ⟨ra, hra, _hr2⟩ := hr
      have hlen : ra.1.length = l₁.length :=
        attachDrive_length i α s ([], []) l₁ hra
      have hne1 : ra.1 ≠ [] := by
        intro hnil; apply hne; apply List.eq_nil_of_length_eq_zero
        rw [← hlen, hnil, List.length_nil]
      rw [PFun.mem_dom]
      refine ⟨ra.1.getLast hne1, ?_⟩
      simp only [attachRaw, Part.mem_bind_iff]
      refine ⟨ra, hra, ?_⟩
      rw [List.getLast?_eq_some_getLast hne1]; exact Part.mem_some _⟩

/-- Transparency: appending a non-`j` entry `e` to the input of `attachAt j β`
just passes `e` straight through to the base resource `s` (it is *not* expanded
by `β`). Immediate from `attachDrive_append` and the pass-through branch. -/
theorem attachDrive_passthrough (j : P) (β : DDC X Y X Y)
    (s : System.Resource P X Y) (e : P × X) (hej : e.1 ≠ j)
    (st : List (CIn X Y) × List (P × X)) (h : List (P × X)) :
    attachDrive j β s st (h ++ [e]) =
      (attachDrive j β s st h).bind fun r =>
        (s.1 (r.2.2 ++ [e])).map fun y => (r.1 ++ [y], (r.2.1, r.2.2 ++ [e])) := by
  rw [attachDrive_append]
  have hbody :
      (fun ra : List Y × (List (CIn X Y) × List (P × X)) =>
          (attachDrive j β s ra.2 [e]).map fun rb => (ra.1 ++ rb.1, rb.2)) =
        (fun r : List Y × (List (CIn X Y) × List (P × X)) =>
          (s.1 (r.2.2 ++ [e])).map fun y => (r.1 ++ [y], (r.2.1, r.2.2 ++ [e]))) := by
    funext ra
    simp [attachDrive, attachEntryStep, hej, Part.bind_some_eq_map, Part.map_map,
      Function.comp_def]
  rw [hbody]

/-- Raw pass-through for the *applied* resource: a `k`-query (`k ≠ m`) to
`attachAt m δ s`, after a history `hΓ` that `δ`-drives to base history `hbase`,
reads exactly `s` at `hbase ++ [(k, x)]`. -/
theorem attachAt_apply_passthrough (m : P) (δ : DDC X Y X Y)
    (s : System.Resource P X Y) (e : P × X) (hem : e.1 ≠ m)
    {hΓ hbase : List (P × X)} {cδ : List (CIn X Y)} {vsδ : List Y}
    (hdrive : attachDrive m δ s ([], []) hΓ = Part.some (vsδ, (cδ, hbase))) :
    (attachAt m δ s).1 (hΓ ++ [e]) = s.1 (hbase ++ [e]) := by
  change attachRaw m δ s (hΓ ++ [e]) = s.1 (hbase ++ [e])
  rw [attachRaw, attachDrive_passthrough m δ s e hem ([], []) hΓ, hdrive]
  simp [Part.bind_some, Part.bind_some_right]

/-- A history that successfully `δ`-drives is in the domain of the applied
resource (or empty); needed to evaluate `keptPrefix`. -/
theorem attachAt_dom_or_nil (m : P) (δ : DDC X Y X Y)
    (s : System.Resource P X Y)
    {hΓ hbase : List (P × X)} {cδ : List (CIn X Y)} {vsδ : List Y}
    (hdrive : attachDrive m δ s ([], []) hΓ = Part.some (vsδ, (cδ, hbase))) :
    hΓ ∈ System.dom (attachAt m δ s) ∨ hΓ = [] := by
  rcases List.eq_nil_or_concat hΓ with rfl | ⟨hΓ', e, rfl⟩
  · exact Or.inr rfl
  · left
    rw [List.concat_eq_append] at hdrive ⊢
    have hmem : (vsδ, (cδ, hbase)) ∈ attachDrive m δ s ([], []) (hΓ' ++ [e]) := by
      rw [hdrive]; exact Part.mem_some _
    have hlen : vsδ.length = (hΓ' ++ [e]).length :=
      attachDrive_length m δ s ([], []) (hΓ' ++ [e]) hmem
    have hvsne : vsδ ≠ [] := by
      intro h; rw [h, List.length_nil] at hlen
      simp at hlen
    rw [System.dom_def, PFun.mem_dom]
    refine ⟨vsδ.getLast hvsne, ?_⟩
    show vsδ.getLast hvsne ∈ attachRaw m δ s (hΓ' ++ [e])
    simp only [attachRaw, Part.mem_bind_iff]
    refine ⟨(vsδ, (cδ, hbase)), hmem, ?_⟩
    rw [List.getLast?_eq_some_getLast hvsne]; exact Part.mem_some _

/-- Transparency at `⊥`: the fully-defined answer to a `k`-query (`k ≠ m`) of the
applied resource equals `s`'s own `⊥`-answer at the base history. Pure function
evaluation via `attachAt_apply_passthrough` and CR18 Definition 3.3. -/
theorem attachAt_fullyDefined_passthrough (m : P) (δ : DDC X Y X Y)
    (s : System.Resource P X Y) (k : P) (x : X) (hkm : k ≠ m)
    {hΓ hbase : List (P × X)} {cδ : List (CIn X Y)} {vsδ : List Y}
    (hdrive : attachDrive m δ s ([], []) hΓ = Part.some (vsδ, (cδ, hbase)))
    (hbaseDom : hbase ∈ System.dom s ∨ hbase = []) :
    System.output (System.fullyDefined (attachAt m δ s)) (hΓ ++ [(k, x)])
        (by rw [System.dom_fullyDefined]; simp) =
      System.output (System.fullyDefined s) (hbase ++ [(k, x)])
        (by rw [System.dom_fullyDefined]; simp) := by
  have hpt : (attachAt m δ s).1 (hΓ ++ [(k, x)]) = s.1 (hbase ++ [(k, x)]) :=
    attachAt_apply_passthrough m δ s (k, x) hkm hdrive
  have hΓdom : hΓ ∈ System.dom (attachAt m δ s) ∨ hΓ = [] :=
    attachAt_dom_or_nil m δ s hdrive
  by_cases hmem : hbase ++ [(k, x)] ∈ System.dom s
  · have hmemΓ : hΓ ++ [(k, x)] ∈ System.dom (attachAt m δ s) := by
      show (((attachAt m δ s).1) (hΓ ++ [(k, x)])).Dom
      rw [hpt]; exact hmem
    rw [System.output_fullyDefined_append_of_mem (attachAt m δ s) hΓ (k, x) hΓdom hmemΓ,
        System.output_fullyDefined_append_of_mem s hbase (k, x) hbaseDom hmem]
    congr 1
    have hv1 : System.output (attachAt m δ s) (hΓ ++ [(k, x)]) hmemΓ ∈
        (attachAt m δ s).1 (hΓ ++ [(k, x)]) := Part.get_mem _
    have hv2 : System.output s (hbase ++ [(k, x)]) hmem ∈ s.1 (hbase ++ [(k, x)]) :=
      Part.get_mem _
    rw [hpt] at hv1
    exact Part.mem_unique hv1 hv2
  · have hmemΓ_not : hΓ ++ [(k, x)] ∉ System.dom (attachAt m δ s) := by
      show ¬ (((attachAt m δ s).1) (hΓ ++ [(k, x)])).Dom
      rw [hpt]; exact hmem
    have hnoneR : System.output (System.fullyDefined s) (hbase ++ [(k, x)])
        (by rw [System.dom_fullyDefined]; simp) = none := by
      rcases Option.eq_none_or_eq_some
          (System.output (System.fullyDefined s) (hbase ++ [(k, x)])
            (by rw [System.dom_fullyDefined]; simp)) with h | ⟨y, hy⟩
      · exact h
      · obtain ⟨hmem', _⟩ :=
          System.mem_of_output_fullyDefined_append_eq_some s hbase (k, x) hbaseDom hy
        exact absurd hmem' hmem
    have hnoneL : System.output (System.fullyDefined (attachAt m δ s)) (hΓ ++ [(k, x)])
        (by rw [System.dom_fullyDefined]; simp) = none := by
      rcases Option.eq_none_or_eq_some
          (System.output (System.fullyDefined (attachAt m δ s)) (hΓ ++ [(k, x)])
            (by rw [System.dom_fullyDefined]; simp)) with h | ⟨y, hy⟩
      · exact h
      · obtain ⟨hmem', _⟩ :=
          System.mem_of_output_fullyDefined_append_eq_some (attachAt m δ s) hΓ (k, x) hΓdom hy
        exact absurd hmem' hmemΓ_not
    rw [hnoneL, hnoneR]

omit [DecidableEq P] in
/-- Membership characterization of `attachStep` terminating (`inl`): `α` output an
outside value, leaving the state unchanged. -/
theorem attachStep_mem_inl (k : P) (γ : DDC X Y X Y) (R : System.Resource P X Y)
    (st : List (CIn X Y) × List (P × X)) (b : Y × (List (CIn X Y) × List (P × X))) :
    Sum.inl b ∈ attachStep k γ R st ↔
      Sum.inl (InLabel.outside, b.1) ∈ γ.1 st.1 ∧ b.2 = st := by
  rw [attachStep, Part.mem_bind_iff]
  constructor
  · rintro ⟨o, ho, hb_o⟩
    rcases o with ⟨lbl, y0⟩ | ⟨lbl, x0⟩ <;> cases lbl <;> simp_all
  · rintro ⟨hmemγ, hst⟩
    exact ⟨Sum.inl (InLabel.outside, b.1), hmemγ, by rw [← hst]; cases b; simp⟩

omit [DecidableEq P] in
/-- Membership characterization of `attachStep` continuing (`inr`): `α` issued an
inside query `x0`; the resource history is extended by `(k, x0)` only when `R` is
defined there. -/
theorem attachStep_mem_inr (k : P) (γ : DDC X Y X Y) (R : System.Resource P X Y)
    (st st'' : List (CIn X Y) × List (P × X)) :
    Sum.inr st'' ∈ attachStep k γ R st ↔
      ∃ x0, Sum.inr (InLabel.inside, x0) ∈ γ.1 st.1 ∧
        st'' = (st.1 ++ [Sum.inr (InLabel.inside,
                  System.output (System.fullyDefined R) (st.2 ++ [(k, x0)])
                    (by rw [System.dom_fullyDefined]; simp))],
                match System.output (System.fullyDefined R) (st.2 ++ [(k, x0)])
                    (by rw [System.dom_fullyDefined]; simp) with
                | some _ => st.2 ++ [(k, x0)]
                | none => st.2) := by
  rw [attachStep, Part.mem_bind_iff]
  constructor
  · rintro ⟨o, ho, ho''⟩
    rcases o with ⟨lbl, y0⟩ | ⟨lbl, x0⟩ <;> cases lbl <;>
      simp only [Part.mem_some_iff, Part.notMem_none, reduceCtorEq, Sum.inr.injEq] at ho''
    exact ⟨x0, ho, ho''⟩
  · rintro ⟨x0, hmemγ, rfl⟩
    refine ⟨Sum.inr (InLabel.inside, x0), hmemγ, ?_⟩
    simp only [Part.mem_some_iff]

omit [DecidableEq P] in
/-- CR18 Definition 3.3 (`keptPrefix`): one `m`-round records only `s`-defined
queries, so the base history it produces stays in `dom s` (or is empty). -/
theorem attachResolve_base_dom (m : P) (δ : DDC X Y X Y)
    (s : System.Resource P X Y)
    {st : List (CIn X Y) × List (P × X)}
    (hst : st.2 ∈ System.dom s ∨ st.2 = [])
    {r : Y × (List (CIn X Y) × List (P × X))} (hr : r ∈ attachResolve m δ s st) :
    r.2.2 ∈ System.dom s ∨ r.2.2 = [] := by
  refine PFun.fixInduction hr
    (C := fun a => (a.2 ∈ System.dom s ∨ a.2 = []) →
      r.2.2 ∈ System.dom s ∨ r.2.2 = []) ?_ hst
  rintro a' hbfix IH ha'
  rw [PFun.mem_fix_iff] at hbfix
  rcases hbfix with hterm | ⟨a'', hstep, _⟩
  · rw [attachStep_mem_inl] at hterm
    obtain ⟨_, hsteq⟩ := hterm
    rw [hsteq]; exact ha'
  · apply IH a'' hstep
    have hstep' := hstep
    rw [attachStep_mem_inr] at hstep'
    obtain ⟨x0, _, ha''eq⟩ := hstep'
    rw [ha''eq]
    rcases Option.eq_none_or_eq_some
        (System.output (System.fullyDefined s) (a'.2 ++ [(m, x0)])
          (by rw [System.dom_fullyDefined]; simp)) with hnone | ⟨yval, hyval⟩
    · rw [hnone]; exact ha'
    · rw [hyval]
      exact Or.inl
        (System.mem_of_output_fullyDefined_append_eq_some s a'.2 (m, x0) ha' hyval).choose

/-- The base history produced by driving a converter `δ` at interface `m`
through a resource `s` stays in `dom s` (or empty); `keptPrefix` again. -/
theorem attachDrive_base_dom (m : P) (δ : DDC X Y X Y)
    (s : System.Resource P X Y) (H : List (P × X)) :
    ∀ {st : List (CIn X Y) × List (P × X)}, (st.2 ∈ System.dom s ∨ st.2 = []) →
      ∀ {r : List Y × (List (CIn X Y) × List (P × X))},
        r ∈ attachDrive m δ s st H → r.2.2 ∈ System.dom s ∨ r.2.2 = [] := by
  induction H with
  | nil =>
      intro st hst r hr
      simp only [attachDrive, Part.mem_some_iff] at hr
      subst hr; exact hst
  | cons e rest ih =>
      intro st hst r hr
      simp only [attachDrive, Part.mem_bind_iff, Part.mem_map_iff] at hr
      obtain ⟨r', hr', rr, hrr, rfl⟩ := hr
      have hr'dom : r'.2.2 ∈ System.dom s ∨ r'.2.2 = [] := by
        rw [attachEntryStep] at hr'
        by_cases hem : e.1 = m
        · rw [if_pos hem] at hr'
          exact attachResolve_base_dom m δ s
            (st := (st.1 ++ [Sum.inl (InLabel.outside, e.2)], st.2)) hst hr'
        · rw [if_neg hem, Part.mem_map_iff] at hr'
          obtain ⟨yy, hyy, rfl⟩ := hr'
          left; rw [System.dom_def, PFun.mem_dom]; exact ⟨yy, hyy⟩
      show rr.2.2 ∈ System.dom s ∨ rr.2.2 = []
      exact ih hr'dom hrr

/-- The bisimulation relation behind the resolve correspondence: the `γ`-histories
agree, the `attachAt`-side resource history `δ`-drives to the `s`-side base
history, and that base is in `dom s` (or empty). -/
def Rel (m : P) (δ : DDC X Y X Y) (s : System.Resource P X Y)
    (cδ : List (CIn X Y)) (a a' : List (CIn X Y) × List (P × X)) : Prop :=
  a.1 = a'.1 ∧
    (∃ vsd, attachDrive m δ s ([], []) a.2 = Part.some (vsd, (cδ, a'.2))) ∧
    (a'.2 ∈ System.dom s ∨ a'.2 = [])

/-- The single step of the bisimulation, written once and used in *both*
directions: from `Rel`-related states an inside query `x0` drives both sides to
`Rel`-related successors. The only mathematical content is
`attachAt_fullyDefined_passthrough` (transparency of `δ` at interface `m`). -/
theorem passthrough_step_rel (k : P) (m : P) (δ : DDC X Y X Y)
    (s : System.Resource P X Y) (hkm : k ≠ m) (cδ : List (CIn X Y))
    {a a' : List (CIn X Y) × List (P × X)} (hRc : a.1 = a'.1) {vsd : List Y}
    (hRd : attachDrive m δ s ([], []) a.2 = Part.some (vsd, (cδ, a'.2)))
    (hRdom : a'.2 ∈ System.dom s ∨ a'.2 = []) (x0 : X) :
    Rel m δ s cδ
      (a.1 ++ [Sum.inr (InLabel.inside,
          System.output (System.fullyDefined (attachAt m δ s)) (a.2 ++ [(k, x0)])
            (by rw [System.dom_fullyDefined]; simp))],
        match System.output (System.fullyDefined (attachAt m δ s)) (a.2 ++ [(k, x0)])
            (by rw [System.dom_fullyDefined]; simp) with
          | some _ => a.2 ++ [(k, x0)] | none => a.2)
      (a'.1 ++ [Sum.inr (InLabel.inside,
          System.output (System.fullyDefined s) (a'.2 ++ [(k, x0)])
            (by rw [System.dom_fullyDefined]; simp))],
        match System.output (System.fullyDefined s) (a'.2 ++ [(k, x0)])
            (by rw [System.dom_fullyDefined]; simp) with
          | some _ => a'.2 ++ [(k, x0)] | none => a'.2) := by
  have htrans := attachAt_fullyDefined_passthrough m δ s k x0 hkm hRd hRdom
  refine ⟨by rw [hRc, htrans], ?_, ?_⟩
  · rcases Option.eq_none_or_eq_some
        (System.output (System.fullyDefined s) (a'.2 ++ [(k, x0)])
          (by rw [System.dom_fullyDefined]; simp)) with hnone | ⟨yval, hyval⟩
    · rw [htrans, hnone]; exact ⟨vsd, hRd⟩
    · rw [htrans, hyval]
      have hmemHb : a'.2 ++ [(k, x0)] ∈ System.dom s :=
        (System.mem_of_output_fullyDefined_append_eq_some s a'.2 (k, x0) hRdom hyval).choose
      have hsval : s.1 (a'.2 ++ [(k, x0)]) =
          Part.some (System.output s (a'.2 ++ [(k, x0)]) hmemHb) :=
        Part.eq_some_iff.mpr (Part.get_mem _)
      refine ⟨vsd ++ [System.output s (a'.2 ++ [(k, x0)]) hmemHb], ?_⟩
      rw [attachDrive_passthrough m δ s (k, x0) hkm ([], []) a.2, hRd]
      simp only [Part.bind_some, hsval, Part.map_some]
  · rcases Option.eq_none_or_eq_some
        (System.output (System.fullyDefined s) (a'.2 ++ [(k, x0)])
          (by rw [System.dom_fullyDefined]; simp)) with hnone | ⟨yval, hyval⟩
    · rw [hnone]; exact hRdom
    · rw [hyval]
      exact Or.inl
        (System.mem_of_output_fullyDefined_append_eq_some s a'.2 (k, x0) hRdom hyval).choose

/-- Forward half of the resolve correspondence: a `k`-round of `γ` against the
applied resource `attachAt m δ s` is mirrored, step for step, by a `k`-round of
`γ` against `s` itself — same outside output and `γ`-history, and the resource
history `δ`-drives to the base history throughout (`k ≠ m`, so `γ`'s queries pass
through `δ`). Now a thin instance of `fix_bisim` with `passthrough_step_rel`. -/
theorem attachResolve_passthrough_fwd
    (k : P) (γ : DDC X Y X Y) (m : P) (δ : DDC X Y X Y)
    (s : System.Resource P X Y) (hkm : k ≠ m) (cδ : List (CIn X Y))
    {y : Y} {c' : List (CIn X Y)} {hΓ'' : List (P × X)}
    {c : List (CIn X Y)} {hΓ hbase : List (P × X)} {vsδ : List Y}
    (hdrive : attachDrive m δ s ([], []) hΓ = Part.some (vsδ, (cδ, hbase)))
    (hbaseDom : hbase ∈ System.dom s ∨ hbase = [])
    (hmem : (y, (c', hΓ'')) ∈ attachResolve k γ (attachAt m δ s) (c, hΓ)) :
    ∃ hbase'' vsδ'', (y, (c', hbase'')) ∈ attachResolve k γ s (c, hbase) ∧
      attachDrive m δ s ([], []) hΓ'' = Part.some (vsδ'', (cδ, hbase'')) := by
  -- Terminated step: `γ` outputs, states unchanged, outputs `Q`-related.
  have hstop : ∀ a a', Rel m δ s cδ a a' → ∀ b,
      Sum.inl b ∈ attachStep k γ (attachAt m δ s) a →
      ∃ b', Sum.inl b' ∈ attachStep k γ s a' ∧
        b.1 = b'.1 ∧ b.2.1 = b'.2.1 ∧
        ∃ vsd, attachDrive m δ s ([], []) b.2.2 = Part.some (vsd, (cδ, b'.2.2)) := by
    rintro a a' ⟨hRc, ⟨vsd0, hRd⟩, -⟩ b hb
    rw [attachStep_mem_inl] at hb
    obtain ⟨houtγ, hbeq⟩ := hb
    exact ⟨(b.1, a'), by rw [attachStep_mem_inl]; exact ⟨hRc ▸ houtγ, rfl⟩,
      rfl, by rw [hbeq]; exact hRc, vsd0, by rw [hbeq]; exact hRd⟩
  -- Inside step: delegate to the shared `passthrough_step_rel`.
  have hstep : ∀ a a', Rel m δ s cδ a a' → ∀ a₁,
      Sum.inr a₁ ∈ attachStep k γ (attachAt m δ s) a →
      ∃ a₁', Sum.inr a₁' ∈ attachStep k γ s a' ∧ Rel m δ s cδ a₁ a₁' := by
    rintro a a' ⟨hRc, ⟨vsd0, hRd⟩, hRdom⟩ a₁ ha₁
    rw [attachStep_mem_inr] at ha₁
    obtain ⟨x0, hqueryγ, rfl⟩ := ha₁
    exact ⟨_, by rw [attachStep_mem_inr]; exact ⟨x0, hRc ▸ hqueryγ, rfl⟩,
      passthrough_step_rel k m δ s hkm cδ hRc hRd hRdom x0⟩
  obtain ⟨⟨by_, bc, bh⟩, hb'mem, hy, hc, vsd'', hd⟩ :=
    PFun.fix_bisim hstop hstep hmem (c, hbase) ⟨rfl, ⟨vsδ, hdrive⟩, hbaseDom⟩
  obtain rfl := hy; obtain rfl := hc
  exact ⟨bh, vsd'', hb'mem, hd⟩

/-- Backward half of the resolve correspondence: every `k`-round of `γ` against
`s` is realized by a `k`-round of `γ` against `attachAt m δ s`, with the resource
history `δ`-driving to the base history. The same `fix_bisim`/`passthrough_step_rel`
as the forward half, run with the relation flipped. -/
theorem attachResolve_passthrough_bwd
    (k : P) (γ : DDC X Y X Y) (m : P) (δ : DDC X Y X Y)
    (s : System.Resource P X Y) (hkm : k ≠ m) (cδ : List (CIn X Y))
    {y : Y} {c' : List (CIn X Y)} {hbase'' : List (P × X)}
    {c : List (CIn X Y)} {hΓ hbase : List (P × X)} {vsδ : List Y}
    (hdrive : attachDrive m δ s ([], []) hΓ = Part.some (vsδ, (cδ, hbase)))
    (hbaseDom : hbase ∈ System.dom s ∨ hbase = [])
    (hmem : (y, (c', hbase'')) ∈ attachResolve k γ s (c, hbase)) :
    ∃ hΓ'' vsδ'', (y, (c', hΓ'')) ∈ attachResolve k γ (attachAt m δ s) (c, hΓ) ∧
      attachDrive m δ s ([], []) hΓ'' = Part.some (vsδ'', (cδ, hbase'')) := by
  have hstop : ∀ a a', Rel m δ s cδ a' a → ∀ b,
      Sum.inl b ∈ attachStep k γ s a →
      ∃ b', Sum.inl b' ∈ attachStep k γ (attachAt m δ s) a' ∧
        b.1 = b'.1 ∧ b.2.1 = b'.2.1 ∧
        ∃ vsd, attachDrive m δ s ([], []) b'.2.2 = Part.some (vsd, (cδ, b.2.2)) := by
    rintro a a' ⟨hRc, ⟨vsd0, hRd⟩, -⟩ b hb
    rw [attachStep_mem_inl] at hb
    obtain ⟨houtγ, hbeq⟩ := hb
    exact ⟨(b.1, a'), by rw [attachStep_mem_inl]; exact ⟨by rw [hRc]; exact houtγ, rfl⟩,
      rfl, by rw [hbeq]; exact hRc.symm, vsd0, by rw [hbeq]; exact hRd⟩
  have hstep : ∀ a a', Rel m δ s cδ a' a → ∀ a₁,
      Sum.inr a₁ ∈ attachStep k γ s a →
      ∃ a₁', Sum.inr a₁' ∈ attachStep k γ (attachAt m δ s) a' ∧ Rel m δ s cδ a₁' a₁ := by
    rintro a a' ⟨hRc, ⟨vsd0, hRd⟩, hRdom⟩ a₁ ha₁
    rw [attachStep_mem_inr] at ha₁
    obtain ⟨x0, hqueryγ, rfl⟩ := ha₁
    exact ⟨_, by rw [attachStep_mem_inr]; exact ⟨x0, by rw [hRc]; exact hqueryγ, rfl⟩,
      passthrough_step_rel k m δ s hkm cδ hRc hRd hRdom x0⟩
  obtain ⟨⟨by_, bc, bh⟩, hb'mem, hy, hc, vsd'', hd⟩ :=
    PFun.fix_bisim hstop hstep hmem (c, hΓ) ⟨rfl, ⟨vsδ, hdrive⟩, hbaseDom⟩
  obtain rfl := hy; obtain rfl := hc
  exact ⟨bh, vsd'', hb'mem, hd⟩

/-- One outer step of the commutativity induction, for an entry `e` at the
*resolving* interface `k` (`k ≠ m`): the side that runs `γ` at `k` (against
`attachAt m δ s`) and the side that passes `e` through `δ` to `attachAt k γ s`'s
own `k`-round agree on the head output and reduce, via the symmetric induction
hypothesis `sih`, to the tails. This is the single argument behind *both* the
`i` and `j` branches of `attachAt_comm` — the latter feeds `(ih …).symm`. -/
theorem cons_step_eq (k : P) (γ : DDC X Y X Y) (m : P) (δ : DDC X Y X Y)
    (s : System.Resource P X Y) (hkm : k ≠ m)
    (rest : List (P × X)) (e : P × X) (hek : e.1 = k)
    (cγ cδ : List (CIn X Y)) (hΓ hΔ hs : List (P × X)) (vsγ vsδ : List Y)
    (hΓeq : attachDrive m δ s ([], []) hΓ = Part.some (vsδ, (cδ, hs)))
    (hΔeq : attachDrive k γ s ([], []) hΔ = Part.some (vsγ, (cγ, hs)))
    (sih : ∀ (cγ' cδ' : List (CIn X Y)) (hΓ' hΔ' : List (P × X)),
        (∃ hs' vsδ' vsγ',
            attachDrive m δ s ([], []) hΓ' = Part.some (vsδ', (cδ', hs')) ∧
            attachDrive k γ s ([], []) hΔ' = Part.some (vsγ', (cγ', hs'))) →
        Part.map Prod.fst (attachDrive k γ (attachAt m δ s) (cγ', hΓ') rest) =
          Part.map Prod.fst (attachDrive m δ (attachAt k γ s) (cδ', hΔ') rest)) :
    Part.map Prod.fst (attachDrive k γ (attachAt m δ s) (cγ, hΓ) (e :: rest)) =
      Part.map Prod.fst (attachDrive m δ (attachAt k γ s) (cδ, hΔ) (e :: rest)) := by
  have hem : ¬ e.1 = m := by rw [hek]; exact hkm
  simp only [attachDrive, attachEntryStep]
  rw [if_pos hek, if_neg hem]
  have hΔres : (attachAt k γ s).1 (hΔ ++ [e]) =
      (attachResolve k γ s (cγ ++ [Sum.inl (InLabel.outside, e.2)], hs)).map Prod.fst := by
    change attachRaw k γ s (hΔ ++ [e]) = _
    rw [attachRaw, attachDrive_append k γ s ([], []) hΔ [e], hΔeq]
    simp [attachDrive, attachEntryStep, hek, Part.bind_some, Part.map_map,
      Function.comp_def, Part.bind_some_eq_map]
  rw [hΔres]
  have hsDom : hs ∈ System.dom s ∨ hs = [] :=
    attachDrive_base_dom m δ s hΓ (Or.inr rfl) (by rw [hΓeq]; exact Part.mem_some _)
  have hΔe : attachDrive k γ s ([], []) (hΔ ++ [e]) =
      (attachResolve k γ s (cγ ++ [Sum.inl (InLabel.outside, e.2)], hs)).map
        (fun q => (vsγ ++ [q.1], q.2)) := by
    rw [attachDrive_append k γ s ([], []) hΔ [e], hΔeq, Part.bind_some]
    simp only [attachDrive, attachEntryStep, if_pos hek,
      Part.bind_some_eq_map, Part.map_map, Function.comp_def, Part.map_some]
  have htail : ∀ (qy : Y) (qc : List (CIn X Y)) (hΓ'' qh : List (P × X)) (vv : List Y),
      attachDrive m δ s ([], []) hΓ'' = Part.some (vv, (cδ, qh)) →
      (qy, (qc, qh)) ∈ attachResolve k γ s (cγ ++ [Sum.inl (InLabel.outside, e.2)], hs) →
      Part.map Prod.fst (attachDrive k γ (attachAt m δ s) (qc, hΓ'') rest) =
        Part.map Prod.fst (attachDrive m δ (attachAt k γ s) (cδ, hΔ ++ [e]) rest) := by
    intro qy qc hΓ'' qh vv hmdrive hq
    refine sih qc cδ hΓ'' (hΔ ++ [e]) ⟨qh, vv, vsγ ++ [qy], hmdrive, ?_⟩
    rw [hΔe, Part.eq_some_iff.mpr hq, Part.map_some]
  simp only [Part.map_bind, Part.bind_map, Part.map_map, Function.comp_def]
  apply Part.ext
  intro z
  simp only [Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨⟨ry, rc, rh⟩, hr, w, hw, rfl⟩
    obtain ⟨hbase'', vsδ'', hq, hmdrive⟩ :=
      attachResolve_passthrough_fwd k γ m δ s hkm cδ hΓeq hsDom hr
    have htl := htail ry rc rh hbase'' vsδ'' hmdrive hq
    have hw' : w.1 ∈ Part.map Prod.fst
        (attachDrive m δ (attachAt k γ s) (cδ, hΔ ++ [e]) rest) := by
      rw [← htl]; exact Part.mem_map _ hw
    rw [Part.mem_map_iff] at hw'
    obtain ⟨w2, hw2, hw2eq⟩ := hw'
    exact ⟨(ry, (rc, hbase'')), hq, w2, hw2, by rw [hw2eq]⟩
  · rintro ⟨⟨qy, qc, qh⟩, hq, w, hw, rfl⟩
    obtain ⟨hΓ'', vsδ'', hr, hmdrive⟩ :=
      attachResolve_passthrough_bwd k γ m δ s hkm cδ hΓeq hsDom hq
    have htl := htail qy qc hΓ'' qh vsδ'' hmdrive hq
    have hw' : w.1 ∈ Part.map Prod.fst
        (attachDrive k γ (attachAt m δ s) (qc, hΓ'') rest) := by
      rw [htl]; exact Part.mem_map _ hw
    rw [Part.mem_map_iff] at hw'
    obtain ⟨w2, hw2, hw2eq⟩ := hw'
    exact ⟨(qy, (qc, hΓ'')), hr, w2, hw2, by rw [hw2eq]⟩

/-- CR18 Lemma 3.1 (general stateful converters): attaching at distinct
interfaces commutes — operator commutativity `αⁱ ∘ βʲ = βʲ ∘ αⁱ`. -/
theorem attachAt_comm (i : P) (α : DDC X Y X Y) (j : P) (β : DDC X Y X Y)
    (s : System.Resource P X Y) (hij : i ≠ j) :
    attachAt i α (attachAt j β s) = attachAt j β (attachAt i α s) := by
  apply Subtype.ext
  funext l
  show attachRaw i α (attachAt j β s) l = attachRaw j β (attachAt i α s) l
  -- The output lists of the two drives agree, under the cross-tied invariant
  -- relating the two nestings through the shared base-`s` history.
  have key : ∀ (l : List (P × X)) (cα cβ : List (CIn X Y)) (hT hU : List (P × X)),
      (∃ (hs : List (P × X)) (vsβ vsα : List Y),
          attachDrive j β s ([], []) hT = Part.some (vsβ, (cβ, hs)) ∧
          attachDrive i α s ([], []) hU = Part.some (vsα, (cα, hs))) →
      (attachDrive i α (attachAt j β s) (cα, hT) l).map Prod.fst =
        (attachDrive j β (attachAt i α s) (cβ, hU) l).map Prod.fst := by
    intro l
    induction l with
    | nil => intro cα cβ hT hU _; simp [attachDrive]
    | cons e rest ih =>
        intro cα cβ hT hU hInv
        obtain ⟨hs, vsβ, vsα, hTeq, hUeq⟩ := hInv
        by_cases hei : e.1 = i
        · -- e at the resolving interface i: one `cons_step_eq`, ih directly.
          exact cons_step_eq i α j β s hij rest e hei cα cβ hT hU hs vsα vsβ hTeq hUeq ih
        · by_cases hej : e.1 = j
          · -- e at the resolving interface j: same lemma with (i,α)↔(j,β), fed
            -- the transposed induction hypothesis `(ih …).symm`.
            refine (cons_step_eq j β i α s hij.symm rest e hej cβ cα hU hT hs vsβ vsα
                hUeq hTeq (fun cγ' cδ' hΓ' hΔ' h => ?_)).symm
            obtain ⟨hs', v1, v2, h1, h2⟩ := h
            exact (ih cδ' cγ' hΔ' hΓ' ⟨hs', v2, v1, h2, h1⟩).symm
          · -- else: e is at an interface other than i and j; both sides pass it
            -- straight through to the shared base `s` (one lemma, used twice).
            simp only [attachDrive, attachEntryStep]
            rw [if_neg hei, if_neg hej,
              attachAt_apply_passthrough j β s e hej hTeq,
              attachAt_apply_passthrough i α s e hei hUeq]
            rcases Part.eq_none_or_eq_some (s.1 (hs ++ [e])) with h0 | ⟨y0, h0⟩
            · rw [h0]; simp
            · rw [h0]
              simp only [Part.map_some, Part.bind_some, Part.map_map, Function.comp_def]
              have hInv' : ∃ (hs' : List (P × X)) (vsβ' vsα' : List Y),
                  attachDrive j β s ([], []) (hT ++ [e]) = Part.some (vsβ', (cβ, hs')) ∧
                  attachDrive i α s ([], []) (hU ++ [e]) = Part.some (vsα', (cα, hs')) := by
                refine ⟨hs ++ [e], vsβ ++ [y0], vsα ++ [y0], ?_, ?_⟩
                · rw [attachDrive_passthrough j β s e hej ([], []) hT, hTeq]
                  simp [Part.bind_some, h0]
                · rw [attachDrive_passthrough i α s e hei ([], []) hU, hUeq]
                  simp [Part.bind_some, h0]
              have hih := ih cα cβ (hT ++ [e]) (hU ++ [e]) hInv'
              rw [show (fun rr : List Y × (List (CIn X Y) × List (P × X)) => y0 :: rr.1) =
                  (fun z : List Y => y0 :: z) ∘ Prod.fst from rfl]
              rw [← Part.map_map, ← Part.map_map, hih]
  have hk := key l [] [] [] [] ⟨[], [], [], rfl, rfl⟩
  have hconv : ∀ d : Part (List Y × (List (CIn X Y) × List (P × X))),
      (d.bind fun r => match r.1.getLast? with
        | some y => Part.some y | none => Part.none) =
      (Part.map Prod.fst d).bind fun vs => match vs.getLast? with
        | some y => Part.some y | none => Part.none := by
    intro d; rw [Part.bind_map]
  simp only [attachRaw]
  rw [hconv, hconv, hk]

end General

end Converter

end RandomSystems


/-!
# The protocol function ν and its trace tree (DESIGN §10.5)

The general presentation of a converter as a **single partial
history-function**, with no state carrier and no machine:

`ν : List U × List (Option Y) →. (X ⊕ V)`

— "after outer inputs `u^k` and inner answers `y^l` (cumulative, across
rounds), the converter's next move is an inner query `inl x` or an outer
answer `inr v`."  The converter's own past outputs are recomputable, so
nothing else is data; round boundaries are derived from ν itself.  Memory
classes (memoryless, outer-memoryless = `ofStep`, round counters, general)
are invariance *predicates* on ν, never part of the type.

This module implements the **identity discipline** of DESIGN §10.5:

* `Reach ν` — the trace tree: the pairs ν can actually be consulted at.
  Undefinedness *inside* the tree is honest partiality (a non-productive
  spot); values *off* the tree are junk.
* `JunkFree`, `normalize` (with stability `reach_normalize` and idempotence
  `normalize_normalize`), and **trace equality** `TraceEquiv ν ν' :⇔
  ν* = ν'*` — the working converter identity.
* `toDDC` — the canonical CR18 Def 3.8 object of a protocol function,
  defined on protocol traces only (junk-free by construction; the parse
  relation `ParsesTo` is deterministic and prefix-closed, which gives
  `Valid` with no further conditions).
* `toDDC_normalize` / `toDDC_congr` — the discipline cashed as theorems:
  `toDDC` only reads ν on its trace tree, so trace-equal protocol functions
  are literally the same DDC.

Stress tests against the worked examples (`simpleFn`, `queryLimitFn`, a
junk-carrying variant) are at the end of the file: the trace trees are
characterized in closed form and confirmed against the pen-and-paper
expectations of DESIGN §10.5.
-/

namespace RandomSystems

/-- A successful `Option`-valued `mapM` preserves list length.  (Answer
histories in this development live in `Y ∪ {⊥}`; sequencing one is the standing
way to say "every answer of this segment is proper", and its length is what the
round counters compare against.) -/
theorem mapM_length {A B : Type*} (f : A → Option B)
    {values : List A} {decoded : List B} (equation : values.mapM f = some decoded) :
    decoded.length = values.length := by
  induction values generalizing decoded with
  | nil =>
      change some [] = some decoded at equation
      have decodedEquation : ([] : List B) = decoded := Option.some.inj equation
      subst decoded
      rfl
  | cons value rest induction =>
      simp only [List.mapM_cons] at equation
      cases headEquation : f value with
      | none => simp [headEquation] at equation
      | some head =>
          simp only [headEquation] at equation
          cases tailEquation : rest.mapM f with
          | none => simp [tailEquation] at equation
          | some tail =>
              rw [tailEquation] at equation
              change some (head :: tail) = some decoded at equation
              have decodedEquation : head :: tail = decoded := Option.some.inj equation
              subst decoded
              simp only [List.length_cons]
              exact congrArg Nat.succ (induction tailEquation)

namespace Converter

open scoped System

universe u v w z

/-- DESIGN §10.5: a converter as a single partial history-function — given
the outer inputs and the (cumulative) inner answers so far, the next move.
No state, no machine; round boundaries are derived from the function
itself. -/
abbrev ProtocolFn (U : Type u) (V : Type w) (X : Type z) (Y : Type v) :=
  List U × List (Option Y) →. X ⊕ V

variable {U : Type u} {V : Type w} {X : Type z} {Y : Type v}

/-! ### The trace tree -/

/-- **The trace tree of ν**: the least set of `(outer inputs, inner answers)`
pairs at which ν can actually be consulted.  A first outer input opens the
tree; after a query (`inl`), *every* answer extends (the converter does not
know the system); after an outer answer (`inr`), *every* next outer input
extends.  Reachable pairs where ν is undefined are non-productive spots
(application diverges); values off the tree are junk. -/
inductive Reach (ν : ProtocolFn U V X Y) : List U × List (Option Y) → Prop
  | first (u : U) : Reach ν ([u], [])
  | answer {us : List U} {ys : List (Option Y)} {x : X} (hr : Reach ν (us, ys))
      (hx : Sum.inl x ∈ ν (us, ys)) (y : Option Y) : Reach ν (us, ys ++ [y])
  | next {us : List U} {ys : List (Option Y)} {v : V} (hr : Reach ν (us, ys))
      (hv : Sum.inr v ∈ ν (us, ys)) (u : U) : Reach ν (us ++ [u], ys)

/-- Every tree pair has a nonempty outer history. -/
theorem Reach.ne_nil {ν : ProtocolFn U V X Y}
    {p : List U × List (Option Y)} (h : Reach ν p) : p.1 ≠ [] := by
  induction h with
  | first u => simp
  | answer hr hx y ih => exact ih
  | next hr hv u ih => simp

/-- Junk-freedom: ν has values only on its own trace tree.  A `Prop`, not a
subtype — constructors produce junk-free values, mirroring how CR18
Def 3.8's query bound stays a predicate. -/
def JunkFree (ν : ProtocolFn U V X Y) : Prop :=
  ∀ p, (ν p).Dom → Reach ν p

/-- CR18 **Definition 3.8**'s finite-bound clause **localized at a single
pair**: from `p`, no streak of `B` consecutive queries opens.  This is the
whole mathematical content of the clause; the quantifier that carries `B`
over the trace tree is a separate, and consequential, choice — see
`AnswersWithin` (uniform), `AnswersWithinDepth` (uniform in the answers)
and `AnswersEventually` (pointwise). -/
def AnswersWithinAt (ν : ProtocolFn U V X Y)
    (p : List U × List (Option Y)) (B : ℕ) : Prop :=
  ∀ ext : List (Option Y), B ≤ ext.length →
    ¬ ∀ k (_ : k < ext.length), ∃ x, Sum.inl x ∈ ν (p.1, p.2 ++ ext.take k)

/-- A larger budget is a weaker demand. -/
theorem AnswersWithinAt.mono {ν : ProtocolFn U V X Y}
    {p : List U × List (Option Y)} {B B' : ℕ}
    (h : AnswersWithinAt ν p B) (hle : B ≤ B') : AnswersWithinAt ν p B' :=
  fun ext hlen => h ext (le_trans hle hlen)

/-- CR18 **Definition 3.8**, the finite-bound clause, verbatim: "There is
a finite upper bound on the number of consecutive outputs of the form
`(in, x)`."  On the trace tree: no reachable pair opens a streak of `B`
consecutive queries.  Silence (a filter going undefined, §3.4.3) remains
allowed — the clause bounds query streaks, nothing more.

**Quantifier order.**  This reads the clause with *one* `B` good at *every*
reachable pair (`∃B ∀p`).  Def 3.8's own prose is weaker — the converter
"invokes the system a finite number of times … and then returns an output",
i.e. `∀p ∃B` (`AnswersEventually`).  The two differ exactly by finiteness of
`sup_p B p`, and the gap is inhabited: `roundGrowthFn` below satisfies the
prose and fails this predicate.  The uniform reading is nevertheless the one
the downstream theory needs; see the `AnswersWithinDepth` docstring. -/
def AnswersWithin (ν : ProtocolFn U V X Y) (B : ℕ) : Prop :=
  ∀ p, Reach ν p → ∀ ext : List (Option Y), B ≤ ext.length →
    ¬ ∀ k (_ : k < ext.length), ∃ x, Sum.inl x ∈ ν (p.1, p.2 ++ ext.take k)

/-- The uniform clause **is** the pointwise clause, quantified over the tree
with a fixed budget.  Definitional: the factorization renames nothing. -/
theorem answersWithin_iff_forall_at (ν : ProtocolFn U V X Y) (B : ℕ) :
    AnswersWithin ν B ↔ ∀ p, Reach ν p → AnswersWithinAt ν p B :=
  Iff.rfl

/-- Localize a uniform budget at a reachable pair. -/
theorem AnswersWithin.at_of_reach {ν : ProtocolFn U V X Y} {B : ℕ}
    (h : AnswersWithin ν B) {p : List U × List (Option Y)} (hp : Reach ν p) :
    AnswersWithinAt ν p B :=
  h p hp

/-- CR18 **Definition 3.8**'s finite-bound clause as its own **prose** reads
it: at every reachable pair the converter invokes the system a finite number
of times.  No bound is claimed across the tree — `∀p ∃B`, against
`AnswersWithin`'s `∃B ∀p`.  CR18 states this reading informally and the
uniform one formally, and never discharges the obligation the bound exists
for (after Def 3.9: "one would have to show that the described object `αs`
is indeed a `(𝒰,𝒱)`-DDS.  Intuitively, this is obvious.").  We discharge it
in `EmulateRealization.lean` (`applyRaw_dom`).  That obligation is a
one-round-at-a-time argument and this class carries it mathematically —
though our present proof of `applyRaw_dom` routes through the uniform fuel
of `emuRun_terminal`, so it is not yet a witness to that.  What does *not*
survive the weakening is the layer above — the environment
emulation of MauRen11 Def 15/16 (`Emulable`), whose inner *fuel* is fixed
before the assumed system is; see `AnswersWithinDepth`. -/
def AnswersEventually (ν : ProtocolFn U V X Y) : Prop :=
  ∀ p, Reach ν p → ∃ B, AnswersWithinAt ν p B

/-- The finite-bound clause with a budget **uniform in the inner answers**
but free in the round index: at every reachable pair, a budget depending
only on how many outer inputs have arrived.

This is the class the downstream theory actually needs — weaker than
`AnswersWithin`, stronger than Def 3.8's prose.
`EmulateRealization.lean` turns the budget into *fuel*:
`transcript_apply` runs the emulated environment for `n * B` inner rounds
to cover `n` outer ones, and `Emulable` must produce that fuel **before**
the assumed system `s` is chosen.  A budget that varied with the answers
therefore cannot be summed into any fuel at all — the answers are `s`'s
output — whereas a budget varying with the round index sums to `∑_{i<n} F i`.
`AnswersEventually` is strictly too weak for that; `AnswersWithin` is
strictly stronger than needed (`roundGrowthFn`). -/
def AnswersWithinDepth (ν : ProtocolFn U V X Y) (F : ℕ → ℕ) : Prop :=
  ∀ p, Reach ν p → AnswersWithinAt ν p (F p.1.length)

theorem AnswersWithin.answersWithinDepth {ν : ProtocolFn U V X Y} {B : ℕ}
    (h : AnswersWithin ν B) : AnswersWithinDepth ν (fun _ => B) :=
  fun _ hp => h.at_of_reach hp

theorem AnswersWithinDepth.answersEventually {ν : ProtocolFn U V X Y}
    {F : ℕ → ℕ} (h : AnswersWithinDepth ν F) : AnswersEventually ν :=
  fun p hp => ⟨F p.1.length, h p hp⟩

theorem AnswersWithin.answersEventually {ν : ProtocolFn U V X Y} {B : ℕ}
    (h : AnswersWithin ν B) : AnswersEventually ν :=
  h.answersWithinDepth.answersEventually

/-- CR18 **Definition 3.8**, the input-alphabet clause, verbatim: "After
an output `(in, x)` the input alphabet is `Y`" — a DDC never moves past
the completion symbol `⊥`: at any reachable pair whose answers contain a
`none`, ν is silent.  (`Reach` extends the tree by *every* answer after
a query — Def 3.3's completed alphabet — so the clause is a definedness
restriction, not a tree restriction.) -/
def AnswersInY (ν : ProtocolFn U V X Y) : Prop :=
  ∀ p, Reach ν p → none ∈ p.2 → ¬ (ν p).Dom

/-- CR18 **Definition 3.8** as a predicate on protocol functions (the
`IsOfStep` pattern): ν is a deterministic discrete converter iff it
answers in `Y` (never moves past a `⊥`, `AnswersInY`) and has a finite
bound on consecutive inner queries (`AnswersWithin`). -/
def IsDDC (ν : ProtocolFn U V X Y) : Prop :=
  AnswersInY ν ∧ ∃ B, AnswersWithin ν B

/-- CR18 **Definition 3.8** read as its own prose reads it: the
input-alphabet clause, and a *pointwise* finite bound on query streaks.
Strictly weaker than `IsDDC` (`roundGrowthFn`), and the class every one of
this development's `isDDC_*` constructions lands in a fortiori
(`IsDDC.isDDCEventually`). -/
def IsDDCEventually (ν : ProtocolFn U V X Y) : Prop :=
  AnswersInY ν ∧ AnswersEventually ν

/-- Every DDC in the uniform sense is one in the prose sense: the 14
`isDDC_*` producers of this development remain valid witnesses for the
weaker class.  The converse fails — `roundGrowthFn`. -/
theorem IsDDC.isDDCEventually {ν : ProtocolFn U V X Y} (h : IsDDC ν) :
    IsDDCEventually ν :=
  ⟨h.1, h.2.elim fun _ hB => hB.answersEventually⟩

/-! ### Normalization and trace equality -/

/-- The canonical representative: ν restricted to its trace tree. -/
def normalize (ν : ProtocolFn U V X Y) : ProtocolFn U V X Y :=
  fun p => ⟨(ν p).Dom ∧ Reach ν p, fun h => (ν p).get h.1⟩

theorem mem_normalize_iff (ν : ProtocolFn U V X Y) (p : List U × List (Option Y))
    (m : X ⊕ V) :
    m ∈ normalize ν p ↔ m ∈ ν p ∧ Reach ν p := by
  constructor
  · rintro ⟨⟨hd, hr⟩, rfl⟩
    exact ⟨Part.get_mem hd, hr⟩
  · rintro ⟨hm, hr⟩
    have hd : (ν p).Dom := Part.dom_iff_mem.mpr ⟨m, hm⟩
    exact ⟨⟨hd, hr⟩, Part.get_eq_of_mem hm hd⟩

/-- **Stability**: normalization does not change the trace tree — reachability
only consults tree pairs, whose values survive the restriction. -/
theorem reach_normalize (ν : ProtocolFn U V X Y) (p : List U × List (Option Y)) :
    Reach (normalize ν) p ↔ Reach ν p := by
  constructor
  · intro h
    induction h with
    | first u => exact Reach.first u
    | answer hr hx y ih =>
        exact Reach.answer ih ((mem_normalize_iff ν _ _).mp hx).1 y
    | next hr hv u ih =>
        exact Reach.next ih ((mem_normalize_iff ν _ _).mp hv).1 u
  · intro h
    induction h with
    | first u => exact Reach.first u
    | answer hr hx y ih =>
        exact Reach.answer ih ((mem_normalize_iff ν _ _).mpr ⟨hx, hr⟩) y
    | next hr hv u ih =>
        exact Reach.next ih ((mem_normalize_iff ν _ _).mpr ⟨hv, hr⟩) u

/-- **Idempotence**: junk-free representatives are canonical. -/
theorem normalize_normalize (ν : ProtocolFn U V X Y) :
    normalize (normalize ν) = normalize ν := by
  funext p
  apply Part.ext
  intro m
  rw [mem_normalize_iff, mem_normalize_iff, reach_normalize]
  tauto

theorem junkFree_normalize (ν : ProtocolFn U V X Y) : JunkFree (normalize ν) := by
  rintro p ⟨hd, hr⟩
  exact (reach_normalize ν p).mpr hr

theorem normalize_eq_self_of_junkFree {ν : ProtocolFn U V X Y}
    (h : JunkFree ν) : normalize ν = ν := by
  funext p
  apply Part.ext
  intro m
  rw [mem_normalize_iff]
  exact ⟨fun hm => hm.1, fun hm => ⟨hm, h p (Part.dom_iff_mem.mpr ⟨m, hm⟩)⟩⟩

/-- **Trace equality** — the working converter identity (DESIGN §10.5):
agreement of the canonical junk-free representatives.  Strictly finer than
apply-equality (separated by dead queries), strictly coarser than raw
equality (junk invisible). -/
def TraceEquiv (ν ν' : ProtocolFn U V X Y) : Prop :=
  normalize ν = normalize ν'

theorem TraceEquiv.refl (ν : ProtocolFn U V X Y) : TraceEquiv ν ν := rfl

theorem TraceEquiv.symm {ν ν' : ProtocolFn U V X Y} (h : TraceEquiv ν ν') :
    TraceEquiv ν' ν := Eq.symm h

theorem TraceEquiv.trans {ν₁ ν₂ ν₃ : ProtocolFn U V X Y}
    (h₁ : TraceEquiv ν₁ ν₂) (h₂ : TraceEquiv ν₂ ν₃) : TraceEquiv ν₁ ν₃ :=
  Eq.trans h₁ h₂

theorem traceEquiv_normalize (ν : ProtocolFn U V X Y) :
    TraceEquiv ν (normalize ν) :=
  (normalize_normalize ν).symm

/-- Two protocol functions that agree on each other's trace trees are trace
equal — the workhorse for identifying a junk-carrying presentation with its
clean version. -/
theorem reach_mono_of_eqOn {ν ν' : ProtocolFn U V X Y}
    (h : ∀ p, Reach ν p → ν p = ν' p) {p : List U × List (Option Y)}
    (hp : Reach ν p) : Reach ν' p := by
  induction hp with
  | first u => exact Reach.first u
  | answer hr hx y ih => exact Reach.answer ih (h _ hr ▸ hx) y
  | next hr hv u ih => exact Reach.next ih (h _ hr ▸ hv) u

theorem traceEquiv_of_eqOn_reach {ν ν' : ProtocolFn U V X Y}
    (h : ∀ p, Reach ν p → ν p = ν' p)
    (h' : ∀ p, Reach ν' p → ν' p = ν p) :
    TraceEquiv ν ν' := by
  funext p
  apply Part.ext
  intro m
  rw [mem_normalize_iff, mem_normalize_iff]
  constructor
  · rintro ⟨hm, hr⟩
    exact ⟨h p hr ▸ hm, reach_mono_of_eqOn h hr⟩
  · rintro ⟨hm, hr⟩
    exact ⟨h' p hr ▸ hm, reach_mono_of_eqOn h' hr⟩

/-! ### The Def 3.8 clauses are trace invariants -/

/-- Trace-equal protocol functions have the same trace trees. -/
theorem reach_congr {ν ν' : ProtocolFn U V X Y} (h : TraceEquiv ν ν')
    (p : List U × List (Option Y)) : Reach ν p ↔ Reach ν' p := by
  rw [← reach_normalize ν, h, reach_normalize]

/-- Trace-equal protocol functions have the same members at tree pairs. -/
theorem mem_congr_of_reach {ν ν' : ProtocolFn U V X Y} (h : TraceEquiv ν ν')
    {p : List U × List (Option Y)} (hr : Reach ν p) (m : X ⊕ V) :
    m ∈ ν p ↔ m ∈ ν' p := by
  have h1 : m ∈ normalize ν p ↔ m ∈ normalize ν' p := by rw [h]
  rw [mem_normalize_iff, mem_normalize_iff] at h1
  constructor
  · intro hm
    exact (h1.mp ⟨hm, hr⟩).1
  · intro hm
    exact (h1.mpr ⟨hm, (reach_congr h p).mp hr⟩).1

/-- `AnswersInY` is a trace invariant. -/
theorem answersInY_congr {ν ν' : ProtocolFn U V X Y} (h : TraceEquiv ν ν') :
    AnswersInY ν ↔ AnswersInY ν' := by
  have hdom : ∀ p, Reach ν p → ((ν p).Dom ↔ (ν' p).Dom) := by
    intro p hr
    rw [Part.dom_iff_mem, Part.dom_iff_mem]
    exact exists_congr fun m => mem_congr_of_reach h hr m
  constructor
  · intro ha p hrp hnone hd
    exact ha p ((reach_congr h p).mpr hrp) hnone
      ((hdom p ((reach_congr h p).mpr hrp)).mpr hd)
  · intro ha p hrp hnone hd
    exact ha p ((reach_congr h p).mp hrp) hnone
      ((hdom p hrp).mp hd)

/-- `AnswersWithin` is a trace invariant. -/
theorem answersWithin_congr {ν ν' : ProtocolFn U V X Y} (h : TraceEquiv ν ν')
    {B : ℕ} : AnswersWithin ν B ↔ AnswersWithin ν' B := by
  have key : ∀ {μ μ' : ProtocolFn U V X Y}, TraceEquiv μ μ' →
      AnswersWithin μ B → AnswersWithin μ' B := by
    intro μ μ' hμ ha p hrp ext hlen hall
    have hrp' : Reach μ p := (reach_congr hμ p).mpr hrp
    have hreachk : ∀ k, k ≤ ext.length →
        Reach μ (p.1, p.2 ++ ext.take k) := by
      intro k
      induction k with
      | zero =>
          intro _
          simpa only [List.take_zero, List.append_nil] using hrp'
      | succ j ih =>
          intro hjk
          have hj : j < ext.length := by omega
          obtain ⟨x, hx⟩ := hall j hj
          have hx' : Sum.inl x ∈ μ (p.1, p.2 ++ ext.take j) :=
            (mem_congr_of_reach hμ (ih (by omega)) _).mpr hx
          have hnext := Reach.answer (ih (by omega)) hx' (ext[j]'hj)
          rw [List.append_assoc, List.take_concat_get' ext j hj] at hnext
          exact hnext
    refine ha p hrp' ext hlen fun k hk => ?_
    obtain ⟨x, hx⟩ := hall k hk
    exact ⟨x, (mem_congr_of_reach hμ (hreachk k (by omega)) _).mpr hx⟩
  exact ⟨key h, key h.symm⟩

/-- `IsDDC` is a trace invariant. -/
theorem isDDC_congr {ν ν' : ProtocolFn U V X Y} (h : TraceEquiv ν ν') :
    IsDDC ν ↔ IsDDC ν' := by
  unfold IsDDC
  rw [answersInY_congr h]
  exact and_congr_right fun _ =>
    exists_congr fun B => answersWithin_congr h

/-! ### The canonical Def 3.8 object: `toDDC`

The parse relation `ParsesTo ν l p` reads a converter history left-to-right,
checking at each element that ν's value at the current pair permits it (an
answer — `⊥` included, Def 3.8's `Y ∪ {⊥}` input alphabet — only while a
query is pending, a fresh outer input only once the round has answered; an
off-protocol label has no parse).  It is deterministic and prefix-closed,
which makes `toDDC ν` a valid DDC with no side conditions. -/

/-- Left-to-right trace parse from a given pair. -/
def ParsesToAux (ν : ProtocolFn U V X Y) :
    List U × List (Option Y) → List (DDC.CIn U Y) → List U × List (Option Y) → Prop
  | st, [], p => p = st
  | st, Sum.inl (InLabel.outside, u) :: rest, p =>
      (∃ v, Sum.inr v ∈ ν st) ∧ ParsesToAux ν (st.1 ++ [u], st.2) rest p
  | st, Sum.inr (InLabel.inside, oy) :: rest, p =>
      (∃ x, Sum.inl x ∈ ν st) ∧ ParsesToAux ν (st.1, st.2 ++ [oy]) rest p
  | _, _ :: _, _ => False

/-- A converter history parses to a pair: it must open with an outer input. -/
def ParsesTo (ν : ProtocolFn U V X Y) :
    List (DDC.CIn U Y) → List U × List (Option Y) → Prop
  | [], _ => False
  | Sum.inl (InLabel.outside, u) :: rest, p => ParsesToAux ν ([u], []) rest p
  | _ :: _, _ => False

theorem parsesTo_nil (ν : ProtocolFn U V X Y) (p : List U × List (Option Y)) :
    ¬ ParsesTo ν [] p :=
  fun h => h

theorem parsesToAux_unique (ν : ProtocolFn U V X Y) :
    ∀ {l : List (DDC.CIn U Y)} {st p p'},
      ParsesToAux ν st l p → ParsesToAux ν st l p' → p = p' := by
  intro l
  induction l with
  | nil =>
      intro st p p' h h'
      exact h.trans h'.symm
  | cons a rest ih =>
      intro st p p' h h'
      rcases a with ⟨lbl, u⟩ | ⟨lbl, oy⟩ <;> cases lbl
      · exact h.elim
      · exact ih h.2 h'.2
      · exact ih h.2 h'.2
      · exact h.elim

theorem parsesTo_unique {ν : ProtocolFn U V X Y} {l : List (DDC.CIn U Y)}
    {p p' : List U × List (Option Y)}
    (h : ParsesTo ν l p) (h' : ParsesTo ν l p') : p = p' := by
  cases l with
  | nil => exact h.elim
  | cons a rest =>
      rcases a with ⟨lbl, u⟩ | ⟨lbl, oy⟩ <;> cases lbl
      · exact h.elim
      · exact parsesToAux_unique ν h h'
      · exact h.elim
      · exact h.elim

theorem parsesToAux_append (ν : ProtocolFn U V X Y) :
    ∀ {l₁ l₂ : List (DDC.CIn U Y)} {st p},
      ParsesToAux ν st (l₁ ++ l₂) p ↔
        ∃ q, ParsesToAux ν st l₁ q ∧ ParsesToAux ν q l₂ p := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ st p
      constructor
      · intro h
        exact ⟨st, rfl, h⟩
      · rintro ⟨q, rfl, h⟩
        exact h
  | cons a rest ih =>
      intro l₂ st p
      rcases a with ⟨lbl, u⟩ | ⟨lbl, oy⟩ <;> cases lbl
      · constructor
        · intro h; exact h.elim
        · rintro ⟨q, h, -⟩; exact h.elim
      · show ((∃ v, Sum.inr v ∈ ν st) ∧ ParsesToAux ν _ (rest ++ l₂) p) ↔ _
        rw [ih]
        constructor
        · rintro ⟨hv, q, h₁, h₂⟩
          exact ⟨q, ⟨hv, h₁⟩, h₂⟩
        · rintro ⟨q, ⟨hv, h₁⟩, h₂⟩
          exact ⟨hv, q, h₁, h₂⟩
      · show ((∃ x, Sum.inl x ∈ ν st) ∧ ParsesToAux ν _ (rest ++ l₂) p) ↔ _
        rw [ih]
        constructor
        · rintro ⟨hx, q, h₁, h₂⟩
          exact ⟨q, ⟨hx, h₁⟩, h₂⟩
        · rintro ⟨q, ⟨hx, h₁⟩, h₂⟩
          exact ⟨hx, q, h₁, h₂⟩
      · constructor
        · intro h; exact h.elim
        · rintro ⟨q, h, -⟩; exact h.elim

/-- Parses land in the trace tree. -/
theorem reach_of_parsesToAux (ν : ProtocolFn U V X Y) :
    ∀ {l : List (DDC.CIn U Y)} {st p},
      ParsesToAux ν st l p → Reach ν st → Reach ν p := by
  intro l
  induction l with
  | nil =>
      intro st p h hst
      rw [show p = st from h]
      exact hst
  | cons a rest ih =>
      intro st p h hst
      rcases a with ⟨lbl, u⟩ | ⟨lbl, oy⟩ <;> cases lbl
      · exact h.elim
      · obtain ⟨⟨v, hv⟩, hrest⟩ := h
        exact ih hrest (Reach.next hst hv u)
      · obtain ⟨⟨x, hx⟩, hrest⟩ := h
        exact ih hrest (Reach.answer hst hx oy)
      · exact h.elim

theorem ParsesTo.reach {ν : ProtocolFn U V X Y} {l : List (DDC.CIn U Y)}
    {p : List U × List (Option Y)} (h : ParsesTo ν l p) : Reach ν p := by
  cases l with
  | nil => exact h.elim
  | cons a rest =>
      rcases a with ⟨lbl, u⟩ | ⟨lbl, oy⟩ <;> cases lbl
      · exact h.elim
      · exact reach_of_parsesToAux ν h (Reach.first u)
      · exact h.elim
      · exact h.elim

/-- Prefix closure of the parse, with the intermediate pair's definedness
witnessed whenever the history continues. -/
theorem parsesTo_prefix {ν : ProtocolFn U V X Y} {l₁ l₂ : List (DDC.CIn U Y)}
    {p : List U × List (Option Y)}
    (h : ParsesTo ν (l₁ ++ l₂) p) (h₁ : l₁ ≠ []) :
    ∃ q, ParsesTo ν l₁ q ∧ (l₂ ≠ [] → (ν q).Dom) := by
  cases l₁ with
  | nil => exact absurd rfl h₁
  | cons a rest =>
      rcases a with ⟨lbl, u⟩ | ⟨lbl, oy⟩ <;> cases lbl
      · exact h.elim
      · rw [show ((Sum.inl (InLabel.outside, u) :: rest : List (DDC.CIn U Y)) ++ l₂)
            = Sum.inl (InLabel.outside, u) :: (rest ++ l₂) from rfl] at h
        rw [show ParsesTo ν (Sum.inl (InLabel.outside, u) :: (rest ++ l₂)) p
            = ParsesToAux ν ([u], []) (rest ++ l₂) p from rfl] at h
        rw [parsesToAux_append] at h
        obtain ⟨q, hq, htail⟩ := h
        refine ⟨q, hq, ?_⟩
        intro hne
        cases l₂ with
        | nil => exact absurd rfl hne
        | cons b l₂' =>
            rcases b with ⟨lbl, u'⟩ | ⟨lbl, oy'⟩ <;> cases lbl
            · exact htail.elim
            · obtain ⟨⟨v, hv⟩, -⟩ := htail
              exact Part.dom_iff_mem.mpr ⟨_, hv⟩
            · obtain ⟨⟨x, hx⟩, -⟩ := htail
              exact Part.dom_iff_mem.mpr ⟨_, hx⟩
            · exact htail.elim
      · exact h.elim
      · exact h.elim

/-- The raw function of `toDDC`: at a history that parses to `p`, the move ν
prescribes at `p` (in converter-output alphabet); no parse, no value. -/
noncomputable def toDDCRaw (ν : ProtocolFn U V X Y) :
    System.Raw (DDC.CIn U Y) (DDC.COut V X) :=
  fun l => (Part.assert (∃ p, ParsesTo ν l p) fun h => ν h.choose).map DDC.moveOf

theorem mem_toDDCRaw_iff (ν : ProtocolFn U V X Y) (l : List (DDC.CIn U Y))
    (o : DDC.COut V X) :
    o ∈ toDDCRaw ν l ↔
      ∃ p, ParsesTo ν l p ∧ ∃ m ∈ ν p, o = DDC.moveOf m := by
  rw [toDDCRaw, Part.mem_map_iff]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [Part.mem_assert_iff] at hm
    obtain ⟨h, hm⟩ := hm
    exact ⟨h.choose, h.choose_spec, m, hm, rfl⟩
  · rintro ⟨p, hp, m, hm, rfl⟩
    refine ⟨m, ?_, rfl⟩
    rw [Part.mem_assert_iff]
    refine ⟨⟨p, hp⟩, ?_⟩
    have hcp : (⟨p, hp⟩ : ∃ q, ParsesTo ν l q).choose = p :=
      parsesTo_unique (Exists.choose_spec _) hp
    rw [hcp]
    exact hm

/-- **The canonical CR18 Def 3.8 object of a protocol function** — junk-free
by construction (defined on protocol traces only), `Valid` with no side
conditions (the ν presentation needs no validity bureaucracy; the parse
relation is prefix-closed). -/
noncomputable def toDDC (ν : ProtocolFn U V X Y) : DDC U V X Y :=
  ⟨toDDCRaw ν, by
    refine ⟨?_, ?_⟩
    · rw [PFun.mem_dom]
      rintro ⟨o, ho⟩
      rw [mem_toDDCRaw_iff] at ho
      obtain ⟨p, hp, -⟩ := ho
      exact parsesTo_nil ν p hp
    · intro l₁ l₂ hpre hne hdom
      obtain ⟨t, rfl⟩ := hpre
      cases t with
      | nil => simpa using hdom
      | cons b t' =>
          rw [PFun.mem_dom] at hdom
          obtain ⟨o, ho⟩ := hdom
          rw [mem_toDDCRaw_iff] at ho
          obtain ⟨p, hp, -⟩ := ho
          obtain ⟨q, hq, hdomq⟩ := parsesTo_prefix hp hne
          have hd : (ν q).Dom := hdomq (by simp)
          rw [PFun.mem_dom]
          refine ⟨DDC.moveOf ((ν q).get hd), ?_⟩
          rw [mem_toDDCRaw_iff]
          exact ⟨q, hq, (ν q).get hd, Part.get_mem hd, rfl⟩⟩

@[simp] theorem toDDC_toPFun (ν : ProtocolFn U V X Y) :
    (toDDC ν).1 = toDDCRaw ν := rfl

/-- `toDDC` reads ν only on its trace tree: normalization is invisible. -/
theorem parsesToAux_normalize (ν : ProtocolFn U V X Y) :
    ∀ {l : List (DDC.CIn U Y)} {st p}, Reach ν st →
      (ParsesToAux (normalize ν) st l p ↔ ParsesToAux ν st l p) := by
  intro l
  induction l with
  | nil => intro st p _; exact Iff.rfl
  | cons a rest ih =>
      intro st p hst
      rcases a with ⟨lbl, u⟩ | ⟨lbl, oy⟩ <;> cases lbl
      · exact Iff.rfl
      · show ((∃ v, Sum.inr v ∈ normalize ν st) ∧ _) ↔ ((∃ v, Sum.inr v ∈ ν st) ∧ _)
        constructor
        · rintro ⟨⟨v, hv⟩, hrest⟩
          have hv' : Sum.inr v ∈ ν st := ((mem_normalize_iff ν st _).mp hv).1
          exact ⟨⟨v, hv'⟩, (ih (Reach.next hst hv' u)).mp hrest⟩
        · rintro ⟨⟨v, hv⟩, hrest⟩
          exact ⟨⟨v, (mem_normalize_iff ν st _).mpr ⟨hv, hst⟩⟩,
            (ih (Reach.next hst hv u)).mpr hrest⟩
      · show ((∃ x, Sum.inl x ∈ normalize ν st) ∧ _) ↔
          ((∃ x, Sum.inl x ∈ ν st) ∧ _)
        constructor
        · rintro ⟨⟨x, hx⟩, hrest⟩
          have hx' : Sum.inl x ∈ ν st := ((mem_normalize_iff ν st _).mp hx).1
          exact ⟨⟨x, hx'⟩, (ih (Reach.answer hst hx' oy)).mp hrest⟩
        · rintro ⟨⟨x, hx⟩, hrest⟩
          exact ⟨⟨x, (mem_normalize_iff ν st _).mpr ⟨hx, hst⟩⟩,
            (ih (Reach.answer hst hx oy)).mpr hrest⟩
      · exact Iff.rfl

theorem parsesTo_normalize (ν : ProtocolFn U V X Y) (l : List (DDC.CIn U Y))
    (p : List U × List (Option Y)) :
    ParsesTo (normalize ν) l p ↔ ParsesTo ν l p := by
  cases l with
  | nil => exact Iff.rfl
  | cons a rest =>
      rcases a with ⟨lbl, u⟩ | ⟨lbl, oy⟩ <;> cases lbl
      · exact Iff.rfl
      · exact parsesToAux_normalize ν (Reach.first u)
      · exact Iff.rfl
      · exact Iff.rfl

/-- **The identity discipline, cashed (1/2)**: the canonical DDC of ν and of
its normalization coincide — `toDDC` cannot see junk. -/
theorem toDDC_normalize (ν : ProtocolFn U V X Y) :
    toDDC (normalize ν) = toDDC ν := by
  apply Subtype.ext
  funext l
  apply Part.ext
  intro o
  rw [show (toDDC (normalize ν)).1 = toDDCRaw (normalize ν) from rfl,
    show (toDDC ν).1 = toDDCRaw ν from rfl,
    mem_toDDCRaw_iff, mem_toDDCRaw_iff]
  constructor
  · rintro ⟨p, hp, m, hm, rfl⟩
    exact ⟨p, (parsesTo_normalize ν l p).mp hp,
      m, ((mem_normalize_iff ν p m).mp hm).1, rfl⟩
  · rintro ⟨p, hp, m, hm, rfl⟩
    exact ⟨p, (parsesTo_normalize ν l p).mpr hp,
      m, (mem_normalize_iff ν p m).mpr ⟨hm, hp.reach⟩, rfl⟩

/-- **The identity discipline, cashed (2/2)**: trace-equal protocol functions
present literally the same Def 3.8 converter (hence a fortiori the same
applied system, for every system). -/
theorem toDDC_congr {ν ν' : ProtocolFn U V X Y} (h : TraceEquiv ν ν') :
    toDDC ν = toDDC ν' := by
  rw [← toDDC_normalize ν, ← toDDC_normalize ν']
  exact congrArg toDDC h

theorem apply_toDDC_congr {ν ν' : ProtocolFn U V X Y} (h : TraceEquiv ν ν')
    (S : System.DDS X Y) :
    DDC.apply (toDDC ν) S = DDC.apply (toDDC ν') S := by
  rw [toDDC_congr h]

/-! ### Stress tests (DESIGN §10.5)

The worked examples, with their trace trees characterized in closed form and
checked against the pen-and-paper expectations.  With the `Y ∪ {⊥}` answer
alphabet (CR18 Def 3.8) the converters are *silent on `⊥`*: an answer
branch fires only on a proper answer `some y`.  Consequently the raw
(length-only) bodies carry invisible junk at improper-answer pairs — those
pairs are off the tree, hence invisible through
`normalize`/`TraceEquiv`/`toDDC` — and the tree characterizations record
the **someness discipline**: every answer consumed along a trace is proper.

* `simpleFn` (fixed arity 1 — lengths determine the round position): the
  tree is the length lattice `{k = l+1} ∪ {k = l > 0}` refined by the
  someness discipline (`reach_simpleFn_iff`).
* `queryLimitFn q` (the `[q]` filter — a *round counter*, the first
  converter outside the outer-memoryless class): the tree is the same
  length lattice cut at the budget, **including the breach pair**
  `(q+1 outer inputs, q answers)`, on which ν is *undefined* — the
  `(q+1)`-st query is a non-productive spot of the tree, not junk, exactly
  CR18 Def 3.10's "undefined as of the `(q+1)`-st query".
* `simpleFnJunk` (a junk-carrying variant of `simpleFn`): *not* junk-free,
  *not* raw-equal to `simpleFn`, but `TraceEquiv` to it — so `toDDC`
  identifies them (`toDDC_congr`).  Junk is invisible, exactly as the
  discipline demands. -/

section StressTests

/-- The simple converter `(c, d)` as a protocol function.  Fixed inner arity
1, so the round position is determined by lengths: one more input than
answers = query pending; equal (nonzero) lengths = round complete — and the
converter answers only if the round's answer was proper (`some y`); on `⊥`
it is silent. -/
def simpleFn (c : U → X) (d : Y → V) : ProtocolFn U V X Y := fun p =>
  if h : p.1.length = p.2.length + 1 then
    Part.some (Sum.inl (c (p.1.getLast (by
      apply List.ne_nil_of_length_pos; omega))))
  else if h' : p.1.length = p.2.length ∧ 0 < p.2.length then
    match p.2.getLast (List.ne_nil_of_length_pos h'.2) with
    | some y => Part.some (Sum.inr (d y))
    | none => Part.none
  else Part.none

theorem simpleFn_inl_inv {c : U → X} {d : Y → V} {us : List U}
    {ys : List (Option Y)} {x : X} (h : Sum.inl x ∈ simpleFn c d (us, ys)) :
    us.length = ys.length + 1 := by
  simp only [simpleFn] at h
  split_ifs at h with h1 h2
  · exact h1
  · split at h <;> simp at h
  · simp at h

theorem simpleFn_inr_inv {c : U → X} {d : Y → V} {us : List U}
    {ys : List (Option Y)} {v : V} (h : Sum.inr v ∈ simpleFn c d (us, ys)) :
    us.length = ys.length ∧ ∃ (h0 : 0 < ys.length) (y : Y),
      ys.getLast (List.ne_nil_of_length_pos h0) = some y ∧ v = d y := by
  simp only [simpleFn] at h
  split_ifs at h with h1 h2
  · simp at h
  · split at h
    · rename_i y hy
      simp only [Part.mem_some_iff, Sum.inr.injEq] at h
      exact ⟨h2.1, h2.2, y, hy, h⟩
    · simp at h
  · simp at h

theorem simpleFn_inl_mem (c : U → X) (d : Y → V) {us : List U}
    {ys : List (Option Y)} (h : us.length = ys.length + 1) :
    Sum.inl (c (us.getLast (by apply List.ne_nil_of_length_pos; omega))) ∈
      simpleFn c d (us, ys) := by
  simp only [simpleFn]
  rw [dif_pos h]
  exact Part.mem_some _

theorem simpleFn_inr_mem (c : U → X) (d : Y → V) {us : List U}
    {ys : List (Option Y)} (h : us.length = ys.length) (h0 : 0 < ys.length)
    {y : Y} (hy : ys.getLast (List.ne_nil_of_length_pos h0) = some y) :
    Sum.inr (d y) ∈ simpleFn c d (us, ys) := by
  simp only [simpleFn]
  rw [dif_neg (by omega), dif_pos ⟨h, h0⟩, hy]
  exact Part.mem_some _

/-- **Stress test — expected tree shape.**  The trace tree of `simpleFn` is
the length lattice `{k = l+1} ∪ {k = l > 0}` predicted by hand, refined by
the someness discipline: a completed round continues only if its answer was
proper, so every answer along a trace is proper — except possibly the last
one, while its round is still unanswered. -/
theorem reach_simpleFn_iff (c : U → X) (d : Y → V) (p : List U × List (Option Y)) :
    Reach (simpleFn c d) p ↔
      (p.1.length = p.2.length + 1 ∧ ∀ oy ∈ p.2, oy.isSome) ∨
        (p.1.length = p.2.length ∧ 0 < p.1.length ∧
          ∀ oy ∈ p.2.dropLast, oy.isSome) := by
  constructor
  · intro h
    induction h with
    | first u => simp
    | answer hr hx y ih =>
        have hlen := simpleFn_inl_inv hx
        dsimp only at ih ⊢
        rcases ih with ⟨-, hsome⟩ | ⟨h', -, -⟩
        · refine Or.inr ⟨?_, ?_, ?_⟩
          · simp only [List.length_append, List.length_singleton]
            omega
          · omega
          · rw [List.dropLast_concat]
            exact hsome
        · omega
    | next hr hv u ih =>
        rename_i us ys v
        obtain ⟨hlen, h0, y, hy, -⟩ := simpleFn_inr_inv hv
        dsimp only at ih ⊢
        rcases ih with ⟨h', -⟩ | ⟨-, -, hdrop⟩
        · omega
        · have hall : ∀ oy ∈ ys, oy.isSome := by
            intro oy hmem
            rw [← List.dropLast_append_getLast
              (List.ne_nil_of_length_pos h0)] at hmem
            rcases List.mem_append.mp hmem with hm | hm
            · exact hdrop oy hm
            · rw [List.mem_singleton.mp hm, hy]
              rfl
          refine Or.inl ⟨?_, hall⟩
          simp only [List.length_append, List.length_singleton]
          omega
  · obtain ⟨us, ys⟩ := p
    dsimp only
    intro h
    induction ys using List.reverseRecOn generalizing us with
    | nil =>
        simp only [List.length_nil] at h
        rcases h with ⟨h, -⟩ | ⟨h, hpos, -⟩
        · obtain ⟨u, rfl⟩ :=
            List.length_eq_one_iff.mp (by omega : us.length = 1)
          exact Reach.first u
        · exact absurd hpos (by omega)
    | append_singleton ys y ih =>
        have hB : ∀ us' : List U, us'.length = ys.length + 1 →
            (∀ oy ∈ ys, oy.isSome) →
            Reach (simpleFn c d) (us', ys ++ [y]) := by
          intro us' hlen hsome
          exact Reach.answer (ih (us := us') (Or.inl ⟨hlen, hsome⟩))
            (simpleFn_inl_mem c d hlen) y
        simp only [List.length_append, List.length_singleton] at h
        rcases h with ⟨h, hsome⟩ | ⟨h, hpos, hsome⟩
        · have hne : us ≠ [] := by
            apply List.ne_nil_of_length_pos
            omega
          obtain ⟨us', u, rfl⟩ := (List.eq_nil_or_concat us).resolve_left hne
          simp only [List.concat_eq_append, List.length_append,
            List.length_singleton] at h ⊢
          obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.mp
            (hsome y (List.mem_append_right _ (List.mem_singleton_self y)))
          exact Reach.next
            (hB us' (by omega)
              (fun oy hm => hsome oy (List.mem_append_left _ hm)))
            (simpleFn_inr_mem c d
              (by simp only [List.length_append, List.length_singleton]; omega)
              (by simp)
              (by rw [List.getLast_concat]; exact hy'))
            u
        · rw [List.dropLast_concat] at hsome
          exact hB us (by omega) hsome

/-- `simpleFn` is silent past a `⊥`: on its tree a `⊥` can only be the
last answer, where both branches refuse. -/
theorem answersInY_simpleFn (c : U → X) (d : Y → V) :
    AnswersInY (simpleFn c d) := by
  rintro ⟨us, ys⟩ hr hn hd
  have hne' : ys ≠ [] := by
    rintro rfl
    simp at hn
  have hsome : ∀ oy ∈ ys.dropLast, oy.isSome := by
    rcases (reach_simpleFn_iff c d (us, ys)).mp hr with ⟨-, hs⟩ | ⟨-, -, hs⟩
    · exact fun oy hm => hs oy (List.mem_of_mem_dropLast hm)
    · exact hs
  have hlast : ys.getLast hne' = none := by
    have hn' := hn
    rw [← List.dropLast_append_getLast hne'] at hn'
    rcases List.mem_append.mp hn' with h' | h'
    · exact absurd (hsome _ h') (by simp)
    · exact (List.mem_singleton.mp h').symm
  rw [Part.dom_iff_mem] at hd
  obtain ⟨m, hm⟩ := hd
  cases m with
  | inl x =>
      have h1 := simpleFn_inl_inv hm
      rcases (reach_simpleFn_iff c d (us, ys)).mp hr with ⟨-, hs⟩ |
        ⟨hlen, -, -⟩
      · exact absurd (hs _ hn) (by simp)
      · have hlen' : us.length = ys.length := hlen
        omega
  | inr v =>
      obtain ⟨-, h0, y, hgl, -⟩ := simpleFn_inr_inv hm
      have h1 : ys.getLast (List.ne_nil_of_length_pos h0) = none := hlast
      rw [h1] at hgl
      simp at hgl

/-- `simpleFn` never opens a streak of two queries: a query forces the
outer history one ahead, which one more answer destroys. -/
theorem answersWithin_simpleFn (c : U → X) (d : Y → V) :
    AnswersWithin (simpleFn c d) 2 := by
  intro p _ ext hlen hall
  obtain ⟨x0, hx0⟩ := hall 0 (by omega)
  obtain ⟨x1, hx1⟩ := hall 1 (by omega)
  have h0 := simpleFn_inl_inv hx0
  have h1 := simpleFn_inl_inv hx1
  simp only [List.length_append, List.length_take] at h0 h1
  omega

/-- `simpleFn` is a DDC (CR18 Def 3.8) — membership in the class. -/
theorem isDDC_simpleFn (c : U → X) (d : Y → V) : IsDDC (simpleFn c d) :=
  ⟨answersInY_simpleFn c d, 2, answersWithin_simpleFn c d⟩

/-- **Smoke test — `toDDC` produces the expected first move**: on the
one-element history "outer input `u`", the canonical DDC of `simpleFn`
queries `c u` inside. -/
theorem toDDC_simpleFn_first_move (c : U → X) (d : Y → V) (u : U) :
    Sum.inr (InLabel.inside, c u) ∈
      (toDDC (simpleFn c d)).1 [Sum.inl (InLabel.outside, u)] := by
  rw [toDDC_toPFun, mem_toDDCRaw_iff]
  refine ⟨([u], []), ?_, Sum.inl (c u), ?_, rfl⟩
  · show ParsesToAux (simpleFn c d) ([u], []) [] ([u], [])
    rfl
  · have h := simpleFn_inl_mem c d (us := [u]) (ys := []) (by simp)
    simpa using h

/-- The identity restriction converter for a decidable predicate on query
histories. It forwards the newest query and its answer exactly while the
current history satisfies `P`, and becomes undefined when `P` is violated. -/
def restrictionFn (P : List X → Prop) [DecidablePred P] :
    ProtocolFn X Y X Y := fun p =>
  if h : p.1.length = p.2.length + 1 ∧ P p.1 then
    Part.some (Sum.inl (p.1.getLast (by
      apply List.ne_nil_of_length_pos
      omega)))
  else if h' : p.1.length = p.2.length ∧ 0 < p.2.length ∧ P p.1 then
    match p.2.getLast (List.ne_nil_of_length_pos h'.2.1) with
    | some y => Part.some (Sum.inr y)
    | none => Part.none
  else
    Part.none

theorem restrictionFn_inl_inv {P : List X → Prop} [DecidablePred P]
    {us : List X} {ys : List (Option Y)} {x : X}
    (h : Sum.inl x ∈ restrictionFn P (us, ys)) :
    us.length = ys.length + 1 ∧ P us := by
  simp only [restrictionFn] at h
  split_ifs at h with hquery hanswer
  · exact hquery
  · split at h <;> simp at h
  · simp at h

theorem restrictionFn_inr_inv {P : List X → Prop} [DecidablePred P]
    {us : List X} {ys : List (Option Y)} {v : Y}
    (h : Sum.inr v ∈ restrictionFn P (us, ys)) :
    us.length = ys.length ∧ P us ∧ ∃ h0 : 0 < ys.length,
      ys.getLast (List.ne_nil_of_length_pos h0) = some v := by
  simp only [restrictionFn] at h
  split_ifs at h with hquery hanswer
  · simp at h
  · split at h
    · rename_i y hy
      simp only [Part.mem_some_iff, Sum.inr.injEq] at h
      exact ⟨hanswer.1, hanswer.2.2, hanswer.2.1, by rw [hy, h]⟩
    · simp at h
  · simp at h

theorem restrictionFn_inl_val {P : List X → Prop} [DecidablePred P]
    {us : List X} {ys : List (Option Y)} {x : X}
    (h : Sum.inl x ∈ restrictionFn P (us, ys)) :
    ∃ hne : us ≠ [], x = us.getLast hne := by
  simp only [restrictionFn] at h
  split_ifs at h with hquery hanswer
  · simp only [Part.mem_some_iff, Sum.inl.injEq] at h
    exact ⟨List.ne_nil_of_length_pos (by omega), h⟩
  · split at h <;> simp at h
  · simp at h

theorem restrictionFn_inl_mem (P : List X → Prop) [DecidablePred P]
    {us : List X} {ys : List (Option Y)}
    (hlen : us.length = ys.length + 1) (hP : P us) :
    Sum.inl (us.getLast (by
      apply List.ne_nil_of_length_pos
      omega)) ∈ restrictionFn P (us, ys) := by
  simp only [restrictionFn]
  rw [dif_pos ⟨hlen, hP⟩]
  exact Part.mem_some _

theorem restrictionFn_inr_mem (P : List X → Prop) [DecidablePred P]
    {us : List X} {ys : List (Option Y)}
    (hlen : us.length = ys.length) (h0 : 0 < ys.length) (hP : P us)
    {y : Y} (hy : ys.getLast (List.ne_nil_of_length_pos h0) = some y) :
    Sum.inr y ∈ restrictionFn P (us, ys) := by
  simp only [restrictionFn]
  rw [dif_neg (by omega), dif_pos ⟨hlen, h0, hP⟩, hy]
  exact Part.mem_some _

/-- The `[q]` query filter as a protocol function — a **round counter**, the
first converter genuinely outside the outer-memoryless (`ofStep`) class:
its move depends on the *lengths* of the history, i.e. on the round number.
(The budget check on the answer branch keeps the never-consulted answered
pairs beyond round `q` silent — without it they would carry junk; the tree
characterization `reach_queryLimitFn_iff` cuts the length lattice at the
budget.  As everywhere under the `Y ∪ {⊥}` alphabet, the answer branch
fires only on a proper answer.) -/
def queryLimitFn (q : ℕ) : ProtocolFn X Y X Y := fun p =>
  if h : p.1.length = p.2.length + 1 ∧ p.1.length ≤ q then
    Part.some (Sum.inl (p.1.getLast (by
      apply List.ne_nil_of_length_pos; omega)))
  else if h' : p.1.length = p.2.length ∧ 0 < p.2.length ∧ p.1.length ≤ q then
    match p.2.getLast (List.ne_nil_of_length_pos h'.2.1) with
    | some y => Part.some (Sum.inr y)
    | none => Part.none
  else Part.none

theorem queryLimitFn_inl_inv {q : ℕ} {us : List X} {ys : List (Option Y)}
    {x : X} (h : Sum.inl x ∈ queryLimitFn q (us, ys)) :
    us.length = ys.length + 1 ∧ us.length ≤ q := by
  simp only [queryLimitFn] at h
  split_ifs at h with h1 h2
  · exact h1
  · split at h <;> simp at h
  · simp at h

theorem queryLimitFn_inr_inv {q : ℕ} {us : List X} {ys : List (Option Y)}
    {v : Y} (h : Sum.inr v ∈ queryLimitFn q (us, ys)) :
    us.length = ys.length ∧ us.length ≤ q ∧ ∃ (h0 : 0 < ys.length),
      ys.getLast (List.ne_nil_of_length_pos h0) = some v := by
  simp only [queryLimitFn] at h
  split_ifs at h with h1 h2
  · simp at h
  · split at h
    · rename_i y hy
      simp only [Part.mem_some_iff, Sum.inr.injEq] at h
      exact ⟨h2.1, h2.2.2, h2.2.1, by rw [hy, h]⟩
    · simp at h
  · simp at h

/-- Move inversion for `queryLimitFn`, query branch, value form: the
forwarded query is the last outer input. -/
theorem queryLimitFn_inl_val {q : ℕ} {us : List X} {ys : List (Option Y)}
    {x : X} (h : Sum.inl x ∈ queryLimitFn q (us, ys)) :
    ∃ hne : us ≠ [], x = us.getLast hne := by
  simp only [queryLimitFn] at h
  split_ifs at h with h1 h2
  · simp only [Part.mem_some_iff, Sum.inl.injEq] at h
    exact ⟨List.ne_nil_of_length_pos (by omega), h⟩
  · split at h <;> simp at h
  · simp at h

theorem queryLimitFn_inl_mem (q : ℕ) {us : List X} {ys : List (Option Y)}
    (h : us.length = ys.length + 1) (hq : us.length ≤ q) :
    Sum.inl (us.getLast (by apply List.ne_nil_of_length_pos; omega)) ∈
      queryLimitFn q (us, ys) := by
  simp only [queryLimitFn]
  rw [dif_pos ⟨h, hq⟩]
  exact Part.mem_some _

theorem queryLimitFn_inr_mem (q : ℕ) {us : List X} {ys : List (Option Y)}
    (h : us.length = ys.length) (h0 : 0 < ys.length) (hq : us.length ≤ q)
    {y : Y} (hy : ys.getLast (List.ne_nil_of_length_pos h0) = some y) :
    Sum.inr y ∈ queryLimitFn q (us, ys) := by
  simp only [queryLimitFn]
  rw [dif_neg (by omega), dif_pos ⟨h, h0, hq⟩, hy]
  exact Part.mem_some _

/-- **Stress test — expected tree shape with a budget.**  The trace tree of
`[q]` is the length lattice cut at the budget, refined by the someness
discipline — and it *includes* the query-pending pairs at round `q+1` (the
breach arrives; ν is undefined there, see `queryLimitFn_breach`). -/
theorem reach_queryLimitFn_iff (q : ℕ) (p : List X × List (Option Y)) :
    Reach (queryLimitFn q) p ↔
      (p.1.length = p.2.length + 1 ∧ p.1.length ≤ q + 1 ∧
          ∀ oy ∈ p.2, oy.isSome) ∨
        (p.1.length = p.2.length ∧ 0 < p.1.length ∧ p.1.length ≤ q ∧
          ∀ oy ∈ p.2.dropLast, oy.isSome) := by
  constructor
  · intro h
    induction h with
    | first u =>
        dsimp only
        refine Or.inl ⟨by simp, ?_, by simp⟩
        simp only [List.length_singleton]
        omega
    | answer hr hx y ih =>
        obtain ⟨hlen, hq⟩ := queryLimitFn_inl_inv hx
        dsimp only at ih ⊢
        rcases ih with ⟨-, -, hsome⟩ | ⟨h', -⟩
        · refine Or.inr ⟨?_, ?_, ?_, ?_⟩
          · simp only [List.length_append, List.length_singleton]
            omega
          · omega
          · omega
          · rw [List.dropLast_concat]
            exact hsome
        · omega
    | next hr hv u ih =>
        rename_i us ys v
        obtain ⟨hlen, hq, h0, hy⟩ := queryLimitFn_inr_inv hv
        dsimp only at ih ⊢
        rcases ih with ⟨h', -⟩ | ⟨-, -, -, hdrop⟩
        · omega
        · have hall : ∀ oy ∈ ys, oy.isSome := by
            intro oy hmem
            rw [← List.dropLast_append_getLast
              (List.ne_nil_of_length_pos h0)] at hmem
            rcases List.mem_append.mp hmem with hm | hm
            · exact hdrop oy hm
            · rw [List.mem_singleton.mp hm, hy]
              rfl
          refine Or.inl ⟨?_, ?_, hall⟩
          · simp only [List.length_append, List.length_singleton]
            omega
          · simp only [List.length_append, List.length_singleton]
            omega
  · obtain ⟨us, ys⟩ := p
    dsimp only
    intro h
    induction ys using List.reverseRecOn generalizing us with
    | nil =>
        simp only [List.length_nil] at h
        rcases h with ⟨h, hq, -⟩ | ⟨h, hpos, -, -⟩
        · obtain ⟨u, rfl⟩ :=
            List.length_eq_one_iff.mp (by omega : us.length = 1)
          exact Reach.first u
        · exact absurd hpos (by omega)
    | append_singleton ys y ih =>
        have hB : ∀ us' : List X, us'.length = ys.length + 1 →
            us'.length ≤ q → (∀ oy ∈ ys, oy.isSome) →
            Reach (queryLimitFn q) (us', ys ++ [y]) := by
          intro us' hlen hq hsome
          exact Reach.answer
            (ih (us := us') (Or.inl ⟨hlen, by omega, hsome⟩))
            (queryLimitFn_inl_mem q hlen hq) y
        simp only [List.length_append, List.length_singleton] at h
        rcases h with ⟨h, hq, hsome⟩ | ⟨h, hpos, hq, hsome⟩
        · have hne : us ≠ [] := by
            apply List.ne_nil_of_length_pos
            omega
          obtain ⟨us', u, rfl⟩ := (List.eq_nil_or_concat us).resolve_left hne
          simp only [List.concat_eq_append, List.length_append,
            List.length_singleton] at h hq ⊢
          obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.mp
            (hsome y (List.mem_append_right _ (List.mem_singleton_self y)))
          exact Reach.next
            (hB us' (by omega) (by omega)
              (fun oy hm => hsome oy (List.mem_append_left _ hm)))
            (queryLimitFn_inr_mem q
              (by simp only [List.length_append, List.length_singleton]; omega)
              (by simp) (by omega)
              (by rw [List.getLast_concat]; exact hy'))
            u
        · rw [List.dropLast_concat] at hsome
          exact hB us (by omega) (by omega) hsome

/-- `queryLimitFn` is silent past a `⊥`: on its tree a `⊥` can only be
the last answer, where both branches refuse. -/
theorem answersInY_queryLimitFn (q : ℕ) :
    AnswersInY (queryLimitFn (X := X) (Y := Y) q) := by
  rintro ⟨us, ys⟩ hr hn hd
  have hne' : ys ≠ [] := by
    rintro rfl
    simp at hn
  have hsome : ∀ oy ∈ ys.dropLast, oy.isSome := by
    rcases (reach_queryLimitFn_iff q (us, ys)).mp hr with ⟨-, -, hs⟩ |
      ⟨-, -, -, hs⟩
    · exact fun oy hm => hs oy (List.mem_of_mem_dropLast hm)
    · exact hs
  have hlast : ys.getLast hne' = none := by
    have hn' := hn
    rw [← List.dropLast_append_getLast hne'] at hn'
    rcases List.mem_append.mp hn' with h' | h'
    · exact absurd (hsome _ h') (by simp)
    · exact (List.mem_singleton.mp h').symm
  rw [Part.dom_iff_mem] at hd
  obtain ⟨m, hm⟩ := hd
  cases m with
  | inl x =>
      obtain ⟨h1, -⟩ := queryLimitFn_inl_inv hm
      rcases (reach_queryLimitFn_iff q (us, ys)).mp hr with ⟨-, -, hs⟩ |
        ⟨hlen, -, -, -⟩
      · exact absurd (hs _ hn) (by simp)
      · have hlen' : us.length = ys.length := hlen
        omega
  | inr v =>
      obtain ⟨-, -, h0, hgl⟩ := queryLimitFn_inr_inv hm
      have h1 : ys.getLast (List.ne_nil_of_length_pos h0) = none := hlast
      rw [h1] at hgl
      simp at hgl

/-- `queryLimitFn` never opens a streak of two queries. -/
theorem answersWithin_queryLimitFn (q : ℕ) :
    AnswersWithin (queryLimitFn (X := X) (Y := Y) q) 2 := by
  intro p _ ext hlen hall
  obtain ⟨x0, hx0⟩ := hall 0 (by omega)
  obtain ⟨x1, hx1⟩ := hall 1 (by omega)
  obtain ⟨h0, -⟩ := queryLimitFn_inl_inv hx0
  obtain ⟨h1, -⟩ := queryLimitFn_inl_inv hx1
  simp only [List.length_append, List.length_take] at h0 h1
  omega

/-- The `[q]` filter is a DDC (CR18 Def 3.8) — membership in the class:
the budget cut restricts the tree, never the two Def 3.8 clauses. -/
theorem isDDC_queryLimitFn (q : ℕ) :
    IsDDC (queryLimitFn (X := X) (Y := Y) q) :=
  ⟨answersInY_queryLimitFn q, 2, answersWithin_queryLimitFn q⟩

/-- **Stress test — the budget breach is a non-productive spot, not junk.**
The pair "q+1 outer inputs, q answers" is *reachable* (the `(q+1)`-st input
arrives), and ν is *undefined* on it — exactly CR18 Def 3.10's "`[q]s` is
undefined as of the `(q+1)`-st query", now read off the tree. -/
theorem queryLimitFn_breach (q : ℕ) (x : X) (y : Y) :
    Reach (queryLimitFn q)
        (List.replicate (q + 1) x, List.replicate q (some y)) ∧
      ¬ ((queryLimitFn q)
        (List.replicate (q + 1) x, List.replicate q (some y))).Dom := by
  constructor
  · rw [reach_queryLimitFn_iff]
    left
    refine ⟨by simp, by simp, fun oy hmem => ?_⟩
    rw [List.eq_of_mem_replicate hmem]
    rfl
  · intro hdom
    obtain ⟨m, hm⟩ := Part.dom_iff_mem.mp hdom
    cases m with
    | inl x' =>
        obtain ⟨-, hq⟩ := queryLimitFn_inl_inv hm
        simp only [List.length_replicate] at hq
        omega
    | inr v =>
        obtain ⟨heq, -⟩ := queryLimitFn_inr_inv hm
        simp only [List.length_replicate] at heq
        omega

/-- A junk-carrying variant of `simpleFn`: an extra (never-consulted) value
at the off-tree pairs `k = l + 2`. -/
def simpleFnJunk (c : U → X) (d : Y → V) (x₀ : X) : ProtocolFn U V X Y :=
  fun p =>
    if p.1.length = p.2.length + 2 then Part.some (Sum.inl x₀)
    else simpleFn c d p

/-- The junk does not enlarge the tree: `simpleFnJunk`'s tree satisfies the
same length constraints (forward direction suffices for the tests). -/
theorem reach_simpleFnJunk_imp {c : U → X} {d : Y → V} {x₀ : X}
    {p : List U × List (Option Y)} (h : Reach (simpleFnJunk c d x₀) p) :
    p.1.length = p.2.length + 1 ∨
      (p.1.length = p.2.length ∧ 0 < p.1.length) := by
  induction h with
  | first u => simp
  | answer hr hx y ih =>
      rename_i us ys x
      dsimp only at ih ⊢
      have hlen : us.length = ys.length + 1 := by
        by_cases hj : us.length = ys.length + 2
        · exfalso
          rcases ih with h' | ⟨h', -⟩ <;> omega
        · rw [show simpleFnJunk c d x₀ (us, ys) = simpleFn c d (us, ys) from
            by simp [simpleFnJunk, hj]] at hx
          exact simpleFn_inl_inv hx
      simp only [List.length_append, List.length_singleton]
      omega
  | next hr hv u ih =>
      rename_i us ys v
      dsimp only at ih ⊢
      have hlen : us.length = ys.length ∧ 0 < ys.length := by
        by_cases hj : us.length = ys.length + 2
        · exfalso
          rcases ih with h' | ⟨h', -⟩ <;> omega
        · rw [show simpleFnJunk c d x₀ (us, ys) = simpleFn c d (us, ys) from
            by simp [simpleFnJunk, hj]] at hv
          obtain ⟨h1, h0, -⟩ := simpleFn_inr_inv hv
          exact ⟨h1, h0⟩
      simp only [List.length_append, List.length_singleton]
      omega

/-- **Stress test — junk is not junk-free**: the discipline detects the
off-tree value. -/
theorem not_junkFree_simpleFnJunk (c : U → X) (d : Y → V) (x₀ : X) (u : U) :
    ¬ JunkFree (simpleFnJunk c d x₀) := by
  intro h
  have hr := h ([u, u], []) (by simp [simpleFnJunk])
  have h2 := reach_simpleFnJunk_imp hr
  simp at h2

/-- **Stress test — junk is invisible to the identity**: the junk-carrying
variant is trace-equal to the clean one … -/
theorem traceEquiv_simpleFnJunk (c : U → X) (d : Y → V) (x₀ : X) :
    TraceEquiv (simpleFnJunk c d x₀) (simpleFn c d) := by
  apply traceEquiv_of_eqOn_reach
  · intro p hp
    have hlen := reach_simpleFnJunk_imp hp
    have hj : ¬ p.1.length = p.2.length + 2 := by
      rcases hlen with h | ⟨h, -⟩ <;> omega
    simp [simpleFnJunk, hj]
  · intro p hp
    have hlen := (reach_simpleFn_iff c d p).mp hp
    have hj : ¬ p.1.length = p.2.length + 2 := by
      rcases hlen with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    simp [simpleFnJunk, hj]

/-- … hence presents the same canonical DDC (`toDDC_congr` in action) … -/
theorem toDDC_simpleFnJunk (c : U → X) (d : Y → V) (x₀ : X) :
    toDDC (simpleFnJunk c d x₀) = toDDC (simpleFn c d) :=
  toDDC_congr (traceEquiv_simpleFnJunk c d x₀)

/-- … while being *raw*-distinct: the junk is real data, only invisible. -/
theorem simpleFnJunk_ne_simpleFn (c : U → X) (d : Y → V) (x₀ : X) (u : U) :
    simpleFnJunk c d x₀ ≠ simpleFn c d := by
  intro h
  have h2 := congrFun h ([u, u], [])
  simp only [simpleFnJunk, simpleFn] at h2
  rw [if_pos (by simp)] at h2
  rw [dif_neg (by simp), dif_neg (by simp)] at h2
  exact Part.some_ne_none _ h2

/-! #### The quantifier gap in Def 3.8

`AnswersWithin` reads Def 3.8's finite-bound clause as `∃B ∀p`; the
definition's own prose reads it `∀p ∃B`.  The two differ by finiteness of
`sup_p B p`, and this section shows the difference is real by inhabiting it.
-/

/-- **Stress test — the `∃B ∀p` / `∀p ∃B` gap is inhabited.**  The converter
that has issued exactly `k²` inner queries once `k` outer inputs have
arrived: on its `k`-th round it queries `2k−1` times, then answers.  At
every reachable pair it invokes the system a finite number of times and then
returns an output — Def 3.8's prose, verbatim — yet no single `B` bounds all
of its streaks.  (Outer and inner alphabets are `Unit`: the growth is in the
round index alone, nothing is hidden in the data.) -/
def roundGrowthFn : ProtocolFn Unit Unit Unit Unit := fun p =>
  if none ∈ p.2 then Part.none
  else if p.2.length < p.1.length * p.1.length then Part.some (Sum.inl ())
  else Part.some (Sum.inr ())

theorem roundGrowthFn_inl_mem {us : List Unit} {ys : List (Option Unit)}
    (hnone : none ∉ ys) (h : ys.length < us.length * us.length) :
    Sum.inl () ∈ roundGrowthFn (us, ys) := by
  simp only [roundGrowthFn, if_neg hnone, if_pos h]
  exact Part.mem_some _

theorem roundGrowthFn_inr_mem {us : List Unit} {ys : List (Option Unit)}
    (hnone : none ∉ ys) (h : ¬ ys.length < us.length * us.length) :
    Sum.inr () ∈ roundGrowthFn (us, ys) := by
  simp only [roundGrowthFn, if_neg hnone, if_neg h]
  exact Part.mem_some _

/-- `roundGrowthFn` satisfies Def 3.8's input-alphabet clause. -/
theorem answersInY_roundGrowthFn : AnswersInY roundGrowthFn := by
  intro p _ hnone hdom
  obtain ⟨mv, hm⟩ := Part.dom_iff_mem.mp hdom
  simp only [roundGrowthFn, if_pos hnone] at hm
  exact Part.notMem_none _ hm

/-- `roundGrowthFn` satisfies the finite-bound clause with a budget uniform
in the answers and growing with the round index — the `AnswersWithinDepth`
class, which is all the downstream fuel arguments need. -/
theorem answersWithinDepth_roundGrowthFn :
    AnswersWithinDepth roundGrowthFn (fun n => n * n + 1) := by
  intro p _ ext hlen hall
  obtain ⟨x, hx⟩ := hall (p.1.length * p.1.length)
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hlen)
  simp only [roundGrowthFn] at hx
  split_ifs at hx with h1 h2
  · exact Part.notMem_none _ hx
  · rw [List.length_append, List.length_take] at h2
    have hmin : min (p.1.length * p.1.length) ext.length
        = p.1.length * p.1.length :=
      min_eq_left (le_trans (Nat.le_succ _) hlen)
    omega
  · simp at hx

/-- Both Def 3.8 clauses hold in the prose reading. -/
theorem isDDCEventually_roundGrowthFn : IsDDCEventually roundGrowthFn :=
  ⟨answersInY_roundGrowthFn,
    answersWithinDepth_roundGrowthFn.answersEventually⟩

/-- One more answered query on the `k`-th round's open streak. -/
theorem reach_roundGrowthFn_step {k m : ℕ}
    (h : Reach roundGrowthFn (List.replicate k (), List.replicate m (some ())))
    (hlt : m < k * k) :
    Reach roundGrowthFn
      (List.replicate k (), List.replicate (m + 1) (some ())) := by
  have hx : Sum.inl () ∈ roundGrowthFn
      (List.replicate k (), List.replicate m (some ())) :=
    roundGrowthFn_inl_mem (by simp) (by simpa using hlt)
  simpa [List.replicate_succ'] using Reach.answer h hx (some ())

/-- The round closes and the next outer input arrives. -/
theorem reach_roundGrowthFn_next {k m : ℕ}
    (h : Reach roundGrowthFn (List.replicate k (), List.replicate m (some ())))
    (hge : ¬ m < k * k) :
    Reach roundGrowthFn
      (List.replicate (k + 1) (), List.replicate m (some ())) := by
  have hv : Sum.inr () ∈ roundGrowthFn
      (List.replicate k (), List.replicate m (some ())) :=
    roundGrowthFn_inr_mem (by simp) (by simpa using hge)
  simpa [List.replicate_succ'] using Reach.next h hv ()

/-- **The round anchors are reachable**: after `k` completed rounds exactly
`k²` answers have been consumed, and the `(k+1)`-st outer input is in. -/
theorem reach_roundGrowthFn_anchor (k : ℕ) :
    Reach roundGrowthFn
      (List.replicate (k + 1) (), List.replicate (k * k) (some ())) := by
  induction k with
  | zero =>
      simpa only [List.replicate_one, Nat.zero_mul, List.replicate_zero] using
        Reach.first ()
  | succ k ih =>
      have hsq : (k + 1) * (k + 1) = k * k + (2 * k + 1) := by ring
      have hfill : ∀ j, j ≤ 2 * k + 1 →
          Reach roundGrowthFn (List.replicate (k + 1) (),
            List.replicate (k * k + j) (some ())) := by
        intro j
        induction j with
        | zero => intro _; simpa only [Nat.add_zero] using ih
        | succ j ihj =>
            intro hj
            have hlt : k * k + j < (k + 1) * (k + 1) := by omega
            exact reach_roundGrowthFn_step (ihj (by omega)) hlt
      exact reach_roundGrowthFn_next (hsq ▸ hfill (2 * k + 1) le_rfl)
        (by omega)

/-- **No uniform budget**: the `(B+1)`-st round of `roundGrowthFn` opens a
streak of `2B+1` queries, so `AnswersWithin` fails at every `B`. -/
theorem not_answersWithin_roundGrowthFn (B : ℕ) :
    ¬ AnswersWithin roundGrowthFn B := by
  intro h
  refine h (List.replicate (B + 1) (), List.replicate (B * B) (some ()))
    (reach_roundGrowthFn_anchor B) (List.replicate B (some ()))
    (by simp) ?_
  intro k hk
  rw [List.length_replicate] at hk
  refine ⟨(), roundGrowthFn_inl_mem ?_ ?_⟩
  · simp
  · simp only [List.length_append, List.length_take, List.length_replicate]
    have hsq : (B + 1) * (B + 1) = B * B + (2 * B + 1) := by ring
    omega

/-- **The separation**, kernel-checked: `roundGrowthFn` is a Def 3.8
converter in the prose reading and is not one in the formal reading.  The
class `IsDDC` cuts out is therefore strictly smaller than the class CR18
describes — every theorem proved about `IsDDC` stays sound, but converters
whose per-round query count grows with the round index are outside it. -/
theorem not_isDDC_roundGrowthFn : ¬ IsDDC roundGrowthFn := by
  rintro ⟨-, B, hB⟩
  exact not_answersWithin_roundGrowthFn B hB

/-! The second half of the map: `AnswersEventually` is not merely weaker than
`AnswersWithin`, it is weaker than `AnswersWithinDepth` — a *pointwise* bound
need not assemble into any bound at all as a function of the round index, and
the round index is the only thing a fuel budget may depend on
(`EmulateRealization.Emulable` fixes its inner fuel before the assumed system
is chosen).  `answerGrowthFn` inhabits that second gap. -/

/-- The number of queries `answerGrowthFn` is allowed to have issued: one in
the first round, and thereafter one more than the number the system named in
its first answer. -/
def growBudget (p : List Unit × List (Option ℕ)) : ℕ :=
  if p.1.length ≤ 1 then 1
  else match p.2.head? with
    | some (some m) => m + 1
    | _ => 1

/-- **Stress test — a pointwise bound need not be a bound in the round
index.**  This converter queries once, reads the number `m` the system
answered, and spends its second round issuing `m` further queries.  At every
reachable pair it stops after finitely many queries — `m` is already fixed
there — but at the *round-two* pairs, all of which have two outer inputs, no
budget depending on the round index alone can cover every `m`. -/
def answerGrowthFn : ProtocolFn Unit Unit Unit ℕ := fun p =>
  if none ∈ p.2 then Part.none
  else if p.2.length < growBudget p then Part.some (Sum.inl ())
  else Part.some (Sum.inr ())

theorem answerGrowthFn_inl_mem {us : List Unit} {ys : List (Option ℕ)}
    (hnone : none ∉ ys) (h : ys.length < growBudget (us, ys)) :
    Sum.inl () ∈ answerGrowthFn (us, ys) := by
  simp only [answerGrowthFn, if_neg hnone, if_pos h]
  exact Part.mem_some _

theorem answerGrowthFn_inr_mem {us : List Unit} {ys : List (Option ℕ)}
    (hnone : none ∉ ys) (h : ¬ ys.length < growBudget (us, ys)) :
    Sum.inr () ∈ answerGrowthFn (us, ys) := by
  simp only [answerGrowthFn, if_neg hnone, if_neg h]
  exact Part.mem_some _

theorem answersInY_answerGrowthFn : AnswersInY answerGrowthFn := by
  intro p _ hnone hdom
  obtain ⟨mv, hm⟩ := Part.dom_iff_mem.mp hdom
  simp only [answerGrowthFn, if_pos hnone] at hm
  exact Part.notMem_none _ hm

/-- The trace invariant that makes the budget stable along a streak: a
second outer input arrives only after the first round has been answered, so
past round one the answer list is nonempty and its head is frozen. -/
theorem reach_answerGrowthFn_inv {p : List Unit × List (Option ℕ)}
    (h : Reach answerGrowthFn p) : p.1.length ≤ 1 ∨ p.2 ≠ [] := by
  induction h with
  | first u => simp
  | answer hr hx y ih => right; simp
  | next hr hv u ih =>
      rename_i us ys v
      rcases ih with hlen | hne
      · refine Or.inr ?_
        show ys ≠ []
        rintro rfl
        have hb : growBudget (us, ([] : List (Option ℕ))) = 1 := by
          simp only [growBudget]
          rw [if_pos hlen]
        simp [answerGrowthFn, hb] at hv
      · exact Or.inr hne

/-- The budget does not move along a streak out of a reachable pair. -/
theorem growBudget_append {p : List Unit × List (Option ℕ)}
    (h : Reach answerGrowthFn p) (l : List (Option ℕ)) :
    growBudget (p.1, p.2 ++ l) = growBudget p := by
  rcases reach_answerGrowthFn_inv h with hlen | hne
  · simp only [growBudget, if_pos hlen]
  · obtain ⟨a, rest, hcons⟩ := List.exists_cons_of_ne_nil hne
    simp only [growBudget, hcons, List.cons_append, List.head?_cons]

/-- `answerGrowthFn` satisfies Def 3.8's finite-bound clause **pointwise** —
CR18's prose, verbatim. -/
theorem answersEventually_answerGrowthFn : AnswersEventually answerGrowthFn := by
  intro p hp
  refine ⟨growBudget p + 1, fun ext hlen hall => ?_⟩
  obtain ⟨x, hx⟩ := hall (growBudget p)
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hlen)
  simp only [answerGrowthFn] at hx
  split_ifs at hx with h1 h2
  · exact Part.notMem_none _ hx
  · rw [growBudget_append hp] at h2
    rw [List.length_append, List.length_take] at h2
    have hmin : min (growBudget p) ext.length = growBudget p :=
      min_eq_left (le_trans (Nat.le_succ _) hlen)
    omega
  · simp at hx

/-- Both Def 3.8 clauses hold in the prose reading. -/
theorem isDDCEventually_answerGrowthFn : IsDDCEventually answerGrowthFn :=
  ⟨answersInY_answerGrowthFn, answersEventually_answerGrowthFn⟩

/-- The round-two anchors — one for each answer the system may have given. -/
theorem reach_answerGrowthFn_anchor (m : ℕ) :
    Reach answerGrowthFn ([(), ()], [some m]) := by
  have h1 : Reach answerGrowthFn ([()], []) := Reach.first ()
  have hq : Sum.inl () ∈ answerGrowthFn ([()], []) :=
    answerGrowthFn_inl_mem (by simp) (by simp [growBudget])
  have h2 : Reach answerGrowthFn ([()], [some m]) := by
    simpa using Reach.answer h1 hq (some m)
  have hv : Sum.inr () ∈ answerGrowthFn ([()], [some m]) :=
    answerGrowthFn_inr_mem (by simp) (by simp [growBudget])
  simpa using Reach.next h2 hv ()

/-- **No budget in the round index**: every round-two pair has two outer
inputs, and the streak they open is as long as the system's first answer. -/
theorem not_answersWithinDepth_answerGrowthFn (F : ℕ → ℕ) :
    ¬ AnswersWithinDepth answerGrowthFn F := by
  intro h
  refine h ([(), ()], [some (F 2)]) (reach_answerGrowthFn_anchor (F 2))
    (List.replicate (F 2) (some (F 2))) (by simp) ?_
  intro k hk
  rw [List.length_replicate] at hk
  refine ⟨(), answerGrowthFn_inl_mem ?_ ?_⟩
  · simp
  · simp only [growBudget, List.cons_append, List.head?_cons,
      List.length_append, List.length_take, List.length_replicate,
      List.length_cons, List.length_nil]
    norm_num
    omega

/-- **The second separation**, kernel-checked: the prose class is not merely
larger than `IsDDC`, it is larger than the answer-uniform class
`AnswersWithinDepth`.  Since `EmulateRealization`'s inner fuel is a function
of the outer round count *chosen before the assumed system is*, a merely
pointwise bound cannot be turned into fuel at all — which is why the
downstream theory cannot simply be re-based on `IsDDCEventually`. -/
theorem not_answersWithin_answerGrowthFn (B : ℕ) :
    ¬ AnswersWithin answerGrowthFn B := fun h =>
  not_answersWithinDepth_answerGrowthFn (fun _ => B) h.answersWithinDepth

end StressTests

end Converter

end RandomSystems
