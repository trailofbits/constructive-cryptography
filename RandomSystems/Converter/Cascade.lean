/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.Converter

/-!
# Cascading converters (CR18 Definition 3.9, and serial composition)

Two theorems, and the machinery they need.

`apply` is the transcript-equation application of a protocol function to a
system: the unique causal solution of `x̂ⱼ = α(active outer prefix, ŷ^{j−1})`,
`ŷⱼ = S⊥(x̂^j)`, realized as a finite unrolling.  Per Definition 3.9 the
queries are answered by the Definition 3.3 completion `S⊥`, so the drive never
stalls on the system: partiality comes from the converter alone.

* **`apply_toDDC`** — Definition 3.9 applied to the canonical Definition 3.8
  object of `α` *is* the transcript-equation solution.  This is what lets the
  `ν` presentation and the `DDC` presentation be used interchangeably.
* **`apply_comp`** — attaching `β` and then `α` is attaching their serial
  composite, together with `serial_composition_is_ddc` closing Definition
  3.8's class under composition.  MauRen11 §6.2's `(αβ)ⁱR := αⁱβⁱR`.

The second is what the constructive instantiation consumes: Definition 16's
emulation closure `𝒟Σ ⊆ 𝒟` is exactly the statement that testing after
attaching a converter is testing with the composite.
-/


/-!
# The ν-level realization theorem (DESIGN §10.5)

`apply α S` is the **transcript-equation application** of a protocol
function `α : List U × List (Option Y) →. X ⊕ V` to a system `S`: the unique
causal solution of

`x̂ⱼ = α(active outer prefix, ŷ^{j−1})`,  `ŷⱼ = S⊥(x̂^j)`,

realized function-natively as a finite unrolling (`drive`, fuel = the
unrolling counter, hidden by `eventual`) — the ν-level generalization of the
read-only reference repository's `CausalApply.applyG` (which has no counterpart
in this tree), with the converter now seeing the *full* history
(cross-round memory: `[q]`, blind `b`, copying `T̃`, CTR all live here).
Per CR18 Def 3.9 the queries are answered by the Def 3.3 completion `S⊥`
(`Y ∪ {⊥}`), so the drive never stalls on the system: partiality comes from
α alone.

The **realization theorem** `apply_toDDC`:

`DDC.apply (toDDC α) S = apply α S`

— CR18 Def 3.9 applied to the canonical Def 3.8 object of α *is* the
transcript-equation solution.  Same two simulations as the reference
repository's `apply_ofStep` (a declaration of *that* tree, not of this one:
neither it nor its `StepConverter.lean` home exists here), with the round state
`(u, ys)` of the outer-memoryless case replaced by the parse
`ParsesTo α l (us, ys)` of the full history; both
sides thread the *same* `S⊥`-answers, so the answer histories coincide on
the nose and no liveness invariant is needed.

As the first cross-round instance, the `[q]` filter is computed:
`apply (queryLimitFn q) S = System.filterQueries q S`, hence
`DDC.apply (toDDC (queryLimitFn q)) S = filterQueries q S` — and combining
with the pre-existing operational theorem, the old `[q]ᶠ` DDC and
`toDDC (queryLimitFn q)` are **apply-equal** representatives of the same
converter, retiring the need for `queryLimit`-style bespoke trace proofs.
-/

namespace RandomSystems

namespace Converter

open scoped System

universe u v w z

variable {U : Type u} {V : Type w} {X : Type z} {Y : Type v}

/-! ### The transcript-equation driver -/

/-- One-round unrolling of the transcript equations from the pair
`(us, ys)` with inner history `xs`: consult α; a query is answered by the
Def 3.3 completion `S⊥` (`⊥` when the extended inner history falls out of
`dom S`) and both histories grow; an answer exits with the final histories.
The system side never stalls — partiality comes from α alone. -/
noncomputable def drive (α : ProtocolFn U V X Y) (S : System.DDS X Y) :
    ℕ → List U → List X → List (Option Y) → Part (V × List X × List (Option Y))
  | 0, _, _, _ => Part.none
  | fuel + 1, us, xs, ys =>
      (α (us, ys)).bind fun m =>
        match m with
        | Sum.inl x =>
            drive α S fuel us (xs ++ [x])
              (ys ++ [System.output (S⊥) (xs ++ [x])
                (by rw [System.dom_fullyDefined]; simp)])
        | Sum.inr v => Part.some (v, xs, ys)

/-- Membership constructor: a query step. -/
theorem drive_mem_query (α : ProtocolFn U V X Y) (S : System.DDS X Y)
    {us : List U} {xs : List X} {ys : List (Option Y)} {x : X}
    (hm : Sum.inl x ∈ α (us, ys))
    {fuel : ℕ} {r : V × List X × List (Option Y)}
    (h : r ∈ drive α S fuel us (xs ++ [x])
      (ys ++ [System.output (S⊥) (xs ++ [x])
        (by rw [System.dom_fullyDefined]; simp)])) :
    r ∈ drive α S (fuel + 1) us xs ys := by
  simp only [drive, Part.mem_bind_iff]
  exact ⟨Sum.inl x, hm, h⟩

/-- Membership constructor: an answer step. -/
theorem drive_mem_answer (α : ProtocolFn U V X Y) (S : System.DDS X Y)
    {us : List U} {xs : List X} {ys : List (Option Y)} {v : V}
    (hm : Sum.inr v ∈ α (us, ys)) (fuel : ℕ) :
    (v, xs, ys) ∈ drive α S (fuel + 1) us xs ys := by
  simp only [drive, Part.mem_bind_iff]
  exact ⟨Sum.inr v, hm, Part.mem_some_iff.mpr rfl⟩

/-- Membership destructor: one unrolling step. -/
theorem drive_succ_elim {α : ProtocolFn U V X Y} {S : System.DDS X Y}
    {fuel : ℕ} {us : List U} {xs : List X} {ys : List (Option Y)}
    {r : V × List X × List (Option Y)}
    (h : r ∈ drive α S (fuel + 1) us xs ys) :
    (∃ x, Sum.inl x ∈ α (us, ys) ∧
        r ∈ drive α S fuel us (xs ++ [x])
          (ys ++ [System.output (S⊥) (xs ++ [x])
            (by rw [System.dom_fullyDefined]; simp)])) ∨
      (∃ v, Sum.inr v ∈ α (us, ys) ∧ r = (v, xs, ys)) := by
  simp only [drive, Part.mem_bind_iff] at h
  obtain ⟨m, hm, h⟩ := h
  cases m with
  | inl x => exact Or.inl ⟨x, hm, h⟩
  | inr v =>
      simp only [Part.mem_some_iff] at h
      exact Or.inr ⟨v, hm, h⟩

theorem drive_mono (α : ProtocolFn U V X Y) (S : System.DDS X Y) :
    ∀ {fuel : ℕ} {us : List U} {xs : List X} {ys : List (Option Y)}
      {r : V × List X × List (Option Y)},
      r ∈ drive α S fuel us xs ys → r ∈ drive α S (fuel + 1) us xs ys := by
  intro fuel
  induction fuel with
  | zero => intro us xs ys r h; simp [drive] at h
  | succ n ih =>
      intro us xs ys r h
      rcases drive_succ_elim h with ⟨x, hm, h⟩ | ⟨v, hm, rfl⟩
      · exact drive_mem_query α S hm (ih h)
      · exact drive_mem_answer α S hm (n + 1)

theorem drive_mono_le (α : ProtocolFn U V X Y) (S : System.DDS X Y)
    {fuel fuel' : ℕ} {us : List U} {xs : List X} {ys : List (Option Y)}
    {r : V × List X × List (Option Y)} (hle : fuel ≤ fuel')
    (h : r ∈ drive α S fuel us xs ys) : r ∈ drive α S fuel' us xs ys := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  clear hle
  induction k with
  | zero => simpa using h
  | succ n ih =>
      have he : fuel + (n + 1) = (fuel + n) + 1 := by ring
      rw [he]
      exact drive_mono α S ih

/-- The outer fold: consume the remaining outer inputs, growing the active
outer prefix and threading the inner histories. -/
noncomputable def driveOuter (α : ProtocolFn U V X Y) (S : System.DDS X Y)
    (fuel : ℕ) :
    List U → List X → List (Option Y) → List U →
      Part (List V × List X × List (Option Y))
  | _, xs, ys, [] => Part.some ([], xs, ys)
  | usPre, xs, ys, u :: rest =>
      (drive α S fuel (usPre ++ [u]) xs ys).bind fun r =>
        (driveOuter α S fuel (usPre ++ [u]) r.2.1 r.2.2 rest).map fun rr =>
          (r.1 :: rr.1, rr.2)

theorem driveOuter_length (α : ProtocolFn U V X Y) (S : System.DDS X Y)
    (fuel : ℕ) :
    ∀ {rest : List U} {usPre : List U} {xs : List X} {ys : List (Option Y)}
      {r : List V × List X × List (Option Y)},
      r ∈ driveOuter α S fuel usPre xs ys rest → r.1.length = rest.length := by
  intro rest
  induction rest with
  | nil =>
      intro usPre xs ys r h
      simp only [driveOuter, Part.mem_some_iff] at h
      subst h
      simp
  | cons u rest ih =>
      intro usPre xs ys r h
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at h
      obtain ⟨r', _, rr, hrr, rfl⟩ := h
      simp [ih hrr]

theorem driveOuter_mono (α : ProtocolFn U V X Y) (S : System.DDS X Y)
    {fuel : ℕ} :
    ∀ {rest : List U} {usPre : List U} {xs : List X} {ys : List (Option Y)}
      {r : List V × List X × List (Option Y)},
      r ∈ driveOuter α S fuel usPre xs ys rest →
        r ∈ driveOuter α S (fuel + 1) usPre xs ys rest := by
  intro rest
  induction rest with
  | nil => intro usPre xs ys r h; simpa [driveOuter] using h
  | cons u rest ih =>
      intro usPre xs ys r h
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at h ⊢
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := h
      exact ⟨r₁, drive_mono α S hr₁, rr, ih hrr, rfl⟩

theorem driveOuter_mono_le (α : ProtocolFn U V X Y) (S : System.DDS X Y)
    {fuel fuel' : ℕ} {rest usPre : List U} {xs : List X} {ys : List (Option Y)}
    {r : List V × List X × List (Option Y)} (hle : fuel ≤ fuel')
    (h : r ∈ driveOuter α S fuel usPre xs ys rest) :
    r ∈ driveOuter α S fuel' usPre xs ys rest := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  clear hle
  induction k with
  | zero => simpa using h
  | succ n ih =>
      have he : fuel + (n + 1) = (fuel + n) + 1 := by ring
      rw [he]
      exact driveOuter_mono α S ih

/-- The per-fuel applied raw function: replay from empty histories, answer
with the last round's output. -/
noncomputable def applyRawAt (α : ProtocolFn U V X Y) (S : System.DDS X Y)
    (fuel : ℕ) :
    System.Raw U V :=
  fun us => (driveOuter α S fuel [] [] [] us).bind fun r =>
    match r.1.getLast? with
    | some v => Part.some v
    | none => Part.none

theorem mem_applyRawAt_iff (α : ProtocolFn U V X Y) (S : System.DDS X Y)
    (fuel : ℕ) (us : List U) (v : V) :
    v ∈ applyRawAt α S fuel us ↔
      ∃ r ∈ driveOuter α S fuel [] [] [] us, r.1.getLast? = some v := by
  simp only [applyRawAt, Part.mem_bind_iff]
  refine exists_congr fun r => and_congr_right fun _ => ?_
  cases r.1.getLast? with
  | none => simp
  | some w => simp [Part.mem_some_iff, eq_comm]

theorem applyRawAt_mono_le (α : ProtocolFn U V X Y) (S : System.DDS X Y)
    {fuel fuel' : ℕ} {us : List U} {v : V} (hle : fuel ≤ fuel')
    (h : v ∈ applyRawAt α S fuel us) : v ∈ applyRawAt α S fuel' us := by
  rw [mem_applyRawAt_iff] at h ⊢
  obtain ⟨r, hr, hlast⟩ := h
  exact ⟨r, driveOuter_mono_le α S hle hr, hlast⟩

/-- The fuel-free applied raw function: eventual value of the unrolling. -/
noncomputable def applyRaw (α : ProtocolFn U V X Y) (S : System.DDS X Y) :
    System.Raw U V :=
  fun us => Part.eventual fun fuel => applyRawAt α S fuel us

theorem mem_applyRaw (α : ProtocolFn U V X Y) (S : System.DDS X Y)
    (us : List U) (v : V) :
    v ∈ applyRaw α S us ↔ ∃ fuel, v ∈ applyRawAt α S fuel us :=
  Part.mem_eventual
    (hmono := fun hle hw => applyRawAt_mono_le α S hle hw)

/-- Split of the outer fold over concatenation (validity engine). -/
theorem driveOuter_append (α : ProtocolFn U V X Y) (S : System.DDS X Y)
    (fuel : ℕ) :
    ∀ (a b : List U) (usPre : List U) (xs : List X) (ys : List (Option Y)),
      driveOuter α S fuel usPre xs ys (a ++ b) =
        (driveOuter α S fuel usPre xs ys a).bind fun ra =>
          (driveOuter α S fuel (usPre ++ a) ra.2.1 ra.2.2 b).map fun rb =>
            (ra.1 ++ rb.1, rb.2) := by
  intro a
  induction a with
  | nil =>
      intro b usPre xs ys
      simp only [List.nil_append, driveOuter, Part.bind_some, List.append_nil]
      refine (Part.map_id' ?_ _).symm
      intro rb
      rfl
  | cons u rest ih =>
      intro b usPre xs ys
      simp only [List.cons_append, driveOuter, ih, Part.bind_assoc,
        Part.bind_map, Part.map_bind, Part.map_map, Function.comp_def,
        List.cons_append, List.append_assoc, List.nil_append]

/-- **The transcript-equation application** (fuel-free): the ν-level
generalization of the reference repository's `CausalApply.applyG` (no such
declaration in this tree) — a valid `DDS U V`, partial exactly where the
equations do not solve. -/
noncomputable def apply (α : ProtocolFn U V X Y) (S : System.DDS X Y) :
    System.DDS U V :=
  ⟨applyRaw α S, by
    refine ⟨?_, ?_⟩
    · rw [PFun.mem_dom]
      rintro ⟨v, hv⟩
      rw [mem_applyRaw] at hv
      obtain ⟨fuel, hv⟩ := hv
      rw [mem_applyRawAt_iff] at hv
      obtain ⟨r, hr, hlast⟩ := hv
      simp only [driveOuter, Part.mem_some_iff] at hr
      subst hr
      simp at hlast
    · intro l₁ l₂ hpre hne hdom
      obtain ⟨t, rfl⟩ := hpre
      rw [PFun.mem_dom] at hdom
      obtain ⟨v, hv⟩ := hdom
      rw [mem_applyRaw] at hv
      obtain ⟨fuel, hv⟩ := hv
      rw [mem_applyRawAt_iff] at hv
      obtain ⟨r, hr, _⟩ := hv
      rw [driveOuter_append, Part.mem_bind_iff] at hr
      obtain ⟨ra, hra, _⟩ := hr
      have hlen : ra.1.length = l₁.length := driveOuter_length α S fuel hra
      have hne1 : ra.1 ≠ [] := by
        intro hnil
        apply hne
        apply List.eq_nil_of_length_eq_zero
        rw [← hlen, hnil, List.length_nil]
      rw [PFun.mem_dom]
      refine ⟨ra.1.getLast hne1, ?_⟩
      rw [mem_applyRaw]
      refine ⟨fuel, ?_⟩
      rw [mem_applyRawAt_iff]
      refine ⟨ra, hra, ?_⟩
      rw [List.getLast?_eq_some_getLast hne1]⟩

@[simp] theorem apply_toPFun (α : ProtocolFn U V X Y) (S : System.DDS X Y) :
    (apply α S).1 = applyRaw α S := rfl

/-! ### Successful-driver reachability and invariant-indexed congruence -/

/-- **Successful-driver reachability**: from a reachable pair, a successful
`drive` run ends at a reachable pair whose move is the delivered outer
answer. -/
theorem drive_result_reachable (α : ProtocolFn U V X Y)
    (S : System.DDS X Y) :
    ∀ (fuel : ℕ) (us : List U) (xs : List X) (ys : List (Option Y))
      (r : V × List X × List (Option Y)),
      Reach α (us, ys) →
        r ∈ drive α S fuel us xs ys →
        Reach α (us, r.2.2) ∧ Sum.inr r.1 ∈ α (us, r.2.2) := by
  intro fuel
  induction fuel with
  | zero =>
      intro us xs ys r _ member
      simp [drive] at member
  | succ fuel induction =>
      intro us xs ys r reachable member
      rcases drive_succ_elim member with
        ⟨x, queryMember, nextMember⟩ | ⟨v, answerMember, rfl⟩
      · exact induction _ _ _ _
          (Reach.answer reachable queryMember _) nextMember
      · exact ⟨reachable, answerMember⟩

/-- **Invariant-indexed application congruence**: two protocol functions that
agree on reachable pairs satisfying an invariant preserved by the resource's
Def 3.3 completions apply equally.  The conclusion is equality only after
application to the resource — the raw trace trees may differ off the
invariant. -/
theorem apply_eq_of_reachable_invariant (α β : ProtocolFn U V X Y)
    (S : System.DDS X Y)
    (invariant : List U → List (Option Y) → Prop)
    (startRound :
      ∀ (us : List U) (ys : List (Option Y)) (u : U),
        ((us = [] ∧ ys = []) ∨
          ∃ v, Reach α (us, ys) ∧ Sum.inr v ∈ α (us, ys) ∧ invariant us ys) →
        Reach α (us ++ [u], ys) ∧ invariant (us ++ [u]) ys)
    (completeInvariant :
      ∀ (us : List U) (xs : List X) (ys : List (Option Y)) (x : X),
        Reach α (us, ys) →
        invariant us ys →
        Sum.inl x ∈ α (us, ys) →
        invariant us
          (ys ++ [System.output (System.fullyDefined S) (xs ++ [x])
            (by rw [System.dom_fullyDefined]; simp)]))
    (agree :
      ∀ (us : List U) (ys : List (Option Y)),
        Reach α (us, ys) → invariant us ys → α (us, ys) = β (us, ys)) :
    apply α S = apply β S := by
  have driveInvariant :
      ∀ (fuel : ℕ) (us : List U) (xs : List X) (ys : List (Option Y))
        (r : V × List X × List (Option Y)),
        Reach α (us, ys) →
        invariant us ys →
        r ∈ drive α S fuel us xs ys →
        invariant us r.2.2 := by
    intro fuel
    induction fuel with
    | zero =>
        intro us xs ys r _ _ member
        simp [drive] at member
    | succ fuel induction =>
        intro us xs ys r reachable valid member
        rcases drive_succ_elim member with
          ⟨x, queryMember, nextMember⟩ | ⟨v, answerMember, rfl⟩
        · exact induction _ _ _ _
            (Reach.answer reachable queryMember _)
            (completeInvariant us xs ys x reachable valid queryMember)
            nextMember
        · exact valid
  have driveIff :
      ∀ (fuel : ℕ) (us : List U) (xs : List X) (ys : List (Option Y))
        (r : V × List X × List (Option Y)),
        Reach α (us, ys) →
        invariant us ys →
        (r ∈ drive α S fuel us xs ys ↔ r ∈ drive β S fuel us xs ys) := by
    intro fuel
    induction fuel with
    | zero =>
        intro us xs ys r _ _
        rfl
    | succ fuel induction =>
        intro us xs ys r reachable valid
        have equation := agree us ys reachable valid
        constructor
        · intro member
          rcases drive_succ_elim member with
            ⟨x, queryMember, nextMember⟩ | ⟨v, answerMember, rfl⟩
          · have rightQuery : Sum.inl x ∈ β (us, ys) :=
              equation ▸ queryMember
            apply drive_mem_query _ S rightQuery
            exact (induction _ _ _ _
              (Reach.answer reachable queryMember _)
              (completeInvariant us xs ys x reachable valid
                queryMember)).mp nextMember
          · apply drive_mem_answer _ S _ fuel
            exact equation ▸ answerMember
        · intro member
          rcases drive_succ_elim member with
            ⟨x, rightQuery, nextMember⟩ | ⟨v, rightAnswer, rfl⟩
          · have queryMember : Sum.inl x ∈ α (us, ys) :=
              equation.symm ▸ rightQuery
            apply drive_mem_query _ S queryMember
            exact (induction _ _ _ _
              (Reach.answer reachable queryMember _)
              (completeInvariant us xs ys x reachable valid
                queryMember)).mpr nextMember
          · apply drive_mem_answer _ S _ fuel
            exact equation.symm ▸ rightAnswer
  have outerIff :
      ∀ (rest : List U) (fuel : ℕ) (us : List U) (xs : List X)
        (ys : List (Option Y))
        (r : List V × List X × List (Option Y)),
        ((us = [] ∧ ys = []) ∨
          ∃ v, Reach α (us, ys) ∧ Sum.inr v ∈ α (us, ys) ∧ invariant us ys) →
        (r ∈ driveOuter α S fuel us xs ys rest ↔
          r ∈ driveOuter β S fuel us xs ys rest) := by
    intro rest
    induction rest with
    | nil =>
        intro fuel us xs ys r _
        rfl
    | cons u rest induction =>
        intro fuel us xs ys r ready
        obtain ⟨reachable, valid⟩ := startRound us ys u ready
        constructor
        · intro member
          rw [driveOuter, Part.mem_bind_iff] at member
          rcases member with ⟨round, roundMember, mappedTail⟩
          rw [Part.mem_map_iff] at mappedTail
          obtain ⟨tail, tailMember, rfl⟩ := mappedTail
          have rightRound :=
            (driveIff fuel (us ++ [u]) xs ys round reachable
              valid).mp roundMember
          obtain ⟨finalReachable, answerMember⟩ :=
            drive_result_reachable α S fuel (us ++ [u]) xs ys round
              reachable roundMember
          have finalValid :=
            driveInvariant fuel (us ++ [u]) xs ys round reachable valid
              roundMember
          have nextReady :
              ((us ++ [u] = [] ∧ round.2.2 = []) ∨
                ∃ v, Reach α (us ++ [u], round.2.2) ∧
                  Sum.inr v ∈ α (us ++ [u], round.2.2) ∧
                  invariant (us ++ [u]) round.2.2) :=
            Or.inr ⟨round.1, finalReachable, answerMember, finalValid⟩
          rw [driveOuter.eq_2]
          apply Part.mem_bind rightRound
          apply Part.mem_map _
          exact (induction fuel (us ++ [u]) round.2.1 round.2.2 tail
            nextReady).mp tailMember
        · intro member
          rw [driveOuter.eq_2, Part.mem_bind_iff] at member
          rcases member with ⟨round, rightRound, mappedTail⟩
          rw [Part.mem_map_iff] at mappedTail
          obtain ⟨tail, rightTail, rfl⟩ := mappedTail
          have roundMember :=
            (driveIff fuel (us ++ [u]) xs ys round reachable
              valid).mpr rightRound
          obtain ⟨finalReachable, answerMember⟩ :=
            drive_result_reachable α S fuel (us ++ [u]) xs ys round
              reachable roundMember
          have finalValid :=
            driveInvariant fuel (us ++ [u]) xs ys round reachable valid
              roundMember
          have nextReady :
              ((us ++ [u] = [] ∧ round.2.2 = []) ∨
                ∃ v, Reach α (us ++ [u], round.2.2) ∧
                  Sum.inr v ∈ α (us ++ [u], round.2.2) ∧
                  invariant (us ++ [u]) round.2.2) :=
            Or.inr ⟨round.1, finalReachable, answerMember, finalValid⟩
          rw [driveOuter.eq_2]
          apply Part.mem_bind roundMember
          apply Part.mem_map _
          exact (induction fuel (us ++ [u]) round.2.1 round.2.2 tail
            nextReady).mpr rightTail
  apply Subtype.ext
  funext us
  change applyRaw α S us = applyRaw β S us
  apply Part.ext
  intro v
  rw [mem_applyRaw, mem_applyRaw]
  apply exists_congr
  intro fuel
  rw [mem_applyRawAt_iff, mem_applyRawAt_iff]
  apply exists_congr
  intro r
  apply and_congr
  · exact outerIff us fuel [] [] [] r (Or.inl ⟨rfl, rfl⟩)
  · rfl

/-! ### Parse-extension lemmas and move inversion -/

theorem parsesTo_singleton (α : ProtocolFn U V X Y) (u : U) :
    ParsesTo α [Sum.inl (InLabel.outside, u)] ([u], []) := rfl

theorem parsesTo_snoc_out {α : ProtocolFn U V X Y} {l : List (DDC.CIn U Y)}
    {us : List U} {ys : List (Option Y)} (h : ParsesTo α l (us, ys)) {v : V}
    (hv : Sum.inr v ∈ α (us, ys)) (u : U) :
    ParsesTo α (l ++ [Sum.inl (InLabel.outside, u)]) (us ++ [u], ys) := by
  cases l with
  | nil => exact h.elim
  | cons a rest =>
      rcases a with ⟨lbl, u₀⟩ | ⟨lbl, oy⟩ <;> cases lbl
      · exact h.elim
      · show ParsesToAux α ([u₀], [])
          (rest ++ [Sum.inl (InLabel.outside, u)]) (us ++ [u], ys)
        rw [parsesToAux_append]
        exact ⟨(us, ys), h, ⟨v, hv⟩, rfl⟩
      · exact h.elim
      · exact h.elim

theorem parsesTo_snoc_in {α : ProtocolFn U V X Y} {l : List (DDC.CIn U Y)}
    {us : List U} {ys : List (Option Y)} (h : ParsesTo α l (us, ys)) {x : X}
    (hx : Sum.inl x ∈ α (us, ys)) (y : Option Y) :
    ParsesTo α (l ++ [Sum.inr (InLabel.inside, y)]) (us, ys ++ [y]) := by
  cases l with
  | nil => exact h.elim
  | cons a rest =>
      rcases a with ⟨lbl, u₀⟩ | ⟨lbl, oy⟩ <;> cases lbl
      · exact h.elim
      · show ParsesToAux α ([u₀], [])
          (rest ++ [Sum.inr (InLabel.inside, y)]) (us, ys ++ [y])
        rw [parsesToAux_append]
        exact ⟨(us, ys), h, ⟨x, hx⟩, rfl⟩
      · exact h.elim
      · exact h.elim

theorem mem_toDDC_of_parses {α : ProtocolFn U V X Y} {l : List (DDC.CIn U Y)}
    {us : List U} {ys : List (Option Y)} {m : X ⊕ V}
    (hp : ParsesTo α l (us, ys)) (hm : m ∈ α (us, ys)) :
    DDC.moveOf m ∈ (toDDC α).1 l :=
  (mem_toDDCRaw_iff α l _).mpr ⟨(us, ys), hp, m, hm, rfl⟩

theorem toDDC_move_inv {α : ProtocolFn U V X Y} {l : List (DDC.CIn U Y)}
    {us : List U} {ys : List (Option Y)} {o : DDC.COut V X}
    (hp : ParsesTo α l (us, ys)) (ho : o ∈ (toDDC α).1 l) :
    ∃ m ∈ α (us, ys), o = DDC.moveOf m := by
  rw [toDDC_toPFun, mem_toDDCRaw_iff] at ho
  obtain ⟨p', hp', m, hm, rfl⟩ := ho
  obtain rfl : p' = (us, ys) := parsesTo_unique hp' hp
  exact ⟨m, hm, rfl⟩

theorem moveOf_eq_out_iff {m : X ⊕ V} {v : V} :
    DDC.moveOf m = Sum.inl (InLabel.outside, v) ↔ m = Sum.inr v := by
  cases m <;> simp

theorem moveOf_eq_in_iff {m : X ⊕ V} {x : X} :
    DDC.moveOf m = Sum.inr (InLabel.inside, x) ↔ m = Sum.inl x := by
  cases m <;> simp

theorem connStep_toDDC_not_mem (α : ProtocolFn U V X Y) (S : System.DDS X Y)
    {st : List (DDC.CIn U Y) × List X}
    (h : ∀ p, ¬ ParsesTo α st.1 p)
    (o : (V × (List (DDC.CIn U Y) × List X)) ⊕ (List (DDC.CIn U Y) × List X)) :
    o ∉ DDC.connStep (toDDC α) S st := by
  intro ho
  rw [DDC.connStep, Part.mem_bind_iff] at ho
  obtain ⟨o', ho', -⟩ := ho
  rw [toDDC_toPFun, mem_toDDCRaw_iff] at ho'
  obtain ⟨p, hp, -⟩ := ho'
  exact h p hp

/-! ### The inner round: `resolve` against `toDDC α` ↔ `drive`

Both sides consult the same `S⊥` (Def 3.3) on the same inner history, so the
answer lists coincide on the nose — no liveness invariant is threaded. -/

theorem resolve_toDDC_of_drive (α : ProtocolFn U V X Y)
    (S : System.DDS X Y) :
    ∀ {fuel : ℕ} {l : List (DDC.CIn U Y)} {us : List U} {xs : List X}
      {ys : List (Option Y)} {p : V × List X × List (Option Y)},
      ParsesTo α l (us, ys) →
      p ∈ drive α S fuel us xs ys →
      ∃ l', ParsesTo α l' (us, p.2.2) ∧ Sum.inr p.1 ∈ α (us, p.2.2) ∧
        (p.1, (l', p.2.1)) ∈ DDC.resolve (toDDC α) S (l, xs) := by
  intro fuel
  induction fuel with
  | zero =>
      intro l us xs ys p _ hp
      simp [drive] at hp
  | succ n ih =>
      intro l us xs ys p hparse hp
      simp only [drive, Part.mem_bind_iff] at hp
      obtain ⟨m, hm, hp⟩ := hp
      cases m with
      | inr v =>
          simp only [Part.mem_some_iff] at hp
          subst hp
          refine ⟨l, hparse, hm, ?_⟩
          exact DDC.resolve_out (toDDC α) S
            (by simpa using mem_toDDC_of_parses hparse hm)
      | inl x =>
          have hquery : Sum.inr (InLabel.inside, x) ∈ (toDDC α).1 l := by
            simpa using mem_toDDC_of_parses hparse hm
          obtain ⟨l', h1, h2, hres⟩ := ih
            (parsesTo_snoc_in hparse hm
              (System.output (S⊥) (xs ++ [x])
                (by rw [System.dom_fullyDefined]; simp))) hp
          refine ⟨l', h1, h2, ?_⟩
          rw [DDC.resolve_in (toDDC α) S hquery]
          exact hres

theorem drive_of_resolve_toDDC (α : ProtocolFn U V X Y)
    (S : System.DDS X Y)
    {st : List (DDC.CIn U Y) × List X}
    {r : V × (List (DDC.CIn U Y) × List X)}
    (hr : r ∈ DDC.resolve (toDDC α) S st) :
    ∀ (us : List U) (ys : List (Option Y)), ParsesTo α st.1 (us, ys) →
      ∃ fuel ys',
        (r.1, r.2.2, ys') ∈ drive α S fuel us st.2 ys ∧
        ParsesTo α r.2.1 (us, ys') ∧ Sum.inr r.1 ∈ α (us, ys') := by
  refine PFun.fixInduction hr (C := fun st₀ =>
      ∀ (us : List U) (ys : List (Option Y)),
      ParsesTo α st₀.1 (us, ys) →
      ∃ fuel ys',
        (r.1, r.2.2, ys') ∈ drive α S fuel us st₀.2 ys ∧
        ParsesTo α r.2.1 (us, ys') ∧ Sum.inr r.1 ∈ α (us, ys')) ?_
  intro st₀ hfix IH us ys hparse
  rw [PFun.mem_fix_iff] at hfix
  rcases hfix with hstop | ⟨st₁, hstep₁, hrec⟩
  · rw [DDC.connStep_mem_inl] at hstop
    obtain ⟨hmove, hsteq⟩ := hstop
    obtain ⟨m, hm, hmv⟩ := toDDC_move_inv hparse hmove
    have hm' : m = Sum.inr r.1 := moveOf_eq_out_iff.mp hmv.symm
    subst hm'
    refine ⟨1, ys, ?_, ?_, hm⟩
    · simp only [drive, Part.mem_bind_iff]
      refine ⟨Sum.inr r.1, hm, ?_⟩
      simp only [Part.mem_some_iff]
      rw [hsteq]
    · rw [hsteq]
      exact hparse
  · have hstep₁' := hstep₁
    rw [DDC.connStep_mem_inr] at hstep₁'
    obtain ⟨x, hquery, hst₁⟩ := hstep₁'
    obtain ⟨m, hm, hmv⟩ := toDDC_move_inv hparse hquery
    have hm' : m = Sum.inl x := moveOf_eq_in_iff.mp hmv.symm
    subst hm'
    have hparse₁ : ParsesTo α st₁.1
        (us, ys ++ [System.output (S⊥) (st₀.2 ++ [x])
          (by rw [System.dom_fullyDefined]; simp)]) := by
      rw [hst₁]
      exact parsesTo_snoc_in hparse hm _
    obtain ⟨fuel, ys', hdrive, hp1, hp2⟩ := IH st₁ hstep₁ us _ hparse₁
    refine ⟨fuel + 1, ys', ?_, hp1, hp2⟩
    simp only [drive, Part.mem_bind_iff]
    refine ⟨Sum.inl x, hm, ?_⟩
    have hst₁2 : st₁.2 = st₀.2 ++ [x] := by rw [hst₁]
    rw [hst₁2] at hdrive
    exact hdrive

/-! ### The outer fold and the realization theorem -/

theorem driveFrom_toDDC_of_driveOuter (α : ProtocolFn U V X Y)
    (S : System.DDS X Y) {fuel : ℕ} :
    ∀ {rest : List U} {l : List (DDC.CIn U Y)} {usPre : List U}
      {xs : List X} {ys : List (Option Y)}
      {p : List V × List X × List (Option Y)},
      (l = [] ∧ usPre = [] ∧ ys = [] ∨
        (ParsesTo α l (usPre, ys) ∧ ∃ v, Sum.inr v ∈ α (usPre, ys))) →
      p ∈ driveOuter α S fuel usPre xs ys rest →
      ∃ l', (p.1, (l', p.2.1)) ∈ DDC.driveFrom (toDDC α) S (l, xs) rest := by
  intro rest
  induction rest with
  | nil =>
      intro l usPre xs ys p _ hp
      simp only [driveOuter, Part.mem_some_iff] at hp
      subst hp
      exact ⟨l, by simp [DDC.driveFrom]⟩
  | cons u rest ih =>
      intro l usPre xs ys p hready hp
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at hp
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := hp
      have hparse : ParsesTo α (l ++ [Sum.inl (InLabel.outside, u)])
          (usPre ++ [u], ys) := by
        rcases hready with ⟨rfl, rfl, rfl⟩ | ⟨hp', v, hv⟩
        · simpa using parsesTo_singleton α u
        · exact parsesTo_snoc_out hp' hv u
      obtain ⟨l₁, hp1, hv1, hres⟩ :=
        resolve_toDDC_of_drive α S hparse hr₁
      obtain ⟨l₂, htail⟩ := ih (Or.inr ⟨hp1, r₁.1, hv1⟩) hrr
      refine ⟨l₂, ?_⟩
      simp only [DDC.driveFrom, Part.mem_bind_iff, Part.mem_map_iff]
      exact ⟨(r₁.1, (l₁, r₁.2.1)), hres, (rr.1, (l₂, rr.2.1)), htail, rfl⟩

theorem driveOuter_of_driveFrom_toDDC (α : ProtocolFn U V X Y)
    (S : System.DDS X Y) :
    ∀ {rest : List U} {l : List (DDC.CIn U Y)} {usPre : List U}
      {xs : List X} {ys : List (Option Y)}
      {q : List V × (List (DDC.CIn U Y) × List X)},
      (l = [] ∧ usPre = [] ∧ ys = [] ∨
        (ParsesTo α l (usPre, ys) ∧ ∃ v, Sum.inr v ∈ α (usPre, ys))) →
      q ∈ DDC.driveFrom (toDDC α) S (l, xs) rest →
      ∃ fuel ys', (q.1, q.2.2, ys') ∈ driveOuter α S fuel usPre xs ys rest := by
  intro rest
  induction rest with
  | nil =>
      intro l usPre xs ys q _ hq
      simp only [DDC.driveFrom, Part.mem_some_iff] at hq
      subst hq
      exact ⟨0, ys, by simp [driveOuter]⟩
  | cons u rest ih =>
      intro l usPre xs ys q hready hq
      simp only [DDC.driveFrom, Part.mem_bind_iff, Part.mem_map_iff] at hq
      obtain ⟨r, hres, rr, htail, rfl⟩ := hq
      have hparse : ParsesTo α (l ++ [Sum.inl (InLabel.outside, u)])
          (usPre ++ [u], ys) := by
        rcases hready with ⟨rfl, rfl, rfl⟩ | ⟨hp', v, hv⟩
        · simpa using parsesTo_singleton α u
        · exact parsesTo_snoc_out hp' hv u
      obtain ⟨fuel₁, ys₁, hdrive, hp1, hp2⟩ :=
        drive_of_resolve_toDDC α S hres (usPre ++ [u]) ys hparse
      obtain ⟨fuel₂, ys₂, htail₂⟩ := ih (Or.inr ⟨hp1, r.1, hp2⟩) htail
      refine ⟨max fuel₁ fuel₂, ys₂, ?_⟩
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
      exact ⟨(r.1, r.2.2, ys₁),
        drive_mono_le α S (le_max_left _ _) hdrive,
        (rr.1, rr.2.2, ys₂),
        driveOuter_mono_le α S (le_max_right _ _) htail₂, rfl⟩

/-- **The ν-level realization theorem** (DESIGN §10.5): CR18 Def 3.9 applied
to the canonical Def 3.8 object of a protocol function *is* the
transcript-equation solution — for arbitrary converters, cross-round memory
included.  Conceptually subsumes the reference repository's `apply_ofStep`
(the outer-memoryless case; that route does not exist in this tree, so every
realization here runs through this theorem) and turns converter equations into
`drive` computations. -/
theorem apply_toDDC (α : ProtocolFn U V X Y) (S : System.DDS X Y) :
    DDC.apply (toDDC α) S = apply α S := by
  apply Subtype.ext
  funext us
  apply Part.ext
  intro v
  rw [show (DDC.apply (toDDC α) S).1 = DDC.applyRaw (toDDC α) S from rfl,
    show (apply α S).1 = applyRaw α S from rfl,
    DDC.mem_apply_iff, mem_applyRaw]
  constructor
  · rintro ⟨r, hr, hlast⟩
    obtain ⟨fuel, ys', hmem⟩ := driveOuter_of_driveFrom_toDDC α S
      (Or.inl ⟨rfl, rfl, rfl⟩) hr
    exact ⟨fuel, (mem_applyRawAt_iff α S fuel us v).mpr
      ⟨(r.1, r.2.2, ys'), hmem, hlast⟩⟩
  · rintro ⟨fuel, hv⟩
    rw [mem_applyRawAt_iff] at hv
    obtain ⟨r, hmem, hlast⟩ := hv
    obtain ⟨l', hr⟩ := driveFrom_toDDC_of_driveOuter α S
      (Or.inl ⟨rfl, rfl, rfl⟩) hmem
    exact ⟨(r.1, (l', r.2.1)), hr, hlast⟩

/-! ### Prefix-closed restrictions

The identity restriction converter realizes the corresponding deterministic
domain restriction.  This is the general mechanism behind both `[q]` and
history-dependent restrictions such as CBC's `θr`. -/

section RestrictionInstance

variable {X : Type z} {Y : Type v}

theorem restrictionFn_inl_elim {P : List X → Prop} [DecidablePred P]
    {us : List X} {ys : List (Option Y)} {x : X}
    (h : Sum.inl x ∈ restrictionFn P (us, ys)) :
    ∃ hne : us ≠ [],
      x = us.getLast hne ∧ us.length = ys.length + 1 ∧ P us := by
  have hshape := restrictionFn_inl_inv h
  obtain ⟨hne, hvalue⟩ := restrictionFn_inl_val h
  exact ⟨hne, hvalue, hshape⟩

theorem restrictionFn_inr_elim {P : List X → Prop} [DecidablePred P]
    {us : List X} {ys : List (Option Y)} {v : Y}
    (h : Sum.inr v ∈ restrictionFn P (us, ys)) :
    ∃ h0 : 0 < ys.length,
      ys.getLast (List.ne_nil_of_length_pos h0) = some v ∧
        us.length = ys.length ∧ P us := by
  obtain ⟨hlen, hP, h0, hy⟩ := restrictionFn_inr_inv h
  exact ⟨h0, hy, hlen, hP⟩

/-- One admitted restriction round, destructed. -/
theorem drive_restrictionFn_round_elim
    {P : List X → Prop} [DecidablePred P] {S : System.DDS X Y}
    {us : List X} {ys : List (Option Y)} {fuel : ℕ} {xs : List X}
    {p : Y × List X × List (Option Y)}
    (hlen : us.length = ys.length + 1)
    (hp : p ∈ drive (restrictionFn P) S fuel us xs ys) :
    ∃ (hne : us ≠ []) (y : Y), P us ∧
      System.output (S⊥) (xs ++ [us.getLast hne])
        (by rw [System.dom_fullyDefined]; simp) = some y ∧
      p = (y, xs ++ [us.getLast hne], ys ++ [some y]) := by
  rcases fuel with _ | fuel
  · simp [drive] at hp
  · rcases drive_succ_elim hp with ⟨x, hm, hp'⟩ | ⟨v, hm, rfl⟩
    · obtain ⟨hne, rfl, -, hP⟩ := restrictionFn_inl_elim hm
      rcases fuel with _ | fuel
      · simp [drive] at hp'
      · rcases drive_succ_elim hp' with ⟨x₂, hm₂, hp''⟩ | ⟨v₂, hm₂, rfl⟩
        · obtain ⟨hshape, -⟩ := restrictionFn_inl_inv hm₂
          exfalso
          simp only [List.length_append, List.length_singleton] at hshape
          omega
        · obtain ⟨h0, hv₂, -, -⟩ := restrictionFn_inr_elim hm₂
          rw [List.getLast_append_singleton] at hv₂
          refine ⟨hne, v₂, hP, hv₂, ?_⟩
          rw [hv₂]
    · obtain ⟨-, -, hshape, -⟩ := restrictionFn_inr_elim hm
      exfalso
      omega

/-- One admitted restriction round, constructed from a proper system answer. -/
theorem drive_restrictionFn_round_mem
    (P : List X → Prop) [DecidablePred P] (S : System.DDS X Y)
    {us : List X} {ys : List (Option Y)}
    (hlen : us.length = ys.length + 1) (hP : P us)
    (xs : List X) {y : Y} (hne : us ≠ [])
    (hy : System.output (S⊥) (xs ++ [us.getLast hne])
      (by rw [System.dom_fullyDefined]; simp) = some y) :
    (y, xs ++ [us.getLast hne], ys ++ [some y]) ∈
      drive (restrictionFn P) S 2 us xs ys := by
  have hm : Sum.inl (us.getLast hne) ∈ restrictionFn P (us, ys) :=
    restrictionFn_inl_mem P hlen hP
  refine drive_mem_query (restrictionFn P) S hm ?_
  rw [hy]
  have hm₂ : Sum.inr y ∈ restrictionFn P (us, ys ++ [some y]) := by
    refine restrictionFn_inr_mem P (by simp [hlen]) (by simp) hP ?_
    rw [List.getLast_append_singleton]
  exact drive_mem_answer (restrictionFn P) S hm₂ 0

/-- Forward realization of an admitted outer history. -/
theorem driveOuter_restrictionFn_of_dom
    (P : List X → Prop) [DecidablePred P] (hP : PrefixClosed P)
    (S : System.DDS X Y) :
    ∀ (rest xs : List X) (ys : List (Option Y)),
      xs.length = ys.length →
      P (xs ++ rest) →
      (xs ++ rest ∈ System.dom S ∨ rest = []) →
      ∃ vs ys',
        (vs, xs ++ rest, ys') ∈
          driveOuter (restrictionFn P) S 2 xs xs ys rest ∧
        ∀ (h : xs ++ rest ∈ System.dom S), rest ≠ [] →
          vs.getLast? = some (System.output S (xs ++ rest) h) := by
  intro rest
  induction rest with
  | nil =>
      intro xs ys _ _ _
      exact ⟨[], ys, by simp [driveOuter], fun _ hne => absurd rfl hne⟩
  | cons u rest ih =>
      intro xs ys hlen hadmit hdom
      have hdom' : xs ++ u :: rest ∈ System.dom S := by
        rcases hdom with h | h
        · exact h
        · exact absurd h (by simp)
      have hxs : xs ∈ System.dom S ∨ xs = [] := by
        rcases eq_or_ne xs [] with h | h
        · exact Or.inr h
        · exact Or.inl (System.prefix_closed S ⟨u :: rest, rfl⟩ h hdom')
      have hnext : xs ++ [u] ∈ System.dom S :=
        System.prefix_closed S ⟨rest, by simp⟩ (by simp) hdom'
      have hadmitNext : P (xs ++ [u]) :=
        hP ⟨rest, by simp⟩ hadmit
      have hout : System.output (S⊥) (xs ++ [u])
          (by rw [System.dom_fullyDefined]; simp)
          = some (System.output S (xs ++ [u]) hnext) :=
        System.output_fullyDefined_append_of_mem S xs u hxs hnext
      have hgl : (xs ++ [u]).getLast (by simp) = u :=
        List.getLast_append_singleton xs
      have hy' : System.output (S⊥) (xs ++ [(xs ++ [u]).getLast (by simp)])
          (by rw [System.dom_fullyDefined]; simp)
          = some (System.output S (xs ++ [u]) hnext) :=
        (System.output_congr (S⊥) (by rw [hgl])
          (by rw [System.dom_fullyDefined]; simp)
          (by rw [System.dom_fullyDefined]; simp)).trans hout
      have hround := drive_restrictionFn_round_mem P S (us := xs ++ [u])
        (ys := ys) (by simp [hlen]) hadmitNext xs (by simp) hy'
      rw [hgl] at hround
      obtain ⟨vs', ys'', hmem', hlast'⟩ := ih (xs ++ [u])
        (ys ++ [some (System.output S (xs ++ [u]) hnext)]) (by simp [hlen])
        (by simpa [List.append_assoc] using hadmit)
        (Or.inl (by simpa [List.append_assoc] using hdom'))
      refine ⟨System.output S (xs ++ [u]) hnext :: vs', ys'', ?_, ?_⟩
      · simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
        exact ⟨(System.output S (xs ++ [u]) hnext, xs ++ [u],
          ys ++ [some (System.output S (xs ++ [u]) hnext)]), hround,
          (vs', (xs ++ [u]) ++ rest, ys''), hmem', by simp [List.append_assoc]⟩
      · intro h hne
        cases hvs : vs' with
        | nil =>
            have hrest : rest = [] := by
              have hlen' := driveOuter_length (restrictionFn P) S 2 hmem'
              rw [hvs] at hlen'
              exact List.eq_nil_of_length_eq_zero (by simpa using hlen'.symm)
            subst hrest
            rw [List.getLast?_singleton]
        | cons v0 vs0 =>
            have hrest : rest ≠ [] := by
              have hlen' := driveOuter_length (restrictionFn P) S 2 hmem'
              rw [hvs] at hlen'
              intro hnil
              rw [hnil] at hlen'
              simp at hlen'
            have h' : (xs ++ [u]) ++ rest ∈ System.dom S := by
              simpa [List.append_assoc] using h
            have hlast'' := hlast' h' hrest
            rw [hvs] at hlast''
            rw [List.getLast?_cons_cons, hlast'']
            exact congrArg some (System.output_congr S (by simp) h' h)

/-- Backward realization: every defined nonempty run certifies both the
underlying system domain and the restriction predicate. -/
theorem driveOuter_restrictionFn_mem_imp
    (P : List X → Prop) [DecidablePred P] (S : System.DDS X Y) :
    ∀ (rest xs : List X) (ys : List (Option Y)) {fuel : ℕ}
      {r : List Y × List X × List (Option Y)},
      xs.length = ys.length →
      (xs ∈ System.dom S ∨ xs = []) →
      r ∈ driveOuter (restrictionFn P) S fuel xs xs ys rest →
      r.2.1 = xs ++ rest ∧
        (rest ≠ [] → P (xs ++ rest) ∧
          ∃ h : xs ++ rest ∈ System.dom S,
            r.1.getLast? = some (System.output S (xs ++ rest) h)) := by
  intro rest
  induction rest with
  | nil =>
      intro xs ys fuel r _ _ hr
      simp only [driveOuter, Part.mem_some_iff] at hr
      subst hr
      exact ⟨by simp, fun hne => absurd rfl hne⟩
  | cons u rest ih =>
      intro xs ys fuel r hlen hxs hr
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at hr
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := hr
      obtain ⟨hne₁, y, hadmit₁, hy, rfl⟩ :=
        drive_restrictionFn_round_elim (by simp [hlen]) hr₁
      have hgl : (xs ++ [u]).getLast hne₁ = u :=
        List.getLast_append_singleton xs
      rw [hgl] at hrr
      have hy' : System.output (S⊥) (xs ++ [u])
          (by rw [System.dom_fullyDefined]; simp) = some y :=
        ((System.output_congr (S⊥) (by rw [hgl])
          (by rw [System.dom_fullyDefined]; simp)
          (by rw [System.dom_fullyDefined]; simp)).symm).trans hy
      obtain ⟨hnext, houtS⟩ :=
        System.mem_of_output_fullyDefined_append_eq_some S xs u hxs hy'
      obtain ⟨hthread, hcond⟩ := ih (xs ++ [u]) (ys ++ [some y])
        (by simp [hlen]) (Or.inl hnext) hrr
      refine ⟨by rw [hthread]; simp [List.append_assoc], fun _ => ?_⟩
      cases hrest : rest with
      | nil =>
          subst hrest
          simp only [driveOuter, Part.mem_some_iff] at hrr
          subst hrr
          refine ⟨by simpa using hadmit₁, by simpa using hnext, ?_⟩
          rw [List.getLast?_singleton]
          refine congrArg some ?_
          rw [System.output_congr S (l₂ := xs ++ [u]) (by simp) _ hnext,
            houtS]
      | cons r0 rs0 =>
          obtain ⟨hadmit', h', hlast'⟩ := hcond (by simp [hrest])
          refine ⟨by simpa [List.append_assoc, hrest] using hadmit',
            by simpa [List.append_assoc, hrest] using h', ?_⟩
          have hlenrr := driveOuter_length (restrictionFn P) S fuel hrr
          cases hrr1 : rr.1 with
          | nil =>
              rw [hrr1] at hlenrr
              simp [hrest] at hlenrr
          | cons v0 vs0 =>
              rw [hrr1] at hlast'
              rw [List.getLast?_cons_cons, hlast']
              exact congrArg some
                (System.output_congr S (by simp [hrest]) h' _)

/-- The transcript-equation application of the identity restriction converter
is exactly the corresponding DDS domain restriction. -/
theorem apply_restrictionFn
    (P : List X → Prop) [DecidablePred P] (hP : PrefixClosed P)
    (S : System.DDS X Y) :
    apply (restrictionFn P) S = System.filterDom P hP S := by
  apply Subtype.ext
  funext us
  apply Part.ext
  intro v
  rw [show (apply (restrictionFn P) S).1 =
      applyRaw (restrictionFn P) S from rfl, mem_applyRaw]
  constructor
  · rintro ⟨fuel, hv⟩
    rw [mem_applyRawAt_iff] at hv
    obtain ⟨r, hr, hlast⟩ := hv
    have hne : us ≠ [] := by
      rintro rfl
      have hlen := driveOuter_length (restrictionFn P) S fuel hr
      rw [List.length_nil] at hlen
      rw [List.eq_nil_of_length_eq_zero hlen] at hlast
      simp at hlast
    obtain ⟨-, hcond⟩ :=
      driveOuter_restrictionFn_mem_imp P S us [] [] rfl (Or.inr rfl) hr
    obtain ⟨hadmit, h, hout⟩ := hcond hne
    rw [hlast] at hout
    have hv' := Option.some.inj hout
    refine ⟨⟨h, hadmit⟩, ?_⟩
    show System.output S us _ = v
    rw [hv']
    exact System.output_congr S (by simp) _ h
  · rintro ⟨⟨hd, hadmit⟩, rfl⟩
    have hdom : us ∈ System.dom S := hd
    have hne : us ≠ [] := by
      rintro rfl
      exact System.empty_not_mem S hdom
    obtain ⟨vs, ys', hmem, hlast⟩ :=
      driveOuter_restrictionFn_of_dom P hP S us [] [] rfl
        (by simpa using hadmit) (Or.inl (by simpa using hdom))
    refine ⟨2, ?_⟩
    rw [mem_applyRawAt_iff]
    refine ⟨(vs, [] ++ us, ys'), hmem, ?_⟩
    rw [hlast (by simpa using hdom) hne]
    exact congrArg some (System.output_congr S (by simp) _ hd)

end RestrictionInstance

/-! ### The `[q]` instance: the first cross-round converter, computed

`queryLimitFn q` (a round counter — outside the outer-memoryless class) applied by
the transcript equations *is* the canonical CR18 Def 3.10 restriction
`filterQueries q`.  Combined with the pre-existing operational theorem, the
old `[q]ᶠ` DDC and `toDDC (queryLimitFn q)` are apply-equal representatives
of the same converter — the bespoke trace proof is retired as the "factors
through lengths" instance of the realization theorem. -/

section QueryLimitInstance

variable {X : Type z} {Y : Type v}

theorem queryLimitFn_inl_elim {q : ℕ} {us : List X} {ys : List (Option Y)}
    {x : X} (h : Sum.inl x ∈ queryLimitFn q (us, ys)) :
    ∃ hne : us ≠ [],
      x = us.getLast hne ∧ us.length = ys.length + 1 ∧ us.length ≤ q := by
  have hlen := queryLimitFn_inl_inv h
  refine ⟨by apply List.ne_nil_of_length_pos; omega, ?_, hlen⟩
  have hval : queryLimitFn q (us, ys) = Part.some (Sum.inl (us.getLast (by
      apply List.ne_nil_of_length_pos; omega))) := by
    simp only [queryLimitFn]
    rw [dif_pos hlen]
  rw [hval, Part.mem_some_iff] at h
  exact Sum.inl.inj h

theorem queryLimitFn_inr_elim {q : ℕ} {us : List X} {ys : List (Option Y)}
    {v : Y} (h : Sum.inr v ∈ queryLimitFn q (us, ys)) :
    ∃ h0 : 0 < ys.length,
      ys.getLast (List.ne_nil_of_length_pos h0) = some v ∧
        us.length = ys.length ∧ us.length ≤ q := by
  obtain ⟨h1, h3, h0, hy⟩ := queryLimitFn_inr_inv h
  exact ⟨h0, hy, h1, h3⟩

/-- One `[q]` round, destructed: forward the last outer input, return the
system's (proper, `some`) answer, budget respected — an improper answer `⊥`
silences the round, so a completed round certifies someness. -/
theorem drive_queryLimitFn_round_elim {q : ℕ} {S : System.DDS X Y}
    {us : List X} {ys : List (Option Y)} {fuel : ℕ} {xs : List X}
    {p : Y × List X × List (Option Y)}
    (hlen : us.length = ys.length + 1)
    (hp : p ∈ drive (queryLimitFn q) S fuel us xs ys) :
    ∃ (hne : us ≠ []) (y : Y), us.length ≤ q ∧
      System.output (S⊥) (xs ++ [us.getLast hne])
        (by rw [System.dom_fullyDefined]; simp) = some y ∧
      p = (y, xs ++ [us.getLast hne], ys ++ [some y]) := by
  rcases fuel with _ | fuel
  · simp [drive] at hp
  · rcases drive_succ_elim hp with ⟨x, hm, hp'⟩ | ⟨v, hm, rfl⟩
    · obtain ⟨hne, rfl, -, hq⟩ := queryLimitFn_inl_elim hm
      rcases fuel with _ | fuel
      · simp [drive] at hp'
      · rcases drive_succ_elim hp' with ⟨x₂, hm₂, hp''⟩ | ⟨v₂, hm₂, rfl⟩
        · obtain ⟨h2, -⟩ := queryLimitFn_inl_inv hm₂
          exfalso
          simp only [List.length_append, List.length_singleton] at h2
          omega
        · obtain ⟨h0, hv₂, -, -⟩ := queryLimitFn_inr_elim hm₂
          rw [List.getLast_append_singleton] at hv₂
          refine ⟨hne, v₂, hq, hv₂, ?_⟩
          rw [hv₂]
    · obtain ⟨-, -, h2, -⟩ := queryLimitFn_inr_elim hm
      exfalso
      omega

/-- One `[q]` round, constructed (from a someness witness for the `S⊥`
answer). -/
theorem drive_queryLimitFn_round_mem (q : ℕ) (S : System.DDS X Y)
    {us : List X} {ys : List (Option Y)} (hlen : us.length = ys.length + 1)
    (hq : us.length ≤ q) (xs : List X) {y : Y} (hne : us ≠ [])
    (hy : System.output (S⊥) (xs ++ [us.getLast hne])
      (by rw [System.dom_fullyDefined]; simp) = some y) :
    (y, xs ++ [us.getLast hne], ys ++ [some y]) ∈
      drive (queryLimitFn q) S 2 us xs ys := by
  have hm : Sum.inl (us.getLast hne) ∈ queryLimitFn q (us, ys) :=
    queryLimitFn_inl_mem q hlen hq
  refine drive_mem_query (queryLimitFn q) S hm ?_
  rw [hy]
  have hm₂ : Sum.inr y ∈ queryLimitFn q (us, ys ++ [some y]) := by
    refine queryLimitFn_inr_mem q (by simp [hlen]) (by simp) hq ?_
    rw [List.getLast_append_singleton]
  exact drive_mem_answer (queryLimitFn q) S hm₂ 0

/-- Forward run of `[q]` over a whole outer history (fuel 2 suffices). -/
theorem driveOuter_queryLimitFn_of_dom (q : ℕ) (S : System.DDS X Y) :
    ∀ (rest xs : List X) (ys : List (Option Y)),
      xs.length = ys.length →
      xs.length + rest.length ≤ q →
      (xs ++ rest ∈ System.dom S ∨ rest = []) →
      ∃ vs ys',
        (vs, xs ++ rest, ys') ∈
          driveOuter (queryLimitFn q) S 2 xs xs ys rest ∧
        ∀ (h : xs ++ rest ∈ System.dom S), rest ≠ [] →
          vs.getLast? = some (System.output S (xs ++ rest) h) := by
  intro rest
  induction rest with
  | nil =>
      intro xs ys _ _ _
      exact ⟨[], ys, by simp [driveOuter], fun _ hne => absurd rfl hne⟩
  | cons u rest ih =>
      intro xs ys hlen hbudget hdom
      have hdom' : xs ++ u :: rest ∈ System.dom S := by
        rcases hdom with h | h
        · exact h
        · exact absurd h (by simp)
      have hxs : xs ∈ System.dom S ∨ xs = [] := by
        rcases eq_or_ne xs [] with h | h
        · exact Or.inr h
        · exact Or.inl (System.prefix_closed S ⟨u :: rest, rfl⟩ h hdom')
      have hnext : xs ++ [u] ∈ System.dom S :=
        System.prefix_closed S ⟨rest, by simp⟩ (by simp) hdom'
      have hout : System.output (S⊥) (xs ++ [u])
          (by rw [System.dom_fullyDefined]; simp)
          = some (System.output S (xs ++ [u]) hnext) :=
        System.output_fullyDefined_append_of_mem S xs u hxs hnext
      have hgl : (xs ++ [u]).getLast (by simp) = u :=
        List.getLast_append_singleton xs
      have hy' : System.output (S⊥) (xs ++ [(xs ++ [u]).getLast (by simp)])
          (by rw [System.dom_fullyDefined]; simp)
          = some (System.output S (xs ++ [u]) hnext) :=
        (System.output_congr (S⊥) (by rw [hgl])
          (by rw [System.dom_fullyDefined]; simp)
          (by rw [System.dom_fullyDefined]; simp)).trans hout
      have hround := drive_queryLimitFn_round_mem q S (us := xs ++ [u])
        (ys := ys) (by simp [hlen])
        (by
          simp only [List.length_cons] at hbudget
          simp only [List.length_append, List.length_singleton]
          omega)
        xs (by simp) hy'
      rw [hgl] at hround
      have hbudget' : (xs ++ [u]).length + rest.length ≤ q := by
        simp only [List.length_append, List.length_singleton]
        simp only [List.length_cons] at hbudget
        omega
      obtain ⟨vs', ys'', hmem', hlast'⟩ := ih (xs ++ [u])
        (ys ++ [some (System.output S (xs ++ [u]) hnext)]) (by simp [hlen])
        hbudget' (Or.inl (by simpa [List.append_assoc] using hdom'))
      refine ⟨System.output S (xs ++ [u]) hnext :: vs', ys'', ?_, ?_⟩
      · simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
        exact ⟨(System.output S (xs ++ [u]) hnext, xs ++ [u],
          ys ++ [some (System.output S (xs ++ [u]) hnext)]), hround,
          (vs', (xs ++ [u]) ++ rest, ys''), hmem', by simp [List.append_assoc]⟩
      · intro h hne
        cases hvs : vs' with
        | nil =>
            have hrest : rest = [] := by
              have hlen' := driveOuter_length (queryLimitFn q) S 2 hmem'
              rw [hvs] at hlen'
              exact List.eq_nil_of_length_eq_zero (by simpa using hlen'.symm)
            subst hrest
            rw [List.getLast?_singleton]
        | cons v0 vs0 =>
            have hrest : rest ≠ [] := by
              have hlen' := driveOuter_length (queryLimitFn q) S 2 hmem'
              rw [hvs] at hlen'
              intro hnil
              rw [hnil] at hlen'
              simp at hlen'
            have h' : (xs ++ [u]) ++ rest ∈ System.dom S := by
              simpa [List.append_assoc] using h
            have hlast'' := hlast' h' hrest
            rw [hvs] at hlast''
            rw [List.getLast?_cons_cons, hlast'']
            exact congrArg some (System.output_congr S (by simp) h' h)

/-- Backward run analysis of `[q]`: a defined run certifies the domain
membership round by round (the `some`-witness of each completed round is
cashed through `S⊥`, anchored at an in-dom-or-empty inner history). -/
theorem driveOuter_queryLimitFn_mem_imp (q : ℕ) (S : System.DDS X Y) :
    ∀ (rest xs : List X) (ys : List (Option Y)) {fuel : ℕ}
      {r : List Y × List X × List (Option Y)},
      xs.length = ys.length →
      (xs ∈ System.dom S ∨ xs = []) →
      r ∈ driveOuter (queryLimitFn q) S fuel xs xs ys rest →
      r.2.1 = xs ++ rest ∧
        (rest ≠ [] → xs.length + rest.length ≤ q ∧
          ∃ h : xs ++ rest ∈ System.dom S,
            r.1.getLast? = some (System.output S (xs ++ rest) h)) := by
  intro rest
  induction rest with
  | nil =>
      intro xs ys fuel r _ _ hr
      simp only [driveOuter, Part.mem_some_iff] at hr
      subst hr
      exact ⟨by simp, fun hne => absurd rfl hne⟩
  | cons u rest ih =>
      intro xs ys fuel r hlen hxs hr
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at hr
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := hr
      obtain ⟨hne₁, y, hq₁, hy, rfl⟩ :=
        drive_queryLimitFn_round_elim (by simp [hlen]) hr₁
      have hgl : (xs ++ [u]).getLast hne₁ = u :=
        List.getLast_append_singleton xs
      rw [hgl] at hrr
      have hy' : System.output (S⊥) (xs ++ [u])
          (by rw [System.dom_fullyDefined]; simp) = some y :=
        ((System.output_congr (S⊥) (by rw [hgl])
          (by rw [System.dom_fullyDefined]; simp)
          (by rw [System.dom_fullyDefined]; simp)).symm).trans hy
      obtain ⟨hnext, houtS⟩ :=
        System.mem_of_output_fullyDefined_append_eq_some S xs u hxs hy'
      obtain ⟨hthread, hcond⟩ := ih (xs ++ [u]) (ys ++ [some y])
        (by simp [hlen]) (Or.inl hnext) hrr
      refine ⟨by rw [hthread]; simp [List.append_assoc], fun _ => ?_⟩
      cases hrest : rest with
      | nil =>
          subst hrest
          simp only [driveOuter, Part.mem_some_iff] at hrr
          subst hrr
          refine ⟨?_, by simpa using hnext, ?_⟩
          · simp only [List.length_cons, List.length_nil]
            simp only [List.length_append, List.length_singleton] at hq₁
            omega
          · rw [List.getLast?_singleton]
            refine congrArg some ?_
            rw [System.output_congr S (l₂ := xs ++ [u]) (by simp) _ hnext,
              houtS]
      | cons r0 rs0 =>
          obtain ⟨hbudget', h', hlast'⟩ := hcond (by simp [hrest])
          rw [hrest] at hbudget'
          refine ⟨?_, by simpa [List.append_assoc, hrest] using h', ?_⟩
          · simp only [List.length_append, List.length_cons,
              List.length_nil] at hbudget' ⊢
            omega
          · have hlenrr := driveOuter_length (queryLimitFn q) S fuel hrr
            cases hrr1 : rr.1 with
            | nil =>
                rw [hrr1] at hlenrr
                simp [hrest] at hlenrr
            | cons v0 vs0 =>
                rw [hrr1] at hlast'
                rw [List.getLast?_cons_cons, hlast']
                exact congrArg some
                  (System.output_congr S (by simp [hrest]) h' _)

/-- **The `[q]` filter, computed by the transcript equations**: the ν-level
application of the round-counter protocol function is exactly CR18
Def 3.10's canonical restriction.  Out-of-dom queries answer `⊥`, on which
`queryLimitFn` is silent — the drive has no result, matching the restricted
domain. -/
theorem apply_queryLimitFn (q : ℕ) (S : System.DDS X Y) :
    apply (queryLimitFn q) S = System.filterQueries q S := by
  apply Subtype.ext
  funext us
  apply Part.ext
  intro v
  rw [show (apply (queryLimitFn q) S).1
      = applyRaw (queryLimitFn q) S from rfl, mem_applyRaw]
  constructor
  · rintro ⟨fuel, hv⟩
    rw [mem_applyRawAt_iff] at hv
    obtain ⟨r, hr, hlast⟩ := hv
    have hne : us ≠ [] := by
      rintro rfl
      have hlen := driveOuter_length (queryLimitFn q) S fuel hr
      rw [List.length_nil] at hlen
      rw [List.eq_nil_of_length_eq_zero hlen] at hlast
      simp at hlast
    obtain ⟨-, hcond⟩ :=
      driveOuter_queryLimitFn_mem_imp q S us [] [] rfl (Or.inr rfl) hr
    obtain ⟨hbudget, h, hout⟩ := hcond hne
    rw [hlast] at hout
    have hv' := Option.some.inj hout
    refine ⟨⟨h, by simpa using hbudget⟩, ?_⟩
    show System.output S us _ = v
    rw [hv']
    exact System.output_congr S (by simp) _ h
  · rintro ⟨⟨hd, hq⟩, rfl⟩
    have hdom : us ∈ System.dom S := hd
    have hne : us ≠ [] := by
      rintro rfl
      exact System.empty_not_mem S hdom
    obtain ⟨vs, ys', hmem, hlast⟩ :=
      driveOuter_queryLimitFn_of_dom q S us [] [] rfl (by simpa using hq)
        (Or.inl (by simpa using hdom))
    refine ⟨2, ?_⟩
    rw [mem_applyRawAt_iff]
    refine ⟨(vs, [] ++ us, ys'), hmem, ?_⟩
    rw [hlast (by simpa using hdom) hne]
    exact congrArg some (System.output_congr S (by simp) _ hd)

/-- Def 3.9 applied to the canonical `[q]` object = Def 3.10's restriction. -/
theorem apply_toDDC_queryLimitFn (q : ℕ) (S : System.DDS X Y) :
    DDC.apply (toDDC (queryLimitFn q)) S = System.filterQueries q S := by
  rw [apply_toDDC, apply_queryLimitFn]

/-- **Two representatives, one converter**: the old operational `[q]ᶠ` DDC
and the canonical `toDDC (queryLimitFn q)` are apply-equal — both realize
`filterQueries q`.  This retires `queryLimit`-style bespoke trace proofs: the
ν route re-proves the same theorem as an instance of `apply_toDDC`. -/
theorem queryLimit_apply_eq_toDDC (q : ℕ) (S : System.DDS X Y) :
    DDC.apply (queryLimit q : Filter X Y) S
      = DDC.apply (toDDC (queryLimitFn q)) S := by
  rw [apply_toDDC_queryLimitFn]
  exact queryLimit_filter_apply_eq_filterQueries q S

end QueryLimitInstance

/-! ### `toNu` and the round-trip: junk-free ν ≅ normalized DDC

`toNu α` reads an arbitrary Def 3.8 DDC back as a protocol function: its
value at a pair is the DDC's move at the pair's canonical trace (the
interleaving the DDC itself dictates, `DDCTrace`).  The round-trip
`toNu (toDDC ν) = normalize ν` says the ν-world is exactly the junk-free
quotient of the DDC-world. -/

section ToNu

variable {U : Type u} {V : Type w} {X : Type z} {Y : Type v}

/-- The canonical trace of a pair under an arbitrary DDC: outer inputs and
inner answers (`⊥` included — the Def 3.8 alphabet) delivered in the order
the DDC's own moves dictate. -/
inductive DDCTrace (α : DDC U V X Y) :
    List (DDC.CIn U Y) → List U × List (Option Y) → Prop
  | first (u : U) : DDCTrace α [Sum.inl (InLabel.outside, u)] ([u], [])
  | next {c us ys v} (ht : DDCTrace α c (us, ys))
      (hv : Sum.inl (InLabel.outside, v) ∈ α.1 c) (u : U) :
      DDCTrace α (c ++ [Sum.inl (InLabel.outside, u)]) (us ++ [u], ys)
  | answer {c us ys x} (ht : DDCTrace α c (us, ys))
      (hx : Sum.inr (InLabel.inside, x) ∈ α.1 c) (y : Option Y) :
      DDCTrace α (c ++ [Sum.inr (InLabel.inside, y)]) (us, ys ++ [y])

/-- Decode a converter-output move back to a protocol move (partial inverse
of `DDC.moveOf`; junk labels have no decoding). -/
def fromCOut : DDC.COut V X → Part (X ⊕ V)
  | Sum.inl (InLabel.outside, v) => Part.some (Sum.inr v)
  | Sum.inr (InLabel.inside, x) => Part.some (Sum.inl x)
  | _ => Part.none

@[simp] theorem fromCOut_moveOf (m : X ⊕ V) :
    fromCOut (DDC.moveOf m) = Part.some m := by
  cases m <;> rfl

/-- **A DDC as a protocol function**: the move at the pair's canonical
trace. -/
noncomputable def toNu (α : DDC U V X Y) : ProtocolFn U V X Y := fun p =>
  Part.assert (∃ c, DDCTrace α c p) fun h =>
    (α.1 h.choose).bind fromCOut

/-- Canonical traces of `toDDC ν` are ν-parses. -/
theorem ddcTrace_toDDC_parses {ν : ProtocolFn U V X Y}
    {c : List (DDC.CIn U Y)} {p : List U × List (Option Y)}
    (h : DDCTrace (toDDC ν) c p) : ParsesTo ν c p := by
  induction h with
  | first u => exact parsesTo_singleton ν u
  | next ht hv u ih =>
      rw [toDDC_toPFun, mem_toDDCRaw_iff] at hv
      obtain ⟨q, hq, mm, hmm, heq⟩ := hv
      obtain rfl := parsesTo_unique hq ih
      have hmv : mm = Sum.inr _ := moveOf_eq_out_iff.mp heq.symm
      subst hmv
      exact parsesTo_snoc_out ih hmm u
  | answer ht hx y ih =>
      rw [toDDC_toPFun, mem_toDDCRaw_iff] at hx
      obtain ⟨q, hq, mm, hmm, heq⟩ := hx
      obtain rfl := parsesTo_unique hq ih
      have hmv : mm = Sum.inl _ := moveOf_eq_in_iff.mp heq.symm
      subst hmv
      exact parsesTo_snoc_in ih hmm y

/-- Every reachable pair has a canonical trace, both as a ν-parse and as a
`toDDC ν`-trace. -/
theorem reach_toDDC_trace {ν : ProtocolFn U V X Y}
    {p : List U × List (Option Y)} (h : Reach ν p) :
    ∃ c, ParsesTo ν c p ∧ DDCTrace (toDDC ν) c p := by
  induction h with
  | first u => exact ⟨_, parsesTo_singleton ν u, DDCTrace.first u⟩
  | answer hr hx y ih =>
      rename_i q x
      obtain ⟨c, hp, ht⟩ := ih
      refine ⟨_, parsesTo_snoc_in hp hx y, DDCTrace.answer (x := x) ht ?_ y⟩
      simpa [DDC.moveOf] using mem_toDDC_of_parses hp hx
  | next hr hv u ih =>
      rename_i q v
      obtain ⟨c, hp, ht⟩ := ih
      refine ⟨_, parsesTo_snoc_out hp hv u, DDCTrace.next (v := v) ht ?_ u⟩
      simpa [DDC.moveOf] using mem_toDDC_of_parses hp hv

/-- **The round-trip**: reading the canonical Def 3.8 object of ν back as a
protocol function yields exactly ν's junk-free normalization — the ν-world
is the junk-free quotient of the DDC-world. -/
theorem toNu_toDDC (ν : ProtocolFn U V X Y) :
    toNu (toDDC ν) = normalize ν := by
  funext p
  apply Part.ext
  intro m
  simp only [toNu, Part.mem_assert_iff, Part.mem_bind_iff]
  constructor
  · rintro ⟨hex, o, ho, hfrom⟩
    have hp₀ : ParsesTo ν hex.choose p :=
      ddcTrace_toDDC_parses hex.choose_spec
    rw [toDDC_toPFun, mem_toDDCRaw_iff] at ho
    obtain ⟨q, hq, mm, hmm, rfl⟩ := ho
    obtain rfl := parsesTo_unique hq hp₀
    rw [fromCOut_moveOf, Part.mem_some_iff] at hfrom
    subst hfrom
    exact (mem_normalize_iff ν _ _).mpr ⟨hmm, hq.reach⟩
  · intro hm
    obtain ⟨hmem, hreach⟩ := (mem_normalize_iff ν p m).mp hm
    obtain ⟨c, hp, ht⟩ := reach_toDDC_trace hreach
    refine ⟨⟨c, ht⟩, ?_⟩
    have hp₀ : ParsesTo ν
        (Exists.choose (⟨c, ht⟩ : ∃ c, DDCTrace (toDDC ν) c p)) p :=
      ddcTrace_toDDC_parses
        (Exists.choose_spec (⟨c, ht⟩ : ∃ c, DDCTrace (toDDC ν) c p))
    exact ⟨DDC.moveOf m, mem_toDDC_of_parses hp₀ hmem,
      by rw [fromCOut_moveOf]; exact Part.mem_some _⟩

/-- Junk-free protocol functions round-trip on the nose. -/
theorem toNu_toDDC_of_junkFree {ν : ProtocolFn U V X Y} (h : JunkFree ν) :
    toNu (toDDC ν) = ν := by
  rw [toNu_toDDC, normalize_eq_self_of_junkFree h]

end ToNu

/-! ### Drive congruence: application sees a protocol only where the drive goes

The trace tree (`Reach`) quantifies over *every* answer, because a converter does
not know the system it will meet.  A single application does know: `drive`
consults `ν` at `(us, ys)` where `ys` is exactly the list of answers **this**
system gave to the queries `ν` has issued so far.  Two protocol functions that
agree at every pair one application actually visits therefore have the same
application at that system, even when they are not `TraceEquiv` — the tree
distinguishes them on answers the system never produces.

`DriveReach ν S us xs` is that visited set, indexed by the outer history and the
issued inner history; the answer history is recovered from the latter by
`sysAnswers`, which is the invariant `drive` maintains.

This is what lets a *count-attributing* converter (`ofHistoryStepPartial`, silent
on an answer it cannot attribute — Def 3.8's citizen) be evaluated by the law of
the *tag-filtering* one (`Converter.par`, which is not one): against a
tag-faithful system the two never disagree. -/

section DriveCongruence

variable {U : Type u} {V : Type w} {X : Type z} {Y : Type v}

/-- The system's own answer to an inner history, in Def 3.3's completion —
exactly the value `drive` appends.  Def 3.3's completion is defined on nonempty
histories only, and `drive` only ever consults it at one (`xs ++ [x]`); the
empty case is a junk value never reached. -/
noncomputable def sysAnswer (S : System.DDS X Y) (xs : List X) : Option Y :=
  if h : xs ≠ [] then
    System.output (S⊥) xs (by rw [System.dom_fullyDefined]; exact h)
  else none

theorem sysAnswer_of_ne_nil (S : System.DDS X Y) {xs : List X} (hne : xs ≠ [])
    (h : xs ∈ System.dom (S⊥)) : sysAnswer S xs = System.output (S⊥) xs h := by
  rw [sysAnswer, dif_pos hne]

/-- The answer history a system produces along an inner history: the invariant
`drive` threads in its third argument. -/
noncomputable def sysAnswers (S : System.DDS X Y) (xs : List X) :
    List (Option Y) :=
  (List.range xs.length).map fun k => sysAnswer S (xs.take (k + 1))

@[simp]
theorem sysAnswers_nil (S : System.DDS X Y) : sysAnswers S [] = [] := by
  simp [sysAnswers]

@[simp]
theorem sysAnswers_length (S : System.DDS X Y) (xs : List X) :
    (sysAnswers S xs).length = xs.length := by
  simp [sysAnswers]

/-- The system's answer depends on the inner history only through its value —
the transport that the dependent `System.output` proof argument blocks `rw`
from doing. -/
theorem sysAnswer_congr (S : System.DDS X Y) {xs xs' : List X} (h : xs = xs') :
    sysAnswer S xs = sysAnswer S xs' := by
  subst h; rfl

/-- One further query appends exactly one further system answer. -/
theorem sysAnswers_concat (S : System.DDS X Y) (xs : List X) (x : X) :
    sysAnswers S (xs ++ [x]) = sysAnswers S xs ++ [sysAnswer S (xs ++ [x])] := by
  simp only [sysAnswers, List.length_append, List.length_singleton,
    List.range_succ, List.map_append, List.map_singleton]
  congr 1
  · refine List.map_congr_left ?_
    intro k hk
    rw [List.mem_range] at hk
    exact sysAnswer_congr S (List.take_append_of_le_length (by omega))
  · exact congrArg (fun value => [value])
      (sysAnswer_congr S (List.take_of_length_le (by simp)))

/-- The append form `drive` actually produces. -/
theorem sysAnswers_concat_output (S : System.DDS X Y) (xs : List X) (x : X)
    (h : xs ++ [x] ∈ System.dom (S⊥)) :
    sysAnswers S xs ++ [System.output (S⊥) (xs ++ [x]) h] =
      sysAnswers S (xs ++ [x]) := by
  rw [sysAnswers_concat, sysAnswer_of_ne_nil S (by simp) h]

/-- **The pairs one application visits**: the outer history `us` and the inner
history `xs` that `ν` has issued against `S`.  A query extends `xs`; an outer
answer extends `us`.  The answer history never appears — it is `sysAnswers S xs`
throughout, which is precisely the difference from `Reach`. -/
inductive DriveReach (ν : ProtocolFn U V X Y) (S : System.DDS X Y) :
    List U → List X → Prop
  | start (u : U) : DriveReach ν S [u] []
  | query {us : List U} {xs : List X} {x : X} (h : DriveReach ν S us xs)
      (hx : Sum.inl x ∈ ν (us, sysAnswers S xs)) : DriveReach ν S us (xs ++ [x])
  | next {us : List U} {xs : List X} {v : V} (h : DriveReach ν S us xs)
      (hv : Sum.inr v ∈ ν (us, sysAnswers S xs)) (u : U) :
      DriveReach ν S (us ++ [u]) xs

/-- A completed round leaves the visited set intact and exposes the answer move
that closed it. -/
theorem drive_mem_driveReach {ν : ProtocolFn U V X Y} {S : System.DDS X Y} :
    ∀ {fuel : ℕ} {us : List U} {xs : List X}
      {r : V × List X × List (Option Y)},
      DriveReach ν S us xs → r ∈ drive ν S fuel us xs (sysAnswers S xs) →
        r.2.2 = sysAnswers S r.2.1 ∧ DriveReach ν S us r.2.1 ∧
          Sum.inr r.1 ∈ ν (us, sysAnswers S r.2.1) := by
  intro fuel
  induction fuel with
  | zero => intro us xs r _ h; simp [drive] at h
  | succ n ih =>
      intro us xs r hreach h
      rcases drive_succ_elim h with ⟨x, hm, h⟩ | ⟨v, hm, rfl⟩
      · rw [sysAnswers_concat_output S xs x
          (by rw [System.dom_fullyDefined]; simp)] at h
        exact ih (DriveReach.query hreach hm) h
      · exact ⟨rfl, hreach, hm⟩

/-- The drive cannot tell two protocols apart at a visited pair. -/
theorem drive_congr_of_driveReach {ν ν' : ProtocolFn U V X Y} {S : System.DDS X Y}
    (agree : ∀ us xs, DriveReach ν S us xs →
      ν (us, sysAnswers S xs) = ν' (us, sysAnswers S xs)) :
    ∀ (fuel : ℕ) (us : List U) (xs : List X), DriveReach ν S us xs →
      drive ν S fuel us xs (sysAnswers S xs) =
        drive ν' S fuel us xs (sysAnswers S xs) := by
  intro fuel
  induction fuel with
  | zero => intro us xs _; rfl
  | succ n ih =>
      intro us xs hreach
      have hstep := agree us xs hreach
      have hcat : ∀ x : X, (sysAnswers S xs ++
          [System.output (S⊥) (xs ++ [x])
            (by rw [System.dom_fullyDefined]; simp)]) =
          sysAnswers S (xs ++ [x]) :=
        fun x => sysAnswers_concat_output S xs x _
      apply Part.ext
      intro r
      constructor
      · intro hr
        rcases drive_succ_elim hr with ⟨x, hm, hr'⟩ | ⟨v, hm, rfl⟩
        · refine drive_mem_query ν' S (by rwa [← hstep]) ?_
          rw [hcat x] at hr' ⊢
          rwa [← ih us (xs ++ [x]) (DriveReach.query hreach hm)]
        · exact drive_mem_answer ν' S (by rwa [← hstep]) n
      · intro hr
        rcases drive_succ_elim hr with ⟨x, hm, hr'⟩ | ⟨v, hm, rfl⟩
        · rw [← hstep] at hm
          refine drive_mem_query ν S hm ?_
          rw [hcat x] at hr' ⊢
          rwa [ih us (xs ++ [x]) (DriveReach.query hreach hm)]
        · rw [← hstep] at hm
          exact drive_mem_answer ν S hm n

/-- …and neither can the outer fold. -/
theorem driveOuter_congr_of_driveReach {ν ν' : ProtocolFn U V X Y} {S : System.DDS X Y}
    (agree : ∀ us xs, DriveReach ν S us xs →
      ν (us, sysAnswers S xs) = ν' (us, sysAnswers S xs)) (fuel : ℕ) :
    ∀ (rest usPre : List U) (xs : List X),
      (∀ u, DriveReach ν S (usPre ++ [u]) xs) →
      driveOuter ν S fuel usPre xs (sysAnswers S xs) rest =
        driveOuter ν' S fuel usPre xs (sysAnswers S xs) rest := by
  intro rest
  induction rest with
  | nil => intro usPre xs _; rfl
  | cons u rest ih =>
      intro usPre xs hreach
      have hround := drive_congr_of_driveReach agree fuel (usPre ++ [u]) xs (hreach u)
      apply Part.ext
      intro result
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
      constructor
      · rintro ⟨r, hr, rr, hrr, hres⟩
        obtain ⟨hys, hxs, hlast⟩ := drive_mem_driveReach (hreach u) hr
        refine ⟨r, hround ▸ hr, rr, ?_, hres⟩
        rw [hys] at hrr ⊢
        rwa [← ih (usPre ++ [u]) r.2.1
          (fun u' => DriveReach.next hxs hlast u')]
      · rintro ⟨r, hr, rr, hrr, hres⟩
        rw [← hround] at hr
        obtain ⟨hys, hxs, hlast⟩ := drive_mem_driveReach (hreach u) hr
        refine ⟨r, hr, rr, ?_, hres⟩
        rw [hys] at hrr ⊢
        rwa [ih (usPre ++ [u]) r.2.1
          (fun u' => DriveReach.next hxs hlast u')]

/-- **Application is a drive invariant**: protocols agreeing on every pair the
application visits apply identically, `TraceEquiv` or not. -/
theorem applyRaw_congr_of_driveReach {ν ν' : ProtocolFn U V X Y}
    {S : System.DDS X Y}
    (agree : ∀ us xs, DriveReach ν S us xs →
      ν (us, sysAnswers S xs) = ν' (us, sysAnswers S xs)) :
    applyRaw ν S = applyRaw ν' S := by
  funext us
  apply Part.ext
  intro value
  rw [mem_applyRaw, mem_applyRaw]
  refine exists_congr fun fuel => ?_
  rw [mem_applyRawAt_iff, mem_applyRawAt_iff]
  have hfold := driveOuter_congr_of_driveReach agree fuel us [] []
    (fun u => by simpa using DriveReach.start (ν := ν) (S := S) u)
  simp only [sysAnswers_nil] at hfold
  rw [hfold]

@[inherit_doc applyRaw_congr_of_driveReach]
theorem apply_congr_of_driveReach {ν ν' : ProtocolFn U V X Y}
    {S : System.DDS X Y}
    (agree : ∀ us xs, DriveReach ν S us xs →
      ν (us, sysAnswers S xs) = ν' (us, sysAnswers S xs)) :
    apply ν S = apply ν' S :=
  Subtype.ext (applyRaw_congr_of_driveReach agree)

end DriveCongruence

end Converter

end RandomSystems


/-!
# Serial composition and the interaction-associativity law

`comp α β` is the serial composite of two protocol functions: an outer
converter `α : List W × List (Option V) →. U ⊕ Z` stacked on an inner
converter `β : List U × List (Option Y) →. X ⊕ V`.  Its move at a composite
pair `(ws, ys)` is
computed by the **flat replay** `compGo`: re-run the two-converter stack,
delivering the outer inputs `ws` and the base answers `ys` in the order the
stack itself dictates (the `absorb` recipe from `AbsorbDPI.lean` with the
distinguisher slot generalized to a protocol; `Part`-partiality absorbs
divergent internal chatter, so the *definition* needs no round bounds).

The target theorem is the **action law**

`apply (comp α β) S = apply α (apply β S)`

— applying the composite is composing the applications; converter
application is a monoid action on systems.  The proof is a three-level
joint-run relation `CompRun` (outer, middle, base transcripts plus the
stack's mode) with flat replay/extraction lemmas on one side and
`drive`/`driveOuter` certification of the middle system on the other.
Under the Def 3.8 `Y ∪ {⊥}` alphabet the staged side can feed α a `⊥`
wherever the β-composite is silent — a run with no stack counterpart — so
the law carries β-productivity hypotheses (`AnswersWithin` plus no silence
on reachable pairs), under which the middle system is total and both sides
thread identical `some`-answers.
-/

namespace RandomSystems

namespace Converter

open scoped System

universe u v w z u' w'

variable {U : Type u} {V : Type w} {X : Type z} {Y : Type v}
variable {W : Type u'} {Z : Type w'}

/-! ### The flat replay -/

/-- Flat replay of the two-converter stack.  State: `wsAct` the active outer
prefix, `wsRest` the undelivered outer inputs, `vs` the β-answers received
by α, `us` the U-queries delivered to β, `ysDone`/`ysRest` the consumed and
remaining base answers, and the mode (`false` = α to move, `true` = β to
move).  A pending base query with everything consumed is the composite's
query move; a final α-answer with everything consumed is its answer move;
mismatched consumption is a malformed pair (undefined). -/
def compGo (α : ProtocolFn W Z U V) (β : ProtocolFn U V X Y) :
    ℕ → List W → List W → List (Option V) → List U → List (Option Y) →
      List (Option Y) → Bool → Part (X ⊕ Z)
  | 0, _, _, _, _, _, _, _ => Part.none
  | fuel + 1, wsAct, wsRest, vs, us, ysDone, ysRest, false =>
      (α (wsAct, vs)).bind fun m =>
        match m with
        | Sum.inl u =>
            compGo α β fuel wsAct wsRest vs (us ++ [u]) ysDone ysRest true
        | Sum.inr z =>
            match wsRest, ysRest with
            | w :: rest, _ =>
                compGo α β fuel (wsAct ++ [w]) rest vs us ysDone ysRest false
            | [], [] => Part.some (Sum.inr z)
            | [], _ :: _ => Part.none
  | fuel + 1, wsAct, wsRest, vs, us, ysDone, ysRest, true =>
      (β (us, ysDone)).bind fun m =>
        match m with
        | Sum.inr v =>
            compGo α β fuel wsAct wsRest (vs ++ [some v]) us ysDone ysRest
              false
        | Sum.inl x =>
            match ysRest with
            | y :: rest =>
                compGo α β fuel wsAct wsRest vs us (ysDone ++ [y]) rest true
            | [] =>
                match wsRest with
                | [] => Part.some (Sum.inl x)
                | _ :: _ => Part.none

variable {α : ProtocolFn W Z U V} {β : ProtocolFn U V X Y}

/-! Membership constructors, one per transition, stated at variable fuel so
`simp` never recursively unfolds a successor-literal `compGo`. -/

theorem compGo_mem_query2 {wsAct wsRest : List W} {vs : List (Option V)}
    {us : List U} {ysDone ysRest : List (Option Y)} {u : U} {m : X ⊕ Z}
    {fuel : ℕ}
    (hm : Sum.inl u ∈ α (wsAct, vs))
    (h : m ∈ compGo α β fuel wsAct wsRest vs (us ++ [u]) ysDone ysRest true) :
    m ∈ compGo α β (fuel + 1) wsAct wsRest vs us ysDone ysRest false := by
  simp only [compGo, Part.mem_bind_iff]
  exact ⟨Sum.inl u, hm, h⟩

theorem compGo_mem_advance {wsAct : List W} {w : W} {wsRest : List W}
    {vs : List (Option V)} {us : List U} {ysDone ysRest : List (Option Y)}
    {z : Z} {m : X ⊕ Z}
    {fuel : ℕ} (hm : Sum.inr z ∈ α (wsAct, vs))
    (h : m ∈ compGo α β fuel (wsAct ++ [w]) wsRest vs us ysDone ysRest
      false) :
    m ∈ compGo α β (fuel + 1) wsAct (w :: wsRest) vs us ysDone ysRest
      false := by
  simp only [compGo, Part.mem_bind_iff]
  exact ⟨Sum.inr z, hm, h⟩

theorem compGo_mem_exit2 {wsAct : List W} {vs : List (Option V)}
    {us : List U} {ysDone : List (Option Y)} {z : Z} {fuel : ℕ}
    (hm : Sum.inr z ∈ α (wsAct, vs)) :
    Sum.inr z ∈ compGo α β (fuel + 1) wsAct [] vs us ysDone [] false := by
  simp only [compGo, Part.mem_bind_iff]
  exact ⟨Sum.inr z, hm, Part.mem_some_iff.mpr rfl⟩

theorem compGo_mem_answer1 {wsAct wsRest : List W} {vs : List (Option V)}
    {us : List U} {ysDone ysRest : List (Option Y)} {v : V} {m : X ⊕ Z}
    {fuel : ℕ}
    (hm : Sum.inr v ∈ β (us, ysDone))
    (h : m ∈ compGo α β fuel wsAct wsRest (vs ++ [some v]) us ysDone ysRest
      false) :
    m ∈ compGo α β (fuel + 1) wsAct wsRest vs us ysDone ysRest true := by
  simp only [compGo, Part.mem_bind_iff]
  exact ⟨Sum.inr v, hm, h⟩

theorem compGo_mem_consume {wsAct wsRest : List W} {vs : List (Option V)}
    {us : List U} {ysDone : List (Option Y)} {y : Option Y}
    {ysRest : List (Option Y)} {x : X} {m : X ⊕ Z} {fuel : ℕ}
    (hm : Sum.inl x ∈ β (us, ysDone))
    (h : m ∈ compGo α β fuel wsAct wsRest vs us (ysDone ++ [y]) ysRest
      true) :
    m ∈ compGo α β (fuel + 1) wsAct wsRest vs us ysDone (y :: ysRest)
      true := by
  simp only [compGo, Part.mem_bind_iff]
  exact ⟨Sum.inl x, hm, h⟩

theorem compGo_mem_exit1 {wsAct : List W} {vs : List (Option V)}
    {us : List U} {ysDone : List (Option Y)} {x : X} {fuel : ℕ}
    (hm : Sum.inl x ∈ β (us, ysDone)) :
    Sum.inl x ∈ compGo α β (fuel + 1) wsAct [] vs us ysDone [] true := by
  simp only [compGo, Part.mem_bind_iff]
  exact ⟨Sum.inl x, hm, Part.mem_some_iff.mpr rfl⟩

/-- Membership destructor, α-mode. -/
theorem compGo_elim2 {wsAct wsRest : List W} {vs : List (Option V)}
    {us : List U} {ysDone ysRest : List (Option Y)} {m : X ⊕ Z} {fuel : ℕ}
    (h : m ∈ compGo α β (fuel + 1) wsAct wsRest vs us ysDone ysRest false) :
    (∃ u, Sum.inl u ∈ α (wsAct, vs) ∧
      m ∈ compGo α β fuel wsAct wsRest vs (us ++ [u]) ysDone ysRest true) ∨
    (∃ z w rest, Sum.inr z ∈ α (wsAct, vs) ∧ wsRest = w :: rest ∧
      m ∈ compGo α β fuel (wsAct ++ [w]) rest vs us ysDone ysRest false) ∨
    (∃ z, Sum.inr z ∈ α (wsAct, vs) ∧ wsRest = [] ∧ ysRest = [] ∧
      m = Sum.inr z) := by
  simp only [compGo, Part.mem_bind_iff] at h
  obtain ⟨mv, hmv, h⟩ := h
  cases mv with
  | inl u => exact Or.inl ⟨u, hmv, h⟩
  | inr z =>
      cases wsRest with
      | cons w rest => exact Or.inr (Or.inl ⟨z, w, rest, hmv, rfl, h⟩)
      | nil =>
          cases ysRest with
          | nil =>
              simp only [Part.mem_some_iff] at h
              exact Or.inr (Or.inr ⟨z, hmv, rfl, rfl, h⟩)
          | cons y rest => simp at h

/-- Membership destructor, β-mode. -/
theorem compGo_elim1 {wsAct wsRest : List W} {vs : List (Option V)}
    {us : List U} {ysDone ysRest : List (Option Y)} {m : X ⊕ Z} {fuel : ℕ}
    (h : m ∈ compGo α β (fuel + 1) wsAct wsRest vs us ysDone ysRest true) :
    (∃ v, Sum.inr v ∈ β (us, ysDone) ∧
      m ∈ compGo α β fuel wsAct wsRest (vs ++ [some v]) us ysDone ysRest
        false) ∨
    (∃ x y rest, Sum.inl x ∈ β (us, ysDone) ∧ ysRest = y :: rest ∧
      m ∈ compGo α β fuel wsAct wsRest vs us (ysDone ++ [y]) rest true) ∨
    (∃ x, Sum.inl x ∈ β (us, ysDone) ∧ ysRest = [] ∧ wsRest = [] ∧
      m = Sum.inl x) := by
  simp only [compGo, Part.mem_bind_iff] at h
  obtain ⟨mv, hmv, h⟩ := h
  cases mv with
  | inr v => exact Or.inl ⟨v, hmv, h⟩
  | inl x =>
      cases ysRest with
      | cons y rest => exact Or.inr (Or.inl ⟨x, y, rest, hmv, rfl, h⟩)
      | nil =>
          cases wsRest with
          | nil =>
              simp only [Part.mem_some_iff] at h
              exact Or.inr (Or.inr ⟨x, hmv, rfl, rfl, h⟩)
          | cons w rest => simp at h

theorem compGo_mono :
    ∀ {fuel : ℕ} {wsAct wsRest : List W} {vs : List (Option V)} {us : List U}
      {ysDone ysRest : List (Option Y)} {mode : Bool} {m : X ⊕ Z},
      m ∈ compGo α β fuel wsAct wsRest vs us ysDone ysRest mode →
      m ∈ compGo α β (fuel + 1) wsAct wsRest vs us ysDone ysRest mode := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ m h; simp [compGo] at h
  | succ n ih =>
      intro wsAct wsRest vs us ysDone ysRest mode m h
      cases mode with
      | false =>
          rcases compGo_elim2 h with ⟨u, hm, h'⟩ |
            ⟨zz, w, rest, hm, heq, h'⟩ | ⟨zz, hm, heq1, heq2, heq3⟩
          · exact compGo_mem_query2 hm (ih h')
          · subst heq
            exact compGo_mem_advance hm (ih h')
          · subst heq1
            subst heq2
            subst heq3
            exact compGo_mem_exit2 hm
      | true =>
          rcases compGo_elim1 h with ⟨v, hm, h'⟩ |
            ⟨x, y, rest, hm, heq, h'⟩ | ⟨x, hm, heq1, heq2, heq3⟩
          · exact compGo_mem_answer1 hm (ih h')
          · subst heq
            exact compGo_mem_consume hm (ih h')
          · subst heq1
            subst heq2
            subst heq3
            exact compGo_mem_exit1 hm

theorem compGo_mono_le {fuel fuel' : ℕ} {wsAct wsRest : List W}
    {vs : List (Option V)} {us : List U} {ysDone ysRest : List (Option Y)}
    {mode : Bool} {m : X ⊕ Z}
    (hle : fuel ≤ fuel')
    (h : m ∈ compGo α β fuel wsAct wsRest vs us ysDone ysRest mode) :
    m ∈ compGo α β fuel' wsAct wsRest vs us ysDone ysRest mode := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  clear hle
  induction k with
  | zero => simpa using h
  | succ n ih =>
      have he : fuel + (n + 1) = (fuel + n) + 1 := by ring
      rw [he]
      exact compGo_mono ih

/-! ### The serial composite -/

/-- Per-fuel composite move. -/
def compAt (α : ProtocolFn W Z U V) (β : ProtocolFn U V X Y) (fuel : ℕ) :
    ProtocolFn W Z X Y := fun p =>
  match p.1 with
  | [] => Part.none
  | w :: wsRest => compGo α β fuel [w] wsRest [] [] [] p.2 false

/-- **Serial composition**: the composite's move at a pair is the eventual
value of the flat replay of the two-converter stack. -/
noncomputable def comp (α : ProtocolFn W Z U V) (β : ProtocolFn U V X Y) :
    ProtocolFn W Z X Y := fun p =>
  Part.eventual fun fuel => compAt α β fuel p

theorem compAt_mono_le {fuel fuel' : ℕ} {p : List W × List (Option Y)}
    {m : X ⊕ Z}
    (hle : fuel ≤ fuel') (h : m ∈ compAt α β fuel p) :
    m ∈ compAt α β fuel' p := by
  obtain ⟨ws, ys⟩ := p
  cases ws with
  | nil => simp [compAt] at h
  | cons w wsRest =>
      simp only [compAt] at h ⊢
      exact compGo_mono_le hle h

theorem mem_comp {p : List W × List (Option Y)} {m : X ⊕ Z} :
    m ∈ comp α β p ↔ ∃ fuel, m ∈ compAt α β fuel p :=
  Part.mem_eventual
    (hmono := fun hle hw => compAt_mono_le hle hw)

theorem mem_comp_cons {w : W} {wsRest : List W} {ys : List (Option Y)}
    {m : X ⊕ Z} :
    m ∈ comp α β (w :: wsRest, ys) ↔
      ∃ fuel, m ∈ compGo α β fuel [w] wsRest [] [] [] ys false := by
  rw [mem_comp]
  rfl

/-- `comp` is nowhere defined at the empty outer history; a raw
`ProtocolFn` can be. -/
theorem comp_apply_nil (α : ProtocolFn W Z U V) (β : ProtocolFn U V X Y)
    (ys : List (Option Y)) : comp α β ([], ys) = Part.none := by
  rw [Part.eq_none_iff]
  intro m hm
  rw [mem_comp] at hm
  obtain ⟨fuel, hf⟩ := hm
  simp [compAt] at hf

/-! ### Gate congruence

Two inner converters that agree at every pair the outer converter's
*gate* can reach compose identically: the flat replay consults the inner
converter only at states whose invariant `Pβ` the outer moves maintain,
so replacing it by an agreeing one is invisible.  The invariants speak
only of the consulted components (`wsAct`, `vs`, `us`, `ysDone`) — the
undelivered outer inputs and unconsumed base answers stay arbitrary. -/

section GateCongruence

variable {β' : ProtocolFn U V X Y}
variable {Pα Pβ : List W → List (Option V) → List U → List (Option Y) → Prop}

/-- Flat-replay congruence under a gate: if `Pα`/`Pβ` are maintained by
every transition and `β`, `β'` agree at `Pβ`-states, the two replays have
the same members at the same fuel. -/
theorem compGo_congr_right_of_gate
    (hagree : ∀ wsAct vs us ysDone, Pβ wsAct vs us ysDone →
      β (us, ysDone) = β' (us, ysDone))
    (hquery : ∀ wsAct vs us ysDone (u : U), Pα wsAct vs us ysDone →
      Sum.inl u ∈ α (wsAct, vs) → Pβ wsAct vs (us ++ [u]) ysDone)
    (hadvance : ∀ wsAct vs us ysDone (z : Z), Pα wsAct vs us ysDone →
      Sum.inr z ∈ α (wsAct, vs) → ∀ w : W, Pα (wsAct ++ [w]) vs us ysDone)
    (hanswer : ∀ wsAct vs us ysDone (v : V), Pβ wsAct vs us ysDone →
      Sum.inr v ∈ β (us, ysDone) → Pα wsAct (vs ++ [some v]) us ysDone)
    (hconsume : ∀ wsAct vs us ysDone (x : X), Pβ wsAct vs us ysDone →
      Sum.inl x ∈ β (us, ysDone) → ∀ y : Option Y,
        Pβ wsAct vs us (ysDone ++ [y])) :
    ∀ (fuel : ℕ) (wsAct wsRest : List W) (vs : List (Option V))
      (us : List U) (ysDone ysRest : List (Option Y)) (mode : Bool)
      (m : X ⊕ Z),
      (mode = false → Pα wsAct vs us ysDone) →
      (mode = true → Pβ wsAct vs us ysDone) →
      (m ∈ compGo α β fuel wsAct wsRest vs us ysDone ysRest mode ↔
        m ∈ compGo α β' fuel wsAct wsRest vs us ysDone ysRest mode) := by
  intro fuel
  induction fuel with
  | zero =>
      intro wsAct wsRest vs us ysDone ysRest mode m _ _
      simp [compGo]
  | succ f ih =>
      intro wsAct wsRest vs us ysDone ysRest mode m hPα hPβ
      cases mode with
      | false =>
          have hP := hPα rfl
          constructor
          · intro h
            rcases compGo_elim2 h with
              ⟨u, hmα, h'⟩ | ⟨z, w, rest, hmα, hwr, h'⟩ |
              ⟨z, hmα, hwr, hyr, hmv⟩
            · exact compGo_mem_query2 hmα
                ((ih wsAct wsRest vs (us ++ [u]) ysDone ysRest true m
                  (fun hc => Bool.noConfusion hc)
                  (fun _ => hquery _ _ _ _ _ hP hmα)).mp h')
            · subst hwr
              exact compGo_mem_advance hmα
                ((ih (wsAct ++ [w]) rest vs us ysDone ysRest false m
                  (fun _ => hadvance _ _ _ _ _ hP hmα w)
                  (fun hc => Bool.noConfusion hc)).mp h')
            · subst hwr
              subst hyr
              subst hmv
              exact compGo_mem_exit2 hmα
          · intro h
            rcases compGo_elim2 h with
              ⟨u, hmα, h'⟩ | ⟨z, w, rest, hmα, hwr, h'⟩ |
              ⟨z, hmα, hwr, hyr, hmv⟩
            · exact compGo_mem_query2 hmα
                ((ih wsAct wsRest vs (us ++ [u]) ysDone ysRest true m
                  (fun hc => Bool.noConfusion hc)
                  (fun _ => hquery _ _ _ _ _ hP hmα)).mpr h')
            · subst hwr
              exact compGo_mem_advance hmα
                ((ih (wsAct ++ [w]) rest vs us ysDone ysRest false m
                  (fun _ => hadvance _ _ _ _ _ hP hmα w)
                  (fun hc => Bool.noConfusion hc)).mpr h')
            · subst hwr
              subst hyr
              subst hmv
              exact compGo_mem_exit2 hmα
      | true =>
          have hP := hPβ rfl
          have heq := hagree _ _ _ _ hP
          constructor
          · intro h
            rcases compGo_elim1 h with
              ⟨v, hmβ, h'⟩ | ⟨x, y, rest, hmβ, hyr, h'⟩ |
              ⟨x, hmβ, hyr, hwr, hmv⟩
            · have hmβ' : Sum.inr v ∈ β' (us, ysDone) := by
                rw [← heq]
                exact hmβ
              exact compGo_mem_answer1 hmβ'
                ((ih wsAct wsRest (vs ++ [some v]) us ysDone ysRest false m
                  (fun _ => hanswer _ _ _ _ _ hP hmβ)
                  (fun hc => Bool.noConfusion hc)).mp h')
            · have hmβ' : Sum.inl x ∈ β' (us, ysDone) := by
                rw [← heq]
                exact hmβ
              subst hyr
              exact compGo_mem_consume hmβ'
                ((ih wsAct wsRest vs us (ysDone ++ [y]) rest true m
                  (fun hc => Bool.noConfusion hc)
                  (fun _ => hconsume _ _ _ _ _ hP hmβ y)).mp h')
            · have hmβ' : Sum.inl x ∈ β' (us, ysDone) := by
                rw [← heq]
                exact hmβ
              subst hyr
              subst hwr
              subst hmv
              exact compGo_mem_exit1 hmβ'
          · intro h
            rcases compGo_elim1 h with
              ⟨v, hmβ, h'⟩ | ⟨x, y, rest, hmβ, hyr, h'⟩ |
              ⟨x, hmβ, hyr, hwr, hmv⟩
            · have hmβ0 : Sum.inr v ∈ β (us, ysDone) := by
                rw [heq]
                exact hmβ
              exact compGo_mem_answer1 hmβ0
                ((ih wsAct wsRest (vs ++ [some v]) us ysDone ysRest false m
                  (fun _ => hanswer _ _ _ _ _ hP hmβ0)
                  (fun hc => Bool.noConfusion hc)).mpr h')
            · have hmβ0 : Sum.inl x ∈ β (us, ysDone) := by
                rw [heq]
                exact hmβ
              subst hyr
              exact compGo_mem_consume hmβ0
                ((ih wsAct wsRest vs us (ysDone ++ [y]) rest true m
                  (fun hc => Bool.noConfusion hc)
                  (fun _ => hconsume _ _ _ _ _ hP hmβ0 y)).mpr h')
            · have hmβ0 : Sum.inl x ∈ β (us, ysDone) := by
                rw [heq]
                exact hmβ
              subst hyr
              subst hwr
              subst hmv
              exact compGo_mem_exit1 hmβ0

/-- **Gate congruence for serial composition**: two inner converters that
agree at every `Pβ`-state compose identically under an outer converter
whose moves maintain the gate invariants from the initial state. -/
theorem comp_congr_right_of_gate
    (hagree : ∀ wsAct vs us ysDone, Pβ wsAct vs us ysDone →
      β (us, ysDone) = β' (us, ysDone))
    (hquery : ∀ wsAct vs us ysDone (u : U), Pα wsAct vs us ysDone →
      Sum.inl u ∈ α (wsAct, vs) → Pβ wsAct vs (us ++ [u]) ysDone)
    (hadvance : ∀ wsAct vs us ysDone (z : Z), Pα wsAct vs us ysDone →
      Sum.inr z ∈ α (wsAct, vs) → ∀ w : W, Pα (wsAct ++ [w]) vs us ysDone)
    (hanswer : ∀ wsAct vs us ysDone (v : V), Pβ wsAct vs us ysDone →
      Sum.inr v ∈ β (us, ysDone) → Pα wsAct (vs ++ [some v]) us ysDone)
    (hconsume : ∀ wsAct vs us ysDone (x : X), Pβ wsAct vs us ysDone →
      Sum.inl x ∈ β (us, ysDone) → ∀ y : Option Y,
        Pβ wsAct vs us (ysDone ++ [y]))
    (hinit : ∀ w : W, Pα [w] [] [] []) :
    comp α β = comp α β' := by
  funext p
  obtain ⟨ws, ys⟩ := p
  apply Part.ext
  intro m
  rcases ws with _ | ⟨w, wsT⟩
  · rw [mem_comp, mem_comp]
    simp [compAt]
  · rw [mem_comp_cons, mem_comp_cons]
    exact exists_congr fun fuel =>
      compGo_congr_right_of_gate hagree hquery hadvance hanswer hconsume
        fuel [w] wsT [] [] [] ys false m (fun _ => hinit w)
        (fun hc => Bool.noConfusion hc)

end GateCongruence

/-! ### The joint run

`CompRun wsAct zs vs us xs ys mode`: the canonical three-level interaction —
`wsAct`/`zs` the outer transcript (active prefix, completed outputs),
`us`/`vs` the middle transcript, `xs`/`ys` the base transcript, `mode` whose
turn it is.  The base answers are the computed `S⊥` outputs, so a `CompRun`
state is simultaneously a flat-replay state and a nested-application
state. -/

section ActionLaw

variable (α : ProtocolFn W Z U V) (β : ProtocolFn U V X Y)
  (S : System.DDS X Y)

inductive CompRun :
    List W → List Z → List (Option V) → List U → List X → List (Option Y) →
      Bool → Prop
  | start (w : W) : CompRun [w] [] [] [] [] [] false
  | query2 {wsAct zs vs us xs ys u} (hr : CompRun wsAct zs vs us xs ys false)
      (hd : Sum.inl u ∈ α (wsAct, vs)) :
      CompRun wsAct zs vs (us ++ [u]) xs ys true
  | answer2 {wsAct zs vs us xs ys z} (w : W)
      (hr : CompRun wsAct zs vs us xs ys false)
      (hd : Sum.inr z ∈ α (wsAct, vs)) :
      CompRun (wsAct ++ [w]) (zs ++ [z]) vs us xs ys false
  | query1 {wsAct zs vs us xs ys x}
      (hr : CompRun wsAct zs vs us xs ys true)
      (hx : Sum.inl x ∈ β (us, ys)) :
      CompRun wsAct zs vs us (xs ++ [x])
        (ys ++ [System.output (S⊥) (xs ++ [x])
          (by rw [System.dom_fullyDefined]; simp)]) true
  | answer1 {wsAct zs vs us xs ys v}
      (hr : CompRun wsAct zs vs us xs ys true)
      (hv : Sum.inr v ∈ β (us, ys)) :
      CompRun wsAct zs (vs ++ [some v]) us xs ys false

variable {α β S}

theorem compRun_ne_nil {wsAct zs vs us xs ys mode}
    (h : CompRun α β S wsAct zs vs us xs ys mode) : wsAct ≠ [] := by
  induction h with
  | start w => simp
  | query2 hr hd ih => exact ih
  | answer2 w hr hd ih => simp
  | query1 hr hx ih => exact ih
  | answer1 hr hv ih => exact ih

/-- **Replay**: a flat run from a reachable joint state embeds into a flat
run from the initial state over the recorded streams. -/
theorem compGo_replay :
    ∀ {wsAct zs vs us xs ys mode},
      CompRun α β S wsAct zs vs us xs ys mode →
      ∀ {fuel : ℕ} {wsRest : List W} {ysRest : List (Option Y)} {m : X ⊕ Z},
      m ∈ compGo α β fuel wsAct wsRest vs us ys ysRest mode →
      ∀ {w₁ : W} {wsTail : List W}, wsAct = w₁ :: wsTail →
      ∃ fuel', m ∈ compGo α β fuel' [w₁] (wsTail ++ wsRest) [] [] []
        (ys ++ ysRest) false := by
  intro wsAct zs vs us xs ys mode h
  induction h with
  | start w =>
      intro fuel wsRest ysRest m hm w₁ wsTail heq
      have h1 : w = w₁ := (List.cons.inj heq).1
      have h2 : ([] : List W) = wsTail := (List.cons.inj heq).2
      subst h1
      subst h2
      exact ⟨fuel, hm⟩
  | query2 hr hd ih =>
      intro fuel wsRest ysRest m hm w₁ wsTail heq
      exact ih (compGo_mem_query2 hd hm) heq
  | answer2 w hr hd ih =>
      rename_i wsAct' zs' vs' us' xs' ys' z
      intro fuel wsRest ysRest m hm w₁ wsTail heq
      have hne := compRun_ne_nil hr
      obtain ⟨a, t, rfl⟩ : ∃ a t, wsAct' = a :: t := by
        cases wsAct' with
        | nil => exact absurd rfl hne
        | cons a t => exact ⟨a, t, rfl⟩
      have h1 : a = w₁ := by
        have := heq
        simp only [List.cons_append] at this
        exact (List.cons.inj this).1
      have h2 : wsTail = t ++ [w] := by
        have := heq
        simp only [List.cons_append] at this
        exact ((List.cons.inj this).2).symm
      subst h1
      subst h2
      obtain ⟨fuel', hf⟩ := ih (compGo_mem_advance hd hm) rfl
      refine ⟨fuel', ?_⟩
      simpa using hf
  | query1 hr hx ih =>
      intro fuel wsRest ysRest m hm w₁ wsTail heq
      obtain ⟨fuel', hf⟩ := ih (compGo_mem_consume hx hm) heq
      refine ⟨fuel', ?_⟩
      simpa using hf
  | answer1 hr hv ih =>
      intro fuel wsRest ysRest m hm w₁ wsTail heq
      exact ih (compGo_mem_answer1 hv hm) heq

/-- **Reverse replay**: an initial-state flat run factors through any
reachable joint state over the recorded streams — the stack deterministically
re-traces its own history. -/
theorem compGo_replay_rev :
    ∀ {wsAct zs vs us xs ys mode},
      CompRun α β S wsAct zs vs us xs ys mode →
      ∀ {fuel : ℕ} {wsRest : List W} {ysRest : List (Option Y)} {m : X ⊕ Z}
        {w₁ : W} {wsTail : List W}, wsAct = w₁ :: wsTail →
      m ∈ compGo α β fuel [w₁] (wsTail ++ wsRest) [] [] []
        (ys ++ ysRest) false →
      ∃ fuel', m ∈ compGo α β fuel' wsAct wsRest vs us ys ysRest mode := by
  intro wsAct zs vs us xs ys mode h
  induction h with
  | start w =>
      intro fuel wsRest ysRest m w₁ wsTail heq hm
      have h1 : w = w₁ := (List.cons.inj heq).1
      have h2 : ([] : List W) = wsTail := (List.cons.inj heq).2
      subst h1
      subst h2
      exact ⟨fuel, hm⟩
  | query2 hr hd ih =>
      intro fuel wsRest ysRest m w₁ wsTail heq hm
      obtain ⟨k, hk⟩ := ih heq hm
      rcases k with _ | k'
      · simp [compGo] at hk
      · rcases compGo_elim2 hk with ⟨u', hm', h'⟩ |
          ⟨z', w', rest', hm', heqw, h'⟩ | ⟨z', hm', heq1, heq2, heq3⟩
        · have := Sum.inl.inj (Part.mem_unique hm' hd)
          subst this
          exact ⟨k', h'⟩
        · exact absurd (Part.mem_unique hm' hd) (by simp)
        · exact absurd (Part.mem_unique hm' hd) (by simp)
  | answer2 w hr hd ih =>
      rename_i wsAct' zs' vs' us' xs' ys' z
      intro fuel wsRest ysRest m w₁ wsTail heq hm
      have hne := compRun_ne_nil hr
      obtain ⟨a, t, rfl⟩ : ∃ a t, wsAct' = a :: t := by
        cases wsAct' with
        | nil => exact absurd rfl hne
        | cons a t => exact ⟨a, t, rfl⟩
      have h1 : a = w₁ := by
        have := heq
        simp only [List.cons_append] at this
        exact (List.cons.inj this).1
      have h2 : wsTail = t ++ [w] := by
        have := heq
        simp only [List.cons_append] at this
        exact ((List.cons.inj this).2).symm
      subst h1
      subst h2
      have hm' : m ∈ compGo α β fuel [a] (t ++ (w :: wsRest)) [] [] []
          (ys' ++ ysRest) false := by
        simpa using hm
      obtain ⟨k, hk⟩ := ih rfl hm'
      rcases k with _ | k'
      · simp [compGo] at hk
      · rcases compGo_elim2 hk with ⟨u', hmv, h'⟩ |
          ⟨z', w', rest', hmv, heqw, h'⟩ | ⟨z', hmv, heq1, heq2, heq3⟩
        · exact absurd (Part.mem_unique hmv hd) (by simp)
        · have hw : w = w' := (List.cons.inj heqw).1
          have hrest : wsRest = rest' := (List.cons.inj heqw).2
          subst hw
          subst hrest
          exact ⟨k', h'⟩
        · exact absurd heq1 (by simp)
  | query1 hr hx ih =>
      rename_i wsAct' zs' vs' us' xs' ys' x
      intro fuel wsRest ysRest m w₁ wsTail heq hm
      have hm' : m ∈ compGo α β fuel [w₁] (wsTail ++ wsRest) [] [] []
          (ys' ++ (System.output (S⊥) (xs' ++ [x])
            (by rw [System.dom_fullyDefined]; simp) :: ysRest)) false := by
        simpa using hm
      obtain ⟨k, hk⟩ := ih heq hm'
      rcases k with _ | k'
      · simp [compGo] at hk
      · rcases compGo_elim1 hk with ⟨v', hmv, h'⟩ |
          ⟨x', y', rest', hmv, heqy, h'⟩ | ⟨x', hmv, heq1, heq2, heq3⟩
        · exact absurd (Part.mem_unique hmv hx) (by simp)
        · have hyy : System.output (S⊥) (xs' ++ [x])
              (by rw [System.dom_fullyDefined]; simp) = y' :=
            (List.cons.inj heqy).1
          have hrest : ysRest = rest' := (List.cons.inj heqy).2
          have hxx : x' = x := Sum.inl.inj (Part.mem_unique hmv hx)
          subst hxx
          subst hyy
          subst hrest
          exact ⟨k', h'⟩
        · exact absurd heq1 (by simp)
  | answer1 hr hv ih =>
      intro fuel wsRest ysRest m w₁ wsTail heq hm
      obtain ⟨k, hk⟩ := ih heq hm
      rcases k with _ | k'
      · simp [compGo] at hk
      · rcases compGo_elim1 hk with ⟨v', hmv, h'⟩ |
          ⟨x', y', rest', hmv, heqy, h'⟩ | ⟨x', hmv, heq1, heq2, heq3⟩
        · have := Sum.inr.inj (Part.mem_unique hmv hv)
          subst this
          exact ⟨k', h'⟩
        · exact absurd (Part.mem_unique hmv hv) (by simp)
        · exact absurd (Part.mem_unique hmv hv) (by simp)

/-- **Extraction**: a flat run from a reachable state with nothing left to
consume lands, after internal steps, at a pending base query or a final
outer answer. -/
theorem compGo_extract :
    ∀ {fuel : ℕ} {wsAct zs vs us xs ys mode} {m : X ⊕ Z},
      CompRun α β S wsAct zs vs us xs ys mode →
      m ∈ compGo α β fuel wsAct [] vs us ys [] mode →
      (∃ vs' us' x, CompRun α β S wsAct zs vs' us' xs ys true ∧
        Sum.inl x ∈ β (us', ys) ∧ m = Sum.inl x) ∨
      (∃ vs' us' z, CompRun α β S wsAct zs vs' us' xs ys false ∧
        Sum.inr z ∈ α (wsAct, vs') ∧ m = Sum.inr z) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ m hr hm; simp [compGo] at hm
  | succ n ih =>
      intro wsAct zs vs us xs ys mode m hr hm
      cases mode with
      | false =>
          rcases compGo_elim2 hm with ⟨u, hmv, h'⟩ |
            ⟨z', w', rest', hmv, heqw, h'⟩ | ⟨z', hmv, heq1, heq2, heq3⟩
          · exact ih (CompRun.query2 hr hmv) h'
          · exact absurd heqw (by simp)
          · subst heq3
            exact Or.inr ⟨vs, us, z', hr, hmv, rfl⟩
      | true =>
          rcases compGo_elim1 hm with ⟨v, hmv, h'⟩ |
            ⟨x', y', rest', hmv, heqy, h'⟩ | ⟨x', hmv, heq1, heq2, heq3⟩
          · exact ih (CompRun.answer1 hr hmv) h'
          · exact absurd heqy (by simp)
          · subst heq3
            exact Or.inl ⟨vs, us, x', hr, hmv, rfl⟩

theorem append_singleton_inj {α : Type*} {l₁ l₂ : List α} {a b : α}
    (h : l₁ ++ [a] = l₂ ++ [b]) : l₁ = l₂ ∧ a = b := by
  have h1 : l₁ = l₂ := by
    have := congrArg List.dropLast h
    simpa using this
  subst h1
  have h2 : a = b := by
    have := congrArg (fun l => List.getLast? l) h
    simpa using this
  exact ⟨rfl, h2⟩

/-- **Middle certification**: the middle transcript of a joint state comes
from a genuine `apply β S` computation — a completed `driveOuter` run at
α-turn states, plus an open-round `drive` continuation at β-turn
states. -/
theorem compRun_middle :
    ∀ {wsAct zs vs us xs ys mode},
      CompRun α β S wsAct zs vs us xs ys mode →
      (mode = false → ∃ vsP : List V, vs = List.map some vsP ∧
        ∃ fuel, (vsP, xs, ys) ∈ driveOuter β S fuel [] [] [] us) ∧
      (mode = true → ∃ us₀ u xs₀ ys₀ vsP, us = us₀ ++ [u] ∧
        vs = List.map (some : V → Option V) vsP ∧
        (∃ fuel, (vsP, xs₀, ys₀) ∈ driveOuter β S fuel [] [] [] us₀) ∧
        ∀ {fuel : ℕ} {m : V × List X × List (Option Y)},
          m ∈ drive β S fuel us xs ys →
          ∃ fuel', m ∈ drive β S fuel' us xs₀ ys₀) := by
  intro wsAct zs vs us xs ys mode h
  induction h with
  | start w =>
      refine ⟨fun _ => ⟨[], rfl, 0, ?_⟩, fun hm => absurd hm (by simp)⟩
      simp [driveOuter]
  | query2 hr hd ih =>
      rename_i wsAct' zs' vs' us' xs' ys' u
      refine ⟨fun hm => absurd hm (by simp), fun _ => ?_⟩
      obtain ⟨vsP, hvsP, hfuel⟩ := ih.1 rfl
      exact ⟨us', u, xs', ys', vsP, rfl, hvsP, hfuel, fun hm => ⟨_, hm⟩⟩
  | answer2 w hr hd ih => exact ih
  | query1 hr hx ih =>
      rename_i wsAct' zs' vs' us' xs' ys' x
      refine ⟨fun hm => absurd hm (by simp), fun _ => ?_⟩
      obtain ⟨us₀, u, xs₀, ys₀, vsP, heq, hvsP, hrun, hcont⟩ := ih.2 rfl
      refine ⟨us₀, u, xs₀, ys₀, vsP, heq, hvsP, hrun, ?_⟩
      intro fuel m hm
      exact hcont (drive_mem_query β S hx hm)
  | answer1 hr hv ih =>
      rename_i wsAct' zs' vs' us' xs' ys' v
      refine ⟨fun _ => ?_, fun hm => absurd hm (by simp)⟩
      obtain ⟨us₀, u, xs₀, ys₀, vsP, heq, hvsP, ⟨fuel₁, hrun⟩, hcont⟩ :=
        ih.2 rfl
      have hstep : (v, xs', ys') ∈ drive β S 1 us' xs' ys' :=
        drive_mem_answer β S hv 0
      obtain ⟨fuel₂, hstep'⟩ := hcont hstep
      refine ⟨vsP ++ [v], by rw [hvsP]; simp, max fuel₁ fuel₂, ?_⟩
      subst heq
      rw [driveOuter_append β S _ us₀ [u]]
      rw [Part.mem_bind_iff]
      refine ⟨(vsP, xs₀, ys₀),
        driveOuter_mono_le β S (le_max_left _ _) hrun, ?_⟩
      rw [Part.mem_map_iff]
      refine ⟨([v], xs', ys'), ?_, rfl⟩
      show _ ∈ (drive β S _ (us₀ ++ [u]) xs₀ ys₀).bind _
      rw [Part.mem_bind_iff]
      refine ⟨(v, xs', ys'),
        drive_mono_le β S (le_max_right _ _) hstep', ?_⟩
      simp [driveOuter]

/-- The middle system answers an open round: pending β-answer at a β-turn
state is a genuine `apply β S` value. -/
theorem compRun_middle_value {wsAct zs vs us xs ys u v}
    (hr : CompRun α β S wsAct zs vs (us ++ [u]) xs ys true)
    (hv : Sum.inr v ∈ β (us ++ [u], ys)) :
    v ∈ applyRaw β S (us ++ [u]) := by
  obtain ⟨us₀, u', xs₀, ys₀, vsP, heq, hvsP, ⟨fuel₁, hrun⟩, hcont⟩ :=
    (compRun_middle hr).2 rfl
  obtain ⟨rfl, rfl⟩ := append_singleton_inj heq
  have hstep : (v, xs, ys) ∈ drive β S 1 (us ++ [u]) xs ys :=
    drive_mem_answer β S hv 0
  obtain ⟨fuel₂, hstep'⟩ := hcont hstep
  rw [mem_applyRaw]
  refine ⟨max fuel₁ fuel₂, ?_⟩
  rw [mem_applyRawAt_iff]
  refine ⟨(vsP ++ [v], xs, ys), ?_, by simp⟩
  rw [driveOuter_append β S _ us [u]]
  rw [Part.mem_bind_iff]
  refine ⟨(vsP, xs₀, ys₀),
    driveOuter_mono_le β S (le_max_left _ _) hrun, ?_⟩
  rw [Part.mem_map_iff]
  refine ⟨([v], xs, ys), ?_, rfl⟩
  show _ ∈ (drive β S _ (us ++ [u]) xs₀ ys₀).bind _
  rw [Part.mem_bind_iff]
  refine ⟨(v, xs, ys),
    drive_mono_le β S (le_max_right _ _) hstep', ?_⟩
  simp [driveOuter]

/-- **Outer certification**: every joint state carries a `driveOuter` run
of α against the middle system over the completed outer rounds, plus a
`drive` continuation from the current round position back to the round
anchor. -/
theorem compRun_outer :
    ∀ {wsAct zs vs us xs ys mode},
      CompRun α β S wsAct zs vs us xs ys mode →
      ∃ usR vsR,
        (∃ wsPre w, wsAct = wsPre ++ [w] ∧
          ∃ fuel, (zs, usR, vsR) ∈
            driveOuter α (apply β S) fuel [] [] [] wsPre) ∧
        (mode = false →
          ∀ {fuel : ℕ} {m : Z × List U × List (Option V)},
            m ∈ drive α (apply β S) fuel wsAct us vs →
            ∃ fuel', m ∈ drive α (apply β S) fuel' wsAct usR vsR) ∧
        (mode = true → ∃ usP uO, us = usP ++ [uO] ∧
          Sum.inl uO ∈ α (wsAct, vs) ∧
          ∀ {fuel : ℕ} {m : Z × List U × List (Option V)},
            m ∈ drive α (apply β S) fuel wsAct usP vs →
            ∃ fuel', m ∈ drive α (apply β S) fuel' wsAct usR vsR) := by
  intro wsAct zs vs us xs ys mode h
  induction h with
  | start w =>
      refine ⟨[], [], ⟨[], w, rfl, 0, by simp [driveOuter]⟩,
        fun _ => fun hm => ⟨_, hm⟩, fun hm => absurd hm (by simp)⟩
  | query2 hr hd ih =>
      rename_i wsAct' zs' vs' us' xs' ys' u
      obtain ⟨usR, vsR, hanch, hcf, hct⟩ := ih
      exact ⟨usR, vsR, hanch, fun hm => absurd hm (by simp),
        fun _ => ⟨us', u, rfl, hd, fun hm => hcf rfl hm⟩⟩
  | answer2 w hr hd ih =>
      rename_i wsAct' zs' vs' us' xs' ys' z
      obtain ⟨usR, vsR, ⟨wsPre, wLast, heqw, fuel₁, hanch⟩, hcf, hct⟩ := ih
      have hstep : (z, us', vs') ∈
          drive α (apply β S) 1 wsAct' us' vs' :=
        drive_mem_answer α (apply β S) hd 0
      obtain ⟨fuel₂, hstep'⟩ := hcf rfl hstep
      refine ⟨us', vs', ⟨wsAct', w, rfl, max fuel₁ fuel₂, ?_⟩,
        fun _ => fun hm => ⟨_, hm⟩, fun hm => absurd hm (by simp)⟩
      subst heqw
      rw [driveOuter_append α (apply β S) _ wsPre [wLast]]
      rw [Part.mem_bind_iff]
      refine ⟨(zs', usR, vsR),
        driveOuter_mono_le α (apply β S) (le_max_left _ _) hanch, ?_⟩
      rw [Part.mem_map_iff]
      refine ⟨([z], us', vs'), ?_, rfl⟩
      show _ ∈ (drive α (apply β S) _ (wsPre ++ [wLast]) usR vsR).bind _
      rw [Part.mem_bind_iff]
      refine ⟨(z, us', vs'),
        drive_mono_le α (apply β S) (le_max_right _ _) hstep', ?_⟩
      simp [driveOuter]
  | query1 hr hx ih =>
      obtain ⟨usR, vsR, hanch, hcf, hct⟩ := ih
      obtain ⟨usP, uO, heq, hdO, hcont⟩ := hct rfl
      exact ⟨usR, vsR, hanch, fun hm => absurd hm (by simp),
        fun _ => ⟨usP, uO, heq, hdO, fun hm => hcont hm⟩⟩
  | answer1 hr hv ih =>
      rename_i wsAct' zs' vs' us' xs' ys' v
      obtain ⟨usR, vsR, hanch, hcf, hct⟩ := ih
      obtain ⟨usP, uO, heq, hdO, hcont⟩ := hct rfl
      refine ⟨usR, vsR, hanch, fun _ => ?_, fun hm => absurd hm (by simp)⟩
      intro fuel m hm
      subst heq
      have hvM : v ∈ applyRaw β S (usP ++ [uO]) :=
        compRun_middle_value hr hv
      have hdom : usP ++ [uO] ∈ System.dom (apply β S) :=
        Part.dom_iff_mem.mpr ⟨v, hvM⟩
      have hprev : usP ∈ System.dom (apply β S) ∨ usP = [] := by
        rcases eq_or_ne usP [] with h | h
        · exact Or.inr h
        · exact Or.inl (System.prefix_closed (apply β S) ⟨[uO], rfl⟩ h hdom)
      have hout : System.output ((apply β S)⊥) (usP ++ [uO])
          (by rw [System.dom_fullyDefined]; simp) = some v := by
        rw [System.output_fullyDefined_append_of_mem (apply β S) usP uO
          hprev hdom]
        exact congrArg some (Part.mem_unique (Part.get_mem hdom) hvM)
      have hm' : m ∈ drive α (apply β S) fuel wsAct' (usP ++ [uO])
          (vs' ++ [System.output ((apply β S)⊥) (usP ++ [uO])
            (by rw [System.dom_fullyDefined]; simp)]) := by
        rw [hout]
        exact hm
      exact hcont (drive_mem_query α (apply β S) hdO hm')

/-- One LHS round simulated: a `drive` run of the composite against `S`
lands the joint machine at a round-ending state. -/
theorem lhs_drive_sim :
    ∀ {fuel : ℕ} {wsAct : List W} {xs : List X} {ys : List (Option Y)}
      {r : Z × List X × List (Option Y)},
      r ∈ drive (comp α β) S fuel wsAct xs ys →
      ∀ {zs vs us mode}, CompRun α β S wsAct zs vs us xs ys mode →
      ∃ vs' us', CompRun α β S wsAct zs vs' us' r.2.1 r.2.2 false ∧
        Sum.inr r.1 ∈ α (wsAct, vs') := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ r hm; simp [drive] at hm
  | succ n ih =>
      intro wsAct xs ys r hm zs vs us mode hr
      have hne := compRun_ne_nil hr
      obtain ⟨w₁, wsTail, rfl⟩ : ∃ a t, wsAct = a :: t := by
        cases wsAct with
        | nil => exact absurd rfl hne
        | cons a t => exact ⟨a, t, rfl⟩
      rcases drive_succ_elim hm with ⟨x, hmc, hrec⟩ | ⟨z, hmc, rfl⟩
      · -- composite query: replay to the machine, extract the pending query
        rw [mem_comp_cons] at hmc
        obtain ⟨f, hgo⟩ := hmc
        have hgo' : Sum.inl x ∈ compGo α β f [w₁] (wsTail ++ [])
            [] [] [] (ys ++ []) false := by simpa using hgo
        obtain ⟨f', hst⟩ := compGo_replay_rev hr rfl hgo'
        rcases compGo_extract hr hst with
          ⟨vsq, usq, x', hrq, hx', hxx⟩ | ⟨vsq, usq, z', hrq, hz', hbad⟩
        · have : x' = x := Sum.inl.inj hxx.symm
          subst this
          exact ih hrec (CompRun.query1 hrq hx')
        · exact absurd hbad (by simp)
      · -- composite answer: the round ends here
        rw [mem_comp_cons] at hmc
        obtain ⟨f, hgo⟩ := hmc
        have hgo' : Sum.inr z ∈ compGo α β f [w₁] (wsTail ++ [])
            [] [] [] (ys ++ []) false := by simpa using hgo
        obtain ⟨f', hst⟩ := compGo_replay_rev hr rfl hgo'
        rcases compGo_extract hr hst with
          ⟨vsq, usq, x', hrq, hx', hbad⟩ | ⟨vsq, usq, z', hrq, hz', hzz⟩
        · exact absurd hbad (by simp)
        · have : z' = z := Sum.inr.inj hzz.symm
          subst this
          exact ⟨vsq, usq, hrq, hz'⟩

/-- The LHS outer fold simulated round by round. -/
theorem lhs_to_rhs_outer :
    ∀ {rest : List W} {fuel : ℕ} {wsPre : List W} {xs : List X}
      {ys : List (Option Y)} {r : List Z × List X × List (Option Y)},
      r ∈ driveOuter (comp α β) S fuel wsPre xs ys rest →
      ∀ {zs vs us},
      (∀ w : W, CompRun α β S (wsPre ++ [w]) zs vs us xs ys false) →
      rest ≠ [] →
      ∃ z, r.1.getLast? = some z ∧
        ∃ zsF vsF usF xsF ysF,
          CompRun α β S (wsPre ++ rest) zsF vsF usF xsF ysF false ∧
          Sum.inr z ∈ α (wsPre ++ rest, vsF) := by
  intro rest
  induction rest with
  | nil => intro fuel wsPre xs ys r hm zs vs us hinv hne; exact absurd rfl hne
  | cons w rest ih =>
      intro fuel wsPre xs ys r hm zs vs us hinv _
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at hm
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := hm
      obtain ⟨vs', us', hr', hz'⟩ := lhs_drive_sim hr₁ (hinv w)
      cases rest with
      | nil =>
          simp only [driveOuter, Part.mem_some_iff] at hrr
          subst hrr
          exact ⟨r₁.1, by simp, zs, vs', us', r₁.2.1, r₁.2.2, hr', hz'⟩
      | cons w' rest' =>
          have hinv' : ∀ w'' : W, CompRun α β S ((wsPre ++ [w]) ++ [w''])
              (zs ++ [r₁.1]) vs' us' r₁.2.1 r₁.2.2 false :=
            fun w'' => CompRun.answer2 w'' hr' hz'
          obtain ⟨z, hlast, zsF, vsF, usF, xsF, ysF, hfin, hzfin⟩ :=
            ih hrr hinv' (by simp)
          refine ⟨z, ?_, zsF, vsF, usF, xsF, ysF, ?_, ?_⟩
          · have hrrne : rr.1 ≠ [] := by
              have hlen := driveOuter_length (comp α β) S _ hrr
              intro hnil
              rw [hnil] at hlen
              simp at hlen
            cases hrr1 : rr.1 with
            | nil => exact absurd hrr1 hrrne
            | cons a as =>
                rw [hrr1] at hlast
                show (r₁.1 :: a :: as).getLast? = some z
                rw [List.getLast?_cons_cons]
                exact hlast
          · have : (wsPre ++ [w]) ++ (w' :: rest') = wsPre ++ (w :: w' :: rest') := by
              simp
            rw [← this]
            exact hfin
          · have : (wsPre ++ [w]) ++ (w' :: rest') = wsPre ++ (w :: w' :: rest') := by
              simp
            rw [← this]
            exact hzfin

/-- The composite's move is derivable at any reachable β-turn state. -/
theorem comp_query_of_state {wsAct zs vs us' xs ys x}
    (hr : CompRun α β S wsAct zs vs us' xs ys true)
    (hx : Sum.inl x ∈ β (us', ys)) :
    Sum.inl x ∈ comp α β (wsAct, ys) := by
  have hne := compRun_ne_nil hr
  obtain ⟨w₁, wsTail, rfl⟩ : ∃ a t, wsAct = a :: t := by
    cases wsAct with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨a, t, rfl⟩
  have hgo : Sum.inl x ∈ compGo α β (0 + 1) (w₁ :: wsTail) [] vs us' ys []
      true := compGo_mem_exit1 hx
  obtain ⟨f', hf⟩ := compGo_replay hr hgo rfl
  rw [mem_comp_cons]
  exact ⟨f', by simpa using hf⟩

/-- The composite's answer is derivable at any reachable α-turn state. -/
theorem comp_answer_of_state {wsAct zs vs us xs ys z}
    (hr : CompRun α β S wsAct zs vs us xs ys false)
    (hz : Sum.inr z ∈ α (wsAct, vs)) :
    Sum.inr z ∈ comp α β (wsAct, ys) := by
  have hne := compRun_ne_nil hr
  obtain ⟨w₁, wsTail, rfl⟩ : ∃ a t, wsAct = a :: t := by
    cases wsAct with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨a, t, rfl⟩
  have hgo : Sum.inr z ∈ compGo α β (0 + 1) (w₁ :: wsTail) [] vs us ys []
      false := compGo_mem_exit2 hz
  obtain ⟨f', hf⟩ := compGo_replay hr hgo rfl
  rw [mem_comp_cons]
  exact ⟨f', by simpa using hf⟩

/-- A β-round segment replayed: the machine advances to the segment's end,
and LHS runs from the end extend to the segment's start. -/
theorem segment_lhs :
    ∀ {fuel : ℕ} {us' : List U} {xs : List X} {ys : List (Option Y)}
      {mres : V × List X × List (Option Y)},
      mres ∈ drive β S fuel us' xs ys →
      ∀ {wsAct zs vs}, CompRun α β S wsAct zs vs us' xs ys true →
      CompRun α β S wsAct zs (vs ++ [some mres.1]) us' mres.2.1 mres.2.2
        false ∧
      ∀ {fuelL : ℕ} {r : Z × List X × List (Option Y)},
        r ∈ drive (comp α β) S fuelL wsAct mres.2.1 mres.2.2 →
        ∃ fuelL', r ∈ drive (comp α β) S fuelL' wsAct xs ys := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ mres hm; simp [drive] at hm
  | succ n ih =>
      intro us' xs ys mres hm wsAct zs vs hr
      rcases drive_succ_elim hm with ⟨x, hx, hrec⟩ | ⟨v, hv, rfl⟩
      · have hr' := CompRun.query1 hr hx
        obtain ⟨hstate, hcont⟩ := ih hrec hr'
        refine ⟨hstate, ?_⟩
        intro fuelL r hL
        obtain ⟨fuelL', hL'⟩ := hcont hL
        exact ⟨fuelL' + 1, drive_mem_query (comp α β) S
          (comp_query_of_state hr hx) hL'⟩
      · exact ⟨CompRun.answer1 hr hv, fun hL => ⟨_, hL⟩⟩

/-- One RHS round simulated backward: a `drive` run of α against the
middle system yields an LHS round run and the round-ending machine state.
Definedness of the middle system is extracted *per consumed answer*: a
proper answer certifies the queried middle history in the β-composite's
domain, while a `⊥` answer silences a Def 3.8 α (`AnswersInY`) at the
very next consultation — the drive states are α-tree pairs — so a
converged run never consumed one. -/
theorem rhs_to_lhs_round (hα : AnswersInY α) :
    ∀ {fuel : ℕ} {wsAct : List W} {us : List U} {vs : List (Option V)}
      {r : Z × List U × List (Option V)},
      r ∈ drive α (apply β S) fuel wsAct us vs →
      Reach α (wsAct, vs) →
      (us ∈ System.dom (apply β S) ∨ us = []) →
      ∀ {zs xs ys}, CompRun α β S wsAct zs vs us xs ys false →
      ∃ xsF ysF fuelL,
        (r.1, xsF, ysF) ∈ drive (comp α β) S fuelL wsAct xs ys ∧
        CompRun α β S wsAct zs r.2.2 r.2.1 xsF ysF false ∧
        Sum.inr r.1 ∈ α (wsAct, r.2.2) ∧
        Reach α (wsAct, r.2.2) ∧
        (r.2.1 ∈ System.dom (apply β S) ∨ r.2.1 = []) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ r hm; simp [drive] at hm
  | succ n ih =>
      intro wsAct us vs r hm hreach hdomus zs xs ys hr
      rcases drive_succ_elim hm with ⟨u, hu, hrec⟩ | ⟨z, hz, rfl⟩
      · rcases hout : System.output ((apply β S)⊥) (us ++ [u])
            (by rw [System.dom_fullyDefined]; simp) with _ | v'
        · -- a ⊥ answer: α is silent at the extended tree pair, the
          -- continued run has no result
          exfalso
          rw [hout] at hrec
          have hreach' : Reach α (wsAct, vs ++ [none]) :=
            Reach.answer hreach hu none
          rcases n with _ | n'
          · simp [drive] at hrec
          · rcases drive_succ_elim hrec with ⟨u₂, hu₂, -⟩ | ⟨z₂, hz₂, -⟩
            · exact hα _ hreach' (by simp)
                (Part.dom_iff_mem.mpr ⟨_, hu₂⟩)
            · exact hα _ hreach' (by simp)
                (Part.dom_iff_mem.mpr ⟨_, hz₂⟩)
        · -- a proper answer certifies the middle history's definedness
          rw [hout] at hrec
          obtain ⟨hdom, houtS⟩ :=
            System.mem_of_output_fullyDefined_append_eq_some
              (apply β S) us u hdomus hout
          have hvM : v' ∈ applyRaw β S (us ++ [u]) := by
            rw [← houtS]
            exact Part.get_mem hdom
          rw [mem_applyRaw] at hvM
          obtain ⟨fM, hM⟩ := hvM
          rw [mem_applyRawAt_iff] at hM
          obtain ⟨R, hR, hRlast⟩ := hM
          rw [driveOuter_append β S fM us [u], Part.mem_bind_iff] at hR
          obtain ⟨ra, hra, hmap⟩ := hR
          rw [Part.mem_map_iff] at hmap
          obtain ⟨rb, hrb, heqR⟩ := hmap
          simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff,
            Part.mem_some_iff] at hrb
          obtain ⟨rr, hrr, rrr, hrrr, heqrb⟩ := hrb
          subst hrrr
          -- merge the prefix run with the machine's middle certification
          obtain ⟨vsP, hvsP, fMid, hMid⟩ := (compRun_middle hr).1 rfl
          have hra' := driveOuter_mono_le β S (le_max_left fM fMid) hra
          have hMid' := driveOuter_mono_le β S (le_max_right fM fMid) hMid
          have hraeq : ra = (vsP, xs, ys) := Part.mem_unique hra' hMid'
          subst hraeq
          -- the segment's answer is the middle value
          have hrr1 : rr.1 = v' := by
            subst heqR
            subst heqrb
            rw [show ((vsP, xs, ys).1 ++ (rr.1 :: [], rr.2.1, rr.2.2).1
              : List V) = vsP ++ [rr.1] from rfl] at hRlast
            rw [List.getLast?_concat] at hRlast
            exact Option.some.inj hRlast
          -- run the segment through the machine
          have hr₂ := CompRun.query2 hr hu
          obtain ⟨hstate, hcont⟩ := segment_lhs hrr hr₂
          rw [hrr1] at hstate
          obtain ⟨xsF, ysF, fuelL, hLrun, hfin, hzfin, hreachF, hdomF⟩ :=
            ih hrec (Reach.answer hreach hu (some v')) (Or.inl hdom) hstate
          obtain ⟨fuelL', hLrun'⟩ := hcont hLrun
          exact ⟨xsF, ysF, fuelL', hLrun', hfin, hzfin, hreachF, hdomF⟩
      · exact ⟨xs, ys, 1,
          drive_mem_answer (comp α β) S (comp_answer_of_state hr hz) 0,
          hr, hz, hreach, hdomus⟩

/-- The RHS outer fold simulated backward, producing an LHS outer run. -/
theorem rhs_to_lhs_outer (hα : AnswersInY α) :
    ∀ {rest : List W} {fuel : ℕ} {wsPre : List W} {us : List U}
      {vs : List (Option V)} {r : List Z × List U × List (Option V)},
      r ∈ driveOuter α (apply β S) fuel wsPre us vs rest →
      (∀ w : W, Reach α (wsPre ++ [w], vs)) →
      (us ∈ System.dom (apply β S) ∨ us = []) →
      ∀ {zs xs ys},
      (∀ w : W, CompRun α β S (wsPre ++ [w]) zs vs us xs ys false) →
      rest ≠ [] →
      ∃ z, r.1.getLast? = some z ∧
        ∃ fuelL rL,
          rL ∈ driveOuter (comp α β) S fuelL wsPre xs ys rest ∧
          rL.1.getLast? = some z := by
  intro rest
  induction rest with
  | nil =>
      intro fuel wsPre us vs r hm hre hdom zs xs ys hinv hne
      exact absurd rfl hne
  | cons w rest ih =>
      intro fuel wsPre us vs r hm hre hdom zs xs ys hinv _
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at hm
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := hm
      obtain ⟨xsF, ysF, fuelL₁, hL₁, hfin, hzfin, hreF, hdomF⟩ :=
        rhs_to_lhs_round hα hr₁ (hre w) hdom (hinv w)
      cases rest with
      | nil =>
          simp only [driveOuter, Part.mem_some_iff] at hrr
          subst hrr
          refine ⟨r₁.1, by simp, fuelL₁, ([r₁.1], xsF, ysF), ?_, by simp⟩
          show ([r₁.1], xsF, ysF) ∈
              (drive (comp α β) S fuelL₁ (wsPre ++ [w]) xs ys).bind
                fun r' =>
              (driveOuter (comp α β) S fuelL₁ (wsPre ++ [w])
                r'.2.1 r'.2.2 []).map fun rr' => (r'.1 :: rr'.1, rr'.2)
          rw [Part.mem_bind_iff]
          refine ⟨(r₁.1, xsF, ysF), hL₁, ?_⟩
          rw [Part.mem_map_iff]
          exact ⟨([], xsF, ysF), by simp [driveOuter], rfl⟩
      | cons w' rest' =>
          have hinv' : ∀ w'' : W, CompRun α β S ((wsPre ++ [w]) ++ [w''])
              (zs ++ [r₁.1]) r₁.2.2 r₁.2.1 xsF ysF false :=
            fun w'' => CompRun.answer2 w'' hfin hzfin
          have hre' : ∀ w'' : W,
              Reach α ((wsPre ++ [w]) ++ [w''], r₁.2.2) :=
            fun w'' => Reach.next hreF hzfin w''
          obtain ⟨z, hlast, fuelL₂, rrL, hrrL, hrrLlast⟩ :=
            ih hrr hre' hdomF hinv' (by simp)
          refine ⟨z, ?_, max fuelL₁ fuelL₂,
            (r₁.1 :: rrL.1, rrL.2), ?_, ?_⟩
          · have hrrne : rr.1 ≠ [] := by
              have hlen := driveOuter_length α (apply β S) _ hrr
              intro hnil
              rw [hnil] at hlen
              simp at hlen
            cases hrr1 : rr.1 with
            | nil => exact absurd hrr1 hrrne
            | cons a as =>
                rw [hrr1] at hlast
                show (r₁.1 :: a :: as).getLast? = some z
                rw [List.getLast?_cons_cons]
                exact hlast
          · show (r₁.1 :: rrL.1, rrL.2) ∈
                (drive (comp α β) S (max fuelL₁ fuelL₂)
                  (wsPre ++ [w]) xs ys).bind fun r' =>
                (driveOuter (comp α β) S (max fuelL₁ fuelL₂)
                  (wsPre ++ [w]) r'.2.1 r'.2.2 (w' :: rest')).map fun rr' =>
                  (r'.1 :: rr'.1, rr'.2)
            rw [Part.mem_bind_iff]
            refine ⟨(r₁.1, xsF, ysF),
              drive_mono_le (comp α β) S (le_max_left _ _) hL₁, ?_⟩
            rw [Part.mem_map_iff]
            exact ⟨rrL, driveOuter_mono_le (comp α β) S
              (le_max_right _ _) hrrL, rfl⟩
          · have hrrLne : rrL.1 ≠ [] := by
              have hlen := driveOuter_length (comp α β) S _ hrrL
              intro hnil
              rw [hnil] at hlen
              simp at hlen
            cases hrrL1 : rrL.1 with
            | nil => exact absurd hrrL1 hrrLne
            | cons a as =>
                rw [hrrL1] at hrrLlast
                show (r₁.1 :: a :: as).getLast? = some z
                rw [List.getLast?_cons_cons]
                exact hrrLlast

/-- **The action law (interaction associativity)**: applying the serial
composite is composing the applications — CR18 converter application is
a monoid action on systems, at the full cross-round-memory generality.

The only hypothesis is Def 3.8's input-alphabet clause on the *outer*
converter (`AnswersInY α`): where the β-composite is silent, the staged
side feeds α a `⊥`, and a Def 3.8-conforming α refuses to move past it —
both sides stall together, undefined both ways.  Nothing is assumed of
β or of the system: definedness of the middle system is certified per
consumed proper answer, run by run. -/
theorem apply_comp (α : ProtocolFn W Z U V) (β : ProtocolFn U V X Y)
    (S : System.DDS X Y) (hα : AnswersInY α) :
    apply (comp α β) S = apply α (apply β S) := by
  apply Subtype.ext
  funext ws
  apply Part.ext
  intro z
  show z ∈ applyRaw (comp α β) S ws ↔
    z ∈ applyRaw α (apply β S) ws
  rw [mem_applyRaw, mem_applyRaw]
  constructor
  · rintro ⟨fuel, hz⟩
    rw [mem_applyRawAt_iff] at hz
    obtain ⟨r, hr, hlast⟩ := hz
    have hne : ws ≠ [] := by
      rintro rfl
      simp only [driveOuter, Part.mem_some_iff] at hr
      subst hr
      simp at hlast
    obtain ⟨z', hz', zsF, vsF, usF, xsF, ysF, hfin, hzfin⟩ :=
      lhs_to_rhs_outer (wsPre := []) hr (fun w => CompRun.start w) hne
    have hzz : z' = z := by
      rw [hlast] at hz'
      exact (Option.some.inj hz').symm
    subst hzz
    obtain ⟨usR, vsR, ⟨wsPre', wl, heqw, fuelA, hanchor⟩, hcf, -⟩ :=
      compRun_outer hfin
    have hstep : (z', usF, vsF) ∈
        drive α (apply β S) 1 ([] ++ ws) usF vsF :=
      drive_mem_answer α (apply β S) hzfin 0
    obtain ⟨f2, hstep'⟩ := hcf rfl hstep
    refine ⟨max fuelA f2, ?_⟩
    rw [mem_applyRawAt_iff]
    refine ⟨(zsF ++ [z'], usF, vsF), ?_, by simp⟩
    have hws : ([] : List W) ++ ws = wsPre' ++ [wl] := heqw
    rw [show ws = wsPre' ++ [wl] from by simpa using hws]
    rw [driveOuter_append α (apply β S) _ wsPre' [wl]]
    rw [Part.mem_bind_iff]
    refine ⟨(zsF, usR, vsR),
      driveOuter_mono_le α (apply β S) (le_max_left _ _) hanchor, ?_⟩
    rw [Part.mem_map_iff]
    refine ⟨([z'], usF, vsF), ?_, rfl⟩
    show _ ∈ (drive α (apply β S) _ (wsPre' ++ [wl]) usR vsR).bind _
    rw [Part.mem_bind_iff]
    refine ⟨(z', usF, vsF), ?_, by simp [driveOuter]⟩
    have := drive_mono_le α (apply β S) (le_max_right fuelA f2) hstep'
    rw [show ([] : List W) ++ ws = wsPre' ++ [wl] from hws] at this
    exact this
  · rintro ⟨fuel, hz⟩
    rw [mem_applyRawAt_iff] at hz
    obtain ⟨r, hr, hlast⟩ := hz
    have hne : ws ≠ [] := by
      rintro rfl
      simp only [driveOuter, Part.mem_some_iff] at hr
      subst hr
      simp at hlast
    obtain ⟨z', hz', fuelL, rL, hrL, hrLlast⟩ :=
      rhs_to_lhs_outer hα (wsPre := []) hr (fun w => Reach.first w)
        (Or.inr rfl) (fun w => CompRun.start w) hne
    have hzz : z' = z := by
      rw [hlast] at hz'
      exact (Option.some.inj hz').symm
    subst hzz
    refine ⟨fuelL, ?_⟩
    rw [mem_applyRawAt_iff]
    exact ⟨rL, hrL, hrLlast⟩

/-- The action law at the Def 3.8/3.9 surface: applying the canonical
DDC of the composite is composing the Def 3.9 applications, for an outer
converter honoring Def 3.8's input alphabet. -/
theorem apply_toDDC_comp (α : ProtocolFn W Z U V)
    (β : ProtocolFn U V X Y) (S : System.DDS X Y) (hα : AnswersInY α) :
    DDC.apply (toDDC (comp α β)) S
      = DDC.apply (toDDC α) (DDC.apply (toDDC β) S) := by
  rw [apply_toDDC, apply_toDDC, apply_toDDC, apply_comp α β S hα]

end ActionLaw

/-! ### The composite on its trace tree: the Def 3.8 clauses

The machine consults β exactly at pairs of β's trace tree (the middle
queries and consumed answers grow by β's own moves), and it never feeds
a `⊥` upward (`vs` only ever receives `some v`).  So when β answers in
`Y` (Def 3.8's input-alphabet clause), the machine cannot consume a `⊥`:
the consultation right after the consuming step is silenced.  Every
exit requires full consumption — hence no composite value survives a
`⊥` anywhere in the input, and `AnswersInY` is preserved by composition
with *no hypothesis on the outer converter*.

**Warning — the finite-bound clause is a tree property here, do not
attempt the uniform off-tree version.**  At a *junk* pair with pending
deliveries the composite's query streak is unbounded even for streak
bounds `2` on both components: with `wsRest ≠ []` the machine can cycle
"consume · β-answer · α-answer · deliver · α-query · β-query" — one
composite query per remaining delivery, so streaks grow with the outer
history and no uniform `B` exists.  On the tree this cannot happen:
`Reach.next` extends only through a composite answer (exit2 = full
delivery), so at a reachable pair the replay has `wsRest = []`, an
α-answer ends the streak, the α-queries form a single α-streak
(`< Bα`), and a successful query run consuming `Bα · Bβ` base answers
is impossible.  The public existential closure theorem below adds one to
obtain a positive threshold and cover empty-alphabet zero-bound witnesses. -/

/-- No composite value survives an unconsumed `⊥` when the inner
converter answers in `Y`.  Invariants: at a β-turn the consulted pair is
on β's tree; at an α-turn it is initial or just β-answered. -/
theorem compGo_not_mem_of_none (hβ : AnswersInY β) :
    ∀ (fuel : ℕ) (wsAct wsRest : List W) (vs : List (Option V))
      (us : List U) (ysDone ysRest : List (Option Y)) (mode : Bool)
      (m : X ⊕ Z),
      (mode = false → us = [] ∧ ysDone = [] ∨
        Reach β (us, ysDone) ∧ ∃ v, Sum.inr v ∈ β (us, ysDone)) →
      (mode = true → Reach β (us, ysDone)) →
      none ∈ ysRest →
      m ∉ compGo α β fuel wsAct wsRest vs us ysDone ysRest mode := by
  intro fuel
  induction fuel with
  | zero =>
      intro wsAct wsRest vs us ysDone ysRest mode m _ _ _ hm
      simp [compGo] at hm
  | succ f ih =>
      intro wsAct wsRest vs us ysDone ysRest mode m hIf hIt hnone hm
      cases mode with
      | false =>
          rcases compGo_elim2 hm with ⟨u, hmα, h'⟩ |
            ⟨z, w, rest, hmα, hwr, h'⟩ | ⟨z, hmα, hwr, hyr, -⟩
          · refine ih wsAct wsRest vs (us ++ [u]) ysDone ysRest true m
              (fun hc => Bool.noConfusion hc) (fun _ => ?_) hnone h'
            rcases hIf rfl with ⟨rfl, rfl⟩ | ⟨hre, v, hv⟩
            · exact Reach.first u
            · exact Reach.next hre hv u
          · subst hwr
            exact ih (wsAct ++ [w]) rest vs us ysDone ysRest false m hIf
              (fun hc => Bool.noConfusion hc) hnone h'
          · subst hyr
            simp at hnone
      | true =>
          have hre := hIt rfl
          rcases compGo_elim1 hm with ⟨v, hmβ, h'⟩ |
            ⟨x, y, rest, hmβ, hyr, h'⟩ | ⟨x, hmβ, hyr, hwr, -⟩
          · exact ih wsAct wsRest (vs ++ [some v]) us ysDone ysRest false m
              (fun _ => Or.inr ⟨hre, v, hmβ⟩)
              (fun hc => Bool.noConfusion hc) hnone h'
          · subst hyr
            rcases List.mem_cons.mp hnone with hy | hn'
            · subst hy
              rcases f with _ | f₂
              · simp [compGo] at h'
              · have hre' : Reach β (us, ysDone ++ [none]) :=
                  Reach.answer hre hmβ none
                rcases compGo_elim1 h' with ⟨v₂, hm₂, -⟩ |
                  ⟨x₂, y₂, r₂, hm₂, -, -⟩ | ⟨x₂, hm₂, -, -, -⟩
                · exact hβ _ hre' (by simp)
                    (Part.dom_iff_mem.mpr ⟨_, hm₂⟩)
                · exact hβ _ hre' (by simp)
                    (Part.dom_iff_mem.mpr ⟨_, hm₂⟩)
                · exact hβ _ hre' (by simp)
                    (Part.dom_iff_mem.mpr ⟨_, hm₂⟩)
            · exact ih wsAct wsRest vs us (ysDone ++ [y]) rest true m
                (fun hc => Bool.noConfusion hc)
                (fun _ => Reach.answer hre hmβ y) hn' h'
          · subst hyr
            simp at hnone

/-- **`AnswersInY` is preserved by composition** — with no hypothesis on
the outer converter.  Stronger than the clause: the composite is silent
at *every* `⊥`-containing input, reachable or not. -/
theorem answersInY_comp (hβ : AnswersInY β) : AnswersInY (comp α β) := by
  rintro ⟨ws, ys⟩ hr hn hd
  obtain ⟨m, hm⟩ := Part.dom_iff_mem.mp hd
  rcases ws with _ | ⟨w, wsT⟩
  · rw [comp_apply_nil] at hm
    simp at hm
  · rw [mem_comp_cons] at hm
    obtain ⟨fuel, hf⟩ := hm
    exact compGo_not_mem_of_none hβ fuel [w] wsT [] [] [] ys false m
      (fun _ => Or.inl ⟨rfl, rfl⟩) (fun hc => Bool.noConfusion hc) hn hf

/-- **Run-extension factoring** (the replay/tree correspondence engine):
a converged composite-query run, replayed on an answer-extended input,
factors through the shorter run's exit state — determinism aligns the
two runs consultation by consultation.  Returns the exit state's tree
facts (the α-consultation with its pending query, the β-consultation
with the exiting query) together with the longer run's membership from
the factored state. -/
theorem compGo_inl_factor :
    ∀ (fuel₁ : ℕ) (wsAct wsRest : List W) (vs : List (Option V))
      (us : List U) (ysDone ysRest : List (Option Y)) (mode : Bool)
      (x : X) (fuel₂ : ℕ) (m' : X ⊕ Z) (ysExt : List (Option Y)),
      (mode = false → Reach α (wsAct, vs)) →
      (mode = true → Reach α (wsAct, vs) ∧
        ∃ x', Sum.inl x' ∈ α (wsAct, vs)) →
      (mode = false → us = [] ∧ ysDone = [] ∨
        Reach β (us, ysDone) ∧ ∃ v, Sum.inr v ∈ β (us, ysDone)) →
      (mode = true → Reach β (us, ysDone)) →
      Sum.inl x ∈ compGo α β fuel₁ wsAct wsRest vs us ysDone ysRest mode →
      m' ∈ compGo α β fuel₂ wsAct wsRest vs us ysDone (ysRest ++ ysExt)
        mode →
      ∃ vsF usF fuel₂',
        Reach α (wsAct ++ wsRest, vsF) ∧
        (∃ x', Sum.inl x' ∈ α (wsAct ++ wsRest, vsF)) ∧
        Reach β (usF, ysDone ++ ysRest) ∧
        Sum.inl x ∈ β (usF, ysDone ++ ysRest) ∧
        m' ∈ compGo α β fuel₂' (wsAct ++ wsRest) [] vsF usF
          (ysDone ++ ysRest) ysExt true := by
  intro fuel₁
  induction fuel₁ with
  | zero =>
      intro wsAct wsRest vs us ysDone ysRest mode x fuel₂ m' ysExt
        _ _ _ _ h₁ _
      simp [compGo] at h₁
  | succ f₁ ih =>
      intro wsAct wsRest vs us ysDone ysRest mode x fuel₂ m' ysExt
        hIαf hIαt hIβf hIβt h₁ h₂
      rcases fuel₂ with _ | f₂
      · simp [compGo] at h₂
      cases mode with
      | false =>
          rcases compGo_elim2 h₁ with hquery | hrest
          · -- run 1 queried α: run 2 must have done the same
            obtain ⟨uMove, hmα, h₁'⟩ := hquery
            rcases compGo_elim2 h₂ with ⟨u₂, hmα₂, h₂'⟩ |
              ⟨z₂, w₂, rest₂, hmα₂, hwr₂, -⟩ | ⟨z₂, hmα₂, -, -, -⟩
            · have huu := Part.mem_unique hmα₂ hmα
              injection huu with huu
              subst uMove
              refine ih wsAct wsRest vs (us ++ [u₂]) ysDone ysRest true x
                f₂ m' ysExt (fun hc => Bool.noConfusion hc)
                (fun _ => ⟨hIαf rfl, u₂, hmα⟩)
                (fun hc => Bool.noConfusion hc) (fun _ => ?_) h₁' h₂'
              rcases hIβf rfl with ⟨rfl, rfl⟩ | ⟨hre, v, hv⟩
              · exact Reach.first u₂
              · exact Reach.next hre hv u₂
            · exact absurd (Part.mem_unique hmα₂ hmα)
                (by simp)
            · exact absurd (Part.mem_unique hmα₂ hmα)
                (by simp)
          · rcases hrest with hadvance | hexit
            · -- run 1 advanced: run 2 must have done the same
              obtain ⟨z, w, rest, hmα, hwr, h₁'⟩ := hadvance
              rcases compGo_elim2 h₂ with ⟨u₂, hmα₂, -⟩ |
                ⟨z₂, w₂, rest₂, hmα₂, hwr₂, h₂'⟩ | ⟨z₂, hmα₂, hwr₂, -, -⟩
              · exact absurd (Part.mem_unique hmα₂ hmα)
                  (by simp)
              · rw [hwr] at hwr₂
                injection hwr₂ with hw hrest
                subst hw
                subst hrest
                subst hwr
                obtain ⟨vsF, usF, fuel₂', hF1, hF2, hF3, hF4, hF5⟩ :=
                  ih (wsAct ++ [w]) rest vs us ysDone ysRest false x
                    f₂ m' ysExt
                    (fun _ => Reach.next (hIαf rfl) hmα w)
                    (fun hc => Bool.noConfusion hc) hIβf
                    (fun hc => Bool.noConfusion hc) h₁' h₂'
                rw [List.append_assoc] at hF1 hF2 hF5
                exact ⟨vsF, usF, fuel₂', hF1, hF2, hF3, hF4, hF5⟩
              · rw [hwr] at hwr₂
                simp at hwr₂
            · -- run 1 exited with an answer: impossible for a query value
              obtain ⟨z, hmα, hwr, hyr, hmv⟩ := hexit
              exact absurd hmv (by simp)
      | true =>
          rcases compGo_elim1 h₁ with hanswer | hrest
          · -- run 1 got a β answer: run 2 must have too
            obtain ⟨vMove, hmβ, h₁'⟩ := hanswer
            rcases compGo_elim1 h₂ with ⟨v₂, hmβ₂, h₂'⟩ |
              ⟨x₂, y₂, rest₂, hmβ₂, hyr₂, -⟩ | ⟨x₂, hmβ₂, -, -, -⟩
            · have hvv := Part.mem_unique hmβ₂ hmβ
              injection hvv with hvv
              subst vMove
              obtain ⟨hreα, x', hx'⟩ := hIαt rfl
              exact ih wsAct wsRest (vs ++ [some v₂]) us ysDone ysRest
                false x f₂ m' ysExt
                (fun _ => Reach.answer hreα hx' (some v₂))
                (fun hc => Bool.noConfusion hc)
                (fun _ => Or.inr ⟨hIβt rfl, v₂, hmβ⟩)
                (fun hc => Bool.noConfusion hc) h₁' h₂'
            · exact absurd (Part.mem_unique hmβ₂ hmβ)
                (by simp)
            · exact absurd (Part.mem_unique hmβ₂ hmβ)
                (by simp)
          · rcases hrest with hconsume | hexit
            · -- run 1 consumed an answer: run 2 consumes the same one
              obtain ⟨x₁, y, rest, hmβ, hyr, h₁'⟩ := hconsume
              subst hyr
              rcases compGo_elim1 h₂ with ⟨v₂, hmβ₂, -⟩ |
                ⟨x₂, y₂, rest₂, hmβ₂, hyr₂, h₂'⟩ | ⟨x₂, hmβ₂, hyr₂, -, -⟩
              · exact absurd (Part.mem_unique hmβ₂ hmβ)
                  (by simp)
              · rw [List.cons_append] at hyr₂
                injection hyr₂ with hy hrest
                subst hy
                subst hrest
                obtain ⟨vsF, usF, fuel₂', hF1, hF2, hF3, hF4, hF5⟩ :=
                  ih wsAct wsRest vs us (ysDone ++ [y]) rest true x
                    f₂ m' ysExt hIαf hIαt
                    (fun hc => Bool.noConfusion hc)
                    (fun _ => Reach.answer (hIβt rfl) hmβ y) h₁' h₂'
                rw [List.append_assoc] at hF3 hF4 hF5
                exact ⟨vsF, usF, fuel₂', hF1, hF2, hF3, hF4, hF5⟩
              · rw [List.cons_append] at hyr₂
                simp at hyr₂
            · -- run 1 exits with the query: the factoring point
              obtain ⟨x₁, hmβ, hyr, hwr, hmv⟩ := hexit
              subst hyr
              subst hwr
              injection hmv with hx₁
              subst hx₁
              obtain ⟨hreα, hcert⟩ := hIαt rfl
              simp only [List.append_nil]
              exact ⟨vs, us, f₂ + 1, hreα, hcert, hIβt rfl, hmβ, h₂⟩

/-! ### The finite query-streak bound

CR18 Definition 3.8 asks only for the existence of a finite bound.  The
proof below records the quantitative accounting in supporting lemmas and exposes
an existential closure theorem.  A successful composite-query run with no
outer inputs left to deliver splits into consecutive β-query segments.  Each
completed segment returns one proper β-answer to α and starts the next
α-query. -/

/-- Consuming one answer after a query uses one slot of the local query
bound.  (The localized clause itself is `Converter.AnswersWithinAt`;
localizing a uniform bound at a reachable pair is
`AnswersWithin.at_of_reach`.) -/
theorem answersWithinAt_after_answer
    {nu : ProtocolFn U V X Y} {us : List U} {ys : List (Option Y)}
    {B : ℕ} {x : X} (hx : Sum.inl x ∈ nu (us, ys))
    (hB : AnswersWithinAt nu (us, ys) (B + 1)) (y : Option Y) :
    AnswersWithinAt nu (us, ys ++ [y]) B := by
  intro ext hlen hqueries
  apply hB (y :: ext)
  · simp only [List.length_cons]
    omega
  · intro k hk
    cases k with
    | zero =>
        simpa using ⟨x, hx⟩
    | succ k =>
        have hk' : k < ext.length := by simp at hk; omega
        obtain ⟨x', hx'⟩ := hqueries k hk'
        refine ⟨x', ?_⟩
        simpa [List.take_succ_cons, List.append_assoc] using hx'

theorem length_lt_of_answersWithinAt
    {nu : ProtocolFn U V X Y} {p : List U × List (Option Y)} {B : ℕ}
    {ext : List (Option Y)} (hB : AnswersWithinAt nu p B)
    (hqueries : ∀ k (_ : k < ext.length),
      ∃ x, Sum.inl x ∈ nu (p.1, p.2 ++ ext.take k)) :
    ext.length < B := by
  by_contra hnot
  exact hB ext (Nat.le_of_not_gt hnot) hqueries

/-- A query streak extends reachability by the corresponding answer list. -/
theorem reach_after_query_extension
    {nu : ProtocolFn U V X Y} {us : List U} {ys : List (Option Y)}
    {ext : List (Option Y)} (hr : Reach nu (us, ys))
    (hqueries : ∀ k (_ : k < ext.length),
      ∃ x, Sum.inl x ∈ nu (us, ys ++ ext.take k)) :
    Reach nu (us, ys ++ ext) := by
  induction ext generalizing ys with
  | nil => simpa using hr
  | cons y rest ih =>
      obtain ⟨x, hx⟩ := hqueries 0 (by simp)
      have hx0 : Sum.inl x ∈ nu (us, ys) := by simpa using hx
      have hr1 : Reach nu (us, ys ++ [y]) := Reach.answer hr hx0 y
      have hrest : ∀ k (_ : k < rest.length),
          ∃ x, Sum.inl x ∈ nu (us, (ys ++ [y]) ++ rest.take k) := by
        intro k hk
        obtain ⟨x', hx'⟩ := hqueries (k + 1) (by simp; omega)
        refine ⟨x', ?_⟩
        simpa [List.take_succ_cons, List.append_assoc, Nat.add_comm] using hx'
      simpa [List.append_assoc] using ih hr1 hrest

/-- Split one successful composite-query run at the end of its current
β-round.  Either β queries throughout the entire supplied answer segment,
or it answers after a query prefix, α issues the next query, and the
remaining run starts at the next β-round. -/
theorem comp_go_query_round_split :
    ∀ {fuel : ℕ} {ws : List W} {vs : List (Option V)} {us : List U}
      {ysDone ysRest : List (Option Y)} {xOut : X},
      Sum.inl xOut ∈ compGo α β fuel ws [] vs us ysDone ysRest true →
      (∀ k (_ : k < ysRest.length),
        ∃ x, Sum.inl x ∈ β (us, ysDone ++ ysRest.take k)) ∨
      ∃ (ysPre ysSuf : List (Option Y)) (v : V) (u : U) (fuel' : ℕ),
        ysRest = ysPre ++ ysSuf ∧
        (∀ k (_ : k < ysPre.length),
          ∃ x, Sum.inl x ∈ β (us, ysDone ++ ysPre.take k)) ∧
        Sum.inr v ∈ β (us, ysDone ++ ysPre) ∧
        Sum.inl u ∈ α (ws, vs ++ [some v]) ∧
        Sum.inl xOut ∈ compGo α β fuel' ws [] (vs ++ [some v])
          (us ++ [u]) (ysDone ++ ysPre) ysSuf true := by
  intro fuel
  induction fuel with
  | zero =>
      intro ws vs us ysDone ysRest xOut h
      simp [compGo] at h
  | succ f ih =>
      intro ws vs us ysDone ysRest xOut h
      rcases compGo_elim1 h with ⟨v, hv, hα⟩ |
        ⟨x, y, rest, hx, hrest, htail⟩ |
        ⟨x, hx, hrest, hws, hout⟩
      · rcases f with _ | f'
        · simp [compGo] at hα
        · rcases compGo_elim2 hα with ⟨u, hu, htail⟩ |
            ⟨z, w, rest, hz, hnil, htail⟩ |
            ⟨z, hz, hnil, hy, hout⟩
          · refine Or.inr ⟨[], ysRest, v, u, f', rfl,
              (by intro k hk; simp at hk), ?_, hu, ?_⟩
            · simpa using hv
            · simpa using htail
          · simp at hnil
          · exact absurd hout (by simp)
      · subst hrest
        rcases ih htail with hqueries | hanswer
        · left
          intro k hk
          cases k with
          | zero =>
              simpa using ⟨x, hx⟩
          | succ k =>
              have hk' : k < rest.length := by simp at hk; omega
              obtain ⟨x', hx'⟩ := hqueries k hk'
              refine ⟨x', ?_⟩
              simpa [List.take_succ_cons, List.append_assoc] using hx'
        · obtain ⟨ysPre, ysSuf, v, u, fuel', heq, hqueries,
            hv, hu, htail'⟩ := hanswer
          right
          refine ⟨y :: ysPre, ysSuf, v, u, fuel', ?_, ?_, ?_, hu, ?_⟩
          · simp [heq]
          · intro k hk
            cases k with
            | zero => simpa using ⟨x, hx⟩
            | succ k =>
                have hk' : k < ysPre.length := by simp at hk; omega
                obtain ⟨x', hx'⟩ := hqueries k hk'
                refine ⟨x', ?_⟩
                simpa [List.take_succ_cons, List.append_assoc] using hx'
          · simpa [List.append_assoc] using hv
          · simpa [List.append_assoc] using htail'
      · subst hrest
        have hxo : xOut = x := Sum.inl.inj hout
        subst xOut
        left
        intro k hk
        simp at hk

/-- Quantitative accounting for one normalized composite-query run.  The
outer local bound decreases whenever a completed β-round supplies the answer
that opens the next α-query; every β-round consumes fewer than `Bbeta` base
answers. -/
theorem comp_go_query_run_length_lt
    {Balpha Bbeta fuel : ℕ} {ws : List W} {vs : List (Option V)} {us : List U}
    {ysDone ysRest : List (Option Y)} {xOut : X}
    (hα : AnswersWithinAt α (ws, vs) Balpha)
    (hβ : AnswersWithin β Bbeta) (hrβ : Reach β (us, ysDone))
    (hαquery : ∃ u, Sum.inl u ∈ α (ws, vs))
    (hrun : Sum.inl xOut ∈
      compGo α β fuel ws [] vs us ysDone ysRest true) :
    ysRest.length < Balpha * Bbeta := by
  induction Balpha generalizing fuel vs us ysDone ysRest xOut with
  | zero =>
      exfalso
      apply hα [] (by simp)
      intro k hk
      simp at hk
  | succ Balpha ih =>
      have hβat : AnswersWithinAt β (us, ysDone) Bbeta :=
        hβ.at_of_reach hrβ
      rcases comp_go_query_round_split hrun with hfinal | hnext
      · have hsegment : ysRest.length < Bbeta :=
          length_lt_of_answersWithinAt hβat hfinal
        rw [Nat.succ_mul]
        omega
      · obtain ⟨ysPre, ysSuf, v, u, fuel', heq, hqueries,
          hv, hu, htail⟩ := hnext
        have hsegment : ysPre.length < Bbeta :=
          length_lt_of_answersWithinAt hβat hqueries
        have hrβpre : Reach β (us, ysDone ++ ysPre) :=
          reach_after_query_extension hrβ hqueries
        have hrβnext : Reach β (us ++ [u], ysDone ++ ysPre) :=
          Reach.next hrβpre hv u
        obtain ⟨u₀, hu₀⟩ := hαquery
        have hαtail : AnswersWithinAt α (ws, vs ++ [some v]) Balpha :=
          answersWithinAt_after_answer hu₀
            (by simpa [Nat.succ_eq_add_one] using hα) (some v)
        have htailBound : ysSuf.length < Balpha * Bbeta :=
          ih hαtail hrβnext ⟨u, hu⟩ htail
        rw [heq, List.length_append, Nat.succ_mul]
        omega

/-- **The finite query-streak clause is preserved by serial composition.**
The public statement follows CR18 Definition 3.8 and exposes only existence
of a finite bound.  Internally, bounds `Balpha` and `Bbeta` give the deliberately
slack positive witness `Balpha * Bbeta + 1`; the final `+ 1` also covers
zero-bound witnesses that can arise when a component's outer alphabet is
empty. -/
theorem serial_composition_has_finite_query_bound
    (hα : ∃ Balpha, AnswersWithin α Balpha)
    (hβ : ∃ Bbeta, AnswersWithin β Bbeta) :
    ∃ B, AnswersWithin (comp α β) B := by
  obtain ⟨Balpha, hBalpha⟩ := hα
  obtain ⟨Bbeta, hBbeta⟩ := hβ
  refine ⟨Balpha * Bbeta + 1, ?_⟩
  rintro ⟨ws, ys⟩ hr ext hlen hqueries
  cases ws with
  | nil =>
      exact hr.ne_nil rfl
  | cons w wsRest =>
      have hzero : 0 < ext.length := by omega
      obtain ⟨x₀, hx₀⟩ := hqueries 0 hzero
      have hproduct : Balpha * Bbeta < ext.length := by omega
      obtain ⟨xN, hxN⟩ := hqueries (Balpha * Bbeta) hproduct
      have hx₀' : Sum.inl x₀ ∈ comp α β (w :: wsRest, ys) := by
        simpa using hx₀
      rw [mem_comp_cons] at hx₀'
      obtain ⟨fuel₀, hrun₀⟩ := hx₀'
      rw [mem_comp_cons] at hxN
      obtain ⟨fuelN, hrunN⟩ := hxN
      obtain ⟨vsF, usF, fuelF, hrα, hqα, hrβ, _hqβ, hrunF⟩ :=
        compGo_inl_factor (α := α) (β := β)
          fuel₀ [w] wsRest [] [] [] ys false x₀ fuelN (Sum.inl xN)
          (ext.take (Balpha * Bbeta))
          (fun _ => Reach.first w) (fun h => Bool.noConfusion h)
          (fun _ => Or.inl ⟨rfl, rfl⟩) (fun h => Bool.noConfusion h)
          hrun₀ hrunN
      simp only [List.singleton_append, List.nil_append] at hrα hqα hrβ hrunF
      have hαat : AnswersWithinAt α (w :: wsRest, vsF) Balpha :=
        hBalpha.at_of_reach hrα
      have hshort := comp_go_query_run_length_lt hαat hBbeta hrβ hqα hrunF
      have htake : (ext.take (Balpha * Bbeta)).length = Balpha * Bbeta := by
        rw [List.length_take, min_eq_left (Nat.le_of_lt hproduct)]
      rw [htake] at hshort
      exact (lt_irrefl (Balpha * Bbeta)) hshort

/-- **CR18 Definition 3.8 converters are closed under serial composition.**
The input-alphabet clause is `answersInY_comp`; the finite-streak clause is
`serial_composition_has_finite_query_bound`. -/
theorem serial_composition_is_ddc (hα : IsDDC α) (hβ : IsDDC β) :
    IsDDC (comp α β) :=
  ⟨answersInY_comp hβ.1,
    serial_composition_has_finite_query_bound hα.2 hβ.2⟩

/-! ### Stress tests

Formal negative results: raw-carrier laws that FAIL, each with its
minimal counterexample.  The composite is supported on replay-coherent
inputs only — a raw `ProtocolFn` owes no coherence to its own prefixes,
so the raw unit laws are false and the positive laws live under the
identity discipline (`AnswersInY`, `TraceEquiv`).  The AC-facing extensional
converter type is constructed later from semantic actions, not from this raw
carrier. -/

section StressTests

/-- The ⊥-reactive outer converter of the `apply_comp` counterexample:
queries once, then answers whatever came back — `⊥` included (violating
Def 3.8's input-alphabet clause). -/
def botReactive : ProtocolFn ℕ ℕ ℕ ℕ := fun p =>
  if p.2.length = 0 then Part.some (Sum.inl 0) else Part.some (Sum.inr 0)

theorem comp_botReactive_none :
    ∀ mv : ℕ ⊕ ℕ,
      mv ∉ comp botReactive
        (fun _ => Part.none : ProtocolFn ℕ ℕ ℕ ℕ) ([0], []) := by
  intro mv hmv
  rw [mem_comp_cons] at hmv
  obtain ⟨f2, hf2⟩ := hmv
  rcases f2 with _ | f3
  · simp [compGo] at hf2
  rcases compGo_elim2 hf2 with ⟨u, hmα, h'⟩ |
    ⟨z, w, rest, -, hwr, -⟩ | ⟨z, hmα, -, -, -⟩
  · rcases f3 with _ | f4
    · simp [compGo] at h'
    rcases compGo_elim1 h' with ⟨v, hv, -⟩ |
      ⟨x', y, rest, hx2, -, -⟩ | ⟨x', hx2, -, -, -⟩
    · simp at hv
    · simp at hx2
    · simp at hx2
  · simp at hwr
  · simp [botReactive] at hmα

/-- **`apply_comp` fails without `AnswersInY α`**: against a silent β,
the staged side feeds the ⊥-reactive α a `⊥` and completes, while the
stacked side stalls inside β — Def 3.8's input-alphabet clause on the
outer converter is not droppable. -/
theorem apply_comp_ne :
    ∃ (α β : ProtocolFn ℕ ℕ ℕ ℕ) (S : System.DDS ℕ ℕ),
      apply (comp α β) S ≠ apply α (apply β S) := by
  refine ⟨botReactive, fun _ => Part.none,
    System.functionEvaluator id, fun h => ?_⟩
  set S := System.functionEvaluator (id : ℕ → ℕ) with hS
  -- the middle system is undefined at [0]
  have hTundef : ([0] : List ℕ) ∉ System.dom
      (apply (fun _ => Part.none : ProtocolFn ℕ ℕ ℕ ℕ) S) := by
    intro hd
    rw [System.dom, PFun.mem_dom] at hd
    obtain ⟨v, hv⟩ := hd
    rw [apply_toPFun, mem_applyRaw] at hv
    obtain ⟨fuel, hv⟩ := hv
    rw [mem_applyRawAt_iff] at hv
    obtain ⟨r, hr, -⟩ := hv
    simp only [driveOuter, Part.mem_bind_iff] at hr
    obtain ⟨r₁, hr₁, -⟩ := hr
    rcases fuel with _ | f
    · simp [drive] at hr₁
    rcases drive_succ_elim hr₁ with ⟨x, hx, -⟩ | ⟨v', hv', -⟩
    · simp at hx
    · simp at hv'
  -- the staged side completes at [0], answering through the ⊥
  have hout : System.output
      ((apply (fun _ => Part.none : ProtocolFn ℕ ℕ ℕ ℕ) S)⊥)
      (([] : List ℕ) ++ [0])
      (by rw [System.dom_fullyDefined]; simp) = none := by
    rw [System.output_fullyDefined]
    exact dif_neg hTundef
  have hA : (0 : ℕ) ∈
      (apply botReactive
        (apply (fun _ => Part.none : ProtocolFn ℕ ℕ ℕ ℕ) S)).1 [0] := by
    rw [apply_toPFun, mem_applyRaw]
    refine ⟨2, ?_⟩
    rw [mem_applyRawAt_iff]
    refine ⟨([0], [0], [none]), ?_, by simp⟩
    simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
    refine ⟨((0 : ℕ), [0], [none]), ?_,
      ([], [0], [none]), by simp, rfl⟩
    have hm1 : Sum.inl (0 : ℕ) ∈ botReactive (([] : List ℕ) ++ [0], []) := by
      simp [botReactive]
    have hm2 : Sum.inr (0 : ℕ) ∈ botReactive (([] : List ℕ) ++ [0], [none]) := by
      simp [botReactive]
    have hstep : ((0 : ℕ), [0], [none]) ∈
        drive botReactive
          (apply (fun _ => Part.none : ProtocolFn ℕ ℕ ℕ ℕ) S) 1
          (([] : List ℕ) ++ [0]) ([0]) ([none]) :=
      drive_mem_answer _ _ hm2 0
    refine drive_mem_query (α := botReactive)
      (S := apply (fun _ => Part.none : ProtocolFn ℕ ℕ ℕ ℕ)
        S)
      (us := ([] : List ℕ) ++ [0]) (xs := []) (ys := []) hm1 ?_
    rw [hout]
    exact hstep
  -- the stacked side stalls at [0]
  have hB : (0 : ℕ) ∉
      (apply (comp botReactive
        (fun _ => Part.none : ProtocolFn ℕ ℕ ℕ ℕ)) S).1 [0] := by
    intro hm
    rw [apply_toPFun, mem_applyRaw] at hm
    obtain ⟨fuel, hm⟩ := hm
    rw [mem_applyRawAt_iff] at hm
    obtain ⟨r, hr, -⟩ := hm
    simp only [driveOuter, Part.mem_bind_iff] at hr
    obtain ⟨r₁, hr₁, -⟩ := hr
    rcases fuel with _ | f
    · simp [drive] at hr₁
    rcases drive_succ_elim hr₁ with ⟨x, hx, -⟩ | ⟨v', hv', -⟩
    · exact comp_botReactive_none _ hx
    · exact comp_botReactive_none _ hv'
  rw [h] at hB
  exact hB hA

end StressTests

end Converter

end RandomSystems
