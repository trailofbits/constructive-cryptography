import RandomSystems.Converter.ConverterDomain
import RandomSystems.DDC.Tensor

/-!
# Direct converter calls

A complete converter input history determines the current outside invocation and the inside
replies it has received so far. The query-count invariant charges each invocation when its
outside query arrives, so it includes a pending inside query and interrupted calls.

The lemmas below are about the existing complete-history and DDC carriers. They introduce no
program state or alternative converter semantics.
-/

namespace SystemAlgebra

/-- The current invocation, read directly from a complete converter input history.
This is the history projection used by the direct-DDC ChaChaPoly model. -/
def currentCall {O J : Type} {U : O → Type} {Y : J → Type} :
    List (Σ l : Two O J, twoFam U Y l) → List (Σ j, Y j) →
      Option ((Σ o, U o) × List (Σ j, Y j))
  | [], _ => none
  | ⟨⟨none, o⟩, x⟩ :: _, replies => some (⟨o, x⟩, replies)
  | ⟨⟨some (), j⟩, y⟩ :: rest, replies => currentCall rest (⟨j, y⟩ :: replies)


/-- Accumulated replies append to the replies of the last outside invocation. -/
lemma currentCall_acc {O J : Type} {U : O → Type} {Y : J → Type}
    (h : List (Σ l : Two O J, twoFam U Y l)) (acc : List (Σ j, Y j)) :
    currentCall h acc = (currentCall h []).map (fun (u, rs) => (u, rs ++ acc)) := by
  induction h generalizing acc with
  | nil => rfl
  | cons x h ih =>
    obtain ⟨⟨_ | ⟨⟩, l⟩, x⟩ := x
    · -- The first outside input in reverse order fixes the invocation.
      rfl
    · -- Prepend this inside reply while scanning back to that outside input.
      simp only [currentCall]
      rw [ih (⟨l, x⟩ :: acc), ih [⟨l, x⟩], Option.map_map]
      simp only [Function.comp_def, List.append_assoc, List.singleton_append]

/-- The newest outside query starts a call; its subsequent inside replies are retained
in their original order, independently of preceding invocations. -/
lemma currentCall_reverse_append_call {O J : Type} {U : O → Type} {Y : J → Type}
    (before : List (Σ l : Two O J, twoFam U Y l)) (u : Σ o, U o)
    (replies : List (Σ j, Y j)) :
    currentCall (before ++ ⟨⟨none, u.1⟩, u.2⟩ ::
      replies.map (fun r => (⟨⟨some (), r.1⟩, r.2⟩ : Σ l, twoFam U Y l))).reverse [] =
      some (u, replies) := by
  -- Scanning back through inside replies reconstructs their chronological order.
  have scan (rs acc : List (Σ j, Y j)) :
      currentCall (rs.map (fun r => (⟨⟨some (), r.1⟩, r.2⟩ : Σ l, twoFam U Y l)) ++
        ⟨⟨none, u.1⟩, u.2⟩ :: before.reverse) acc = some (u, rs.reverse ++ acc) := by
    induction rs generalizing acc with
    | nil => rfl
    | cons r rs ih =>
      simp only [List.map_cons, List.cons_append, currentCall, ih,
        List.reverse_cons, List.append_assoc, List.nil_append, Sigma.eta]
  -- The first outside query encountered ends the scan; older calls are irrelevant.
  simpa only [List.reverse_append, List.reverse_cons, List.map_reverse,
    List.append_assoc, List.singleton_append, List.reverse_reverse, List.append_nil]
    using scan replies.reverse []

/-- A silent complete-history rule identifies the invocation of every nonempty admissible
history. The run length is bounded by the replies recorded in that invocation plus one. -/
lemma currentCall_of_admissible {O J : Type} {U V : O → Type} {X Y : J → Type}
    (a : InsideOutsideSystem O J U V X Y) (hzero : ¬ (a []).Dom)
    (h) (ha : Admissible a h) :
    h = [] ∨ ∃ (u : Σ o, U o) (replies : List (Σ j, Y j)),
      currentCall h.reverse [] = some (u, replies) ∧
      lastOuter h = some u.1 ∧ insideRun a h ≤ replies.length + 1 := by
  classical
  induction h using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton h x ih =>
    obtain ⟨ha0, _, hx⟩ := admissible_snoc.mp ha
    obtain ⟨⟨_ | ⟨⟨⟩⟩, i⟩, x⟩ := x
    · refine Or.inr ⟨⟨i, x⟩, [], ?_, ?_, ?_⟩
      · simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
          currentCall]
      · rw [lastOuter_snoc]; rfl
      · have hrun : insideRun a h = 0 := by
          rcases List.eq_nil_or_concat h with rfl | ⟨h, z, rfl⟩
          · rfl
          · rw [List.concat_eq_append] at hx ⊢
            rw [insideRun, run_snoc, if_neg]
            rintro ⟨y, hy, hi⟩
            unfold Admits at hx
            rw [replyLabel_of_mem _ hy] at hx
            obtain ⟨⟨_ | ⟨⟨⟩⟩, j⟩, y⟩ := y
            · exact absurd hi (by simp only [IsInside, reduceCtorEq, not_false_eq_true])
            · cases hx
        rw [insideRun, run_snoc]
        change run IsInside a h = 0 at hrun
        rw [hrun]
        split_ifs <;> omega
    · rcases ih ha0 with rfl | ⟨u, replies, hc, hl, hr⟩
      · simp only [Admits, replyLabel, hzero, ↓reduceDIte, admitAfter, reduceCtorEq] at hx
      · refine Or.inr ⟨u, replies ++ [⟨i, x⟩], ?_, ?_, ?_⟩
        · simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
            currentCall]
          rw [currentCall_acc, hc]
          rfl
        · rw [lastOuter_snoc, hl]; rfl
        · rw [insideRun, run_snoc]
          change run IsInside a h ≤ replies.length + 1 at hr
          simp only [List.length_append, List.length_singleton]
          split_ifs <;> omega

/-- Charge every invocation for its total number of inside queries. The phase condition
also covers interrupted calls and arbitrary inside replies. -/
lemma currentCall_query_count {O J : Type} {U V : O → Type} {X Y : J → Type}
    (a : InsideOutsideSystem O J U V X Y) (cost : (Σ o, U o) → Nat)
    (hnone : ∀ h, currentCall h.reverse [] = none → a h = Part.none)
    (hphase : ∀ h u replies, currentCall h.reverse [] = some (u, replies) →
      (∃ y, y ∈ a h ∧ IsInside y) → replies.length < cost u)
    (T : List (_ × _)) (hr : Replies a (T.map Prod.fst) (T.map Prod.snd)) :
    (insideQueries (T.map Prod.snd)).length ≤
      ((outsideInputs (T.map Prod.fst)).map cost).sum := by
  let remaining (h : List (Σ l : Two O J, twoFam U Y l)) : Nat :=
    match currentCall h.reverse [] with
    | none => 0
    | some (u, replies) => cost u - (replies.length + 1)
  suffices count : ∀ T : List (_ × _), Replies a (T.map Prod.fst) (T.map Prod.snd) →
      (insideQueries (T.map Prod.snd)).length + remaining (T.map Prod.fst) ≤
        ((outsideInputs (T.map Prod.fst)).map cost).sum by
    exact (Nat.le_add_right _ _).trans (count T hr)
  intro T
  induction T using List.reverseRecOn with
  | nil => intro _; exact Nat.le_refl 0
  | append_singleton T z ih =>
    intro hr
    obtain ⟨x, y⟩ := z
    simp only [List.map_append, List.map_singleton] at hr ⊢
    obtain ⟨hr, hy⟩ := replies_snoc.mp hr
    have hi := ih hr
    have hym := Part.eq_some_iff.mp hy
    rw [insideQueries_append, List.length_append, outsideInputs_append,
      List.map_append, List.sum_append]
    obtain ⟨⟨_ | ⟨⟨⟩⟩, i⟩, x⟩ := x
    · have hc : currentCall ((T.map Prod.fst) ++
          [(⟨⟨none, i⟩, x⟩ : Σ l : Two O J, twoFam U Y l)]).reverse [] =
          some (⟨i, x⟩, []) := by
        simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
          currentCall]
      simp only [remaining, hc, List.length_nil, zero_add, outsideInputs_outside,
        List.map_singleton, List.sum_singleton]
      obtain ⟨⟨_ | ⟨⟨⟩⟩, j⟩, y⟩ := y
      · simp only [insideQueries_outside, List.length_nil]
        omega
      · have hp := hphase _ _ _ hc ⟨_, hym, rfl⟩
        simp only [List.length_nil] at hp
        simp only [insideQueries_inside, List.length_singleton]
        omega
    · have hc : currentCall ((T.map Prod.fst) ++
          [(⟨⟨some (), i⟩, x⟩ : Σ l : Two O J, twoFam U Y l)]).reverse [] =
          (currentCall (T.map Prod.fst).reverse []).map
            (fun (u, rs) => (u, rs ++ [⟨i, x⟩])) := by
        simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
          currentCall]
        exact currentCall_acc _ _
      cases he : currentCall (T.map Prod.fst).reverse [] with
      | none =>
        have hd := hnone _ (by rw [hc, he]; rfl)
        rw [hd] at hym
        exact (Part.notMem_none _ hym).elim
      | some call =>
        obtain ⟨u, replies⟩ := call
        rw [he] at hc
        simp only [Option.map_some] at hc
        simp only [remaining, he] at hi
        simp only [remaining, hc, List.length_append, List.length_singleton]
        obtain ⟨⟨_ | ⟨⟨⟩⟩, j⟩, y⟩ := y
        · simp only [insideQueries_outside, List.length_nil]
          omega
        · have hp := hphase _ _ _ hc ⟨_, hym, rfl⟩
          simp only [List.length_append, List.length_singleton] at hp
          simp only [insideQueries_inside, List.length_singleton, outsideInputs_inside,
            List.map_nil, List.sum_nil]
          omega

/-- An admitted inside reply has exactly the port charge of the preceding pending query. -/
lemma converterAdmits_inside_charge_eq {O J : Type} {U V : O → Type} {X Y : J → Type}
    (cost : J → Nat)
    (h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l)))
    (x : Σ l, twoFam U Y l) (hx : converterAdmits h x) :
    ((insideQueries [x]).map fun z => cost z.1).sum =
      ((insideQueries (h.getLast?.toList.map Prod.snd)).map fun z => cost z.1).sum := by
  cases he : h.getLast? with
  | none =>
    simp only [converterAdmits, he, Option.map_none, admitAfter] at hx
    rcases x with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, x⟩
    · simp only [insideQueries_outside, Option.toList_none, List.map_nil]
      rfl
    · cases hx
  | some z =>
    rcases z with ⟨y, ⟨⟨_ | ⟨⟨⟩⟩, j⟩, z⟩⟩
    · simp only [converterAdmits, he, Option.map_some, admitAfter] at hx
      rcases x with ⟨⟨_ | ⟨⟨⟩⟩, k⟩, x⟩
      · simp only [Option.toList_some, List.map_singleton,
          insideQueries_outside, List.map_nil, List.sum_nil]
      · cases hx
    · simp only [converterAdmits, he, Option.map_some, admitAfter] at hx
      rcases x with ⟨⟨_ | ⟨⟨⟩⟩, k⟩, x⟩
      · cases hx
      · have hk : k = j := by cases hx; rfl
        subst k
        simp only [Option.toList_some, List.map_singleton, insideQueries_inside]

/-- Per-port charges of each partial invocation sum to the outside charge budget. The explicit
admission premise matches each inside reply with the previous pending query's port. -/
lemma currentCall_query_charge {O J : Type} {U V : O → Type} {X Y : J → Type}
    (a : InsideOutsideSystem O J U V X Y) (charge : J → Nat)
    (cost : (Σ o, U o) → Nat)
    (hnone : ∀ h, currentCall h.reverse [] = none → a h = Part.none)
    (hphase : ∀ h u replies y, currentCall h.reverse [] = some (u, replies) → y ∈ a h →
      (replies.map fun r => charge r.1).sum +
        ((insideQueries [y]).map fun q => charge q.1).sum ≤ cost u)
    (T : List (_ × _)) (hr : Replies a (T.map Prod.fst) (T.map Prod.snd))
    (ha : Admitted converterAdmits T) :
    ((insideQueries (T.map Prod.snd)).map fun q => charge q.1).sum ≤
      ((outsideInputs (T.map Prod.fst)).map cost).sum := by
  let pending (T : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))) : Nat :=
    ((insideQueries (T.getLast?.toList.map Prod.snd)).map fun q => charge q.1).sum
  let remaining (T : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))) : Nat :=
    match currentCall (T.map Prod.fst).reverse [] with
    | none => 0
    | some (u, replies) => cost u - ((replies.map fun r => charge r.1).sum + pending T)
  suffices hbound : ∀ T : List (_ × _),
      Replies a (T.map Prod.fst) (T.map Prod.snd) → Admitted converterAdmits T →
      ((insideQueries (T.map Prod.snd)).map fun q => charge q.1).sum + remaining T ≤
        ((outsideInputs (T.map Prod.fst)).map cost).sum from
    (Nat.le_add_right _ _).trans (hbound T hr ha)
  intro T
  induction T using List.reverseRecOn with
  | nil => intro _ _; exact Nat.le_refl 0
  | append_singleton T z ih =>
    intro hr ha
    obtain ⟨x, y⟩ := z
    obtain ⟨ha, hx⟩ := admitted_snoc.mp ha
    simp only [List.map_append, List.map_singleton] at hr ⊢
    obtain ⟨hr, hy⟩ := replies_snoc.mp hr
    have hi := ih hr ha
    have hym := Part.eq_some_iff.mp hy
    have hcharge := converterAdmits_inside_charge_eq charge T x hx
    change ((insideQueries [x]).map fun r => charge r.1).sum = pending T at hcharge
    rw [insideQueries_append, List.map_append, List.sum_append, outsideInputs_append,
      List.map_append, List.sum_append]
    rcases x with ⟨⟨_ | ⟨⟨⟩⟩, i⟩, x⟩
    · have hc : currentCall ((T.map Prod.fst) ++
          [(⟨⟨none, i⟩, x⟩ : Σ l, twoFam U Y l)]).reverse [] = some (⟨i, x⟩, []) := by
        simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
          currentCall]
      have hp := hphase _ _ _ y hc hym
      simp only [List.map_nil, List.sum_nil, Nat.zero_add] at hp
      simp only [remaining, List.map_append, List.map_singleton, hc, pending,
        List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.toList_some,
        List.map_nil, List.sum_nil, Nat.zero_add, outsideInputs_outside,
        List.sum_singleton]
      omega
    · have hc : currentCall ((T.map Prod.fst) ++
          [(⟨⟨some (), i⟩, x⟩ : Σ l, twoFam U Y l)]).reverse [] =
          (currentCall (T.map Prod.fst).reverse []).map
            (fun (u, rs) => (u, rs ++ [⟨i, x⟩])) := by
        simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
          currentCall]
        exact currentCall_acc _ _
      cases he : currentCall (T.map Prod.fst).reverse [] with
      | none =>
        rw [hnone _ (by rw [hc, he]; rfl)] at hym
        exact (Part.notMem_none _ hym).elim
      | some call =>
        obtain ⟨u, replies⟩ := call
        rw [he] at hc
        simp only [Option.map_some] at hc
        have hp := hphase _ _ _ y hc hym
        simp only [List.map_append, List.map_singleton, List.sum_append,
          List.sum_singleton] at hp
        simp only [insideQueries_inside, List.map_singleton, List.sum_singleton] at hcharge
        simp only [remaining, he] at hi
        simp only [remaining, List.map_append, List.map_singleton, hc, pending,
          List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.toList_some,
          List.sum_append, List.sum_singleton, outsideInputs_inside, List.map_nil, List.sum_nil]
        omega


/-- The current invocation's outside input occurs in the complete outside-input history. -/
lemma currentCall_mem_outsideInputs {O J : Type} {U : O → Type} {Y : J → Type}
    (h : List (Σ l, twoFam U Y l)) (u : Σ o, U o) (rs : List (Σ j, Y j))
    (hc : currentCall h.reverse [] = some (u, rs)) : u ∈ outsideInputs h := by
  induction h using List.reverseRecOn generalizing u rs with
  | nil => cases hc
  | append_singleton h x ih =>
    rcases x with ⟨⟨_ | ⟨⟨⟩⟩, i⟩, x⟩
    · simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
        currentCall, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      rw [outsideInputs_append, outsideInputs_outside]
      exact List.mem_append_right _ List.mem_cons_self
    · simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
        currentCall] at hc
      rw [currentCall_acc] at hc
      cases he : currentCall h.reverse [] with
      | none => rw [he] at hc; cases hc
      | some call =>
        obtain ⟨v, replies⟩ := call
        rw [he] at hc
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        rw [outsideInputs_append, outsideInputs_inside, List.append_nil]
        exact ih v replies he


/-! ## A complete-history rule for dependent calls -/

/-- Read the current invocation and either return at its outside label or issue the next
inside query. The rule has no state beyond the complete input history.

Jost, Definition 2.2.2, printed pp. 17–18: “Upon an input at an outside interface, the
converter is allowed to make a bounded number of queries to the inside interfaces ... before
returning a value at the queried interface.” The bound is certified separately. -/
def callRule {O J : Type} {U V : O → Type} {X Y : J → Type}
    (call : (u : Σ o, U o) → List (Σ j, Y j) → V u.1 ⊕ (Σ j, X j)) :
    InsideOutsideSystem O J U V X Y :=
  fun h => match currentCall h.reverse [] with
    | none => Part.none
    | some (u, replies) =>
      match call u replies with
      | .inl v => Part.some ⟨⟨none, u.1⟩, v⟩
      | .inr x => Part.some ⟨⟨some (), x.1⟩, x.2⟩

/-- The direct rule answers exactly when an outside invocation has begun. -/
lemma callRule_dom_iff {O J : Type} {U V : O → Type} {X Y : J → Type}
    (call : (u : Σ o, U o) → List (Σ j, Y j) → V u.1 ⊕ (Σ j, X j)) (h) :
    (callRule call h).Dom ↔ (currentCall h.reverse []).isSome := by
  cases hc : currentCall h.reverse [] with
  | none => simp [callRule, hc]
  | some ur =>
    obtain ⟨u, replies⟩ := ur
    cases hstep : call u replies with
    | inl v => simp [callRule, hc, hstep]
    | inr x => simp [callRule, hc, hstep]

/-- An inside output is exactly the right branch of the current call rule. -/
lemma callRule_inside_iff {O J : Type} {U V : O → Type} {X Y : J → Type}
    (call : (u : Σ o, U o) → List (Σ j, Y j) → V u.1 ⊕ (Σ j, X j))
    (h) (u : Σ o, U o) (replies : List (Σ j, Y j))
    (hc : currentCall h.reverse [] = some (u, replies)) :
    (∃ y, y ∈ callRule call h ∧ IsInside y) ↔ (call u replies).isRight = true := by
  cases hs : call u replies with
  | inl v => simp [callRule, hc, hs, IsInside]
  | inr x => simp [callRule, hc, hs, IsInside]

/-- A phase-bounded direct call is a responsive canonical DDC. The phase contract holds for
all reply histories, whether or not they come from a fixed inside function. -/
lemma callRule_isResponsiveDDC {O J : Type} {U V : O → Type} {X Y : J → Type}
    (call : (u : Σ o, U o) → List (Σ j, Y j) → V u.1 ⊕ (Σ j, X j))
    (cost : (Σ o, U o) → Nat) (bound : Nat)
    (hphase : ∀ u replies, (call u replies).isRight = true → replies.length < cost u)
    (hbound : ∀ u, cost u ≤ bound) : IsResponsiveDDC bound (canon (callRule call)) := by
  have hzero : ¬ (callRule call ([] : List (Σ l, twoFam U Y l))).Dom := by
    simp [callRule, currentCall]
  refine canon_isResponsiveDDC hzero ?_ ?_ ?_
  · -- Every nonempty admissible history has a current outside invocation.
    intro h ha hne
    obtain ⟨u, replies, hc, _, _⟩ :=
      (currentCall_of_admissible (callRule call) hzero h ha).resolve_left hne
    rw [callRule_dom_iff, hc]
    rfl
  · -- During an inside phase, the pending query fits within that invocation's cost.
    intro h ha hd
    obtain ⟨u, replies, hc, _, hr⟩ :=
      (currentCall_of_admissible (callRule call) hzero h ha).resolve_left
        (fun he => hzero (he ▸ hd))
    by_cases hi : ∃ y, y ∈ callRule call h ∧ IsInside y
    · have hp := hphase u replies ((callRule_inside_iff call h u replies hc).mp hi)
      exact hr.trans ((Nat.succ_le_iff.mpr hp).trans (hbound u))
    · -- A final outside reply resets the consecutive inside run.
      rcases List.eq_nil_or_concat h with rfl | ⟨h, z, rfl⟩
      · exact Nat.zero_le _
      · rw [List.concat_eq_append] at hi ⊢
        rw [insideRun, run_snoc, if_neg hi]
        exact Nat.zero_le _
  · -- The result label is the label of the current outside invocation.
    intro h y o ha hy ho
    obtain ⟨u, replies, hc, hl, _⟩ :=
      (currentCall_of_admissible (callRule call) hzero h ha).resolve_left
        (fun he => hzero (he ▸ Part.dom_iff_mem.mpr ⟨y, hy⟩))
    cases hs : call u replies with
    | inl v =>
      simp only [callRule, hc, hs, Part.mem_some_iff] at hy
      subst y
      have hlabel : u.1 = o := by cases u with | mk i x => cases ho; rfl
      simpa only [hlabel] using hl
    | inr x =>
      simp only [callRule, hc, hs, Part.mem_some_iff] at hy
      subst y
      cases ho

/-- Every completed or pending direct-call transcript spends at most the costs already
charged to its outside invocations. -/
lemma callRule_query_count {O J : Type} {U V : O → Type} {X Y : J → Type}
    (call : (u : Σ o, U o) → List (Σ j, Y j) → V u.1 ⊕ (Σ j, X j))
    (cost : (Σ o, U o) → Nat)
    (hphase : ∀ u replies, (call u replies).isRight = true → replies.length < cost u)
    (T : List (_ × _)) (hr : Replies (callRule call) (T.map Prod.fst) (T.map Prod.snd)) :
    (insideQueries (T.map Prod.snd)).length ≤
      ((outsideInputs (T.map Prod.fst)).map cost).sum := by
  -- Apply the reservation invariant to the raw rule; no functional consistency is needed.
  apply currentCall_query_count _ _ _ _ T hr
  · intro h hc
    simp only [callRule, hc]
  · intro h u replies hc hi
    exact hphase u replies ((callRule_inside_iff call h u replies hc).mp hi)

/-- Canonicalize the complete-history call rule, then restrict its outside input history to
`F`. The raw rule is never exposed as a DDC. -/
noncomputable def callConverter {O J : Type} {U V : O → Type} {X Y : J → Type}
    (call : (u : Σ o, U o) → List (Σ j, Y j) → V u.1 ⊕ (Σ j, X j))
    (F : List (Σ o, U o) → Prop) : InsideOutsideSystem O J U V X Y :=
  filterDom (fun h => outsideInputs h = [] ∨ F (outsideInputs h)) (canon (callRule call))

/-- The charged outside domain implies the inside query budget. Any further inside-domain
condition `P` remains an explicit obligation on the actual converter transcripts. -/
lemma callConverter_isDDCFrom {O J : Type} {U V : O → Type} {X Y : J → Type}
    (call : (u : Σ o, U o) → List (Σ j, Y j) → V u.1 ⊕ (Σ j, X j))
    (cost : (Σ o, U o) → Nat) (bound work : Nat)
    (F : List (Σ o, U o) → Prop) (P : List (Σ j, X j) → Prop)
    (hphase : ∀ u replies, (call u replies).isRight = true → replies.length < cost u)
    (hbound : ∀ u, cost u ≤ bound)
    (hF : ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (hwork : ∀ us, F us → (us.map cost).sum ≤ work)
    (hP : ∀ T : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l)),
      Replies (callConverter call F) (T.map Prod.fst) (T.map Prod.snd) →
      insideQueries (T.map Prod.snd) ≠ [] → P (insideQueries (T.map Prod.snd))) :
    IsDDCFrom (fun qs => qs ≠ [] ∧ qs.length ≤ work ∧ P qs) F bound
      (callConverter call F) := by
  -- Canonical responsiveness and the outside filter establish the exact converter domain.
  apply (callRule_isResponsiveDDC call cost bound hphase hbound).isDDCFrom_filterDom hF
  intro T hr
  by_cases hnil : T.map Prod.fst = []
  · have hT : T = [] := List.map_eq_nil_iff.mp hnil
    subst T
    exact Or.inl rfl
  -- Forget the filter only for the raw call-count invariant.
  have houtside := ((filterDom_dom _ _ _).mp (hr.dom hnil)).1
  have hraw := hr.mono fun h y hy => canon_mem ((filterDom_mem_iff _ _ h y).mp hy).2
  have hcount := callRule_query_count call cost hphase T hraw
  have hlength : (insideQueries (T.map Prod.snd)).length ≤ work := by
    rcases houtside with he | hf
    · rw [he] at hcount
      simp only [List.map_nil, List.sum_nil] at hcount
      exact hcount.trans (Nat.zero_le _)
    · exact hcount.trans (hwork _ hf)
  by_cases hi : insideQueries (T.map Prod.snd) = []
  · exact Or.inl hi
  · exact Or.inr ⟨hi, hlength, hP T hr hi⟩

end SystemAlgebra
