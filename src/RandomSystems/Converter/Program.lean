import RandomSystems.Converter.ConverterDomain

/-!
# Deterministic programs

A deterministic program answers an outside query from its private state. From the state, the
query and the inside exchanges of the current invocation, it computes either its reply and its
next state, or its next inside query. Run over the inputs it receives, it is a responsive DDC:
it answers every admissible input, and it makes at most `b` inside queries per invocation when
its body does.

## Main definitions

* `Program S O J U V X Y`: deterministic oracle bodies
* `Program.Bounded b P`, `Program.Costs cost P`: at most `b`, and exactly `cost u`, inside queries
  per invocation
* `Program.PortPreserving ι P`: along the partial port map `ι`, an invocation at `o` queries the
  labels `ι o'` only at `ι o`, at most once, and none of them when `ι o = none`
* `Program.step`, `Program.after`: the program run over its inputs
* `DDC.ofProgram s P`: the converter of `P` started in the state `s`
* `DDC.ofProgramOn s P F`: that converter on the outside domain `F`

## Main results

* `DDC.ofProgram_dom`: the converter answers exactly the inputs its run admits
* `DDC.ofProgram_isResponsiveDDC`: a bounded program is a responsive DDC
* `DDC.ofProgramOn_isDDCFrom`: on an outside domain, a DDC from every inside domain containing
  its inside queries
* `DDC.insideQueries_length_le`, `DDC.insideQueries_length_le_of_budget`: `b` inside queries per
  invocation, `b * q` on `q` outside queries
* `DDC.insideQueries_length_le_of_costs`: exact costs bound the inside queries by the total cost
* `DDC.insideQueries_restrict_length_le`: a port-preserving program queries `j = ι o` at most as
  often as it is queried at `o`
-/

namespace SystemAlgebra

open Classical

variable {S O J : Type} {U V : O → Type} {X Y : J → Type}

/-- A deterministic oracle body: from the private state, the outside query and the inside
exchanges of the current invocation, the reply with the next state, or the next inside
query. -/
abbrev Program (S O J : Type) (U V : O → Type) (X Y : J → Type) :=
  S → (o : O) → U o → List ((Σ j, X j) × (Σ j, Y j)) → (S × V o) ⊕ (Σ j, X j)

namespace Program

/-- The inside exchanges that the body `f` of an invocation made itself: each recorded query is
its query on the exchanges before it, and each reply comes at the queried label. -/
def ExchangesOf {A : Type} (f : List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j))
    (h : List ((Σ j, X j) × (Σ j, Y j))) : Prop :=
  ∀ i (hi : i < h.length), f (h.take i) = .inr h[i].1 ∧ h[i].2.1 = h[i].1.1

/-- A body making at most `b` inside queries along its own exchanges. -/
def CallBound {A : Type} (b : ℕ) (f : List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j)) : Prop :=
  ∀ h q, ExchangesOf f h → f h = .inr q → h.length < b

/-- A body making exactly `n` inside queries along its own exchanges. -/
def CallCost {A : Type} (n : ℕ) (f : List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j)) : Prop :=
  ∀ h, ExchangesOf f h → (∀ q, f h = .inr q → h.length < n) ∧ (∀ a, f h = .inl a → h.length = n)

/-- The inside exchanges of an invocation that the program made itself. -/
abbrev Consistent (P : Program S O J U V X Y) (s : S) (o : O) (u : U o) :
    List ((Σ j, X j) × (Σ j, Y j)) → Prop :=
  ExchangesOf (P s o u)

/-- At most `b` inside queries per invocation. -/
def Bounded (b : ℕ) (P : Program S O J U V X Y) : Prop :=
  ∀ s o u, CallBound b (P s o u)

theorem consistent_nil (P : Program S O J U V X Y) (s : S) (o : O) (u : U o) :
    P.Consistent s o u [] := fun i hi => absurd hi (Nat.not_lt_zero i)

theorem Consistent.snoc {P : Program S O J U V X Y} {s : S} {o : O} {u : U o}
    {h : List ((Σ j, X j) × (Σ j, Y j))} (hc : P.Consistent s o u h) {q : Σ j, X j}
    (hq : P s o u h = .inr q) (v : Y q.1) : P.Consistent s o u (h ++ [(q, ⟨q.1, v⟩)]) := by
  intro i hi
  rw [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [List.take_append_of_le_length hi.le, List.getElem_append_left hi]
    exact hc i hi
  · rw [List.take_left' rfl, List.getElem_append_right (le_refl _)]
    simpa using hq

/-- Each invocation on the outside query `⟨o, u⟩` makes exactly `cost ⟨o, u⟩` inside queries. -/
def Costs (cost : (Σ o, U o) → ℕ) (P : Program S O J U V X Y) : Prop :=
  ∀ s o u, CallCost (cost ⟨o, u⟩) (P s o u)

/-- **Port preservation** of an invocation at `o` along the partial port map `ι`: a query at a
label `ι o'` is at `ι o`, and it is the invocation's first query there. -/
def PreservesAt {A : Type} (ι : O → Option J) (o : O)
    (f : List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j)) : Prop :=
  ∀ h q, ExchangesOf f h → f h = .inr q → ∀ o', ι o' = some q.1 → o' = o ∧ ∀ e ∈ h, e.1.1 ≠ q.1

/-- Each invocation at `o` makes at most one query at the labels `ι o'`, and at `ι o`; none when
`ι o = none`. -/
def PortPreserving (ι : O → Option J) (P : Program S O J U V X Y) : Prop :=
  ∀ s o u, PreservesAt ι o (P s o u)

/-- Between invocations a program holds its state; during one it also holds the outside query,
the inside exchanges so far, and the pending inside query. -/
inductive Mode (S O J : Type) (U : O → Type) (X Y : J → Type)
  | idle (s : S)
  | busy (o : O) (s : S) (u : U o) (h : List ((Σ j, X j) × (Σ j, Y j))) (q : Σ j, X j)

/-- The output of the body and the mode it leaves. -/
def emit (P : Program S O J U V X Y) (s : S) (o : O) (u : U o)
    (h : List ((Σ j, X j) × (Σ j, Y j))) : Mode S O J U X Y × (Σ l, twoFam V X l) :=
  match P s o u h with
  | .inl (s', v) => (.idle s', ⟨⟨none, o⟩, v⟩)
  | .inr q => (.busy o s u h q, ⟨⟨some (), q.1⟩, q.2⟩)

/-- One input: an outside query starts an invocation, and the reply to the pending inside query
continues it; no other input is admitted. -/
noncomputable def step (P : Program S O J U V X Y) :
    Mode S O J U X Y → (Σ l, twoFam U Y l) → Option (Mode S O J U X Y × (Σ l, twoFam V X l))
  | .idle s, ⟨⟨none, o⟩, u⟩ => some (P.emit s o u [])
  | .busy o s u h q, ⟨⟨some (), j⟩, y⟩ =>
    if j = q.1 then some (P.emit s o u (h ++ [(q, ⟨j, y⟩)])) else none
  | _, _ => none

/-- The mode reached from `m` after a sequence of inputs, if every input was admitted. -/
noncomputable def run (P : Program S O J U V X Y) (m : Option (Mode S O J U X Y))
    (xs : List (Σ l, twoFam U Y l)) : Option (Mode S O J U X Y) :=
  xs.foldl (fun m x => m.bind fun m => (P.step m x).map Prod.fst) m

/-- The mode after a sequence of inputs, started idle in the state `s`. -/
noncomputable def after (P : Program S O J U V X Y) (s : S) (xs : List (Σ l, twoFam U Y l)) :
    Option (Mode S O J U X Y) :=
  P.run (some (.idle s)) xs

/-- The labels a mode admits: any outside label when idle, the pending query's label when
busy. -/
def Mode.AdmitsLabel : Mode S O J U X Y → Two O J → Prop
  | .idle _, l => l.1 = none
  | .busy _ _ _ _ q, l => l = ⟨some (), q.1⟩

/-- The inside queries made so far in the current invocation. -/
def Mode.pending : Mode S O J U X Y → ℕ
  | .idle _ => 0
  | .busy _ _ _ h _ => h.length + 1

/-- The outside label of the current invocation. -/
def Mode.owner : Mode S O J U X Y → Option O
  | .idle _ => none
  | .busy o _ _ _ _ => some o

/-- The inside queries the current invocation still owes by its cost. -/
def Mode.owed (cost : (Σ o, U o) → ℕ) : Mode S O J U X Y → ℕ
  | .idle _ => 0
  | .busy o _ u h _ => cost ⟨o, u⟩ - (h.length + 1)

/-- The inside queries the current invocation may still make within `b`. -/
def Mode.credit (b : ℕ) : Mode S O J U X Y → ℕ
  | .idle _ => 0
  | .busy _ _ _ h _ => b - (h.length + 1)

/-- The query at `j` the current invocation may still make: one while an invocation at `o` has
not made it. -/
noncomputable def Mode.portCredit (o : O) (j : J) : Mode S O J U X Y → ℕ
  | .idle _ => 0
  | .busy o' _ _ h q => if o' = o ∧ (∀ e ∈ h, e.1.1 ≠ j) ∧ q.1 ≠ j then 1 else 0

/-- A busy mode waits for the reply to the query its body made on exchanges it made itself. -/
def Mode.Sound (P : Program S O J U V X Y) : Mode S O J U X Y → Prop
  | .idle _ => True
  | .busy o s u h q => P.Consistent s o u h ∧ P s o u h = .inr q

variable (P : Program S O J U V X Y)

@[simp] theorem run_nil (m : Option (Mode S O J U X Y)) : P.run m [] = m := rfl

@[simp] theorem run_none (xs : List (Σ l, twoFam U Y l)) : P.run none xs = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih

theorem run_append (m : Option (Mode S O J U X Y)) (xs ys : List (Σ l, twoFam U Y l)) :
    P.run m (xs ++ ys) = P.run (P.run m xs) ys := by
  simp only [run, List.foldl_append]

theorem run_snoc (m : Option (Mode S O J U X Y)) (xs : List (Σ l, twoFam U Y l))
    (x : Σ l, twoFam U Y l) :
    P.run m (xs ++ [x]) = (P.run m xs).bind fun m => (P.step m x).map Prod.fst := by
  rw [run_append]; rfl

@[simp] theorem after_nil (s : S) : P.after s [] = some (.idle s) := rfl

theorem after_snoc (s : S) (xs : List (Σ l, twoFam U Y l)) (x : Σ l, twoFam U Y l) :
    P.after s (xs ++ [x]) = (P.after s xs).bind fun m => (P.step m x).map Prod.fst :=
  P.run_snoc _ xs x

theorem after_isSome_of_append (s : S) {xs ys : List (Σ l, twoFam U Y l)}
    (h : (P.after s (xs ++ ys)).isSome) : (P.after s xs).isSome := by
  rw [after, run_append] at h
  cases hx : P.run (some (.idle s)) xs with
  | none => rw [hx, run_none] at h; exact absurd h (by simp)
  | some m => rw [after, hx]; rfl

theorem step_isSome_iff (m : Mode S O J U X Y) (z : Σ l, twoFam U Y l) :
    (P.step m z).isSome ↔ m.AdmitsLabel z.1 := by
  rcases m with s | ⟨o, s, u, h, q⟩ <;> rcases z with ⟨⟨_ | ⟨⟨⟩⟩, i⟩, x⟩
  · simp [step, Mode.AdmitsLabel]
  · simp [step, Mode.AdmitsLabel]
  · simp [step, Mode.AdmitsLabel]
  · by_cases hi : i = q.1
    · simp [step, Mode.AdmitsLabel, hi]
    · simp [step, Mode.AdmitsLabel, hi]

/-- After an output, the next admitted labels are those of the new mode. -/
theorem admitAfter_emit (s : S) (o : O) (u : U o) (h : List ((Σ j, X j) × (Σ j, Y j)))
    (l : Two O J) :
    admitAfter (some (P.emit s o u h).2.1) l ↔ (P.emit s o u h).1.AdmitsLabel l := by
  unfold emit
  cases P s o u h with
  | inl a => rfl
  | inr q => rfl

/-- A step starts an invocation from an idle mode on an outside query, or continues one on the
reply to its pending query. -/
theorem step_cases {m m' : Mode S O J U X Y} {z : Σ l, twoFam U Y l} {y : Σ l, twoFam V X l}
    (hs : P.step m z = some (m', y)) :
    (∃ s o u, m = .idle s ∧ z = ⟨⟨none, o⟩, u⟩ ∧ (m', y) = P.emit s o u []) ∨
      ∃ o s u h q, ∃ v : Y q.1, m = .busy o s u h q ∧ z = ⟨⟨some (), q.1⟩, v⟩ ∧
        (m', y) = P.emit s o u (h ++ [(q, ⟨q.1, v⟩)]) := by
  rcases m with s | ⟨o, s, u, h, q⟩ <;> rcases z with ⟨⟨_ | ⟨⟨⟩⟩, i⟩, x⟩
  · exact Or.inl ⟨s, i, x, rfl, rfl, (Option.some.inj hs).symm⟩
  · simp [step] at hs
  · simp [step] at hs
  · by_cases hi : i = q.1
    · subst hi
      simp only [step, if_true] at hs
      exact Or.inr ⟨o, s, u, h, q, x, rfl, rfl, (Option.some.inj hs).symm⟩
    · simp [step, hi] at hs

/-- The body's result determines the output and the mode. -/
theorem emit_cases (s : S) (o : O) (u : U o) (h : List ((Σ j, X j) × (Σ j, Y j))) :
    (∃ s' v, P s o u h = .inl (s', v) ∧ P.emit s o u h = (.idle s', ⟨⟨none, o⟩, v⟩)) ∨
      ∃ q, P s o u h = .inr q ∧ P.emit s o u h = (.busy o s u h q, ⟨⟨some (), q.1⟩, q.2⟩) := by
  unfold emit
  cases hP : P s o u h with
  | inl a => exact Or.inl ⟨a.1, a.2, rfl, rfl⟩
  | inr q => exact Or.inr ⟨q, rfl, rfl⟩

theorem after_snoc_eq_some (s : S) (xs : List (Σ l, twoFam U Y l)) (x : Σ l, twoFam U Y l)
    (m' : Mode S O J U X Y) :
    P.after s (xs ++ [x]) = some m' ↔
      ∃ m y, P.after s xs = some m ∧ P.step m x = some (m', y) := by
  rw [after_snoc]
  cases P.after s xs with
  | none => simp
  | some m =>
    cases hs : P.step m x with
    | none => simp
    | some r => simp [eq_comm]

end Program

/-- The converter of a program started in the state `s`: its reply to the last input of a
history, computed from the mode after the earlier inputs. -/
noncomputable def DDC.ofProgram (s : S) (P : Program S O J U V X Y) : InsideOutsideSystem O J U V X Y :=
  fun xs => Part.ofOption (xs.getLast?.bind fun x =>
    (P.after s xs.dropLast).bind fun m => (P.step m x).map Prod.snd)

namespace DDC

variable (s : S) (P : Program S O J U V X Y)

@[simp] theorem ofProgram_nil : DDC.ofProgram s P [] = Part.none := rfl

theorem mem_ofProgram_snoc (xs : List (Σ l, twoFam U Y l)) (x : Σ l, twoFam U Y l)
    (y : Σ l, twoFam V X l) :
    y ∈ DDC.ofProgram s P (xs ++ [x]) ↔
      ∃ m m', P.after s xs = some m ∧ P.step m x = some (m', y) := by
  simp only [DDC.ofProgram, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil x []),
    List.getLast?_singleton, Option.bind_some, List.dropLast_concat, Part.mem_ofOption]
  cases P.after s xs with
  | none => simp
  | some m =>
    cases hs : P.step m x with
    | none => simp
    | some r => simp [eq_comm]

theorem ofProgram_snoc (xs : List (Σ l, twoFam U Y l)) (x : Σ l, twoFam U Y l) :
    DDC.ofProgram s P (xs ++ [x]) =
      Part.ofOption ((P.after s xs).bind fun m => (P.step m x).map Prod.snd) := by
  simp [DDC.ofProgram]

/-- **The converter answers exactly the inputs its run admits.** -/
theorem ofProgram_dom (xs : List (Σ l, twoFam U Y l)) :
    (DDC.ofProgram s P xs).Dom ↔ xs ≠ [] ∧ (P.after s xs).isSome := by
  rcases List.eq_nil_or_concat xs with rfl | ⟨xs, x, rfl⟩
  · simp
  · rw [List.concat_eq_append, ofProgram_snoc, Program.after_snoc]
    simp only [Part.ofOption_dom, ne_eq, List.append_eq_nil_iff, List.cons_ne_self, and_false,
      not_false_eq_true, true_and]
    cases P.after s xs with
    | none => simp
    | some m => cases P.step m x <;> simp

variable {s P}

/-- The reply to an admitted history is the output of its last step. -/
theorem ofProgram_mem_iff {xs : List (Σ l, twoFam U Y l)} {x : Σ l, twoFam U Y l}
    {y y' : Σ l, twoFam V X l} (hy : y ∈ DDC.ofProgram s P (xs ++ [x])) :
    y' ∈ DDC.ofProgram s P (xs ++ [x]) ↔ y' = y :=
  ⟨fun hy' => Part.mem_unique hy' hy, fun he => he ▸ hy⟩

/-- **Invariants of the run.** After an admitted history the mode waits for its body's query,
counts the inside queries of the current invocation, knows that invocation's outside label, and
admits exactly the labels the last reply admits. -/
theorem after_invariant {xs : List (Σ l, twoFam U Y l)} {m : Program.Mode S O J U X Y}
    (hm : P.after s xs = some m) :
    m.Sound P ∧ insideRun (DDC.ofProgram s P) xs = m.pending ∧
      (∀ o, m.owner = some o → lastOuter xs = some o) ∧
      (∀ l, admitAfter (replyLabel (DDC.ofProgram s P) xs) l ↔ m.AdmitsLabel l) := by
  induction xs using List.reverseRecOn generalizing m with
  | nil =>
    obtain rfl : m = .idle s := (Option.some.inj hm).symm
    refine ⟨trivial, by simp [insideRun, Program.Mode.pending], by simp [Program.Mode.owner],
      fun l => ?_⟩
    simp [replyLabel, Program.Mode.AdmitsLabel, admitAfter]
  | append_singleton xs x ih =>
    obtain ⟨m₀, y, h₀, hs⟩ := (Program.after_snoc_eq_some P s xs x m).mp hm
    obtain ⟨sound, runEq, owner, -⟩ := ih h₀
    have hy : y ∈ DDC.ofProgram s P (xs ++ [x]) :=
      (mem_ofProgram_snoc s P xs x y).mpr ⟨m₀, m, h₀, hs⟩
    have hrun : insideRun (DDC.ofProgram s P) (xs ++ [x]) =
        if IsInside y then insideRun (DDC.ofProgram s P) xs + 1 else 0 := by
      rw [insideRun, run_snoc]
      congr 1
      exact propext ⟨fun ⟨y', hy', hi⟩ => (ofProgram_mem_iff hy).mp hy' ▸ hi,
        fun hi => ⟨y, hy, hi⟩⟩
    have hlabel : replyLabel (DDC.ofProgram s P) (xs ++ [x]) = some y.1 := replyLabel_of_mem _ hy
    rw [hrun, hlabel, lastOuter_snoc]
    rcases Program.step_cases P hs with ⟨s', o, u, rfl, rfl, he⟩ | ⟨o, s', u, h, q, v, rfl, rfl, he⟩
    · rcases Program.emit_cases P s' o u [] with ⟨s'', w, _, hE⟩ | ⟨q, hP, hE⟩
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact ⟨trivial, by simp [IsInside, Program.Mode.pending],
          by simp [Program.Mode.owner], fun l => by
            simp [admitAfter, Program.Mode.AdmitsLabel]⟩
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        refine ⟨⟨Program.consistent_nil P s' o u, hP⟩, ?_, fun o' ho => ?_, fun l => ?_⟩
        · simp only [IsInside, if_true, runEq]
          simp [Program.Mode.pending]
        · simp only [Program.Mode.owner, Option.some.injEq] at ho
          subst ho
          rfl
        · simp [admitAfter, Program.Mode.AdmitsLabel]
    · rcases Program.emit_cases P s' o u (h ++ [(q, ⟨q.1, v⟩)]) with
          ⟨s'', w, _, hE⟩ | ⟨q', hP, hE⟩
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact ⟨trivial, by simp [IsInside, Program.Mode.pending],
          by simp [Program.Mode.owner], fun l => by
            simp [admitAfter, Program.Mode.AdmitsLabel]⟩
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        refine ⟨⟨sound.1.snoc sound.2 v, hP⟩, ?_, fun o' ho => ?_, fun l => ?_⟩
        · simp only [IsInside, if_true, runEq]
          simp [Program.Mode.pending]
        · simp only [Program.Mode.owner, Option.some.injEq] at ho
          subst ho
          simpa [outerOf] using owner o rfl
        · simp [admitAfter, Program.Mode.AdmitsLabel]

/-- **A bounded program is a responsive DDC.** -/
theorem ofProgram_isResponsiveDDC {b : ℕ} (hP : P.Bounded b) :
    IsResponsiveDDC b (DDC.ofProgram s P) where
  dds := ⟨by simp [SilentAtEmpty], fun p h hp hne hd => by
    obtain ⟨e, rfl⟩ := hp
    rw [ofProgram_dom] at hd ⊢
    exact ⟨hne, P.after_isSome_of_append s hd.2⟩⟩
  admits h z hd := by
    obtain ⟨-, hz⟩ := (ofProgram_dom s P (h ++ [z])).mp hd
    obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp hz
    obtain ⟨m, y, hm, hs⟩ := (Program.after_snoc_eq_some P s h z m').mp hm'
    exact ((after_invariant hm).2.2.2 z.1).mpr
      ((P.step_isSome_iff m z).mp (by rw [hs]; rfl))
  bound h hd := by
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp ((ofProgram_dom s P h).mp hd).2
    obtain ⟨sound, runEq, -, -⟩ := after_invariant hm
    rw [runEq]
    rcases m with s' | ⟨o, s', u, h', q⟩
    · exact Nat.zero_le _
    · exact hP s' o u h' q sound.1 sound.2
  responsive h ha hne := by
    rw [ofProgram_dom]
    refine ⟨hne, ?_⟩
    induction h using List.reverseRecOn with
    | nil => rfl
    | append_singleton h z ih =>
      obtain ⟨ha', hd, hz⟩ := admissible_snoc.mp ha
      have hh : (P.after s h).isSome := by
        by_cases hn : h = []
        · subst hn; rfl
        · exact ((ofProgram_dom s P h).mp (hd hn)).2
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hh
      have hadm := ((after_invariant hm).2.2.2 z.1).mp hz
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp ((P.step_isSome_iff m z).mpr hadm)
      rw [Program.after_snoc, hm]
      simp [hr]
  replies h y o hy hl := by
    rcases List.eq_nil_or_concat h with rfl | ⟨h, x, rfl⟩
    · simp at hy
    rw [List.concat_eq_append] at hy ⊢
    obtain ⟨m, m', hm, hs⟩ := (mem_ofProgram_snoc s P h x y).mp hy
    have owner := (after_invariant hm).2.2.1
    rw [lastOuter_snoc]
    rcases Program.step_cases P hs with ⟨s', o', u, rfl, rfl, he⟩ | ⟨o', s', u, h', q, v, rfl, rfl, he⟩
    · rcases Program.emit_cases P s' o' u [] with ⟨s'', w, _, hE⟩ | ⟨q, _, hE⟩
      · rw [hE] at he
        obtain ⟨-, rfl⟩ := Prod.mk.inj he
        obtain rfl : o' = o := by
          simpa using hl
        rfl
      · rw [hE] at he
        obtain ⟨-, rfl⟩ := Prod.mk.inj he
        simp at hl
    · rcases Program.emit_cases P s' o' u (h' ++ [(q, ⟨q.1, v⟩)]) with
          ⟨s'', w, _, hE⟩ | ⟨q', _, hE⟩
      · rw [hE] at he
        obtain ⟨-, rfl⟩ := Prod.mk.inj he
        obtain rfl : o' = o := by
          simpa using hl
        simpa [outerOf] using owner o' rfl
      · rw [hE] at he
        obtain ⟨-, rfl⟩ := Prod.mk.inj he
        simp at hl

/-- The mode after an admitted history of converter inputs. -/
theorem after_of_replies {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies (DDC.ofProgram s P) (h.map Prod.fst) (h.map Prod.snd)) :
    ∃ m, P.after s (h.map Prod.fst) = some m := by
  by_cases hn : h.map Prod.fst = []
  · exact ⟨.idle s, by rw [hn]; rfl⟩
  · exact Option.isSome_iff_exists.mp ((ofProgram_dom s P _).mp (hr.dom hn)).2

/-- **A program making at most `b` inside queries per invocation** makes at most `b` inside
queries per outside query along its transcripts. -/
theorem insideQueries_length_le {b : ℕ} (hP : P.Bounded b)
    {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies (DDC.ofProgram s P) (h.map Prod.fst) (h.map Prod.snd)) :
    (insideQueries (h.map Prod.snd)).length ≤ b * (outsideInputs (h.map Prod.fst)).length := by
  suffices key : ∀ m, P.after s (h.map Prod.fst) = some m →
      (insideQueries (h.map Prod.snd)).length + m.credit b ≤
        b * (outsideInputs (h.map Prod.fst)).length by
    obtain ⟨m, hm⟩ := after_of_replies hr
    exact (Nat.le_add_right _ _).trans (key m hm)
  induction h using List.reverseRecOn with
  | nil =>
    intro m hm
    obtain rfl : m = .idle s := (Option.some.inj hm).symm
    simp [insideQueries, outsideInputs, Program.Mode.credit]
  | append_singleton h z ih =>
    intro m hm
    rcases z with ⟨x, y⟩
    simp only [List.map_append, List.map_singleton] at hr hm ⊢
    obtain ⟨hr₀, hy⟩ := replies_snoc.mp hr
    obtain ⟨m₀, hm₀⟩ := after_of_replies hr₀
    have prior := ih hr₀ m₀ hm₀
    have hmem : y ∈ DDC.ofProgram s P (h.map Prod.fst ++ [x]) := by rw [hy]; exact Part.mem_some y
    obtain ⟨m₁, m', h₁, hs⟩ := (mem_ofProgram_snoc s P _ x y).mp hmem
    rw [hm₀] at h₁
    obtain rfl := Option.some.inj h₁
    have hm' : P.after s (h.map Prod.fst ++ [x]) = some m' :=
      (Program.after_snoc_eq_some P s _ x m').mpr ⟨m₀, y, hm₀, hs⟩
    rw [hm] at hm'
    obtain rfl := Option.some.inj hm'
    have sound₀ := (after_invariant hm₀).1
    rw [insideQueries_append, outsideInputs_append, List.length_append, List.length_append]
    rcases Program.step_cases P hs with ⟨s', o, u, rfl, rfl, he⟩ | ⟨o, s', u, hs', q, v, rfl, rfl, he⟩
    · rcases Program.emit_cases P s' o u [] with ⟨s'', w, _, hE⟩ | ⟨q, hq, hE⟩
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        simp only [Program.Mode.credit, add_zero] at prior ⊢
        simp only [insideQueries_outside, outsideInputs_outside, List.length_nil,
          List.length_singleton, add_zero, Nat.mul_succ]
        omega
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        have hb := hP s' o u [] q (Program.consistent_nil P s' o u) hq
        simp only [Program.Mode.credit, add_zero, List.length_nil] at prior hb ⊢
        simp only [insideQueries_inside, outsideInputs_outside, List.length_singleton,
          Nat.mul_succ]
        omega
    · rcases Program.emit_cases P s' o u (hs' ++ [(q, ⟨q.1, v⟩)]) with
          ⟨s'', w, _, hE⟩ | ⟨q', hq', hE⟩
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        simp only [Program.Mode.credit] at prior ⊢
        simp only [insideQueries_outside, List.length_nil, add_zero]
        rw [show outsideInputs [(⟨⟨some (), q.1⟩, v⟩ : Σ l, twoFam U Y l)] = [] from
          outsideInputs_inside _ _]
        simp only [List.length_nil, add_zero]
        omega
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        have hb := hP s' o u _ q' (sound₀.1.snoc sound₀.2 v) hq'
        simp only [Program.Mode.credit, List.length_append, List.length_singleton] at prior hb ⊢
        simp only [insideQueries_inside, List.length_singleton]
        rw [show outsideInputs [(⟨⟨some (), q.1⟩, v⟩ : Σ l, twoFam U Y l)] = [] from
          outsideInputs_inside _ _]
        simp only [List.length_nil, add_zero]
        omega

/-- **A port-preserving program** makes, along its transcripts, at most as many inside queries at
`j = ι o` as outside queries at `o`. -/
theorem insideQueries_restrict_length_le {ι : O → Option J} (hP : P.PortPreserving ι)
    {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies (DDC.ofProgram s P) (h.map Prod.fst) (h.map Prod.snd)) {o : O} {j : J}
    (hj : ι o = some j) :
    (restrict j (insideQueries (h.map Prod.snd))).length ≤
      (restrict o (outsideInputs (h.map Prod.fst))).length := by
  suffices key : ∀ m, P.after s (h.map Prod.fst) = some m →
      (restrict j (insideQueries (h.map Prod.snd))).length + m.portCredit o j ≤
        (restrict o (outsideInputs (h.map Prod.fst))).length by
    obtain ⟨m, hm⟩ := after_of_replies hr
    exact (Nat.le_add_right _ _).trans (key m hm)
  induction h using List.reverseRecOn with
  | nil =>
    intro m hm
    obtain rfl : m = .idle s := (Option.some.inj hm).symm
    simp [insideQueries, outsideInputs, Program.Mode.portCredit]
  | append_singleton h z ih =>
    intro m hm
    rcases z with ⟨x, y⟩
    simp only [List.map_append, List.map_singleton] at hr hm ⊢
    obtain ⟨hr₀, hy⟩ := replies_snoc.mp hr
    obtain ⟨m₀, hm₀⟩ := after_of_replies hr₀
    have prior := ih hr₀ m₀ hm₀
    have hmem : y ∈ DDC.ofProgram s P (h.map Prod.fst ++ [x]) := by rw [hy]; exact Part.mem_some y
    obtain ⟨m₁, m', h₁, hs⟩ := (mem_ofProgram_snoc s P _ x y).mp hmem
    rw [hm₀] at h₁
    obtain rfl := Option.some.inj h₁
    have hm' : P.after s (h.map Prod.fst ++ [x]) = some m' :=
      (Program.after_snoc_eq_some P s _ x m').mpr ⟨m₀, y, hm₀, hs⟩
    rw [hm] at hm'
    obtain rfl := Option.some.inj hm'
    have sound₀ := (after_invariant hm₀).1
    rw [insideQueries_append, outsideInputs_append, restrict_append, restrict_append,
      List.length_append, List.length_append]
    rcases Program.step_cases P hs with ⟨s', o₁, u, rfl, rfl, he⟩ | ⟨o₁, s', u, hs', q, v, rfl, rfl, he⟩
    · rcases Program.emit_cases P s' o₁ u [] with ⟨s'', w, _, hE⟩ | ⟨q, hq, hE⟩
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        simp only [Program.Mode.portCredit, add_zero] at prior ⊢
        simp only [insideQueries_outside, outsideInputs_outside, restrict_nil, List.length_nil,
          add_zero]
        omega
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        have hpres := hP s' o₁ u [] q (Program.consistent_nil P s' o₁ u) hq
        have hq1 : q.1 = j → o₁ = o := fun h' => (hpres o (by rw [hj, h'])).1.symm
        simp only [Program.Mode.portCredit, add_zero] at prior
        simp only [insideQueries_inside, outsideInputs_outside, length_restrict_singleton,
          Program.Mode.portCredit, List.not_mem_nil, false_implies, implies_true, true_and]
        split_ifs <;> first | omega | tauto
    · rcases Program.emit_cases P s' o₁ u (hs' ++ [(q, ⟨q.1, v⟩)]) with
          ⟨s'', w, _, hE⟩ | ⟨q', hq', hE⟩
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        simp only [Program.Mode.portCredit] at prior ⊢
        simp only [insideQueries_outside, restrict_nil, List.length_nil, add_zero]
        rw [show outsideInputs [(⟨⟨some (), q.1⟩, v⟩ : Σ l, twoFam U Y l)] = [] from
          outsideInputs_inside _ _]
        simp only [restrict_nil, List.length_nil, add_zero]
        omega
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        have hpres := hP s' o₁ u _ q' (sound₀.1.snoc sound₀.2 v) hq'
        have hq1 : q'.1 = j → o₁ = o ∧ (∀ e ∈ hs', e.1.1 ≠ j) ∧ q.1 ≠ j := by
          intro h'
          obtain ⟨ho, hfree⟩ := hpres o (by rw [hj, h'])
          subst ho h'
          exact ⟨rfl, fun e he => hfree e (List.mem_append_left _ he),
            hfree _ (List.mem_append_right _ (List.mem_singleton_self _))⟩
        rw [show outsideInputs [(⟨⟨some (), q.1⟩, v⟩ : Σ l, twoFam U Y l)] = [] from
          outsideInputs_inside _ _]
        simp only [Program.Mode.portCredit] at prior
        simp only [insideQueries_inside, restrict_nil, List.length_nil, add_zero,
          length_restrict_singleton, Program.Mode.portCredit, List.forall_mem_append,
          List.forall_mem_singleton]
        split_ifs at prior ⊢ <;> first | omega | tauto

variable (s P) in
/-- **The converter of a program on the outside domain `F`**: it answers the inputs whose
outside queries lie in `F`. -/
noncomputable def ofProgramOn (F : List (Σ o, U o) → Prop) : InsideOutsideSystem O J U V X Y :=
  filterDom (fun xs => outsideInputs xs = [] ∨ F (outsideInputs xs)) (DDC.ofProgram s P)

/-- A transcript of the restricted converter is a transcript of the program whose outside
queries lie in `F`. -/
theorem replies_ofProgramOn {F : List (Σ o, U o) → Prop}
    {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies (ofProgramOn s P F) (h.map Prod.fst) (h.map Prod.snd)) :
    Replies (DDC.ofProgram s P) (h.map Prod.fst) (h.map Prod.snd) ∧
      (outsideInputs (h.map Prod.fst) = [] ∨ F (outsideInputs (h.map Prod.fst))) := by
  refine ⟨hr.mono fun h y hy => ((filterDom_mem_iff _ _ h y).mp hy).2, ?_⟩
  by_cases hn : h.map Prod.fst = []
  · exact Or.inl (by rw [hn]; rfl)
  · exact ((filterDom_dom _ _ _).mp (hr.dom hn)).1

/-- **A bounded program on the outside domain `F`** is a DDC from `E` to `F` when the inside
queries of its transcripts lie in `E`. -/
theorem ofProgramOn_isDDCFrom {E : List (Σ j, X j) → Prop} {F : List (Σ o, U o) → Prop}
    {b : ℕ} (hP : P.Bounded b) (hF : ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (hq : ∀ h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l)),
      Replies (DDC.ofProgram s P) (h.map Prod.fst) (h.map Prod.snd) →
      (outsideInputs (h.map Prod.fst) = [] ∨ F (outsideInputs (h.map Prod.fst))) →
      insideQueries (h.map Prod.snd) = [] ∨ E (insideQueries (h.map Prod.snd))) :
    IsDDCFrom E F b (ofProgramOn s P F) :=
  (ofProgram_isResponsiveDDC hP).isDDCFrom_filterDom hF fun h hr =>
    hq h (replies_ofProgramOn hr).1 (replies_ofProgramOn hr).2

/-- **Budgets.** On outside histories of at most `q` queries, a program making at most `b` inside
queries per invocation makes at most `b * q` inside queries. -/
theorem insideQueries_length_le_of_budget {b q : ℕ} (hP : P.Bounded b)
    {F : List (Σ o, U o) → Prop} (hFq : ∀ xs, F xs → xs.length ≤ q)
    {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies (DDC.ofProgram s P) (h.map Prod.fst) (h.map Prod.snd))
    (hF : outsideInputs (h.map Prod.fst) = [] ∨ F (outsideInputs (h.map Prod.fst))) :
    (insideQueries (h.map Prod.snd)).length ≤ b * q := by
  refine (insideQueries_length_le hP hr).trans (Nat.mul_le_mul_left b ?_)
  rcases hF with he | hF
  · rw [he]; exact Nat.zero_le _
  · exact hFq _ hF

/-- **Exact costs.** A program making exactly `cost u` inside queries on the outside query `u`
makes at most the total cost of its outside queries along its transcripts. -/
theorem insideQueries_length_le_of_costs {cost : (Σ o, U o) → ℕ} (hP : P.Costs cost)
    {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies (DDC.ofProgram s P) (h.map Prod.fst) (h.map Prod.snd)) :
    (insideQueries (h.map Prod.snd)).length ≤ ((outsideInputs (h.map Prod.fst)).map cost).sum := by
  suffices key : ∀ m, P.after s (h.map Prod.fst) = some m →
      (insideQueries (h.map Prod.snd)).length + m.owed cost ≤
        ((outsideInputs (h.map Prod.fst)).map cost).sum by
    obtain ⟨m, hm⟩ := after_of_replies hr
    exact (Nat.le_add_right _ _).trans (key m hm)
  induction h using List.reverseRecOn with
  | nil =>
    intro m hm
    obtain rfl : m = .idle s := (Option.some.inj hm).symm
    simp [insideQueries, outsideInputs, Program.Mode.owed]
  | append_singleton h z ih =>
    intro m hm
    rcases z with ⟨x, y⟩
    simp only [List.map_append, List.map_singleton] at hr hm ⊢
    obtain ⟨hr₀, hy⟩ := replies_snoc.mp hr
    obtain ⟨m₀, hm₀⟩ := after_of_replies hr₀
    have prior := ih hr₀ m₀ hm₀
    have hmem : y ∈ DDC.ofProgram s P (h.map Prod.fst ++ [x]) := by rw [hy]; exact Part.mem_some y
    obtain ⟨m₁, m', h₁, hs⟩ := (mem_ofProgram_snoc s P _ x y).mp hmem
    rw [hm₀] at h₁
    obtain rfl := Option.some.inj h₁
    have hm' : P.after s (h.map Prod.fst ++ [x]) = some m' :=
      (Program.after_snoc_eq_some P s _ x m').mpr ⟨m₀, y, hm₀, hs⟩
    rw [hm] at hm'
    obtain rfl := Option.some.inj hm'
    have sound₀ := (after_invariant hm₀).1
    rw [insideQueries_append, outsideInputs_append, List.map_append, List.sum_append,
      List.length_append]
    rcases Program.step_cases P hs with ⟨s', o, u, rfl, rfl, he⟩ | ⟨o, s', u, hs', q, v, rfl, rfl, he⟩
    · have hc := hP s' o u [] (Program.consistent_nil P s' o u)
      rcases Program.emit_cases P s' o u [] with ⟨s'', w, hw, hE⟩ | ⟨q, hq, hE⟩
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        simp only [Program.Mode.owed, add_zero] at prior ⊢
        simp only [insideQueries_outside, outsideInputs_outside, List.length_nil,
          List.map_singleton, List.sum_singleton, add_zero]
        omega
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        have hb := hc.1 q hq
        simp only [Program.Mode.owed, add_zero, List.length_nil] at prior hb ⊢
        simp only [insideQueries_inside, outsideInputs_outside, List.length_singleton,
          List.map_singleton, List.sum_singleton]
        omega
    · have hc := hP s' o u _ (sound₀.1.snoc sound₀.2 v)
      rcases Program.emit_cases P s' o u (hs' ++ [(q, ⟨q.1, v⟩)]) with
          ⟨s'', w, hw, hE⟩ | ⟨q', hq', hE⟩
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        have he' := hc.2 _ hw
        simp only [Program.Mode.owed, List.length_append, List.length_singleton] at prior he' ⊢
        simp only [insideQueries_outside, List.length_nil, add_zero]
        rw [show outsideInputs [(⟨⟨some (), q.1⟩, v⟩ : Σ l, twoFam U Y l)] = [] from
          outsideInputs_inside _ _]
        simp only [List.map_nil, List.sum_nil, add_zero]
        omega
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        have hb := hc.1 q' hq'
        simp only [Program.Mode.owed, List.length_append, List.length_singleton] at prior hb ⊢
        simp only [insideQueries_inside, List.length_singleton]
        rw [show outsideInputs [(⟨⟨some (), q.1⟩, v⟩ : Σ l, twoFam U Y l)] = [] from
          outsideInputs_inside _ _]
        simp only [List.map_nil, List.sum_nil, add_zero]
        omega

end DDC

end SystemAlgebra
