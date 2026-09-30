import RandomSystems.Converter.Program
import RandomSystems.Converter.FilterAttachment
import RandomSystems.System.Automaton

/-!
# Attaching a program

Attaching a program to a deterministic resource inlines it: each outside query runs the body,
and each inside query is answered by the resource from its inputs so far (Maurer 2002, §3.3:
a system `C(.)` invoking an internal system `F` is the combined system `C(F)`).

## Main definitions

* `Program.feed P r n m x rh`: an invocation continued from the input `x` in the mode `m`, the
  resource having received `rh`
* `Program.inline s P r b`: the system of the program with its inside queries answered by `r`
* `Program.invoke`, `Program.combine`: an invocation against an automaton, and the program
  attached to an automaton as an automaton on pairs of states

## Main results

* `Program.apply_ofProgram`, `Program.trim_apply_ofProgram`: attaching the program is the
  inlined program
* `Program.trim_apply_ofProgramOn`: on an outside domain, the inlined program on that domain
* `Program.inline_automatonSystem`, `Program.trim_apply_ofProgramOn_automaton`: attaching a
  program to an automaton is the combined automaton, also on domains
* `Program.combine_bisim`, `Program.combine_congr`: attached to bisimilar automata, or to
  automata with the same system, a program gives bisimilar automata, or the same system
-/

namespace SystemAlgebra

open Classical

variable {S O J : Type} {U V : O → Type} {X Y : J → Type}

namespace Program

variable (P : Program S O J U V X Y) (r : InterfaceSystem J X Y)

/-- **An invocation, continued** from the converter input `x` in the mode `m`, the resource
having received `rh`: an inside query is answered by the resource and fed back, until the
program replies outside. `n` bounds the number of steps. -/
noncomputable def feed : ℕ → Mode S O J U X Y → (Σ l, twoFam U Y l) → List (Σ j, X j) →
    Option (Mode S O J U X Y × List (Σ j, X j) × (Σ o, V o))
  | 0, _, _, _ => none
  | n + 1, m, x, rh =>
    match P.step m x with
    | none => none
    | some (m', ⟨⟨none, o⟩, v⟩) => some (m', rh, ⟨o, v⟩)
    | some (m', ⟨⟨some (), j⟩, q⟩) =>
      if hd : (r (rh ++ [⟨j, q⟩])).Dom then
        feed n m' ⟨⟨some (), ((r (rh ++ [⟨j, q⟩])).get hd).1⟩,
          ((r (rh ++ [⟨j, q⟩])).get hd).2⟩ (rh ++ [⟨j, q⟩])
      else none

variable {P r}

/-- **One completed invocation is one exchange** of the attached system: from an internal
history whose converter inputs leave the program in the mode `m` and whose resource inputs are
`rh`, the input `x` leads to the reply `w`, and the internal history reached records the new
mode and resource inputs. -/
theorem exchange_of_feed (s : S) :
    ∀ (n : ℕ) (G : List (Two (Σ l, twoFam U Y l) (Σ j, X j))) (m : Mode S O J U X Y)
      (x : Σ l, twoFam U Y l) (rh : List (Σ j, X j)) (m' : Mode S O J U X Y)
      (rh' : List (Σ j, X j)) (w : Σ o, V o),
      P.after s (restrict none G) = some m → restrict (some ()) G = rh →
      P.feed r n m x rh = some (m', rh', w) →
      ∃ G', Exchange (pair (DDC.ofProgram s P) r) resourceRoute (G ++ [⟨none, x⟩]) (some w) G' ∧
        P.after s (restrict none G') = some m' ∧ restrict (some ()) G' = rh'
  | 0, _, _, _, _, _, _, _, _, _, hf => by simp [feed] at hf
  | n + 1, G, m, x, rh, m', rh', w, hm, hrh, hf => by
    have hstep : ∀ r', P.step m x = some r' →
        (⟨none, r'.2⟩ : Two (Σ l, twoFam V X l) (Σ j, Y j)) ∈
          pair (DDC.ofProgram s P) r (G ++ [⟨none, x⟩]) := by
      intro r' hr'
      rw [pair_left, DDC.ofProgram_snoc, hm]
      simp [hr']
    have hafter : ∀ r', P.step m x = some r' →
        P.after s (restrict none (G ++ [⟨none, x⟩])) = some r'.1 := by
      intro r' hr'
      rw [restrict_none_snoc_left, after_snoc, hm]
      simp [hr']
    cases hs : P.step m x with
    | none => simp [feed, hs] at hf
    | some r' =>
      rcases r' with ⟨m₁, ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩⟩
      · simp only [feed, hs, Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl, rfl⟩ := hf
        refine ⟨G ++ [⟨none, x⟩], Exchange.out (route := resourceRoute) _ _ ⟨o, v⟩ (hstep _ hs) rfl, hafter _ hs, ?_⟩
        rw [restrict_some_snoc_left, hrh]
      · simp only [feed, hs] at hf
        split_ifs at hf with hd
        set y := (r (rh ++ [⟨o, v⟩])).get hd
        have hG₁ : P.after s (restrict none (G ++ [⟨none, x⟩] ++ [⟨some (), ⟨o, v⟩⟩])) =
            some m₁ := by
          rw [restrict_none_snoc_right]; exact hafter _ hs
        have hrh₁ : restrict (some ()) (G ++ [⟨none, x⟩] ++ [⟨some (), ⟨o, v⟩⟩]) =
            rh ++ [⟨o, v⟩] := by
          rw [restrict_some_snoc_right, restrict_some_snoc_left, hrh]
        obtain ⟨G', l, hm', hrh'⟩ := exchange_of_feed s n _ m₁ _ _ m' rh' w hG₁ hrh₁ hf
        refine ⟨G', Exchange.feed (route := resourceRoute) _ _ _ _ _ (hstep _ hs) rfl
          (Exchange.feed (route := resourceRoute) _ ⟨some (), y⟩ _ _ _ ?_ rfl l), hm', hrh'⟩
        rw [pair_right, restrict_some_snoc_left, hrh]
        exact Part.mem_map _ (Part.get_mem hd)

variable (P) in
/-- The program no longer admits an outside query: its run failed, or it waits for a reply. -/
def Dead (s : S) (G : List (Two (Σ l, twoFam U Y l) (Σ j, X j))) : Prop :=
  ∀ m, P.after s (restrict none G) = some m → ∃ o s' u h q, m = .busy o s' u h q

/-- A step producing an inside query counts one more inside query and keeps the mode sound. -/
theorem step_inside {m m' : Mode S O J U X Y} {x : Σ l, twoFam U Y l} {j : J} {q : X j}
    (hm : m.Sound P) (hs : P.step m x = some (m', ⟨⟨some (), j⟩, q⟩)) :
    m'.pending = m.pending + 1 ∧ m'.Sound P := by
  rcases P.step_cases hs with ⟨s', o, u, rfl, rfl, he⟩ | ⟨o, s', u, h, q', v, rfl, rfl, he⟩
  · rcases P.emit_cases s' o u [] with ⟨s'', w, _, hE⟩ | ⟨q'', hq, hE⟩
    · rw [hE] at he; cases (Prod.mk.inj he).2
    · rw [hE] at he
      obtain ⟨rfl, -⟩ := Prod.mk.inj he
      exact ⟨by simp [Mode.pending], consistent_nil P s' o u, hq⟩
  · rcases P.emit_cases s' o u (h ++ [(q', ⟨q'.1, v⟩)]) with ⟨s'', w, _, hE⟩ | ⟨q'', hq, hE⟩
    · rw [hE] at he; cases (Prod.mk.inj he).2
    · rw [hE] at he
      obtain ⟨rfl, -⟩ := Prod.mk.inj he
      exact ⟨by simp [Mode.pending], hm.1.snoc hm.2 v, hq⟩

/-- A sound mode of a bounded program has made at most `b` inside queries. -/
theorem pending_le {b : ℕ} (hP : P.Bounded b) {m : Mode S O J U X Y} (hm : m.Sound P) :
    m.pending ≤ b := by
  rcases m with s | ⟨o, s, u, h, q⟩
  · exact Nat.zero_le _
  · exact hP s o u h q hm.1 hm.2

/-- A step producing an outside reply leaves the program idle. -/
theorem step_outside {m m' : Mode S O J U X Y} {x : Σ l, twoFam U Y l} {o : O} {v : V o}
    (hs : P.step m x = some (m', ⟨⟨none, o⟩, v⟩)) : ∃ s', m' = .idle s' := by
  rcases P.step_cases hs with ⟨s', o', u, rfl, rfl, he⟩ | ⟨o', s', u, h, q', v', rfl, rfl, he⟩
  · rcases P.emit_cases s' o' u [] with ⟨s'', w, _, hE⟩ | ⟨q'', _, hE⟩
    · rw [hE] at he; exact ⟨s'', (Prod.mk.inj he).1⟩
    · rw [hE] at he; cases (Prod.mk.inj he).2
  · rcases P.emit_cases s' o' u (h ++ [(q', ⟨q'.1, v'⟩)]) with ⟨s'', w, _, hE⟩ | ⟨q'', _, hE⟩
    · rw [hE] at he; exact ⟨s'', (Prod.mk.inj he).1⟩
    · rw [hE] at he; cases (Prod.mk.inj he).2

/-- A completed invocation leaves the program idle. -/
theorem feed_idle :
    ∀ (n : ℕ) (m : Mode S O J U X Y) (x : Σ l, twoFam U Y l) (rh : List (Σ j, X j))
      (m' : Mode S O J U X Y) (rh' : List (Σ j, X j)) (w : Σ o, V o),
      P.feed r n m x rh = some (m', rh', w) → ∃ s', m' = .idle s'
  | 0, _, _, _, _, _, _, hf => by simp [feed] at hf
  | n + 1, m, x, rh, m', rh', w, hf => by
    cases hs : P.step m x with
    | none => simp [feed, hs] at hf
    | some r' =>
      rcases r' with ⟨m₁, ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩⟩
      · simp only [feed, hs, Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, -, -⟩ := hf
        exact step_outside hs
      · simp only [feed, hs] at hf
        split_ifs at hf
        exact feed_idle n _ _ _ m' rh' w hf

/-- **An invocation that does not complete is a silent exchange**, after which the program
admits no outside query. -/
theorem exchange_of_feed_none (s : S) {b : ℕ} (hP : P.Bounded b) :
    ∀ (n : ℕ) (G : List (Two (Σ l, twoFam U Y l) (Σ j, X j))) (m : Mode S O J U X Y)
      (x : Σ l, twoFam U Y l) (rh : List (Σ j, X j)),
      P.after s (restrict none G) = some m → m.Sound P → b + 1 ≤ n + m.pending →
      restrict (some ()) G = rh → P.feed r n m x rh = none →
      ∃ G', Exchange (pair (DDC.ofProgram s P) r) resourceRoute (G ++ [⟨none, x⟩]) none G' ∧
        Dead P s G'
  | 0, _, m, _, _, _, hs, hn, _, _ => by
    have := pending_le hP hs; omega
  | n + 1, G, m, x, rh, hm, hsound, hn, hrh, hf => by
    have hpair : pair (DDC.ofProgram s P) r (G ++ [⟨none, x⟩]) =
        (Part.ofOption ((P.step m x).map Prod.snd)).map (Sigma.mk none) := by
      rw [pair_left, DDC.ofProgram_snoc, hm]; rfl
    have hafter : P.after s (restrict none (G ++ [⟨none, x⟩])) =
        (P.step m x).map Prod.fst := by
      rw [restrict_none_snoc_left, after_snoc, hm]; rfl
    cases hs : P.step m x with
    | none =>
      refine ⟨G ++ [⟨none, x⟩], Exchange.silent _ ?_, fun m' hm' => ?_⟩
      · rw [hpair, hs]; simp
      · rw [hafter, hs] at hm'; cases hm'
    | some r' =>
      rcases r' with ⟨m₁, ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩⟩
      · simp [feed, hs] at hf
      · obtain ⟨hpend, hsound₁⟩ := step_inside hsound hs
        have hy : (⟨none, ⟨⟨some (), o⟩, v⟩⟩ : Two (Σ l, twoFam V X l) (Σ j, Y j)) ∈
            pair (DDC.ofProgram s P) r (G ++ [⟨none, x⟩]) := by
          rw [hpair, hs]; simp
        have hG₁ : P.after s (restrict none (G ++ [⟨none, x⟩] ++ [⟨some (), ⟨o, v⟩⟩])) =
            some m₁ := by
          rw [restrict_none_snoc_right, hafter, hs]; rfl
        have hrh₁ : restrict (some ()) (G ++ [⟨none, x⟩] ++ [⟨some (), ⟨o, v⟩⟩]) =
            rh ++ [⟨o, v⟩] := by
          rw [restrict_some_snoc_right, restrict_some_snoc_left, hrh]
        have hpr : pair (DDC.ofProgram s P) r (G ++ [⟨none, x⟩] ++ [⟨some (), ⟨o, v⟩⟩]) =
            (r (rh ++ [⟨o, v⟩])).map (Sigma.mk (some ())) := by
          rw [pair_right, restrict_some_snoc_left, hrh]
        simp only [feed, hs] at hf
        by_cases hd : (r (rh ++ [⟨o, v⟩])).Dom
        · rw [dif_pos hd] at hf
          obtain ⟨G', l, hdead⟩ := exchange_of_feed_none s hP n _ m₁ _ _ hG₁ hsound₁
            (by omega) hrh₁ hf
          refine ⟨G', Exchange.feed (route := resourceRoute) _ _ _ _ _ hy rfl
            (Exchange.feed (route := resourceRoute) _ ⟨some (), (r (rh ++ [⟨o, v⟩])).get hd⟩
              _ _ _ ?_ rfl l), hdead⟩
          rw [hpr]; exact Part.mem_map _ (Part.get_mem hd)
        · refine ⟨_, Exchange.feed (route := resourceRoute) _ _ _ _ _ hy rfl
            (Exchange.silent _ ?_), fun m' hm' => ?_⟩
          · rw [hpr]; simpa using hd
          · rw [hG₁] at hm'
            obtain rfl := Option.some.inj hm'
            rcases P.step_cases hs with ⟨s', o', u, -, -, he⟩ | ⟨o', s', u, h, q', v', -, -, he⟩
            · rcases P.emit_cases s' o' u [] with ⟨s'', w, _, hE⟩ | ⟨q'', _, hE⟩
              · rw [hE] at he; cases (Prod.mk.inj he).2
              · rw [hE] at he
                exact ⟨o', s', u, [], q'', (Prod.mk.inj he).1⟩
            · rcases P.emit_cases s' o' u (h ++ [(q', ⟨q'.1, v'⟩)]) with
                  ⟨s'', w, _, hE⟩ | ⟨q'', _, hE⟩
              · rw [hE] at he; cases (Prod.mk.inj he).2
              · rw [hE] at he
                exact ⟨o', s', u, _, q'', (Prod.mk.inj he).1⟩

/-- From a dead internal history, every outside query is a silent exchange. -/
theorem exchange_of_dead (s : S) {G : List (Two (Σ l, twoFam U Y l) (Σ j, X j))}
    (hG : Dead P s G) (o : O) (u : U o) :
    Exchange (pair (DDC.ofProgram s P) r) resourceRoute (G ++ [⟨none, ⟨⟨none, o⟩, u⟩⟩]) none
      (G ++ [⟨none, ⟨⟨none, o⟩, u⟩⟩]) ∧ Dead P s (G ++ [⟨none, ⟨⟨none, o⟩, u⟩⟩]) := by
  have hnone : ∀ m, P.after s (restrict none G) = some m → P.step m ⟨⟨none, o⟩, u⟩ = none := by
    intro m hm
    obtain ⟨o', s', u', h, q, rfl⟩ := hG m hm
    rfl
  refine ⟨Exchange.silent _ ?_, fun m hm => ?_⟩
  · rw [pair_left, DDC.ofProgram_snoc]
    cases hm : P.after s (restrict none G) with
    | none => simp
    | some m => simp [hnone m hm]
  · rw [restrict_none_snoc_left, after_snoc] at hm
    cases hm' : P.after s (restrict none G) with
    | none => simp [hm'] at hm
    | some m' => simp [hm', hnone m' hm'] at hm

variable (P r) in
/-- The mode and resource inputs after a sequence of outside queries, each run to completion
with at most `b` inside queries. -/
noncomputable def inlineAfter (b : ℕ) (s : S) (us : List (Σ o, U o)) :
    Option (Mode S O J U X Y × List (Σ j, X j)) :=
  us.foldl (fun st u => st.bind fun mr =>
    (P.feed r (b + 1) mr.1 ⟨⟨none, u.1⟩, u.2⟩ mr.2).map fun t => (t.1, t.2.1)) (some (.idle s, []))

variable (P r) in
/-- **The inlined program**: each outside query runs the body, whose inside queries the
resource `r` answers. -/
noncomputable def inline (b : ℕ) (s : S) : InterfaceSystem O U V := fun us =>
  Part.ofOption (us.getLast?.bind fun u => (P.inlineAfter r b s us.dropLast).bind fun mr =>
    (P.feed r (b + 1) mr.1 ⟨⟨none, u.1⟩, u.2⟩ mr.2).map fun t => t.2.2)

@[simp] theorem inlineAfter_nil (b : ℕ) (s : S) :
    P.inlineAfter r b s [] = some (.idle s, []) := rfl

theorem inlineAfter_snoc (b : ℕ) (s : S) (us : List (Σ o, U o)) (u : Σ o, U o) :
    P.inlineAfter r b s (us ++ [u]) = (P.inlineAfter r b s us).bind fun mr =>
      (P.feed r (b + 1) mr.1 ⟨⟨none, u.1⟩, u.2⟩ mr.2).map fun t => (t.1, t.2.1) := by
  simp only [inlineAfter, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem inline_snoc (b : ℕ) (s : S) (us : List (Σ o, U o)) (u : Σ o, U o) :
    P.inline r b s (us ++ [u]) = Part.ofOption ((P.inlineAfter r b s us).bind fun mr =>
      (P.feed r (b + 1) mr.1 ⟨⟨none, u.1⟩, u.2⟩ mr.2).map fun t => t.2.2) := by
  simp [inline]

/-- **The internal histories of the attachment follow the inlined program.** -/
theorem induces_inline (s : S) {b : ℕ} (hP : P.Bounded b) : ∀ us : List (Σ o, U o),
    (∀ m rh, P.inlineAfter r b s us = some (m, rh) →
      ∃ o H, Induces (pair (DDC.ofProgram s P) r) resourceRoute resourceInput us o H ∧
        P.after s (restrict none H) = some m ∧ (∃ s', m = .idle s') ∧
        restrict (some ()) H = rh) ∧
    (P.inlineAfter r b s us = none →
      ∃ H, Induces (pair (DDC.ofProgram s P) r) resourceRoute resourceInput us none H ∧
        Dead P s H) := by
  intro us
  induction us using List.reverseRecOn with
  | nil =>
    refine ⟨fun m rh hm => ?_, fun hm => by simp at hm⟩
    simp only [inlineAfter_nil, Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ⟨none, [], Induces.nil, rfl, ⟨s, rfl⟩, rfl⟩
  | append_singleton us a ih =>
    obtain ⟨ihSome, ihNone⟩ := ih
    rw [inlineAfter_snoc]
    cases hst : P.inlineAfter r b s us with
    | none =>
      obtain ⟨H, hi, hdead⟩ := ihNone hst
      obtain ⟨l, hdead'⟩ := exchange_of_dead (r := r) s hdead a.1 a.2
      exact ⟨fun m rh hm => by simp at hm, fun _ => ⟨_, Induces.snoc _ _ _ _ _ _ hi l, hdead'⟩⟩
    | some mr =>
      obtain ⟨m, rh⟩ := mr
      obtain ⟨o₀, H, hi, hm, ⟨s', rfl⟩, hrh⟩ := ihSome m rh hst
      cases hf : P.feed r (b + 1) (.idle s') ⟨⟨none, a.1⟩, a.2⟩ rh with
      | none =>
        obtain ⟨G', l, hdead⟩ := exchange_of_feed_none s hP (b + 1) H (.idle s') _ rh hm trivial
          (by simp [Mode.pending]) hrh hf
        exact ⟨fun m rh hm => by simp [hf] at hm,
          fun _ => ⟨G', Induces.snoc _ _ _ _ _ _ hi l, hdead⟩⟩
      | some t =>
        obtain ⟨m', rh', w⟩ := t
        refine ⟨fun m₂ rh₂ hm₂ => ?_, fun hn => by simp [hf] at hn⟩
        simp only [hf, Option.bind_some, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at hm₂
        obtain ⟨rfl, rfl⟩ := hm₂
        obtain ⟨G', l, hm', hrh'⟩ := exchange_of_feed s (b + 1) H (.idle s') _ rh m' rh' w
          hm hrh hf
        exact ⟨some w, G', Induces.snoc _ _ _ _ _ _ hi l, hm',
          feed_idle _ _ _ _ _ _ _ hf, hrh'⟩

/-- **Attaching a program is the inlined program**: each outside query runs the body, and the
resource answers its inside queries (Maurer 2002, §3.3). -/
theorem apply_ofProgram (s : S) {b : ℕ} (hP : P.Bounded b) :
    apply (DDC.ofProgram s P) r = P.inline r b s := by
  funext us
  rw [apply_eq]
  rcases List.eq_nil_or_concat us with rfl | ⟨us, a, rfl⟩
  · rw [interconnect_eq_none Induces.nil]; rfl
  rw [List.concat_eq_append, inline_snoc]
  obtain ⟨ihSome, ihNone⟩ := induces_inline (r := r) s hP us
  cases hst : P.inlineAfter r b s us with
  | none =>
    obtain ⟨H, hi, hdead⟩ := ihNone hst
    obtain ⟨l, -⟩ := exchange_of_dead (r := r) s hdead a.1 a.2
    rw [interconnect_eq_none (Induces.snoc _ _ _ _ _ _ hi l)]; rfl
  | some mr =>
    obtain ⟨m, rh⟩ := mr
    obtain ⟨o₀, H, hi, hm, ⟨s', rfl⟩, hrh⟩ := ihSome m rh hst
    cases hf : P.feed r (b + 1) (.idle s') ⟨⟨none, a.1⟩, a.2⟩ rh with
    | none =>
      obtain ⟨G', l, -⟩ := exchange_of_feed_none s hP (b + 1) H (.idle s') _ rh hm trivial
        (by simp [Mode.pending]) hrh hf
      rw [interconnect_eq_none (Induces.snoc _ _ _ _ _ _ hi l)]
      simp [hf]
    | some t =>
      obtain ⟨m', rh', w⟩ := t
      obtain ⟨G', l, -, -⟩ := exchange_of_feed s (b + 1) H (.idle s') _ rh m' rh' w hm hrh hf
      rw [interconnect_eq_some (Induces.snoc _ _ _ _ _ _ hi l)]
      simp [hf]

theorem inlineAfter_isSome_of_append (b : ℕ) (s : S) {us e : List (Σ o, U o)}
    (h : (P.inlineAfter r b s (us ++ e)).isSome) : (P.inlineAfter r b s us).isSome := by
  induction e using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton e u ih =>
    rw [← List.append_assoc, inlineAfter_snoc] at h
    apply ih
    cases hst : P.inlineAfter r b s (us ++ e) with
    | none => rw [hst] at h; simp at h
    | some _ => rfl

theorem inline_dom (b : ℕ) (s : S) (us : List (Σ o, U o)) :
    (P.inline r b s us).Dom ↔ us ≠ [] ∧ (P.inlineAfter r b s us).isSome := by
  rcases List.eq_nil_or_concat us with rfl | ⟨us, u, rfl⟩
  · simp [inline]
  · rw [List.concat_eq_append, inline_snoc, inlineAfter_snoc]
    simp only [Part.ofOption_dom, ne_eq, List.append_eq_nil_iff, List.cons_ne_self, and_false,
      not_false_eq_true, true_and]
    cases P.inlineAfter r b s us with
    | none => simp
    | some mr => cases P.feed r (b + 1) mr.1 ⟨⟨none, u.1⟩, u.2⟩ mr.2 <;> simp

theorem inline_isDDS (b : ℕ) (s : S) : IsDDS (P.inline r b s) := by
  refine ⟨by simp [SilentAtEmpty, inline], fun p h hp hne hd => ?_⟩
  obtain ⟨e, rfl⟩ := hp
  rw [inline_dom] at hd ⊢
  exact ⟨hne, inlineAfter_isSome_of_append b s hd.2⟩

/-- The attachment of a program, as a deterministic system, is the inlined program. -/
theorem trim_apply_ofProgram (s : S) {b : ℕ} (hP : P.Bounded b) :
    trim (apply (DDC.ofProgram s P) r) = P.inline r b s := by
  rw [apply_ofProgram s hP]
  exact (inline_isDDS b s).trim_eq

/-- **Attaching the program on the outside domain `F`** is the inlined program on `F`. -/
theorem trim_apply_ofProgramOn (s : S) {b : ℕ} (hP : P.Bounded b) (F : List (Σ o, U o) → Prop)
    (hF : ∀ {p h}, p <+: h → p ≠ [] → F h → F p) :
    trim (apply (DDC.ofProgramOn s P F) r) = filterDom F (P.inline r b s) := by
  rw [DDC.ofProgramOn, apply_filterDom_outside F hF, apply_ofProgram s hP]
  exact ((inline_isDDS b s).filterDom F hF).trim_eq

/-! ## Attaching a program to an automaton -/

section Automaton

variable {R : Type} (stepR : R → (j : J) → X j → R × Y j)

variable (P) in
/-- **An invocation against an automaton**: the body runs from the exchanges `h`, the automaton
in the state `r` answering its inside queries, with at most `n` more of them. -/
def invoke (s : S) (o : O) (u : U o) :
    ℕ → R → List ((Σ j, X j) × (Σ j, Y j)) → Option ((S × R) × V o)
  | 0, r, h => (P s o u h).elim (fun a => some ((a.1, r), a.2)) (fun _ => none)
  | n + 1, r, h =>
    match P s o u h with
    | .inl (s', v) => some ((s', r), v)
    | .inr q => invoke s o u n (stepR r q.1 q.2).1 (h ++ [(q, ⟨q.1, (stepR r q.1 q.2).2⟩)])

/-- A bounded program completes each invocation against an automaton. -/
theorem invoke_isSome {b : ℕ} (hP : P.Bounded b) (s : S) (o : O) (u : U o) :
    ∀ n r h, P.Consistent s o u h → b ≤ n + h.length →
      (P.invoke stepR s o u n r h).isSome := by
  intro n
  induction n with
  | zero =>
    intro r h hc hb
    cases hq : P s o u h with
    | inl a => simp [invoke, hq]
    | inr q => exact absurd (hP s o u h q hc hq) (by omega)
  | succ n ih =>
    intro r h hc hb
    cases hq : P s o u h with
    | inl a => simp [invoke, hq]
    | inr q =>
      simp only [invoke, hq]
      exact ih _ _ (hc.snoc hq _) (by simp; omega)

variable (P) in
/-- **The program attached to an automaton**, an automaton on pairs of states: each input runs
an invocation, the automaton answering its inside queries. -/
noncomputable def combine {b : ℕ} (hP : P.Bounded b) : S × R → (o : O) → U o → (S × R) × V o :=
  fun sr o u => (P.invoke stepR sr.1 o u b sr.2 []).get
    (invoke_isSome stepR hP sr.1 o u b sr.2 [] (consistent_nil P _ _ _) (by simp))

/-- More inside queries allowed do not change a completed invocation. -/
theorem invoke_add {s : S} {o : O} {u : U o} {v : (S × R) × V o} :
    ∀ n r h k, P.invoke stepR s o u n r h = some v → P.invoke stepR s o u (n + k) r h = some v := by
  intro n
  induction n with
  | zero =>
    intro r h k hv
    cases k with
    | zero => exact hv
    | succ k =>
      cases hq : P s o u h with
      | inl a => simpa [invoke, hq] using hv
      | inr q => simp [invoke, hq] at hv
  | succ n ih =>
    intro r h k hv
    rw [show n + 1 + k = (n + k) + 1 by omega]
    cases hq : P s o u h with
    | inl a => simpa [invoke, hq] using hv
    | inr q =>
      simp only [invoke, hq] at hv ⊢
      exact ih _ _ k hv

theorem invoke_eq_combine {b : ℕ} (hP : P.Bounded b) (sr : S × R) (o : O) (u : U o) :
    P.invoke stepR sr.1 o u b sr.2 [] = some (P.combine stepR hP sr o u) := by
  simp [combine]

/-- The combined automaton answers as any invocation that completes. -/
theorem combine_eq_of_invoke {b : ℕ} (hP : P.Bounded b) {sr : S × R} {o : O} {u : U o} {n : ℕ}
    {v : (S × R) × V o} (hv : P.invoke stepR sr.1 o u n sr.2 [] = some v) :
    P.combine stepR hP sr o u = v := by
  have h₁ := invoke_add stepR n sr.2 [] b hv
  have h₂ := invoke_add stepR b sr.2 [] n (invoke_eq_combine stepR hP sr o u)
  rw [Nat.add_comm] at h₂
  exact Option.some.inj (h₂.symm.trans h₁)

/-- Against bisimilar automata an invocation makes the same queries and replies, and leaves
related states. -/
theorem invoke_bisim {R' : Type} {stepR' : R' → (j : J) → X j → R' × Y j} {rel : R → R' → Prop}
    (hR : IsBisim stepR stepR' rel) (s : S) (o : O) (u : U o) :
    ∀ n r r' h, rel r r' →
      Option.Rel (fun a b => a.1.1 = b.1.1 ∧ rel a.1.2 b.1.2 ∧ a.2 = b.2)
        (P.invoke stepR s o u n r h) (P.invoke stepR' s o u n r' h) := by
  intro n
  induction n with
  | zero =>
    intro r r' h hr
    cases hq : P s o u h with
    | inl a =>
      simp only [invoke, hq, Sum.elim_inl]
      exact Option.Rel.some ⟨rfl, hr, rfl⟩
    | inr q =>
      simp only [invoke, hq, Sum.elim_inr]
      exact Option.Rel.none
  | succ n ih =>
    intro r r' h hr
    cases hq : P s o u h with
    | inl a =>
      simp only [invoke, hq]
      exact Option.Rel.some ⟨rfl, hr, rfl⟩
    | inr q =>
      simp only [invoke, hq]
      obtain ⟨hy, hr'⟩ := hR r r' q.1 q.2 hr
      rw [hy]
      exact ih _ _ _ hr'

/-- **Attaching a program to bisimilar automata** gives bisimilar automata. -/
theorem combine_bisim {R' : Type} {stepR' : R' → (j : J) → X j → R' × Y j} {rel : R → R' → Prop}
    (hR : IsBisim stepR stepR' rel) {b : ℕ} (hP : P.Bounded b) :
    IsBisim (P.combine stepR hP) (P.combine stepR' hP) (fun a a' => a.1 = a'.1 ∧ rel a.2 a'.2) := by
  rintro ⟨s, r⟩ ⟨s', r'⟩ o u ⟨rfl, hr⟩
  have h := invoke_bisim (P := P) stepR hR s o u b r r' [] hr
  rw [invoke_eq_combine stepR hP (s, r), invoke_eq_combine stepR' hP (s, r')] at h
  obtain ⟨h₁, h₂, h₃⟩ := Option.rel_some_some.mp h
  exact ⟨h₃, h₁, h₂⟩

/-- An invocation fed by an automaton is the invocation against the automaton. -/
theorem feed_automatonSystem (r₀ : R) :
    ∀ (n : ℕ) (s : S) (o : O) (u : U o) (h : List ((Σ j, X j) × (Σ j, Y j)))
      (rh : List (Σ j, X j)) (m : Mode S O J U X Y) (x : Σ l, twoFam U Y l),
      P.step m x = some (P.emit s o u h) →
      (P.feed (automatonSystem stepR r₀) (n + 1) m x rh).map
          (fun t => (t.1, stateAfter stepR r₀ t.2.1, t.2.2)) =
        (P.invoke stepR s o u n (stateAfter stepR r₀ rh) h).map
          (fun t => (.idle t.1.1, t.1.2, ⟨o, t.2⟩)) := by
  intro n
  induction n with
  | zero =>
    intro s o u h rh m x hs
    rw [feed, hs]
    cases hq : P s o u h with
    | inl a => simp [emit, hq, invoke]
    | inr q =>
      simp only [emit, hq]
      simp [automatonSystem_dom, feed, invoke, hq]
  | succ n ih =>
    intro s o u h rh m x hs
    rw [feed, hs]
    cases hq : P s o u h with
    | inl a => simp [emit, hq, invoke]
    | inr q =>
      simp only [emit, hq]
      have hd : (automatonSystem stepR r₀ (rh ++ [⟨q.1, q.2⟩])).Dom :=
        (automatonSystem_dom stepR r₀ _).mpr (by simp)
      rw [dif_pos hd]
      have hget : (automatonSystem stepR r₀ (rh ++ [⟨q.1, q.2⟩])).get hd =
          ⟨q.1, (stepR (stateAfter stepR r₀ rh) q.1 q.2).2⟩ := by
        simp [automatonSystem_snoc]
      rw [hget]
      dsimp only
      refine (ih s o u (h ++ [(q, ⟨q.1, (stepR (stateAfter stepR r₀ rh) q.1 q.2).2⟩)])
        (rh ++ [⟨q.1, q.2⟩]) (.busy o s u h q)
        ⟨⟨some (), q.1⟩, (stepR (stateAfter stepR r₀ rh) q.1 q.2).2⟩ (by simp [step])).trans ?_
      simp only [invoke, hq, stateAfter_snoc]

/-- **Attaching a program to an automaton is the combined automaton.** -/
theorem inline_automatonSystem {b : ℕ} (hP : P.Bounded b) (s : S) (r₀ : R) :
    P.inline (automatonSystem stepR r₀) b s = automatonSystem (P.combine stepR hP) (s, r₀) := by
  have after : ∀ us : List (Σ o, U o),
      (P.inlineAfter (automatonSystem stepR r₀) b s us).map
          (fun mr => (mr.1, stateAfter stepR r₀ mr.2)) =
        some (.idle (stateAfter (P.combine stepR hP) (s, r₀) us).1,
          (stateAfter (P.combine stepR hP) (s, r₀) us).2) := by
    intro us
    induction us using List.reverseRecOn with
    | nil => rfl
    | append_singleton us a ih =>
      rw [inlineAfter_snoc, stateAfter_snoc]
      cases hst : P.inlineAfter (automatonSystem stepR r₀) b s us with
      | none => rw [hst] at ih; cases ih
      | some mr =>
        rw [hst] at ih
        obtain ⟨m, rh⟩ := mr
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ih
        obtain ⟨rfl, hrh⟩ := ih
        have hf := feed_automatonSystem (P := P) stepR r₀ b (stateAfter (P.combine stepR hP) (s, r₀) us).1
          a.1 a.2 [] rh (.idle (stateAfter (P.combine stepR hP) (s, r₀) us).1) ⟨⟨none, a.1⟩, a.2⟩ rfl
        rw [hrh, invoke_eq_combine stepR hP] at hf
        cases hfeed : P.feed (automatonSystem stepR r₀) (b + 1) (.idle _) ⟨⟨none, a.1⟩, a.2⟩ rh with
        | none => rw [hfeed] at hf; cases hf
        | some t =>
          rw [hfeed] at hf
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
          rw [Option.bind_some, hfeed]
          simp only [Option.map_some, hf.1, hf.2.1]
  funext us
  rcases List.eq_nil_or_concat us with rfl | ⟨us, a, rfl⟩
  · simp [inline]
  rw [List.concat_eq_append, inline_snoc, automatonSystem_snoc]
  have ha := after us
  cases hst : P.inlineAfter (automatonSystem stepR r₀) b s us with
  | none => rw [hst] at ha; cases ha
  | some mr =>
    rw [hst] at ha
    obtain ⟨m, rh⟩ := mr
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, hrh⟩ := ha
    have hf := feed_automatonSystem (P := P) stepR r₀ b (stateAfter (P.combine stepR hP) (s, r₀) us).1
          a.1 a.2 [] rh (.idle (stateAfter (P.combine stepR hP) (s, r₀) us).1) ⟨⟨none, a.1⟩, a.2⟩ rfl
    rw [hrh, invoke_eq_combine stepR hP] at hf
    cases hfeed : P.feed (automatonSystem stepR r₀) (b + 1) (.idle _) ⟨⟨none, a.1⟩, a.2⟩ rh with
    | none => rw [hfeed] at hf; cases hf
    | some t =>
      rw [hfeed] at hf
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      rw [Option.bind_some, hfeed]
      simp only [Option.map_some, Part.coe_some, hf.2.2]

/-- Attached to automata with the same system, a program gives automata with the same system. -/
theorem combine_congr {R' : Type} {stepR' : R' → (j : J) → X j → R' × Y j} {b : ℕ}
    (hP : P.Bounded b) (s : S) {r₀ : R} {r₀' : R'}
    (h : automatonSystem stepR r₀ = automatonSystem stepR' r₀') :
    automatonSystem (P.combine stepR hP) (s, r₀) = automatonSystem (P.combine stepR' hP) (s, r₀') := by
  rw [← inline_automatonSystem stepR hP, ← inline_automatonSystem stepR' hP, h]

/-- **A program on the outside domain `F` attached to an automaton on the inside domain `E`** is
the combined automaton on `F`, when the program is a DDC from `E`. -/
theorem trim_apply_ofProgramOn_automaton {b : ℕ} (hP : P.Bounded b) (s : S) (r₀ : R)
    {E : List (Σ j, X j) → Prop} {F : List (Σ o, U o) → Prop}
    (hE : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (hα : IsDDCFrom E F b (DDC.ofProgramOn s P F)) :
    trim (apply (DDC.ofProgramOn s P F) (filterDom E (automatonSystem stepR r₀))) =
      filterDom F (automatonSystem (P.combine stepR hP) (s, r₀)) := by
  let aut := automatonSystem stepR r₀
  have hsub : ∀ h y, y ∈ filterDom E aut h → y ∈ aut h :=
    fun h y hy => ((filterDom_mem_iff E aut h y).mp hy).2
  have hdomE : ∀ h, (filterDom E aut h).Dom ↔ E h := by
    intro h
    rw [filterDom_dom, automatonSystem_dom]
    exact ⟨fun hd => hd.1, fun hd => ⟨hd, fun he => hE.1 (he ▸ hd)⟩⟩
  obtain ⟨-, hdom⟩ := hα.mapsDomain hF _ ((automatonSystem_isDDS stepR r₀).filterDom E hE.2)
    (fun h x y hy => automatonSystem_replies stepR r₀ h x y (hsub _ _ hy)) hdomE
  have hfull : trim (apply (DDC.ofProgramOn s P F) aut) =
      filterDom F (automatonSystem (P.combine stepR hP) (s, r₀)) := by
    rw [trim_apply_ofProgramOn s hP F hF.2, inline_automatonSystem stepR hP]
  rw [← hfull]
  apply IsDDS.eq_of_replies_iff (SilentAtEmpty.isDDS_trim (by simp [SilentAtEmpty, apply_eq]))
    (SilentAtEmpty.isDDS_trim (by simp [SilentAtEmpty, apply_eq]))
  apply replies_iff_of_dom_iff
  · intro h
    rw [hdom, hfull, filterDom_dom, automatonSystem_dom]
    exact ⟨fun hd => ⟨hd, fun he => hF.1 (he ▸ hd)⟩, fun hd => hd.1⟩
  · intro xs ys hr
    rw [replies_trim_iff, apply_eq] at hr ⊢
    exact hr.interconnect_mono (pair_mono (fun _ _ h => h) hsub)

end Automaton

end Program

end SystemAlgebra
