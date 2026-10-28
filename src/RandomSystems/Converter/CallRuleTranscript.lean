import RandomSystems.Converter.Calls
import RandomSystems.Converter.CallTranscript

/-!
# Transcripts of direct call rules

A call transcript's input prefix remembers precisely the replies already received in the
current invocation. This links a pointwise call schedule to the canonical complete-history DDC.
-/

namespace SystemAlgebra

/-- The current invocation after the first `n` completed inside exchanges of a call. -/
lemma currentCall_callTranscript_take {O J : Type} {U V : O → Type} {X Y : J → Type}
    (before : List (Σ l, twoFam U Y l)) (u : Σ o, U o)
    (qs : List ((Σ j, X j) × (Σ j, Y j))) (v : Σ o, V o) (n : Nat) :
    currentCall (before ++ ((callTranscript u qs v).map Prod.fst).take (n + 1)).reverse [] =
      some (u, (qs.take n).map Prod.snd) := by
  rw [callTranscript, callSteps_map_fst]
  simp only [List.take_succ_cons, ← List.map_take]
  simpa only [List.map_map, Function.comp_def] using
    (currentCall_reverse_append_call before u ((qs.take n).map Prod.snd))

/-- A pointwise schedule for one call determines every complete-history output prefix,
independently of preceding calls. -/
lemma callRule_callTranscript_step {O J : Type} {U V : O → Type} {X Y : J → Type}
    (call : (u : Σ o, U o) → List (Σ j, Y j) → V u.1 ⊕ (Σ j, X j))
    (before : List (Σ l, twoFam U Y l)) (u : Σ o, U o)
    (qs : List ((Σ j, X j) × (Σ j, Y j))) (v : V u.1)
    (hquery : ∀ n (hn : n < qs.length),
      call u ((qs.take n).map Prod.snd) = .inr qs[n].1)
    (hreturn : call u (qs.map Prod.snd) = .inl v)
    (n : Nat) (w : Σ l, twoFam V X l)
    (hw : ((callTranscript u qs ⟨u.1, v⟩).map Prod.snd)[n]? = some w) :
    callRule call (before ++ ((callTranscript u qs ⟨u.1, v⟩).map Prod.fst).take (n + 1)) =
      Part.some w := by
  have hlen : n < qs.length + 1 := by
    have h := (List.getElem?_eq_some_iff.mp hw).1
    rw [callTranscript, callSteps_map_snd] at h
    simpa only [List.length_append, List.length_map, List.length_cons, List.length_nil,
      zero_add] using h
  by_cases hn : n < qs.length
  · -- Before the last output, the pointwise rule issues the scheduled inside query.
    have hout : w = (⟨⟨some (), qs[n].1.1⟩, qs[n].1.2⟩ : Σ l, twoFam V X l) := by
      rw [callTranscript, callSteps_map_snd,
        List.getElem?_append_left (by simpa only [List.length_map] using hn),
        List.getElem?_map, List.getElem?_eq_getElem hn] at hw
      exact Option.some.inj hw.symm
    subst w
    simp only [callRule, currentCall_callTranscript_take, hquery n hn]
  · -- At the last output, all inside replies have arrived and the rule returns outside.
    have he : n = qs.length := by omega
    subst n
    have hout : w = (⟨⟨none, u.1⟩, v⟩ : Σ l, twoFam V X l) := by
      rw [callTranscript, callSteps_map_snd,
        List.getElem?_append_right (by simp only [List.length_map, le_refl])] at hw
      simpa only [List.length_map, tsub_self, List.getElem?_cons_zero,
        Option.some.injEq] using hw.symm
    subst w
    simp only [callRule, currentCall_callTranscript_take,
      List.take_of_length_le (le_refl _), hreturn]

/-- Under an exact phase contract, a completed call has exactly its advertised number of
inside queries. The upper-bound phase contract alone does not imply this equality. -/
lemma callRule_completed_exact_length {O J : Type} {U V : O → Type} {X Y : J → Type}
    (call : (u : Σ o, U o) → List (Σ j, Y j) → V u.1 ⊕ (Σ j, X j))
    (cost : (Σ o, U o) → Nat)
    (hphase : ∀ u replies, (call u replies).isRight = true ↔ replies.length < cost u)
    (u : Σ o, U o) (qs : List ((Σ j, X j) × (Σ j, Y j))) (v : V u.1)
    (hquery : ∀ n (hn : n < qs.length),
      call u ((qs.take n).map Prod.snd) = .inr qs[n].1)
    (hreturn : call u (qs.map Prod.snd) = .inl v) :
    (insideQueries ((callTranscript u qs ⟨u.1, v⟩).map Prod.snd)).length = cost u := by
  have hle : qs.length ≤ cost u := by
    by_contra hn
    have hnext := hquery (cost u) (by omega)
    have hphaseNext := (hphase u ((qs.take (cost u)).map Prod.snd)).mp (by
      rw [hnext]
      rfl)
    simp only [List.length_map, List.length_take] at hphaseNext
    omega
  have hge : cost u ≤ qs.length := by
    by_contra hn
    have hmore := (hphase u (qs.map Prod.snd)).mpr (by
      simp only [List.length_map]
      omega)
    rw [hreturn] at hmore
    cases hmore
  rw [callTranscript, insideQueries_callSteps, List.length_map]
  omega

/-- Pointwise next-query and final-result equations make every sequence of fixed-function
calls a canonical converter transcript. -/
lemma replies_canon_callRule_of_schedule {O J : Type} {U V : O → Type} {X Y : J → Type}
    (call : (u : Σ o, U o) → List (Σ j, Y j) → V u.1 ⊕ (Σ j, X j))
    (f : ∀ j, X j → Y j) (g : ∀ o, U o → V o)
    (queries : (Σ o, U o) → List (Σ j, X j))
    (hquery : ∀ u n (hn : n < (queries u).length),
      call u (((queries u).take n).map fun x => ⟨x.1, f x.1 x.2⟩) =
        .inr (queries u)[n])
    (hreturn : ∀ u, call u ((queries u).map fun x => ⟨x.1, f x.1 x.2⟩) =
      .inl (g u.1 u.2))
    (us : List (Σ o, U o)) :
    let calls : List ((Σ o, U o) × List ((Σ j, X j) × (Σ j, Y j)) × (Σ o, V o)) :=
      us.map fun u =>
      (u, (queries u).map fun x => (x, ⟨x.1, f x.1 x.2⟩), ⟨u.1, g u.1 u.2⟩)
    Replies (canon (callRule call))
      ((calls.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.fst)
      ((calls.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.snd) := by
  dsimp only
  let calls : List ((Σ o, U o) × List ((Σ j, X j) × (Σ j, Y j)) × (Σ o, V o)) :=
    us.map fun u =>
    (u, (queries u).map fun x => (x, ⟨x.1, f x.1 x.2⟩), ⟨u.1, g u.1 u.2⟩)
  apply replies_canon_calls (c := callRule call) (by rfl) calls
  · -- A fixed-function reply is tagged with the query's inside label.
    intro c hc xy hxy
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hc
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hxy
    rfl
  · -- Earlier completed calls do not affect the current invocation's reply prefix.
    intro pre c post he n w hw
    have hc : c ∈ calls := by rw [he]; simp
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hc
    apply callRule_callTranscript_step call _ u _ (g u.1 u.2)
    · intro m hm
      simpa only [List.length_map, List.map_take, List.map_map, List.getElem_map,
        Function.comp_def] using
        hquery u m (by simpa only [List.length_map] using hm)
    · simpa only [List.map_map, Function.comp_def] using hreturn u
    · exact hw

/-- A fixed-function call schedule in the outside domain is a transcript of the restricted
canonical DDC. This is the systems-level realization step used by typed attachment. -/
lemma replies_callConverter_of_schedule {O J : Type} {U V : O → Type} {X Y : J → Type}
    (call : (u : Σ o, U o) → List (Σ j, Y j) → V u.1 ⊕ (Σ j, X j))
    (F : List (Σ o, U o) → Prop)
    (hF : ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (f : ∀ j, X j → Y j) (g : ∀ o, U o → V o)
    (queries : (Σ o, U o) → List (Σ j, X j))
    (hquery : ∀ u n (hn : n < (queries u).length),
      call u (((queries u).take n).map fun x => ⟨x.1, f x.1 x.2⟩) =
        .inr (queries u)[n])
    (hreturn : ∀ u, call u ((queries u).map fun x => ⟨x.1, f x.1 x.2⟩) =
      .inl (g u.1 u.2))
    (us : List (Σ o, U o)) (hUs : F us) :
    Replies (callConverter call F)
      ((us.flatMap fun u => callTranscript u ((queries u).map fun x =>
          (x, ⟨x.1, f x.1 x.2⟩)) ⟨u.1, g u.1 u.2⟩).map Prod.fst)
      ((us.flatMap fun u => callTranscript u ((queries u).map fun x =>
          (x, ⟨x.1, f x.1 x.2⟩)) ⟨u.1, g u.1 u.2⟩).map Prod.snd) := by
  let calls : List ((Σ o, U o) × List ((Σ j, X j) × (Σ j, Y j)) × (Σ o, V o)) :=
    us.map fun u =>
      (u, (queries u).map fun x => (x, ⟨x.1, f x.1 x.2⟩), ⟨u.1, g u.1 u.2⟩)
  have hprefix : ∀ {p h : List (Σ l, twoFam U Y l)}, p <+: h → p ≠ [] →
      (outsideInputs h = [] ∨ F (outsideInputs h)) →
      (outsideInputs p = [] ∨ F (outsideInputs p)) := by
    intro p h hp _ hh
    exact prefix_or_nil hF (p := outsideInputs p) (h := outsideInputs h) (by
      obtain ⟨e, rfl⟩ := hp
      exact ⟨outsideInputs e, (outsideInputs_append p e).symm⟩) hh
  have houtside : outsideInputs
      ((calls.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.fst) = us := by
    rw [outsideInputs_flatMap_callTranscript]
    simp only [calls, List.map_map, Function.comp_def]
    exact List.map_id us
  have hcanon := replies_canon_callRule_of_schedule call f g queries hquery hreturn us
  change Replies (canon (callRule call))
    ((calls.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.fst)
    ((calls.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.snd) at hcanon
  have hrestricted := (replies_filterDom_iff hprefix (canon (callRule call))
    (xs := (calls.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.fst)
    (ys := (calls.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.snd)
    (by intro _; exact Or.inr (houtside ▸ hUs))).mpr hcanon
  simpa only [callConverter, calls, List.flatMap_map] using hrestricted

end SystemAlgebra
