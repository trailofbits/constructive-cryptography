module

public import RandomSystems.Converter.Program

/-!
# Programs with fixed query schedules

A schedule `queries u` lists the inside queries of each outside invocation `u`, independently
of retained state and earlier replies. Its contracts hold for every state and every consistent
exchange prefix. The exact call cost fixes its length; the next-query equation fixes each entry.
The invariant
`DDC.insideQueries_append_remaining` shows that issued queries plus the pending suffix equal
the concatenated schedules of all outside inputs. `DDC.insideQueries_prefix_schedule` retains
just the prefix relation.

`DDC.ofProgramOn_isDDCFrom_of_schedule` turns admission of complete schedules into the domain
guarantee for the existing program converter. Nonempty-prefix closure covers pending calls;
an empty schedule requires no inside admission. This specializes the bounded internal calls
of [1, Definition 2.2.2, pp. 17–18: “a bounded number of queries to the inside interfaces”].

## References

1. D. Jost. *On Generalizations of Composable Security*. Doctoral thesis, ETH Zurich, 2020.
-/

@[expose] public section

namespace SystemAlgebra.Program

-- `S` carries retained states; `O`, `U`, `V` are outside ports, inputs and replies.
-- `J`, `X`, `Y` give the corresponding inside alphabets.
variable {S O J : Type} {U V : O → Type} {X Y : J → Type}

/-- The scheduled queries still unissued by a program mode. An idle mode owes none; a busy
mode has already issued its pending query, so its remaining suffix starts after that query. -/
def Mode.remainingQueries (queries : (Σ o, U o) → List (Σ j, X j)) :
    Mode S O J U X Y → List (Σ j, X j)
  | .idle _ => []
  | .busy o _ u h _ => (queries ⟨o, u⟩).drop (h.length + 1)

end SystemAlgebra.Program

namespace SystemAlgebra.DDC

-- `S` carries retained states; `O`, `U`, `V` are outside ports, inputs and replies.
-- `J`, `X`, `Y` give the corresponding inside alphabets.
variable {S O J : Type} {U V : O → Type} {X Y : J → Type}
    -- `P` is the program body and `s` its initial retained state.
    {P : Program S O J U V X Y} {s : S}

/-- Issued queries followed by the pending schedule equal the schedules of all outside inputs. -/
lemma insideQueries_append_remaining
    -- `queries u` is the complete inside schedule for outside input `u`.
    (queries : (Σ o, U o) → List (Σ j, X j))
    -- `hcost` fixes the completion length; `hnext` identifies each next query on own exchanges.
    (hcost : P.Costs fun u => (queries u).length)
    (hnext : ∀ s' o u h q, P.Consistent s' o u h → P s' o u h = .inr q →
      (queries ⟨o, u⟩)[h.length]? = some q)
    -- `h` is a converter transcript; `hr` admits it, and `hm` identifies its final mode `m`.
    {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies (DDC.ofProgram s P) (h.map Prod.fst) (h.map Prod.snd))
    {m : Program.Mode S O J U X Y} (hm : P.after s (h.map Prod.fst) = some m) :
    insideQueries (h.map Prod.snd) ++ m.remainingQueries queries =
      (outsideInputs (h.map Prod.fst)).flatMap queries := by
  -- Track the unissued suffix as each outside input or inside reply extends the transcript.
  induction h using List.reverseRecOn generalizing m with
  | nil =>
    obtain rfl : m = .idle s := (Option.some.inj hm).symm
    rfl
  | append_singleton h z ih =>
    rcases z with ⟨x, y⟩
    simp only [List.map_append, List.map_singleton] at hr hm ⊢
    obtain ⟨hr₀, hy⟩ := replies_snoc.mp hr
    obtain ⟨m₀, hm₀⟩ := after_of_replies hr₀
    have prior := ih hr₀ hm₀
    have hmem : y ∈ DDC.ofProgram s P (h.map Prod.fst ++ [x]) := by
      rw [hy]; exact Part.mem_some y
    obtain ⟨m₁, m', h₁, hs⟩ := (mem_ofProgram_snoc s P _ x y).mp hmem
    rw [hm₀] at h₁
    obtain rfl := Option.some.inj h₁
    have hm' : P.after s (h.map Prod.fst ++ [x]) = some m' :=
      (Program.after_snoc_eq_some P s _ x m').mpr ⟨m₀, y, hm₀, hs⟩
    rw [hm] at hm'
    obtain rfl := Option.some.inj hm'
    have sound₀ := (after_invariant hm₀).1
    rw [insideQueries_append, outsideInputs_append, List.flatMap_append]
    rcases Program.step_cases P hs with ⟨s', o, u, rfl, rfl, he⟩ |
      ⟨o, s', u, hs', q, v, rfl, rfl, he⟩
    · -- A new invocation contributes its complete schedule, issuing its first query if nonempty.
      rcases Program.emit_cases P s' o u [] with ⟨s'', w, hw, hE⟩ | ⟨q, hq, hE⟩
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        have hl : queries ⟨o, u⟩ = [] := List.eq_nil_of_length_eq_zero
          ((hcost s' o u [] (P.consistent_nil s' o u)).2 _ hw).symm
        simpa only [Program.Mode.remainingQueries, insideQueries_outside,
          outsideInputs_outside, List.flatMap_singleton, hl, List.append_nil] using prior
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        obtain ⟨hlt, hq'⟩ := List.getElem?_eq_some_iff.mp
          (hnext s' o u [] q (P.consistent_nil s' o u) hq)
        have hd := List.drop_eq_getElem_cons hlt
        simp only [List.length_nil] at hq'
        simp only [List.length_nil, List.drop_zero, zero_add] at hd
        rw [hq'] at hd
        simp only [Program.Mode.remainingQueries, List.append_nil] at prior
        simp only [Program.Mode.remainingQueries, List.length_nil, zero_add,
          insideQueries_inside, outsideInputs_outside, List.flatMap_singleton,
          List.append_assoc, List.singleton_append]
        rw [← hd, prior]
    · -- A matching inside reply either completes the schedule or issues its next query.
      have hc := sound₀.1.snoc sound₀.2 v
      rcases Program.emit_cases P s' o u (hs' ++ [(q, ⟨q.1, v⟩)]) with
          ⟨s'', w, hw, hE⟩ | ⟨q', hq', hE⟩
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        have hl := (hcost s' o u _ hc).2 _ hw
        simp only [List.length_append, List.length_singleton] at hl
        simpa only [Program.Mode.remainingQueries, insideQueries_outside,
          outsideInputs_inside, List.flatMap_nil, List.append_nil, hl,
          List.drop_length] using prior
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        obtain ⟨hlt, hq''⟩ := List.getElem?_eq_some_iff.mp (hnext s' o u _ q' hc hq')
        have hd := List.drop_eq_getElem_cons hlt
        rw [hq''] at hd
        simp only [List.length_append, List.length_singleton] at hd
        simp only [Program.Mode.remainingQueries] at prior
        simp only [Program.Mode.remainingQueries, List.length_append, List.length_singleton,
          insideQueries_inside, outsideInputs_inside, List.flatMap_nil, List.append_nil,
          List.append_assoc, List.singleton_append]
        rw [← hd]
        exact prior

/-- Every issued inside history is a prefix of the complete scheduled history, including a
pending invocation. -/
lemma insideQueries_prefix_schedule
    -- `queries u` is the inside schedule for outside input `u`; `hcost` gives its exact length.
    (queries : (Σ o, U o) → List (Σ j, X j))
    (hcost : P.Costs fun u => (queries u).length)
    -- `hnext` identifies the next scheduled query after each consistent exchange prefix `h`.
    (hnext : ∀ s' o u h q, P.Consistent s' o u h → P s' o u h = .inr q →
      (queries ⟨o, u⟩)[h.length]? = some q)
    -- `hr` admits the transcript `h` from initial state `s`.
    {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies (DDC.ofProgram s P) (h.map Prod.fst) (h.map Prod.snd)) :
    insideQueries (h.map Prod.snd) <+: (outsideInputs (h.map Prod.fst)).flatMap queries := by
  obtain ⟨m, hm⟩ := after_of_replies hr
  exact ⟨m.remainingQueries queries, insideQueries_append_remaining queries hcost hnext hr hm⟩

/-- A scheduled program preserves domains when every complete schedule is empty or admitted.
Prefix closure then admits every pending invocation as well. -/
lemma ofProgramOn_isDDCFrom_of_schedule
    -- `queries u` is the complete schedule; `hcost` certifies its exact number of calls.
    (queries : (Σ o, U o) → List (Σ j, X j))
    (hcost : P.Costs fun u => (queries u).length)
    -- `hnext` identifies each call; `hbound` bounds every invocation by `b` calls.
    (hnext : ∀ s' o u h q, P.Consistent s' o u h → P s' o u h = .inr q →
      (queries ⟨o, u⟩)[h.length]? = some q)
    {b : ℕ} (hbound : ∀ u, (queries u).length ≤ b)
    -- `E`, `F` admit inside and outside input histories and are closed under nonempty prefixes.
    {E : List (Σ j, X j) → Prop} {F : List (Σ o, U o) → Prop}
    (hE : ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF : ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    -- `hmap` checks the concatenated complete schedules, retaining the empty-schedule case.
    (hmap : ∀ us, F us → us.flatMap queries = [] ∨ E (us.flatMap queries)) :
    IsDDCFrom E F b (DDC.ofProgramOn s P F) := by
  have hb : P.Bounded b := fun s o u h q hc hq =>
    ((hcost s o u h hc).1 q hq).trans_le (hbound ⟨o, u⟩)
  apply ofProgramOn_isDDCFrom hb hF
  intro h hr hf
  have hp := insideQueries_prefix_schedule queries hcost hnext hr
  by_cases he : insideQueries (h.map Prod.snd) = []
  · exact Or.inl he
  · right
    -- The issued prefix is nonempty, so its complete schedule is admitted rather than empty.
    rcases hf with hf | hf
    · rw [hf, List.flatMap_nil] at hp
      exact False.elim (he (List.prefix_nil.mp hp))
    · rcases hmap _ hf with hz | hz
      · rw [hz] at hp
        exact False.elim (he (List.prefix_nil.mp hp))
      · exact hE hp he hz

end SystemAlgebra.DDC
