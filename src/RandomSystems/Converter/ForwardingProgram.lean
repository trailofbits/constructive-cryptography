module

public import RandomSystems.Converter.Program

/-!
# Programs that forward selected inputs

A forwarding program either answers directly or passes the current outside query inside
once, unchanged. `insideQueries_sublist_outsideInputs` proves that its inside queries form a
subsequence of the outside inputs, even while an invocation is pending.
`ofProgramOn_isDDCFrom_of_forwarding` then transfers admission from the outside domain to
nonempty inside subsequences. Direct replies may read the retained state
and shorten the inside history.

This is the zero-or-one-call case of [1, Definition 3.8, p. 62]: “There is a finite upper
bound on the number of consecutive outputs of the form (in, x).”

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

@[expose] public section

open scoped List

namespace SystemAlgebra.Program

/-- A program that calls only before any inside exchange makes at most one call per invocation. -/
lemma bounded_one_of_history_eq_nil
    -- `P` has retained state `S`, ports `J`, inputs `X j` and replies `Y j` on both sides.
    {S J : Type} {X Y : J → Type} {P : Program S J J X Y X Y}
    -- `hcall` permits an inside call only while the inside history `h` is empty.
    (hcall : ∀ s j x h q, P.Consistent s j x h → P s j x h = .inr q →
      h = []) : P.Bounded 1 := by
  intro s j x h q hc hq
  rw [hcall s j x h q hc hq]
  exact Nat.zero_lt_one

end SystemAlgebra.Program

namespace SystemAlgebra.DDC

-- `S` carries retained states; ports `J` have input alphabets `X j` and reply alphabets `Y j`.
variable {S J : Type} {X Y : J → Type}
  -- `P` is the forwarding program, initialized in retained state `s`.
  {P : Program S J J X Y X Y} {s : S}

/-- The issued inside queries are a subsequence of the outside inputs. -/
theorem insideQueries_sublist_outsideInputs
    -- `hcall` permits only the unchanged current input, before any inside exchange.
    (hcall : ∀ s' j x h q, P.Consistent s' j x h → P s' j x h = .inr q →
      h = [] ∧ q = ⟨j, x⟩)
    -- `hr` admits the converter transcript `h`, starting from state `s`.
    {h : List ((Σ l, twoFam X Y l) × (Σ l, twoFam Y X l))}
    (hr : Replies (DDC.ofProgram s P) (h.map Prod.fst) (h.map Prod.snd)) :
    insideQueries (h.map Prod.snd) <+ outsideInputs (h.map Prod.fst) := by
  -- An outside input adds zero or one matching call; an inside reply completes that call.
  induction h using List.reverseRecOn with
  | nil => exact List.Sublist.refl []
  | append_singleton h z ih =>
    rcases z with ⟨x, y⟩
    simp only [List.map_append, List.map_singleton] at hr ⊢
    obtain ⟨hr₀, hy⟩ := replies_snoc.mp hr
    have prior := ih hr₀
    -- Replay the earlier transcript; the last exchange advances its final mode `m₀`.
    obtain ⟨m₀, hm₀⟩ := after_of_replies hr₀
    have hmem : y ∈ DDC.ofProgram s P (h.map Prod.fst ++ [x]) := by
      rw [hy]; exact Part.mem_some y
    obtain ⟨m₁, m', h₁, hs⟩ := (mem_ofProgram_snoc s P _ x y).mp hmem
    rw [hm₀] at h₁
    obtain rfl := Option.some.inj h₁
    have sound₀ := (after_invariant hm₀).1
    rw [insideQueries_append, outsideInputs_append]
    rcases Program.step_cases P hs with ⟨s', j, u, rfl, rfl, he⟩ |
      ⟨j, s', u, hs', q, v, rfl, rfl, he⟩
    · -- A direct answer adds no inside query; forwarding appends the same query on both sides.
      rcases Program.emit_cases P s' j u [] with ⟨s'', w, hw, hE⟩ | ⟨q, hq, hE⟩
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        simp only [insideQueries_outside, outsideInputs_outside, List.append_nil]
        exact prior.trans (List.sublist_append_left _ _)
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        obtain ⟨_, rfl⟩ := hcall s' j u [] q (P.consistent_nil s' j u) hq
        simpa only [insideQueries_inside, outsideInputs_outside] using
          prior.append (List.Sublist.refl [⟨j, u⟩])
    · -- After one inside reply, another call would contradict the empty-exchange requirement.
      have hc := sound₀.1.snoc sound₀.2 v
      rcases Program.emit_cases P s' j u (hs' ++ [(q, ⟨q.1, v⟩)]) with
        ⟨s'', w, hw, hE⟩ | ⟨q', hq', hE⟩
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        simpa only [insideQueries_outside, outsideInputs_inside, List.append_nil] using prior
      · have hz := (hcall s' j u _ q' hc hq').1
        simp only [List.append_eq_nil_iff, List.cons_ne_self, and_false] at hz

/-- Forwarding preserves domains when every nonempty subsequence of an admitted outside
history is admitted inside, with at most one call per outside input. -/
lemma ofProgramOn_isDDCFrom_of_forwarding
    -- `hcall` allows one unchanged inside call per outside input, or a direct answer.
    (hcall : ∀ s' j x h q, P.Consistent s' j x h → P s' j x h = .inr q →
      h = [] ∧ q = ⟨j, x⟩)
    -- `E`, `F` are inside and outside domains on the same query alphabet.
    {E F : List (Σ j, X j) → Prop}
    -- `hF` closes the outside domain under nonempty prefixes.
    (hF : ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    -- `hsub` admits every nonempty subsequence inside, including a pending query.
    (hsub : ∀ {xs ys}, xs <+ ys → xs ≠ [] → F ys → E xs) :
    IsDDCFrom E F 1 (DDC.ofProgramOn s P F) := by
  apply ofProgramOn_isDDCFrom (Program.bounded_one_of_history_eq_nil (fun s j x h q hc hq =>
    (hcall s j x h q hc hq).1)) hF
  intro h hr hf
  -- The subsequence includes a pending inside query.
  have hs := insideQueries_sublist_outsideInputs hcall hr
  by_cases he : insideQueries (h.map Prod.snd) = []
  · exact Or.inl he
  · right
    -- A nonempty inside subsequence forces a nonempty, admitted outside history.
    rcases hf with hz | hf
    · rw [hz] at hs
      exact False.elim (he (List.sublist_nil.mp hs))
    · exact hsub hs he hf

end SystemAlgebra.DDC
