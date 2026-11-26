module

public import RandomSystems.Distance.Decision

/-!
# Query bounds survive a final decision

Natural-number replies select the second query adaptively. Adding a decision keeps its exact
two-query bound, including the zero-query case of an immediately stopping environment.
-/

@[expose] public section

namespace Tests.ProbeQueryBound

open SystemAlgebra

/-- One port accepts and returns arbitrary natural numbers. -/
abbrev Value := Σ _ : Unit, ℕ

/-- Ask `0`, then the successor of the first reply, and stop after two replies. -/
def adaptive : DDE Value Value :=
  ⟨fun ys => match ys with
    | [] => Part.some ⟨(), 0⟩
    | [⟨(), n⟩] => Part.some ⟨(), n + 1⟩
    | _ => Part.none, by
      intro ys y hd
      rcases ys with _ | ⟨z, zs⟩
      · exact Part.some_dom _
      · rcases zs with _ | ⟨z', zs⟩
        · rcases z with ⟨⟨⟩, n⟩
          exact Part.some_dom _
        · simp only [List.cons_append, Part.not_none_dom] at hd⟩

lemma adaptive_bounded : QueryBounded 2 adaptive := by
  intro ys hd
  rcases ys with _ | ⟨z, zs⟩
  · simp only [List.length_nil]; omega
  · rcases zs with _ | ⟨z', zs⟩
    · simp only [List.length_cons, List.length_nil]; omega
    · exact False.elim (Part.not_none_dom hd)

/-- The decision tests both replies, and still costs no extra oracle query. -/
example : QueryBounded 2 (ddeOf (envProbe_isDDD
    (A := fun t => t.2 = [⟨(), 3⟩, ⟨(), 4⟩]) adaptive_bounded)) :=
  ddeOf_envProbe_queryBounded adaptive_bounded _

/-- The probe really asks its adaptive second query after receiving `3`. -/
lemma second_query : (ddeOf (envProbe_isDDD
    (A := fun _ => True) adaptive_bounded)).1 [⟨(), 3⟩] = Part.some ⟨(), 4⟩ := by
  have fits : EFits adaptive.1 [⟨(), 3⟩] :=
    EFits.snoc EFits.nil (show (⟨(), 0⟩ : Value) ∈ adaptive.1 [] from Part.mem_some _) rfl
  exact (envOf_trim_envProbe (A := fun _ => True) fits).trans rfl

/-- The exact two-query example cannot satisfy a one-query bound. -/
example : ¬ QueryBounded 1 (ddeOf (envProbe_isDDD
    (A := fun _ => True) adaptive_bounded)) := by
  intro hn
  have queried : ((ddeOf (envProbe_isDDD
      (A := fun _ => True) adaptive_bounded)).1 [⟨(), 3⟩]).Dom := by
    rw [second_query]
    exact Part.some_dom _
  exact Nat.lt_irrefl 1 (hn _ queried)

/-- Stop before any query. -/
def stop : DDE Value Value := DDE.ofQueries []

lemma stop_bounded : QueryBounded 0 stop := by
  intro ys hd
  simpa only [stop, DDE.ofQueries, fixedQueries, Part.ofOption_dom,
    isSome_getElem?, List.length_nil] using hd

/-- Even an accepting final decision preserves the zero-query bound. -/
example : QueryBounded 0 (ddeOf (envProbe_isDDD (A := fun _ => True) stop_bounded)) :=
  ddeOf_envProbe_queryBounded stop_bounded _

#print axioms ddeOf_envProbe_queryBounded

end Tests.ProbeQueryBound
