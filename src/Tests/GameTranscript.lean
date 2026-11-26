module

public import RandomSystems.Game.Transcript
public import RandomSystems.Typed.AutomatonGame

/-!
# Completed game scores

An echo resource accepts two Boolean queries. The observer asks `false`, then the negation
of its first reply. An initially true condition wins after a reply, but not before one.
The same concrete game and legal observer instantiate the PDG score law at two horizons.
-/

@[expose] public section

namespace Tests.GameTranscript

open SystemAlgebra Probability Probability.Distribution

/-- Two Boolean queries and replies on one port. -/
abbrev port : Interface := Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) 2

/-- Echo the query and retain the unit state. -/
def echo (_ : Unit) (_ : port.I) (b : port.X ()) : Unit × port.Y () := ((), b)

/-- The hidden condition is true on every input history, including the empty one. -/
def always : MC (Σ i, port.X i) := ⟨fun _ => True, fun _ _ _ h => h⟩

/-- A deterministic presentation of the echo resource and its initially true condition. -/
noncomputable def game : DDG (Σ i, port.X i) (Σ i, port.Y i) :=
  (⟨(port.automatonDDS echo ()).1, (port.automatonDDS echo ()).2.1⟩, always)

/-- Ask `false`, then negate the first reply; stop after the second reply. -/
def adaptive : DDE (Σ i, port.X i) (Σ i, port.Y i) :=
  ⟨fun ys => match ys with
    | [] => Part.some ⟨(), false⟩
    | [⟨(), b⟩] => Part.some ⟨(), !b⟩
    | _ => Part.none, by
      intro ys y hd
      rcases ys with _ | ⟨z, zs⟩
      · exact Part.some_dom _
      · rcases zs with _ | ⟨z', zs⟩
        · rcases z with ⟨⟨⟩, b⟩
          exact Part.some_dom _
        · simp only [List.cons_append, Part.not_none_dom] at hd⟩

lemma adaptive_bounded : QueryBounded 2 adaptive := by
  intro ys hd
  rcases ys with _ | ⟨z, zs⟩
  · simp only [List.length_nil]; omega
  · rcases zs with _ | ⟨z', zs⟩
    · simp only [List.length_cons, List.length_nil]; omega
    · exact False.elim (Part.not_none_dom hd)

lemma adaptive_compatible : port.inputDomain.Compatible adaptive := by
  intro _ _ h x _ _ hx
  have hl := adaptive_bounded (h.map Prod.snd) (Part.dom_iff_mem.mpr ⟨x, hx⟩)
  simp only [List.length_map] at hl
  exact ⟨List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _), by
    simp only [List.length_append, List.length_singleton, List.length_map]; omega⟩

/-- The transcript adapts its second query to the first reply. -/
lemma adaptive_transcript : game.1.1.tr adaptive.1 2 =
    [(⟨(), false⟩, ⟨(), false⟩), (⟨(), true⟩, ⟨(), true⟩)] := by
  simp only [port, Interface.queryBudget, ne_eq, System.tr, adaptive, List.map_nil,
    Part.some_dom, ↓reduceDIte, game, Interface.automatonDDS, Part.get_some, List.nil_append,
    filterDom, List.cons_ne_self, not_false_eq_true, List.length_cons, List.length_nil,
    zero_add, Nat.one_le_ofNat, and_self, ↓reduceIte, automatonSystem, echo, Sigma.eta,
    List.getLast?_singleton, Option.map_some, Part.coe_some, List.map_cons, Bool.not_false,
    List.cons_append, reduceCtorEq, Nat.reduceAdd, Std.le_refl, List.getLast?_cons_cons]

/-- An environment that stops immediately emits no winning bit, even at a later horizon. -/
example : finalMBO ((DDG.withMBO game).1.tr
    (DDE.blindMBO (DDE.ofQueries [])).1 2) = false := by
  simp only [finalMBO, System.tr, DDE.blindMBO, DDE.ofQueries, fixedQueries,
    List.length_map, List.length_nil, not_lt_zero, not_false_eq_true, getElem?_neg,
    Part.coe_none, List.map_nil, Part.not_none_dom, ↓reduceDIte, List.getLast?_nil,
    Option.map_none, Option.getD_none]

/-- One legal reply already emits an initially true bit. -/
example : finalMBO ((DDG.withMBO game).1.tr (DDE.blindMBO adaptive).1 1) = true := by
  rw [DDG.finalMBO_tr_withMBO_iff]
  simp only [port, Interface.queryBudget, ne_eq, System.tr, adaptive, List.map_nil,
    Part.some_dom, ↓reduceDIte, game, Interface.automatonDDS, always, Part.get_some,
    List.nil_append, filterDom, List.cons_ne_self, not_false_eq_true, List.length_cons,
    List.length_nil, zero_add, Nat.one_le_ofNat, and_self, ↓reduceIte, automatonSystem,
    echo, Sigma.eta, List.getLast?_singleton, Option.map_some, Part.coe_some, List.map_cons]

/-- A legal completed interaction emits the initially true bit. -/
example : finalMBO ((DDG.withMBO game).1.tr (DDE.blindMBO adaptive).1 2) = true := by
  rw [DDG.finalMBO_tr_withMBO_iff, adaptive_transcript]
  exact ⟨List.cons_ne_nil _ _, trivial⟩

/-- Retain the single initial state; the distribution is normalized by construction. -/
noncomputable def samples := PDG.ofAutomaton port echo (ProbDist.single ()) (fun _ => always)

/-- The observer's final decision does not affect the hidden game score. -/
noncomputable def winner : DDD port.I port.X port.Y := envProbe adaptive (fun _ => True)

lemma winner_isDDD : IsDDD winner := envProbe_isDDD adaptive_bounded

lemma winner_compatible :
    (PDG.behavior samples.1 samples.2).visible.Compatible (ddeOf winner_isDDD).1 := by
  have admitted := Domain.envProbe_decisionCompatible adaptive_compatible (fun _ => True)
  let G := TypedGame.ofAutomaton port echo (ProbDist.single ()) (fun _ => always)
  change G.visible.1.Compatible (ddeOf winner_isDDD).1
  exact admitted.environment winner_isDDD _
    (TypedGame.ofAutomaton port echo (ProbDist.single ()) (fun _ => always)).visible.2

/-- The same score is the sampled condition mass at either certified stopping horizon. -/
example : let n := winner_isDDD.2.1.choose
    (PDG.behavior samples.1 samples.2).winProbability winner winner_isDDD =
      samples.1.mass (fun g => g.1.1.1.tr (ddeOf winner_isDDD).1 (n + 1) ≠ [] ∧
        g.1.2.1 ((g.1.1.1.tr (ddeOf winner_isDDD).1 (n + 1)).map Prod.fst)) := by
  apply PDG.winProbability_behavior _ _ _ _ winner_compatible
  intro ys hd
  exact (ddeOf_bounded winner_isDDD ys hd).trans_le (Nat.le_succ _)

example : let n := winner_isDDD.2.1.choose
    (PDG.behavior samples.1 samples.2).winProbability winner winner_isDDD =
      samples.1.mass (fun g => g.1.1.1.tr (ddeOf winner_isDDD).1 n ≠ [] ∧
        g.1.2.1 ((g.1.1.1.tr (ddeOf winner_isDDD).1 n).map Prod.fst)) :=
  PDG.winProbability_behavior _ _ _ _ winner_compatible (ddeOf_bounded winner_isDDD)

#print axioms PDG.winProbability_behavior

end Tests.GameTranscript
