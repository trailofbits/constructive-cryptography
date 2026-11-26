module

public import RandomSystems.Game.FunctionGame

/-!
# Functional monitors on their admitted domains

The law applies to an unbounded natural-number alphabet and an initially true condition.
A second monitor detects input `7`: on its one-query domain the condition is determined by
that input, while on a rejected two-query history it need not equal the last-input predicate.
-/

@[expose] public section

namespace Tests.FunctionalGameMonitor

open SystemAlgebra

/-- Natural-number queries at one port; this alphabet has no finite-type instance. -/
abbrev Input := Σ _ : Unit, Nat

/-- Increment the query at the same port. -/
def increment (x : Input) : Input := ⟨x.1, x.2 + 1⟩

/-- Admit every nonempty input history, with no bound on its length. -/
def nonemptyHistory (xs : List Input) : Prop := xs ≠ []

lemma nonemptyHistory_domain : ¬ nonemptyHistory [] ∧
    ∀ {initial history}, initial <+: history → initial ≠ [] →
      nonemptyHistory history → nonemptyHistory initial :=
  ⟨fun h => h rfl, fun _ hn _ => hn⟩

/-- This monitor already holds before the first query. -/
def always : MC Input := ⟨fun _ => True, fun _ _ _ _ => True.intro⟩

/-- The generic equation permits an initially true condition on an unbounded domain. -/
lemma always_function :
    DDG.withMBO (DDS.ofFunction nonemptyHistory nonemptyHistory_domain increment, always) =
      DDS.ofFunction nonemptyHistory nonemptyHistory_domain
        (fun x => tagMBO true (increment x)) := by
  simpa only [decide_true] using DDG.withMBO_ofFunction nonemptyHistory nonemptyHistory_domain
    increment always (fun _ => True) (fun _ _ _ => Iff.rfl)

/-- Initial truth still emits no reply before the first query. -/
example : (DDG.withMBO
    (DDS.ofFunction nonemptyHistory nonemptyHistory_domain increment, always)).1 [] =
      Part.none := by
  rw [always_function]
  simp only [DDS.ofFunction, nonemptyHistory, ne_eq, not_true_eq_false, ite_false]

/-- Two legal queries are allowed; the last reply carries the current condition. -/
example : (DDG.withMBO
    (DDS.ofFunction nonemptyHistory nonemptyHistory_domain increment, always)).1
      [⟨(), 1⟩, ⟨(), 3⟩] = Part.some ⟨(), (4, true)⟩ := by
  rw [always_function]
  change (DDS.ofFunction nonemptyHistory nonemptyHistory_domain _).1
    ([⟨(), 1⟩] ++ [⟨(), 3⟩]) = _
  rw [DDS.ofFunction_snoc, ite_eq_left
    (show nonemptyHistory ([⟨(), 1⟩] ++ [⟨(), 3⟩]) from List.cons_ne_nil _ _)]
  rfl

/-- Admit at most one query. -/
def oneQuery (xs : List Input) : Prop := xs ≠ [] ∧ xs.length ≤ 1

lemma oneQuery_domain : ¬ oneQuery [] ∧
    ∀ {initial history}, initial <+: history → initial ≠ [] →
      oneQuery history → oneQuery initial :=
  ⟨fun h => h.1 rfl, fun hp hn hd => ⟨hn, hp.length_le.trans hd.2⟩⟩

/-- The condition holds once an input carrying `7` has appeared. -/
def seenSeven : MC Input :=
  ⟨fun xs => ∃ x ∈ xs, x.2 = 7,
    fun {_ _} hp ⟨x, hx, he⟩ => ⟨x, hp.sublist.subset hx, he⟩⟩

/-- The last-input contract is needed only on admitted histories. -/
example : DDG.withMBO (DDS.ofFunction oneQuery oneQuery_domain increment, seenSeven) =
    DDS.ofFunction oneQuery oneQuery_domain
      (fun x => tagMBO (decide (x.2 = 7)) (increment x)) := by
  apply DDG.withMBO_ofFunction
  intro xs x admitted
  have empty : xs = [] := by
    apply List.length_eq_zero_iff.mp
    have bound := admitted.2
    simp only [List.length_append, List.length_singleton] at bound
    omega
  subst xs
  simp only [seenSeven, List.nil_append, List.mem_singleton, exists_eq_left]

/-- Off the admitted domain, a previous `7` need not agree with the final input test. -/
example : seenSeven.1 [⟨(), 7⟩, ⟨(), 3⟩] ∧ ¬ ((⟨(), 3⟩ : Input).2 = 7) := by
  exact ⟨⟨⟨(), 7⟩, List.mem_cons_self, rfl⟩, by change ¬ (3 : Nat) = 7; omega⟩

#print axioms DDG.withMBO_ofFunction

end Tests.FunctionalGameMonitor
