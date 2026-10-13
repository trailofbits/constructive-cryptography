import RandomSystems.Typed.DSL.Programs
import RandomSystems.Typed.Filter
import RandomSystems.Typed.Source
import RandomSystems.Typed.Parallel

/-!
# Programs as converters

A program making at most `b` inside queries per invocation is a typed converter from `A` to
`B` whenever `B` admits every nonempty history of at most `b` times `A`'s bound; a program making
exactly `cost u` inside queries on `u` is a typed converter from outside histories of total cost
at most `q` to an inside budget of `q`.

## Main definitions

* `TypedConverter.ofProgram s P`: the converter of a bounded program
* `TypedConverter.ofCostedProgram s P`: the converter of a program with exact costs
* `TypedConverter.ofPreservingProgram s P ι`: the converter of a program preserving the
  partial port map `ι`, typed by per-port budgets

## Main results

* `TypedConverter.ofDDC_ofProgramOn_smul_ofPDS`: attaching the converter of a program to a
  typed system inlines the program
* `TypedConverter.ofDDC_ofProgramOn_smul_ofAutomaton`,
  `TypedConverter.ofProgram_smul_ofAutomaton`,
  `TypedConverter.ofPreservingProgram_smul_ofAutomaton`: attached to an automaton, it is
  the combined automaton
-/

namespace SystemAlgebra

open Classical

variable {S : Type}

/-- **The converter of a program** making at most `b` inside queries per invocation, started in
the state `s`. -/
noncomputable def TypedConverter.ofProgram {A B : Interface} (s : S)
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    (hB : ∀ xs, xs ≠ [] → xs.length ≤ b * A.bound → B.domain xs) : TypedConverter A B :=
  TypedConverter.ofDDC (DDC.ofProgramOn s P A.domain)
    (DDC.ofProgramOn_isDDCFrom hb A.nonempty_prefix.2 fun h hr hF => by
      by_cases hne : insideQueries (h.map Prod.snd) = []
      · exact Or.inl hne
      · exact Or.inr (hB _ hne
          (DDC.insideQueries_length_le_of_budget hb A.length_le hr hF)))

/-- **The converter of a program with exact costs**: outside histories of total cost at most `q`
make at most `q` inside queries. -/
noncomputable def TypedConverter.ofCostedProgram {A B : Interface} (s : S)
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    (cost : (Σ o, A.X o) → ℕ) (hc : P.Costs cost) {q : ℕ}
    (hA : ∀ us, A.domain us → (us.map cost).sum ≤ q)
    (hB : ∀ xs, xs ≠ [] → xs.length ≤ q → B.domain xs) : TypedConverter A B :=
  TypedConverter.ofDDC (DDC.ofProgramOn s P A.domain)
    (DDC.ofProgramOn_isDDCFrom hb A.nonempty_prefix.2 fun h hr hF => by
      by_cases hne : insideQueries (h.map Prod.snd) = []
      · exact Or.inl hne
      · refine Or.inr (hB _ hne ((DDC.insideQueries_length_le_of_costs hc hr).trans ?_))
        rcases hF with he | hF
        · rw [he]; exact Nat.zero_le _
        · exact hA _ hF)

/-- **The converter of a port-preserving program**: on outside histories with at most `q o`
queries at each label `o`, it makes at most `q o` inside queries at `ι o`, and none for
`ι o = none`. -/
noncomputable def TypedConverter.ofPreservingProgram {A B : Interface} (s : S)
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b) (ι : A.I → Option B.I)
    (hι : P.PortPreserving ι) (q : A.I → ℕ)
    (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    (hB : ∀ ys, ys ≠ [] → ys.length ≤ b * A.bound →
      (∀ o j, ι o = some j → (SystemAlgebra.restrict j ys).length ≤ q o) → B.domain ys) :
    TypedConverter A B :=
  TypedConverter.ofDDC (DDC.ofProgramOn s P A.domain)
    (DDC.ofProgramOn_isDDCFrom hb A.nonempty_prefix.2 fun h hr hF => by
      by_cases hne : insideQueries (h.map Prod.snd) = []
      · exact Or.inl hne
      · refine Or.inr (hB _ hne (DDC.insideQueries_length_le_of_budget hb A.length_le hr hF)
          fun o j hj => (DDC.insideQueries_restrict_length_le hι hr hj).trans ?_)
        rcases hF with he | hF
        · rw [he]; exact Nat.zero_le _
        · exact hA _ hF o)

/-- An interface admitting the histories with at most `q o` queries at each label, beside `B`,
admits the histories with at most `q o` queries at each left label and at most `k` queries in
all, when `B` admits every nonempty history of at most `k`. -/
lemma Interface.perPort_tensor_admits {A B : Interface} (q : A.I → ℕ)
    (hA : ∀ xs, xs ≠ [] → (∀ o, (SystemAlgebra.restrict o xs).length ≤ q o) → A.domain xs)
    {k : ℕ} (hB : ∀ xs, xs ≠ [] → xs.length ≤ k → B.domain xs) :
    ∀ ys, ys ≠ [] → ys.length ≤ k → (∀ o, (SystemAlgebra.restrict (Sum.inl o) ys).length ≤ q o) →
      (Interface.tensor A B).domain ys := by
  intro ys hne hl hc
  refine ⟨hne, ?_, ?_⟩
  · by_cases he : SystemAlgebra.restrict none (ys.map (sumAlphabet (Sum.rec A.X B.X)).symm) = []
    · exact Or.inl he
    · exact Or.inr (hA _ he fun o => by rw [SystemAlgebra.restrict_restrict_sumAlphabet]; exact hc o)
  · by_cases he : SystemAlgebra.restrict (some ()) (ys.map (sumAlphabet (Sum.rec A.X B.X)).symm) = []
    · exact Or.inl he
    · exact Or.inr (hB _ he ((SystemAlgebra.length_restrict_le _ _).trans (by simpa using hl)))

/-- **Attaching the converter of a program** to the typed system of a PDS: a transcript has the
mass of the deterministic systems on which the inlined program, on the outside domain, gives
it. -/
lemma TypedConverter.ofDDC_ofProgramOn_smul_ofPDS {A B : Interface} (s : S)
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    (hα : IsDDCFrom B.domain A.domain b (DDC.ofProgramOn s P A.domain))
    (Q : Probability.Distribution.ProbDist {r : InterfaceSystem B.I B.X B.Y //
      IsDDS r ∧ RepliesAtQueriedInterface r ∧ ∀ h, (r h).Dom ↔ B.domain h})
    (t : List ((Σ i, A.X i) × (Σ i, A.Y i))) :
    (TypedConverter.ofDDC (DDC.ofProgramOn s P A.domain) hα • TypedSystem.ofPDS Q).1 t =
      Q.1.mass fun r =>
        Replies (filterDom A.domain (P.inline r.1 b s)) (t.map Prod.fst) (t.map Prod.snd) := by
  rw [TypedConverter.smul_val, PDCBehavior.attach_presents B.nonempty_prefix A.nonempty_prefix _ _ _
    ⟨Finsupp.single ⟨_, hα⟩ 1, Probability.Distribution.isProbDist_single _⟩ Q (fun _ => rfl)
    (fun _ => rfl) t, behaviorMass_attachPDS, Probability.Distribution.prod_single_left,
    Probability.Distribution.mass_fTransform]
  refine Probability.Distribution.mass_congr _ fun r => ?_
  rw [Program.trim_apply_ofProgramOn s hb A.domain A.nonempty_prefix.2]

/-- **Attaching the converter of a program to an automaton** gives the combined automaton, its
initial state paired with the program's. -/
lemma TypedConverter.ofDDC_ofProgramOn_smul_ofAutomaton {A B : Interface} {R : Type} (s : S)
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    (hα : IsDDCFrom B.domain A.domain b (DDC.ofProgramOn s P A.domain))
    (stepR : R → (j : B.I) → B.X j → R × B.Y j) (initial : Probability.Distribution.ProbDist R) :
    TypedConverter.ofDDC (DDC.ofProgramOn s P A.domain) hα •
        TypedSystem.ofAutomaton B stepR initial =
      TypedSystem.ofAutomaton A (P.combine stepR hb)
        ⟨Probability.Distribution.fTransform (fun r => (s, r)) initial.1,
          Probability.Distribution.fTransform_isProbDist _ initial.2⟩ := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro t
  rw [TypedSystem.ofAutomaton_mass]
  conv_lhs => rw [TypedSystem.ofAutomaton]
  rw [TypedConverter.ofDDC_ofProgramOn_smul_ofPDS s P hb hα,
    Probability.Distribution.mass_fTransform, Probability.Distribution.mass_fTransform]
  refine Probability.Distribution.mass_congr _ fun r => ?_
  change Replies (filterDom A.domain (P.inline (filterDom B.domain (automatonSystem stepR r)) b s))
    _ _ ↔ _
  rw [← Program.trim_apply_ofProgramOn s hb A.domain A.nonempty_prefix.2,
    Program.trim_apply_ofProgramOn_automaton stepR hb s r B.nonempty_prefix A.nonempty_prefix hα]

lemma TypedConverter.ofProgram_smul_ofAutomaton {A B : Interface} {R : Type} (s : S)
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    (hB : ∀ xs, xs ≠ [] → xs.length ≤ b * A.bound → B.domain xs)
    (stepR : R → (j : B.I) → B.X j → R × B.Y j) (initial : Probability.Distribution.ProbDist R) :
    TypedConverter.ofProgram s P hb hB • TypedSystem.ofAutomaton B stepR initial =
      TypedSystem.ofAutomaton A (P.combine stepR hb)
        ⟨Probability.Distribution.fTransform (fun r => (s, r)) initial.1,
          Probability.Distribution.fTransform_isProbDist _ initial.2⟩ :=
  TypedConverter.ofDDC_ofProgramOn_smul_ofAutomaton s P hb _ stepR initial

lemma TypedConverter.ofPreservingProgram_smul_ofAutomaton {A B : Interface} {R : Type}
    (s : S) (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    (ι : A.I → Option B.I) (hι : P.PortPreserving ι) (q : A.I → ℕ)
    (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    (hB : ∀ ys, ys ≠ [] → ys.length ≤ b * A.bound →
      (∀ o j, ι o = some j → (SystemAlgebra.restrict j ys).length ≤ q o) → B.domain ys)
    (stepR : R → (j : B.I) → B.X j → R × B.Y j) (initial : Probability.Distribution.ProbDist R) :
    TypedConverter.ofPreservingProgram s P hb ι hι q hA hB •
        TypedSystem.ofAutomaton B stepR initial =
      TypedSystem.ofAutomaton A (P.combine stepR hb)
        ⟨Probability.Distribution.fTransform (fun r => (s, r)) initial.1,
          Probability.Distribution.fTransform_isProbDist _ initial.2⟩ :=
  TypedConverter.ofDDC_ofProgramOn_smul_ofAutomaton s P hb _ stepR initial

end SystemAlgebra
