module

public import RandomSystems.Converter.ChronologicalLabeling.Laws
public import Mathlib.Tactic.NormNum

/-!
# A two-label chronological encoder

Natural-number inputs use a two-label pool while arbitrary natural-number replies pass through.
The primitive equations cover fresh inputs, repeats after exhaustion, and prefix retention.
Attachment to a fixed noninjective function checks the same replies and original domain;
the pending-query and zero-allowance checks discharge their compiler certificates.
-/

@[expose] public section

namespace Tests.ChronologicalLabeling

open SystemAlgebra

-- The pool has labels `0,1`; exhausted fresh positions use label `0`.
variable (labels : Fin (Fintype.card (Fin 2)) ≃ Fin 2)

/-- A repeated input still queries its old second label after a third distinct input. -/
example : chronologicalLabelingProgram (C := ℕ) labels 0 [7, 9, 11] () 9 [] =
    .inr ⟨(), labels ⟨1, by norm_num⟩⟩ := by
  rw [chronologicalLabelingProgram_query]
  norm_num [List.eraseDups_cons, List.filter_cons, List.filter_nil]

/-- A fresh third input falls back to the supplied label `0`. -/
example : chronologicalLabelingProgram (C := ℕ) labels 0 [7, 9] () 11 [] = .inr ⟨(), 0⟩ := by
  rw [chronologicalLabelingProgram_query]
  norm_num [List.eraseDups_cons, List.filter_cons, List.filter_nil]

/-- The caller receives its inside reply `42`; the retained prefix records the repeat. -/
example : chronologicalLabelingProgram labels 0 [7, 9, 11] () 9
    [(⟨(), (1 : Fin 2)⟩, ⟨(), (42 : ℕ)⟩)] = .inl ([7, 9, 11, 9], 42) :=
  chronologicalLabelingProgram_reply labels 0 [7, 9, 11] 9 1 42 []

/-- The actual encoder has exact unit query cost with an infinite outside alphabet. -/
example : (chronologicalLabelingProgram (A := ℕ) (C := ℕ) labels 0).Costs (fun _ => 1) :=
  chronologicalLabelingProgram_cost labels 0

#print axioms SystemAlgebra.chronologicalLabelingProgram
#print axioms SystemAlgebra.chronologicalLabelingProgram_query
#print axioms SystemAlgebra.chronologicalLabelingProgram_reply
#print axioms SystemAlgebra.chronologicalLabelingProgram_cost
#print axioms SystemAlgebra.chronologicalLabelingProgram_bounded

/-! ## Attaching one fixed function -/

/-- `fixedReply b = 42` on both labels; its reply carrier is the infinite type `ℕ`. -/
def fixedReply (_ : Fin 2) : ℕ := 42

/-- The chosen inside function is noninjective. -/
example : ¬ Function.Injective fixedReply := by
  intro injective
  have equal : (0 : Fin 2) = 1 := injective rfl
  norm_num at equal

/-- `outsideDomain q` admits nonempty natural-input histories of length at most `q`. -/
def outsideDomain (q : ℕ) (us : List (Σ _ : Unit, ℕ)) : Prop :=
  us ≠ [] ∧ us.length ≤ q

/-- `insideDomain q` gives the same allowance to the finite label inputs. -/
def insideDomain (q : ℕ) (bs : List (Σ _ : Unit, Fin 2)) : Prop :=
  bs ≠ [] ∧ bs.length ≤ q

/-- The natural-input domain excludes empty histories and retains nonempty prefixes. -/
lemma outsideDomain_prefix (q : ℕ) : ¬ outsideDomain q [] ∧
    ∀ {p h}, p <+: h → p ≠ [] → outsideDomain q h → outsideDomain q p :=
  ⟨fun h => h.1 rfl, fun hp hn hh => ⟨hn, hp.length_le.trans hh.2⟩⟩

/-- The label-input domain excludes empty histories and retains nonempty prefixes. -/
lemma insideDomain_prefix (q : ℕ) : ¬ insideDomain q [] ∧
    ∀ {p h}, p <+: h → p ≠ [] → insideDomain q h → insideDomain q p :=
  ⟨fun h => h.1 rfl, fun hp hn hh => ⟨hn, hp.length_le.trans hh.2⟩⟩

/-- `encodedReplies q` attaches the chronological encoder to the retained evaluator of `42`.
Both sides use allowance `q`; the encoder remains the only owner of the outside prefix. -/
noncomputable def encodedReplies (q : ℕ) : System (Σ _ : Unit, ℕ) (Σ _ : Unit, ℕ) :=
  trim (apply
    (DDC.ofProgramOn [] (chronologicalLabelingProgram labels 0) (outsideDomain q))
    (DDS.ofFunction (insideDomain q) (insideDomain_prefix q)
      (fun b => ⟨b.1, fixedReply b.2⟩)).1)

/-- Repeating the second input after pool exhaustion still returns the retained reply. -/
example : encodedReplies labels 4 [⟨(), 7⟩, ⟨(), 9⟩, ⟨(), 11⟩, ⟨(), 9⟩] =
    Part.some ⟨(), 42⟩ := by
  classical
  have replay := chronologicalLabelingProgram_apply_ofFunction_snoc labels 0
    (insideDomain_prefix 4) (outsideDomain_prefix 4)
    (chronologicalLabelingProgram_isDDCFrom labels 0 4)
    fixedReply [⟨(), 7⟩, ⟨(), 9⟩, ⟨(), 11⟩] 9
  simpa only [encodedReplies, outsideDomain, List.cons_append, List.nil_append,
    ne_eq, List.cons_ne_nil, not_false_eq_true, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.le_refl, and_self, fixedReply, ↓reduceIte] using replay

/-- A fresh third input uses the fallback call and still forwards the natural reply `42`. -/
example : encodedReplies labels 3 [⟨(), 7⟩, ⟨(), 9⟩, ⟨(), 11⟩] =
    Part.some ⟨(), 42⟩ := by
  classical
  have replay := chronologicalLabelingProgram_apply_ofFunction_snoc labels 0
    (insideDomain_prefix 3) (outsideDomain_prefix 3)
    (chronologicalLabelingProgram_isDDCFrom labels 0 3)
    fixedReply [⟨(), 7⟩, ⟨(), 9⟩] 11
  simpa only [encodedReplies, outsideDomain, List.cons_append, List.nil_append,
    ne_eq, List.cons_ne_nil, not_false_eq_true, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.le_refl, and_self, fixedReply, ↓reduceIte] using replay

/-- The same third input is refused when the original outside allowance is two. -/
example : encodedReplies labels 2 [⟨(), 7⟩, ⟨(), 9⟩, ⟨(), 11⟩] = Part.none := by
  classical
  have replay := chronologicalLabelingProgram_apply_ofFunction_snoc labels 0
    (insideDomain_prefix 2) (outsideDomain_prefix 2)
    (chronologicalLabelingProgram_isDDCFrom labels 0 2)
    fixedReply [⟨(), 7⟩, ⟨(), 9⟩] 11
  simpa only [encodedReplies, outsideDomain, List.cons_append, List.nil_append,
    ne_eq, List.cons_ne_nil, not_false_eq_true, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceLeDiff, and_false, ↓reduceIte] using replay

/-- The zero-allowance converter has a discharged domain certificate. -/
example : IsDDCFrom (insideDomain 0) (outsideDomain 0) 1
    (DDC.ofProgramOn [] (chronologicalLabelingProgram (A := ℕ) (C := ℕ) labels 0)
      (outsideDomain 0)) :=
  chronologicalLabelingProgram_isDDCFrom labels 0 0

/-- The initial outside input leaves one inside query pending, before any reply arrives. -/
lemma pending_query :
    (chronologicalLabelingProgram (A := ℕ) (C := ℕ) labels 0).after []
      [⟨⟨none, ()⟩, 7⟩] =
      some (.busy () [] 7 [] ⟨(), labels ⟨0, by norm_num⟩⟩) := by
  apply (Program.after_snoc_eq_some _ [] [] ⟨⟨none, ()⟩, 7⟩ _).mpr
  refine ⟨.idle [], ⟨⟨some (), ()⟩, labels ⟨0, by norm_num⟩⟩, rfl, ?_⟩
  simp only [Program.step, Program.emit, chronologicalLabelingProgram_query]
  norm_num [List.eraseDups_cons, List.filter_nil]

/-- The pending current input contributes once to the prefix, although no reply was received. -/
example : ([] : List ℕ) ++ [7] =
    (outsideInputs ([⟨⟨none, ()⟩, 7⟩] :
      List (Σ l, twoFam (fun _ : Unit => ℕ) (fun _ : Unit => ℕ) l))).map Sigma.snd := by
  simpa only [List.nil_append] using chronologicalLabelingProgram_after labels 0 []
    [⟨⟨none, ()⟩, 7⟩] (.busy () [] 7 [] ⟨(), labels ⟨0, by norm_num⟩⟩)
    (pending_query labels)

#print axioms SystemAlgebra.chronologicalLabelingProgram_after
#print axioms SystemAlgebra.chronologicalLabelingProgram_isDDCFrom
#print axioms SystemAlgebra.chronologicalLabelingProgram_apply_ofFunction_snoc
#print axioms pending_query

end Tests.ChronologicalLabeling
