module

public import RandomSystems.Converter.ChronologicalLabeling
public import RandomSystems.Converter.ProgramAttachment
public import RandomSystems.System.AutomatonFunction

/-!
# Chronological labeling calls

`chronologicalLabelingProgram_query` identifies the single issued label. After its reply,
`chronologicalLabelingProgram_reply` returns that reply and the extended outside prefix.
`chronologicalLabelingProgram_cost` and `chronologicalLabelingProgram_bounded` count one inside
call per outside input, including repetitions and exhausted label pools.
`chronologicalLabelingProgram_after` identifies its prefix during completed and pending calls;
`chronologicalLabelingProgram_isDDCFrom` preserves the same query allowance on both sides.
`chronologicalLabelingProgram_apply_ofFunction_snoc` gives the reply under attachment to one
fixed function, preserving the original domain and the explicit exhaustion fallback.
-/

@[expose] public section

namespace SystemAlgebra

open DSL

-- `A` carries outside inputs, `B` the finite query labels, and `C` the forwarded replies.
variable {A B C : Type}
  -- These call equations allow any selected comparison; repeat laws additionally need LawfulBEq.
  [BEq A] [Fintype B]
  -- `labels` fixes their order; exhaustion selects the explicit `fallback`.
  (labels : Fin (Fintype.card B) ≃ B) (fallback : B)

/-- Before an inside reply, query the first-occurrence position of the current input. -/
lemma chronologicalLabelingProgram_query
    -- `xs` is the earlier outside prefix and `a` is its next input.
    (xs : List A) (a : A) :
    chronologicalLabelingProgram (C := C) labels fallback xs () a [] =
      .inr ⟨(), if h : (xs ++ [a]).eraseDups.idxOf a < Fintype.card B then
        labels ⟨(xs ++ [a]).eraseDups.idxOf a, h⟩ else fallback⟩ := rfl

/-- Receiving `c` retains the extended input prefix and returns `c` unchanged. -/
lemma chronologicalLabelingProgram_reply
    -- `b` and `c` are the recorded inside query and reply; `h` is the remaining history.
    (xs : List A) (a : A) (b : B) (c : C)
    (h : List ((Σ _ : Unit, B) × (Σ _ : Unit, C))) :
    chronologicalLabelingProgram labels fallback xs () a ((⟨(), b⟩, ⟨(), c⟩) :: h) =
      .inl (xs ++ [a], c) := by
  simp only [chronologicalLabelingProgram, callProg, returnProg, ↓reduceDIte]

/-- Each invocation spends exactly one inside query. -/
lemma chronologicalLabelingProgram_cost :
    (chronologicalLabelingProgram (A := A) (C := C) labels fallback).Costs (fun _ => 1) := by
  intro xs o a
  exact callCost_call () _ _ (fun c => callCost_return (xs ++ [a], c))

/-- The one-call bound is independent of repetitions, label capacity and the reply. -/
lemma chronologicalLabelingProgram_bounded :
    (chronologicalLabelingProgram (A := A) (C := C) labels fallback).Bounded 1 := by
  intro xs o a
  exact callBound_call () _ _ (fun c => callBound_return 0 (xs ++ [a], c))

/-! ## Retained prefix and domain -/

/-- The retained prefix is exactly the initial prefix followed by outside inputs. A pending
invocation contributes its current input once, before any inside reply arrives. -/
lemma chronologicalLabelingProgram_after
    -- `start` is the initial prefix; `inputs` is the complete converter-input history.
    (start : List A) (inputs : List (Σ l, twoFam (fun _ : Unit => A) (fun _ : Unit => C) l))
    -- `accepted` identifies the compiled program's current idle or pending mode `m`.
    (m : Program.Mode (List A) Unit Unit (fun _ => A) (fun _ => B) (fun _ => C))
    (accepted : (chronologicalLabelingProgram labels fallback).after start inputs = some m) :
    (match m with
      | .idle xs => xs
      | .busy _ xs a _ _ => xs ++ [a]) =
      start ++ (outsideInputs inputs).map Sigma.snd := by
  have returned : ∀ xs (o : Unit) a h xs' (c : C),
      chronologicalLabelingProgram (A := A) (C := C) labels fallback xs o a h =
        .inl (xs', c) →
      xs' = xs ++ [a] := by
    intro xs o a h xs' c result
    cases o
    cases h with
    | nil => rw [chronologicalLabelingProgram_query] at result; cases result
    | cons z h =>
      obtain ⟨⟨j, b⟩, ⟨j', c'⟩⟩ := z
      cases j
      cases j'
      rw [chronologicalLabelingProgram_reply] at result
      exact (congrArg Prod.fst (Sum.inl.inj result)).symm
  -- The compiler's generic fold law also handles a query that is still pending.
  have folded := Program.after_fold (chronologicalLabelingProgram labels fallback) id
    (fun xs u => xs ++ [u.2]) returned start inputs m accepted
  cases m <;>
    simpa only [id_eq, List.foldl_append_eq_append, ← List.flatMap_def,
      ← List.map_eq_flatMap] using folded

/-- One inside query per outside input preserves the same allowance `q` on both domains. -/
lemma chronologicalLabelingProgram_isDDCFrom
    -- `q` admits nonempty histories with at most `q` inputs on either side.
    (q : ℕ) :
    IsDDCFrom (fun bs : List (Σ _ : Unit, B) => bs ≠ [] ∧ bs.length ≤ q)
      (fun us : List (Σ _ : Unit, A) => us ≠ [] ∧ us.length ≤ q) 1
      (DDC.ofProgramOn [] (chronologicalLabelingProgram (C := C) labels fallback)
        (fun us => us ≠ [] ∧ us.length ≤ q)) := by
  apply DDC.ofProgramOn_isDDCFrom_of_costs (q := q)
    (chronologicalLabelingProgram_bounded labels fallback)
  · intro p h hp hn legal
    exact ⟨hn, hp.length_le.trans legal.2⟩
  · exact chronologicalLabelingProgram_cost labels fallback
  · intro us legal
    simpa only [List.map_const', List.sum_replicate_nat, Nat.mul_one] using legal.2
  · intro bs nonempty bound
    exact ⟨nonempty, bound⟩

/-! ## Fixed-function attachment -/

/-- One invocation retains the extended prefix and returns `f` at its chronological label. -/
lemma chronologicalLabelingProgram_combine
    -- `f` is the fixed inside function; `xs` is the retained prefix and `a` the new input.
    (f : B → C) (xs : List A) (a : A) :
    (chronologicalLabelingProgram labels fallback).combine
        (fun (_ : Unit) (_ : Unit) b => ((), f b))
        (chronologicalLabelingProgram_bounded labels fallback) (xs, ()) () a =
      ((xs ++ [a], ()), f (if h : (xs ++ [a]).eraseDups.idxOf a < Fintype.card B then
        labels ⟨(xs ++ [a]).eraseDups.idxOf a, h⟩ else fallback)) := by
  apply Program.combine_eq_of_invoke _ (chronologicalLabelingProgram_bounded labels fallback)
    (n := 1)
  simp only [Program.invoke, chronologicalLabelingProgram_query, List.nil_append,
    chronologicalLabelingProgram_reply, Sum.elim_inl]

/-- Attaching the encoder to `f` evaluates `f` at the current input's first-occurrence label.
The original outside domain `F` still controls whether the system replies. -/
lemma chronologicalLabelingProgram_apply_ofFunction_snoc
    -- `E` and `F` are the inside and outside input domains; both admit nonempty prefixes.
    {E : List (Σ _ : Unit, B) → Prop} {F : List (Σ _ : Unit, A) → Prop}
    (hE : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    -- `domain` certifies this encoder from `E` to `F`, including a pending inside query.
    (domain : IsDDCFrom E F 1
      (DDC.ofProgramOn [] (chronologicalLabelingProgram (C := C) labels fallback) F))
    -- `f` stays fixed across all calls; `us` is the earlier outside prefix.
    (f : B → C) (us : List (Σ _ : Unit, A)) (a : A) [DecidablePred F] :
    trim (apply (DDC.ofProgramOn [] (chronologicalLabelingProgram labels fallback) F)
      (DDS.ofFunction E hE (fun b => ⟨b.1, f b.2⟩)).1) (us ++ [⟨(), a⟩]) =
      if F (us ++ [⟨(), a⟩]) then Part.some ⟨(),
        f (if h : (us.map Sigma.snd ++ [a]).eraseDups.idxOf a < Fintype.card B then
          labels ⟨(us.map Sigma.snd ++ [a]).eraseDups.idxOf a, h⟩ else fallback)⟩
      else Part.none := by
  let P := chronologicalLabelingProgram (A := A) (C := C) labels fallback
  let stepR := fun (_ : Unit) (_ : Unit) b => ((), f b)
  have bounded := chronologicalLabelingProgram_bounded (A := A) (C := C) labels fallback
  -- The combined state projects to the outside prefix by the existing fold homomorphism.
  have prefix_eq : (stateAfter (P.combine stepR bounded) ([], ()) us).1 =
      us.map Sigma.snd := by
    have folded := List.foldl_hom Prod.fst
      (g₁ := fun sr u => (P.combine stepR bounded sr u.1 u.2).1)
      (g₂ := fun xs u => xs ++ [u.2]) (l := us) (init := ([], ())) (by
        rintro ⟨xs, ⟨⟩⟩ ⟨⟨⟩, a⟩
        rw [chronologicalLabelingProgram_combine])
    simpa only [stateAfter, List.foldl_append_eq_append, ← List.flatMap_def,
      ← List.map_eq_flatMap, List.nil_append] using folded.symm
  have state : stateAfter (P.combine stepR bounded) ([], ()) us =
      (us.map Sigma.snd, ()) := Prod.ext prefix_eq (Subsingleton.elim _ _)
  -- Replace the fixed evaluator by its retained-function presentation, then attach once.
  rw [← filterDom_automatonSystem_eq_ofFunction E hE (fun (_ : Unit) (_ : Unit) b => f b) ()]
  rw [Program.trim_apply_ofProgramOn_automaton stepR bounded [] () hE hF domain]
  -- The last reply uses exactly the prefix computed above; exhaustion keeps its fallback.
  by_cases legal : F (us ++ [⟨(), a⟩])
  · simp only [filterDom, legal, ↓reduceIte, automatonSystem_snoc]
    rw [state]
    dsimp only [stepR]
    rw [chronologicalLabelingProgram_combine]
  · simp only [filterDom, legal, ↓reduceIte]

end SystemAlgebra
