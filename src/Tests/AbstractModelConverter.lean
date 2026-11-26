module

public import Commons.Definitions.AbstractModel.RegisterConverter

/-!
# Register converter checks

A Boolean model negates a selected register and observes it at either of two ports. The tests
check overwrite followed by shared reads, immediate submission, and the one pending observation
against the actual source and target domains.
-/

@[expose] public noncomputable section

namespace Tests.AbstractModelConverter

open Commons.AbstractModel SystemAlgebra SystemAlgebra.DSL

/-- One operation negates a bit; either observation returns its selected operand. -/
abbrev model : Commons.AbstractModel Bool Unit where
  Operation := Unit
  Query := Bool
  arity _ := 1
  queryArity _ := 1
  Reply _ := Bool
  operate _ _ values := !(values 0)
  evaluate _ _ values := values 0

/-- The initial register `false` is overwritten with its negation. -/
def overwrite : model.Command Bool := ⟨.compute (), (fun _ => false, false)⟩

/-- Observation at port `ρ` reads the shared initial address. -/
def observe (ρ : Bool) : model.Command Bool := ⟨.query ρ, fun _ => false⟩

/-- All three ordinary commands access the same initialized register. -/
lemma shared_admitted : model.Admitted false 3 [overwrite, observe false, observe true] := by
  apply (admitted_snoc_iff false 3 [overwrite, observe false] (observe true)).mpr
  refine ⟨Or.inr ?_, by simp [overwrite, observe, List.countP_cons, List.countP_nil, ordinary],
    by simp [overwrite, observe, ordinary], ?_⟩
  · apply (admitted_snoc_iff false 3 [overwrite] (observe false)).mpr
    refine ⟨Or.inr ?_, by simp [overwrite, observe, List.countP_cons, List.countP_nil, ordinary],
      by simp [overwrite, ordinary], ?_⟩
    · apply (admitted_snoc_iff false 3 [] overwrite).mpr
      simp [overwrite, ordinary, reads, initialized]
    · simp [reads, observe, initialized, overwrite, target]
  · simp [reads, observe, initialized, overwrite, target]

example : model.registerProgram false () false [] (.compute ()) (fun _ => false, false) [] =
    .inl ([overwrite], ()) := rfl

example : model.registerProgram false () false [] .submit true [] =
    .inl ([⟨.submit, true⟩], ()) := rfl

/-- After overwrite, the first pending observation requests the updated bit. -/
lemma pending_request :
    model.registerProgram false () false [overwrite] (.query false) (fun _ => false) [] =
      .inr ⟨false, fun _ => true⟩ := by
  simp [registerProgram, callProg, registers, write, overwrite, Commons.AbstractModel.read,
    initial]

/-- Completing the first observation preserves the same value for the second caller. -/
example : model.registerProgram false () false [overwrite, observe false]
    (.query true) (fun _ => false) [] = .inr ⟨true, fun _ => true⟩ := by
  simp [registerProgram, callProg, registers, write, overwrite, observe,
    Commons.AbstractModel.read, initial]

example : (model.observationInterface 3).domain [⟨false, fun _ => true⟩] :=
  ⟨List.cons_ne_nil _ _, by simp only [List.length_singleton]; omega⟩

/-- The full costed converter uses the source's initialized-register domain unchanged. -/
example : TypedConverter (model.interface false 3) (model.observationInterface 3) :=
  model.registersConverter false 3 () false

example : ([overwrite, observe false, observe true].map model.observationCost).sum = 2 := rfl

example : (model.interface false 0).domain [⟨.submit, true⟩] := by
  apply (admitted_snoc_iff false 0 [] ⟨.submit, true⟩).mpr
  simp [ordinary, reads]

/-- The first observation is legal before its inside reply arrives; its call is already counted. -/
example :
    let u : Σ l : Two (Port Unit Bool) Bool, twoFam (model.Input Bool) model.Reply l :=
      ⟨⟨none, .query false⟩, fun _ => false⟩
    let v : Σ l : Two (Port Unit Bool) Bool,
        twoFam model.Output (fun _ => Fin 1 → Bool) l :=
      ⟨⟨some (), false⟩, fun _ => false⟩
    Replies (DDC.ofProgramOn [] (model.registerProgram false () false)
      (model.Admitted false 1)) [u] [v] ∧
      (model.observationInterface 1).domain (insideQueries [v]) ∧
        (insideQueries [v]).length = 1 := by
  intro u v
  have admitted : model.Admitted false 1 [⟨.query false, fun _ => false⟩] := by
    apply (admitted_snoc_iff (M := model) false 1 [] ⟨.query false, fun _ => false⟩).mpr
    simp [ordinary, reads, initialized]
  have outside : outsideInputs [u] = [⟨.query false, fun _ => false⟩] :=
    outsideInputs_outside _ _
  have inside : insideQueries [v] = [⟨false, fun _ => false⟩] :=
    insideQueries_inside _ _
  have request : model.registerProgram false () false [] (.query false)
      (fun _ => false) [] = .inr ⟨false, fun _ => false⟩ := by
    simp [registerProgram, callProg, registers, Commons.AbstractModel.read, initial]
  refine ⟨?_, ?_, ?_⟩
  · apply (replies_snoc (xs := []) (ys := [])).mpr
    refine ⟨replies_nil _, ?_⟩
    change filterDom (fun xs => outsideInputs xs = [] ∨ model.Admitted false 1 (outsideInputs xs))
      (DDC.ofProgram [] (model.registerProgram false () false)) [u] = Part.some v
    rw [filterDom, ite_eq_left (Or.inr (outside ▸ admitted))]
    calc
      _ = Part.ofOption (((model.registerProgram false () false).after [] []).bind
          fun m => ((model.registerProgram false () false).step m u).map Prod.snd) :=
        DDC.ofProgram_snoc _ _ [] u
      _ = Part.some v := by
        simp only [Program.after_nil, Option.bind_some, u, Program.step, Program.emit, request]
        rfl
  · rw [inside]
    exact ⟨List.cons_ne_nil _ _, le_rfl⟩
  · rw [inside]
    rfl

#print axioms Commons.AbstractModel.registerProgram_bounded
#print axioms Commons.AbstractModel.registerProgram_costs
#print axioms Commons.AbstractModel.observationCost_sum_le
#print axioms Commons.AbstractModel.read_registers_getD
#print axioms Commons.AbstractModel.registersConverter
#print axioms shared_admitted
#print axioms pending_request

end Tests.AbstractModelConverter
