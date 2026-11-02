module

public import RandomSystems.Typed.FiniteFamilyCollect
public import Mathlib.Logic.Equiv.Bool

/-!
# Ordered collection of heterogeneous families

The tuple client sends the ternary coordinate first and the Boolean coordinate second, then
returns the replies at their original Boolean indices. Its only domain obligation is the
component query budget. The source client has independent tuple replies on successive calls;
each specified pair of tuples has mass `1/36`, including unequal Boolean coordinates.
The empty family returns without inside calls.
-/

@[expose] public section

namespace SystemAlgebra.Tests

open Probability Probability.Distribution
open scoped SystemAlgebra

/-- Coordinate `false` carries a Boolean; coordinate `true` carries a value in `Fin 3`. -/
abbrev collectionAlphabet : Bool → Type
  | false => Bool
  | true => Fin 3

/-- Both coordinate alphabets are finite, with their existing instances. -/
instance collectionAlphabet_fintype : (k : Bool) → Fintype (collectionAlphabet k)
  | false => inferInstance
  | true => inferInstance

/-- Each outside query and reply is the original heterogeneous tuple, with two invocations. -/
abbrev collectionInterface : Interface :=
  Interface.queryBudget Unit (fun _ => ∀ k, collectionAlphabet k)
    (fun _ => ∀ k, collectionAlphabet k) 2

/-- Component `k` accepts its coordinate and returns that coordinate type, at most twice. -/
abbrev collectionComponent (k : Bool) : Interface :=
  Interface.queryBudget Unit (fun _ => collectionAlphabet k) (fun _ => collectionAlphabet k) 2

/-- Visit the ternary component first and the Boolean component second. -/
def collectionOrder : Fin 2 ≃ Bool := finTwoEquiv.trans Equiv.boolNot

/-- One tuple query sends coordinate `k` to component `k`'s sole port. -/
def collectionRequest (u : Σ o, collectionInterface.X o) (k : Bool) :
    Σ j, (collectionComponent k).X j := ⟨(), u.2 k⟩

/-- Each invocation makes one component call; two invocations fit each component's budget of two. -/
lemma collectionRequest_domain (k : Bool) (us : List (Σ o, collectionInterface.X o))
    (hu : collectionInterface.domain us) :
    (collectionComponent k).domain (us.map fun u => collectionRequest u k) :=
  Interface.queryBudget_domain_map _ le_rfl hu

/-- Send one query per coordinate in `collectionOrder`, returning the original indexed tuple. -/
noncomputable def tupleCollector :
    TypedConverter collectionInterface (⨂ k, collectionComponent k) :=
  TypedConverter.collect collectionOrder collectionRequest (fun _ ys => ys) collectionRequest_domain

/-- The variable components leave only their local functional contracts to prove. -/
example
    -- `R k` supplies component `k`; `f k` is its stated input/output function.
    (R : ∀ k, TypedSystem (collectionComponent k))
    (f : ∀ k j, (collectionComponent k).X j → (collectionComponent k).Y j)
    (hR : ∀ k, R k = TypedSystem.ofFunction (f k)) :
    tupleCollector • (∥ k, R k) =
      TypedSystem.ofFunction (A := collectionInterface)
        (fun _ u k => f k () (u k)) := by
  simp_rw [hR]
  exact TypedConverter.collect_smul_parallelAll_ofFunction
    collectionOrder collectionRequest (fun _ ys => ys) collectionRequest_domain f

/-- The actual call schedule respects the chosen reverse order. -/
example (u : Σ o, collectionInterface.X o) :
    List.ofFn (collectSchedule collectionOrder collectionRequest u) =
      [⟨⟨true, ()⟩, u.2 true⟩, ⟨⟨false, ()⟩, u.2 false⟩] := rfl

/-- Replies received in reverse order return the original indexed tuple. -/
example (u : Σ o, collectionInterface.X o) (ys : ∀ k, collectionAlphabet k) :
    collectProgram collectionOrder collectionRequest (fun _ zs => zs) () u.1 u.2
      (List.ofFn fun i => (collectSchedule collectionOrder collectionRequest u i,
        ⟨(collectSchedule collectionOrder collectionRequest u i).1, ys (collectionOrder i)⟩)) =
      .inl ((), ys) := by
  have hr := DSL.collectCalls_reply (Y := (⨂ k, collectionComponent k).Y) 2
    (collectSchedule collectionOrder collectionRequest u)
    (fun zs => ((), Equiv.piCongrLeft collectionAlphabet collectionOrder zs))
    (fun i => ys (collectionOrder i))
  -- The final explicit reindexing cancels the order used by the received tuple.
  exact hr.trans (congrArg (fun zs => Sum.inl ((), zs))
    ((Equiv.piCongrLeft collectionAlphabet collectionOrder).apply_symm_apply ys))

/-- The exact call count is two, independent of component replies. -/
example : (collectProgram collectionOrder collectionRequest (fun _ ys => ys)).Costs
    (fun _ => 2) := collectProgram_costs _ _ _

/-- The Boolean coordinate is fair; the ternary coordinate is uniform. Each source draws afresh. -/
noncomputable def collectionLaw : (k : Bool) → ProbDist (collectionAlphabet k)
  | false => 𝒰[Bool]
  | true => 𝒰[Fin 3]

/-- Every tuple has mass `1/6`, the product of its Boolean and ternary coordinate masses. -/
lemma collectionLaw_mass (z : ∀ k, collectionAlphabet k) :
    (ProbDist.piDep collectionLaw).1 z = 1 / 6 := by
  norm_num only [ProbDist.piDep_val, piDep, Finsupp.onFinset_apply, Fintype.prod_bool,
    collectionLaw, ProbDist.uniform, uniform_apply, Fintype.card_bool, Fintype.card_fin]

/-- Assemble the two sources with the existing collector; each outer trigger returns a tuple. -/
noncomputable def collectedSources : TypedSystem (Interface.source (∀ k, collectionAlphabet k) 2) :=
  TypedConverter.collect (A := Interface.source (∀ k, collectionAlphabet k) 2)
    (B := fun k => Interface.source (collectionAlphabet k) 2)
    collectionOrder (fun _ _ => ⟨(), ()⟩) (fun _ ys => ys)
    (fun _ _ hu => Interface.queryBudget_domain_map _ le_rfl hu) •
      (∥ k, TypedSystem.source (collectionLaw k) 2)

/-- The assembled family is a fresh tuple source, on the same two-query domain. -/
lemma collectedSources_eq :
    collectedSources = TypedSystem.source (ProbDist.piDep collectionLaw) 2 :=
  TypedConverter.collect_smul_parallelAll_source collectionOrder 2 collectionLaw

/-- Two successive tuple replies have mass `1/36`, also when their Boolean coordinates differ. -/
lemma collectedSources_two_replies
    -- `z`, `w` are arbitrary heterogeneous tuples returned by the two invocations.
    (z w : ∀ k, collectionAlphabet k) :
    collectedSources.1 [(⟨(), ()⟩, ⟨(), z⟩), (⟨(), ()⟩, ⟨(), w⟩)] = 1 / 36 := by
  rw [collectedSources_eq, TypedSystem.source_eq_ofMemoryless, TypedSystem.ofMemoryless_val]
  -- The fresh source chain rule contributes one tuple mass for each admitted trigger.
  change RandomSystem.memoryless (Interface.source (∀ k, collectionAlphabet k) 2).inputDomain
    (RandomSystem.portLaw fun _ _ => ProbDist.piDep collectionLaw)
    ([(⟨(), ()⟩, ⟨(), z⟩)] ++ [(⟨(), ()⟩, ⟨(), w⟩)]) = _
  rw [RandomSystem.memoryless_snoc]
  norm_num only [Interface.inputDomain, Domain.ofInputs, Interface.source,
    Interface.queryBudget, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.length_cons, List.length_nil, List.cons_ne_nil, not_false_eq_true, and_self,
    ite_true, RandomSystem.portLaw_apply_mk, collectionLaw_mass]
  change RandomSystem.memoryless (Interface.source (∀ k, collectionAlphabet k) 2).inputDomain
    (RandomSystem.portLaw fun _ _ => ProbDist.piDep collectionLaw)
    ([] ++ [(⟨(), ()⟩, ⟨(), z⟩)]) * _ = _
  rw [RandomSystem.memoryless_snoc]
  norm_num only [Interface.inputDomain, Domain.ofInputs, Interface.source,
    Interface.queryBudget, List.map_nil, List.nil_append, List.length_cons, List.length_nil,
    List.cons_ne_nil, not_false_eq_true, and_self, ite_true, RandomSystem.portLaw_apply_mk,
    collectionLaw_mass, RandomSystem.mass_nil]
  rw [collectionLaw_mass, collectionLaw_mass]
  norm_num

/-- A component with only one query cannot support this two-invocation outside domain. -/
example : ¬ ∀ us, collectionInterface.domain us →
    (Interface.source Unit 1).domain (us.map fun _ => ⟨(), ()⟩) := by
  intro h
  let z : ∀ k, collectionAlphabet k := fun k => match k with | false => false | true => 0
  have hu : collectionInterface.domain [⟨(), z⟩, ⟨(), z⟩] := by
    exact ⟨List.cons_ne_nil _ _, le_rfl⟩
  have hb := (h _ hu).2
  norm_num only [List.length_map, List.length_cons, List.length_nil] at hb

/-- With no components, each invocation has exact call cost zero. -/
example : (collectProgram (A := Interface.source (Empty → Bool) 2)
    (B := fun _ : Empty => Interface.source Bool 2) finZeroEquiv
    (fun _ _ => ⟨(), ()⟩) (fun _ ys => ys)).Costs (fun _ => 0) :=
  collectProgram_costs _ _ _

/-- The empty family yields the source of the unique empty tuple, even on repeated invocations. -/
example :
    TypedConverter.collect (A := Interface.source (Empty → Bool) 2)
      (B := fun _ : Empty => Interface.source Bool 2) finZeroEquiv
      (fun _ _ => ⟨(), ()⟩) (fun _ ys => ys)
      (fun k => Empty.elim k) •
      (∥ k : Empty, TypedSystem.source (Empty.elim k : ProbDist Bool) 2) =
      TypedSystem.source (ProbDist.piDep (fun k : Empty => (Empty.elim k : ProbDist Bool))) 2 :=
  TypedConverter.collect_smul_parallelAll_source finZeroEquiv 2 (fun k => Empty.elim k)

#print axioms DDC.ofProgramOn_isDDCFrom_of_schedule
#print axioms Program.memorylessReplyLaw_collectCalls
#print axioms TypedConverter.collect_smul_parallelAll_ofMemoryless
#print axioms TypedConverter.collect_smul_parallelAll_ofFunction
#print axioms TypedConverter.collect_smul_parallelAll_source
#print axioms collectedSources_two_replies

end SystemAlgebra.Tests
