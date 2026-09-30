import ConstructiveCryptography.Tactics.Substitution

set_option autoImplicit false

/-!
# Substitution proof commands

`cc_substitute`, `cc_calc`, `cc_calc counted`, `cc_substitution_chain` and `cc_usage` on
abstract witnesses and on concrete quantitative chains, including the traced count rules.
-/

namespace Tests.Substitution.Tactics

open CategoryTheory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open SubstitutionRelation

universe u v w x y
variable {C : Type u} [Category.{v} C] {Phi : C → Type w} [ResourceTheory C Phi]
variable {ι : Type x} {boundary : ι → C}
variable (systems : ∀ i, Bool → Phi (boundary i)) {A B : C}

/-- Banfi p. 15: "sequence of steps". The indices may have different source
interfaces; the explicit reverse use is retained in the finite witness. -/
noncomputable def countedChain (i j : ι)
    (α : A ⟶ boundary i) (β : A ⟶ boundary j)
    (X Y : Phi A) (start : X = α • systems i false)
    (join : α • systems i true = β • systems j true)
    (finish : β • systems j false = Y) : Implication boundary systems A 1 := by
  cc_calc counted systems
    X = α • systems i false := start
    _ ≃ α • systems i true := i
    _ = β • systems j true := join
    _ ≃ β • systems j false := ← j
    _ = Y := finish

theorem countedChain_usageCount [DecidableEq ι] (i j k : ι)
    (α : A ⟶ boundary i) (β : A ⟶ boundary j)
    (X Y : Phi A) (start : X = α • systems i false)
    (join : α • systems i true = β • systems j true)
    (finish : β • systems j false = Y) :
    (countedChain systems i j α β X Y start join finish).usageCount k =
      (if i = k then 1 else 0) + (if j = k then 1 else 0) := by
  cc_usage

-- These are the user's displayed endpoints, not just definitionally convenient ones.
example (i j : ι) (α : A ⟶ boundary i) (β : A ⟶ boundary j)
    (X Y : Phi A) (start : X = α • systems i false)
    (join : α • systems i true = β • systems j true)
    (finish : β • systems j false = Y) :
    (countedChain systems i j α β X Y start join finish).targetLeft = X ∧
    (countedChain systems i j α β X Y start join finish).targetRight = Y := ⟨rfl, rfl⟩

-- The result is the original witness, immediately consumable by its interpreter.
example (relation : SubstitutionRelation C) (i j : ι)
    (α : A ⟶ boundary i) (β : A ⟶ boundary j)
    (X Y : Phi A) (start : X = α • systems i false)
    (join : α • systems i true = β • systems j true)
    (finish : β • systems j false = Y)
    (premises : ∀ k, relation.substitutes (boundary k) (systems k false) (systems k true)) :
    relation.substitutes A X Y := by
  cc_substitution_chain relation using
    (countedChain systems i j α β X Y start join finish), premises

-- Repeat one assumption in both directions; neither orientation erases a use.
noncomputable def repeatedChain (i : ι) (α : A ⟶ boundary i) :
    Implication boundary systems A 2 := by
  cc_calc counted systems
    α • systems i false ≃ α • systems i true := i
    _ ≃ α • systems i false := ← i
    _ ≃ α • systems i true := i

-- The total length can be inferred from the calculation, rather than entered.
noncomputable def inferredChain (i : ι) (α : A ⟶ boundary i) := by
  cc_calc counted systems
    α • systems i false ≃ α • systems i true := i
    _ ≃ α • systems i false := ← i

noncomputable example (i : ι) (α : A ⟶ boundary i) :
    Implication boundary systems A 1 := inferredChain systems i α

example [DecidableEq ι] (i : ι) (α : A ⟶ boundary i) :
    (repeatedChain systems i α).usageCount i = 3 := by
  cc_usage

example [DecidableEq ι] (i : ι) (α : A ⟶ boundary i) :
    (repeatedChain systems i α).usageCount i = 3 := by
  let witness := repeatedChain systems i α
  change witness.usageCount i = 3
  cc_usage

example [DecidableEq ι] {n : Nat} (chain : Implication boundary systems A n)
    (i : ι) (given : chain.usageCount i = 7) : chain.usageCount i = 7 := by
  -- No search for a local proof of an unknown witness's count.
  fail_if_success solve | cc_usage
  exact given

/-- trace: [ConstructiveCryptography.ProofAutomation.rule] cc_calc counted; assumption=i; reverse=true; transformation=α -/
#guard_msgs in
set_option trace.ConstructiveCryptography.ProofAutomation.rule true in
noncomputable def reverseChain (i : ι) (α : A ⟶ boundary i) :
    Implication boundary systems A 0 := by
  cc_calc counted systems
    α • systems i true ≃ α • systems i false := ← i through α

-- Counted calculations do not synthesize an assumption, orientation, or exact join.
noncomputable example (i : ι) (α _β : A ⟶ boundary i)
    (X : Phi A) (start : X = α • systems i false) :
    Implication boundary systems A 0 := by
  fail_if_success
    cc_calc counted systems
      X = α • systems i false := start
  fail_if_success
    cc_calc counted systems
      α • systems i true ≃ α • systems i false := i
  fail_if_success
    cc_calc counted systems
      α • systems i false ≃ _β • systems i true := i through α
  fail_if_success
    cc_calc counted systems
      X = α • systems i false := by skip
      _ ≃ α • systems i true := i
  fail_if_success
    cc_calc counted systems
      X = α • systems i false := _
      _ ≃ α • systems i true := i
  fail_if_success
    cc_calc counted systems
      X = α • systems i false := start
      _β • systems i false ≃ _β • systems i true := i through _β
  fail_if_success
    cc_calc counted systems
      α • systems i false ≃ α • systems i true := i
      _ ≃ α • systems i false := ← i
  cc_calc counted systems
    X = α • systems i false := by exact start
    _ ≃ α • systems i true := i

-- The count tactic scales structurally even when the chain length is symbolic.
/--
trace: [ConstructiveCryptography.ProofAutomation.rule] cc_usage ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.usageCount_map
[ConstructiveCryptography.ProofAutomation.rule] cc_usage ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.usageCount_reverse
-/
#guard_msgs in
set_option trace.ConstructiveCryptography.ProofAutomation.rule true in
example [DecidableEq ι] {n : Nat} (chain : Implication boundary systems B n)
    (α : A ⟶ B) (i : ι) :
    (chain.reverse.map α).usageCount i = chain.usageCount i := by
  cc_usage

-- Both sides normalize without repeatedly matching an unchanged variable count.
example [DecidableEq ι] {n : Nat} (chain : Implication boundary systems B n)
    (α : A ⟶ B) (i : ι) :
    chain.usageCount i = (chain.reverse.map α).usageCount i := by
  cc_usage

example [DecidableEq ι] (i : ι) (α : A ⟶ boundary i) :
    (repeatedChain systems i α).usageCount i = 3 := by
  fail_if_success
    have : (repeatedChain systems i α).usageCount i = 1 := by
      cc_usage
  cc_usage

section Quantitative
variable [MonoidalCategory C] [CompatiblePseudoMetric C Phi] {D : C → Type y}

-- Distances are scalar, may be supplied before attachment, and can be reversed.
theorem statistical_chain (α : A ⟶ B) (R S T : Phi B)
    (X Y : Phi A) (a b : ENNReal)
    (h : distance R S ≤ a) (g : distance T S ≤ b)
    (start : X = α • R) (finish : α • T = Y) : distance X Y ≤ a + b := by
  cc_calc statistical
    X = α • R := start
    _ ≈[a] α • S := h
    _ ≈[b] α • T := ← g
    _ = Y := finish

-- Statistical steps do not become assumptions, and concrete losses retain D.
theorem mixed_chain (model : DistinguisherAdvantage C Phi D)
    (R S T U X Y : Phi A) (a b : D A → ENNReal) (ε : ENNReal)
    (domination : ∀ d ∈ model.admissible A,
      ∀ r s, model.advantage A d r s ≤ distance r s)
    (h : model.SubstitutesWithin a R S) (g : distance S T ≤ ε)
    (k : model.SubstitutesWithin b U T) (start : X = R) (finish : U = Y) :
    model.SubstitutesWithin (fun d => a d + ε + b d) X Y := by
  cc_calc mixed model using domination
    X = R := start
    _ ≃[a] S := h
    _ ≈[ε] T := g
    _ ≃[b] U := ← k
    _ = Y := finish

/-- trace: [ConstructiveCryptography.ProofAutomation.rule] cc_calc supplied concrete substitution -/
#guard_msgs in
set_option trace.ConstructiveCryptography.ProofAutomation.rule true in
example (model : DistinguisherAdvantage C Phi D) (R S : Phi A)
    (loss : D A → ENNReal) (bound : model.SubstitutesWithin loss R S) :
    model.SubstitutesWithin loss S R := by
  cc_calc quantitative model
    S ≃[loss] R := ← bound

/-- trace: [ConstructiveCryptography.ProofAutomation.rule] cc_calc distance_attach_le -/
#guard_msgs in
set_option trace.ConstructiveCryptography.ProofAutomation.rule true in
example (α : A ⟶ B) (R S : Phi B) (ε : ENNReal)
    (bound : distance R S ≤ ε) : distance (α • R) (α • S) ≤ ε := by
  cc_calc statistical
    α • R ≈[ε] α • S := bound

set_option linter.unreachableTactic false in
example (model : DistinguisherAdvantage C Phi D) (R S _T : Phi A)
    (loss : D A → ENNReal) (ε : ENNReal)
    (bound : model.SubstitutesWithin loss R S) (_statistical : distance R S ≤ ε) :
    model.SubstitutesWithin loss R S := by
  fail_if_success
    have : distance R S ≤ ε := by
      cc_calc statistical
        R ≃[loss] S := bound
  fail_if_success
    have : model.SubstitutesWithin (fun _ => ε) R S := by
      cc_calc quantitative model
        R ≈[ε] S := _statistical
  fail_if_success
    cc_calc quantitative model
      R ≃[(fun _ => 0)] S := bound
  fail_if_success
    cc_calc quantitative model
      R ≃[loss] S := _
  fail_if_success
    cc_calc quantitative model
      R ≃[loss] S := by skip
  fail_if_success
    cc_calc quantitative model
      R ≃[loss] S := bound
      _ = _T := by skip
  cc_calc quantitative model
    R ≃[loss] S := by exact bound

example (model _other : DistinguisherAdvantage C Phi D) (R S : Phi A)
    (loss : D A → ENNReal) (_wrong : _other.SubstitutesWithin loss R S)
    (bound : model.SubstitutesWithin loss R S) : model.SubstitutesWithin loss R S := by
  fail_if_success
    cc_calc quantitative model
      R ≃[loss] S := _wrong
  cc_calc quantitative model
    R ≃[loss] S := bound

example (R S T : Phi A) (a b : ENNReal)
    (first : distance R S ≤ a) (second : distance S T ≤ b) :
    distance R T ≤ a + b := by
  fail_if_success
    have : distance R T ≤ a := by
      cc_calc statistical
        R ≈[a] S := first
        _ ≈[b] T := second
  fail_if_success
    cc_calc statistical
      R ≈[a] S := first
  fail_if_success
    cc_calc statistical
      R ≈[a] S := first
      R ≈[b] T := second
  fail_if_success
    cc_calc statistical
      R ≈[a] S := first
      _ ≈[b] T := by skip
  fail_if_success
    cc_calc statistical
      R ≈[a] S := first
      _ ≈[b] T := _
  cc_calc statistical
    R ≈[a] S := first
    _ ≈[b] T := second
end Quantitative

section Observations

-- Finite observation bounds need neither a category on systems nor a
-- resource metric. These are the same quantitative laws as above.
variable {Sys O : Type}
variable (model : DistinguisherAdvantage Unit (fun _ => Sys) (fun _ => O))
variable (statistical : O → Sys → Sys → ENNReal)
variable (domination : ∀ D ∈ model.admissible (), ∀ R T,
  model.advantage () D R T ≤ statistical D R T)
include domination

theorem observation_chain (R S T : Sys) (loss : O → ENNReal) (ε : ENNReal)
    (h : model.SubstitutesWithin (A := ()) loss R S)
    (g : ∀ D ∈ model.admissible (), statistical D T S ≤ ε) :
    model.SubstitutesWithin (A := ()) (fun D => loss D + ε) R T := by
  cc_calc mixed model using domination
    R ≃[loss] S := h
    _ ≈[ε] T := ← g

example (R S T : Sys) (loss : O → ENNReal) (ε : ENNReal)
    (D : O) (_admitted : D ∈ model.admissible ())
    (h : model.SubstitutesWithin (A := ()) loss R S)
    (g : ∀ D ∈ model.admissible (), statistical D S T ≤ ε) :
    model.SubstitutesWithin (A := ()) (fun D => loss D + ε) R T := by
  -- Reversal and exact joins are still checked; no metric is invented.
  fail_if_success
    cc_calc mixed model using domination
      R ≃[loss] S := ← h
      _ ≈[ε] T := g
  fail_if_success
    cc_calc mixed model using domination
      R ≃[loss] S := h
      R ≈[ε] T := g
  fail_if_success
    cc_calc mixed model using domination
      R ≃[loss] S := h
      _ ≈[ε] T := g D _admitted
  cc_calc mixed model using domination
    R ≃[loss] S := h
    _ ≈[ε] T := g

/-- trace: [ConstructiveCryptography.ProofAutomation.rule] cc_calc supplied statistical observation -/
#guard_msgs in
set_option trace.ConstructiveCryptography.ProofAutomation.rule true in
example (R S : Sys) (ε : ENNReal)
    (g : ∀ D ∈ model.admissible (), statistical D R S ≤ ε) :
    model.SubstitutesWithin (A := ()) (fun _ => ε) R S := by
  cc_calc mixed model using domination
    R ≈[ε] S := g

end Observations

-- Grammar and dedentation: none of the new forms owns the following tactic.
run_cmd do
  let environment ← Lean.getEnv
  for input in ["cc_calc counted systems\n  X ≃ Y := i",
      "cc_calc counted systems\n  X ≃ Y := ← i through α\n  _ = Z := equation",
      "cc_calc statistical\n  X ≈[ε] Y := ← bound",
      "cc_calc quantitative (id model)\n  X ≃[loss] Y := bound",
      "cc_calc mixed model using domination\n  X ≃[loss] Y := h\n  _ ≈[ε] Z := g"] do
    match Lean.Parser.runParserCategory environment `tactic input with
    | .ok _ => pure ()
    | .error message => throwError "valid chain rejected: {message}"
  for input in ["cc_calc counted systems", "cc_calc counted systems\n  X ≃ Y :=",
      "cc_calc statistical", "cc_calc statistical\n  X ≈ Y := bound",
      "cc_calc mixed model\n  X ≈[ε] Y := bound",
      "cc_calc quantitative model\n  X ≃[loss] Y"] do
    match Lean.Parser.runParserCategory environment `tactic input with
    | .ok _ => throwError "invalid chain accepted: {input}"
    | .error _ => pure ()

#print axioms countedChain
#print axioms Implication.withEndpoints
#print axioms Implication.usageCount_withEndpoints
#print axioms DistinguisherAdvantage.SubstitutesWithin.of_distance
#print axioms countedChain_usageCount
#print axioms statistical_chain
#print axioms mixed_chain
#print axioms observation_chain
#print axioms DistinguisherAdvantage.SubstitutesWithin.of_statistical

end Tests.Substitution.Tactics
