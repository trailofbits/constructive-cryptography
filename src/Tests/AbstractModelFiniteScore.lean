module

public import Commons.Definitions.AbstractModel.ExtractionGame.Recoding
public import Tests.AbstractModelConverter

/-!
# Exact extraction scores with natural register addresses

The existing Boolean model uses natural-number registers, initialized at 5, and one fixed
terminal guess. A single finite address suffices. The tests discharge source closing and
support-local decoding, and the same retained original-secret law gives score `1/2`.
-/

@[expose] public noncomputable section

namespace Tests.AbstractModelFiniteScore

open Commons.AbstractModel SystemAlgebra Probability Probability.Distribution
open Tests.AbstractModelConverter (model)

/-- The same Boolean model, with natural register names, submits the fixed guess `false`. -/
def guess : model.Command ℕ := ⟨.submit, false⟩

/-- The existing fixed-query environment asks only that terminal submission. -/
def queries : DDE (model.Command ℕ) (Σ i, model.Output i) := DDE.ofQueries [guess]

/-- This caller's final decision is false; extraction uses its submitted value instead. -/
noncomputable def caller : DDD (Port model.Operation model.Query) (model.Input ℕ) model.Output :=
  envProbe queries (fun _ => False)

lemma valid : IsDDD caller := envProbe_isDDD (DDE.ofQueries_queryBounded [guess])

lemma bounded : QueryBounded 1 (ddeOf valid) :=
  ddeOf_envProbe_queryBounded (DDE.ofQueries_queryBounded [guess]) (fun _ => False)

lemma first : (ddeOf valid).1 [] = Part.some guess :=
  (envOf_trim_envProbe (A := fun _ => False) EFits.nil).trans rfl

/-- The terminal submission costs no ordinary command and needs no initialized operand. -/
lemma admitted : model.Admitted 5 0 [guess] := by
  change model.Admitted 5 0 ([] ++ [guess])
  rw [admitted_snoc_iff]
  simp only [guess, ordinary, reads, List.countP_cons, List.countP_nil, Bool.false_eq_true,
    ite_false, Finset.empty_subset, List.mem_nil_iff, false_implies,
    List.nil_append, true_or]
  exact ⟨trivial, Nat.le_refl 0, fun _ => trivial, trivial⟩

/-- Every correctly tagged source DDS on the exact model domain answers the terminal guess. -/
lemma closes (R : InterfaceSystem (Port model.Operation model.Query) (model.Input ℕ) model.Output)
    (_ : IsDDS R) (replyPort : RepliesAtQueriedInterface R)
    (exactDomain : ∀ xs, (R xs).Dom ↔ model.Admitted 5 0 xs) :
    (close caller R [startIn]).Dom :=
  close_envProbe_ofQueries_singleton R guess ((exactDomain [guess]).mpr admitted)
    (fun y hy => replyPort [] guess y hy) (fun _ => False)

/-- All addresses use one code; the sole code decodes to the initialized address 5. -/
def code (_ : ℕ) : Unit := ()

/-- The single finite address refers to source register 5. -/
def decode : Unit ↪ ℕ :=
  ⟨fun _ => 5, fun a b _ => Subsingleton.elim a b⟩

/-- The initial address is represented exactly, despite collisions elsewhere. -/
example : decode (code 5) = 5 := rfl

example : code 6 = code 7 := rfl

/-- The caller proposes only the address-free terminal command, on every reply branch. -/
lemma command_inverse (ys : List (Σ i, model.Output i)) (q : model.Command ℕ)
    (present : q ∈ (ddeOf valid).1 ys) :
    model.mapCommand decode (model.mapCommand code q) = q := by
  have length := bounded ys (Part.dom_iff_mem.mpr ⟨q, present⟩)
  have empty : ys = [] := List.length_eq_zero_iff.mp (Nat.lt_one_iff.mp length)
  subst ys
  rw [first] at present
  obtain rfl := Part.mem_some_iff.mp present
  rfl

/-- One joint draw retains the model parameter together with its fair original secret. -/
noncomputable def retained : ProbDist (Unit × Bool) := 𝒰[Bool].map fun x => ((), x)

/-- The actual source interaction contains exactly the submitted command. -/
lemma completed_inputs (z : Unit × Bool) :
    ((model.extractionDDS 5 0 z).1.tr (ddeOf valid).1 1).map Prod.fst = [guess] := by
  have answered : ((model.extractionDDS 5 0 z).1 [guess]).Dom :=
    ((model.extractionDDS_domain 5 0 z) [] guess (replies_nil _)).mpr admitted
  let R : System (model.Command ℕ) (Σ i, model.Output i) := (model.extractionDDS 5 0 z).1
  let σ : System (Σ i, model.Output i) (model.Command ℕ) := (ddeOf valid).1
  have query : σ [] = Part.some guess := first
  have reply : (R [guess]).Dom := answered
  change (R.tr σ 1).map Prod.fst = [guess]
  simp only [System.tr, List.map_nil, query, Part.some_dom, ↓reduceDIte, Part.get_some,
    List.nil_append, reply, List.map_singleton]

/-- The raw source event tests the original secret, with the retained parameter unchanged. -/
lemma original_secret_event (z : Unit × Bool) :
    let h := (model.extractionDDS 5 0 z).1.tr (ddeOf valid).1 1
    (h ≠ [] ∧ model.submitted (h.map Prod.fst) = some z.2) ↔ z.2 = false := by
  dsimp only
  have inputs := completed_inputs z
  have nonempty : (model.extractionDDS 5 0 z).1.tr (ddeOf valid).1 1 ≠ [] := by
    intro empty
    rw [empty, List.map_nil] at inputs
    exact List.cons_ne_nil guess [] inputs.symm
  rw [inputs]
  change (_ ∧ some false = some z.2) ↔ z.2 = false
  constructor
  · intro event
    exact (Option.some.inj event.2).symm
  · intro secret
    exact ⟨nonempty, congrArg some secret.symm⟩

/-- The full recoding endpoint applies with all source-closing and inverse contracts proved. -/
lemma coded_score_eq_original_secret :
    (model.extractionGame () 0 retained).1.1.winProbability
      (DDD.relabelQueries caller (model.mapInput code))
      (IsDDD.relabelQueries valid (model.mapInput code)) =
        retained.1.mass (fun z => z.2 = false) := by
  refine (extractionGame_winProbability_relabelQueries model caller valid 5 0 closes
    code decode rfl command_inverse retained 1 bounded).trans ?_
  exact Distribution.mass_congr _ original_secret_event

/-- The retained original secret equals the fixed guess with probability one half. -/
lemma retained_mass_false : retained.1.mass (fun z => z.2 = false) = 1 / 2 := by
  rw [retained, ProbDist.map_val, mass_fTransform]
  simp only [ProbDist.uniform, mass_singleton, uniform_apply, Fintype.card_bool, Nat.cast_ofNat]

/-- Natural-register execution and its one-register presentation both score one half. -/
example :
    (model.extractionGame () 0 retained).1.1.winProbability
      (DDD.relabelQueries caller (model.mapInput code))
      (IsDDD.relabelQueries valid (model.mapInput code)) = 1 / 2 :=
  coded_score_eq_original_secret.trans retained_mass_false

/-- The support theorem chooses a finite capacity and preserves the same original-secret score. -/
lemma exists_finite_score :
    ∃ (capacity : ℕ) (code : ℕ → Fin capacity) (decode : Fin capacity ↪ ℕ),
      decode (code 5) = 5 ∧
      (model.extractionGame (code 5) 0 retained).1.1.winProbability
        (DDD.relabelQueries caller (model.mapInput code))
        (IsDDD.relabelQueries valid (model.mapInput code)) = 1 / 2 := by
  obtain ⟨capacity, code, decode, initial, _, score⟩ :=
    exists_fin_extractionGame_winProbability_eq model caller valid 5 0 closes 1 bounded
  refine ⟨capacity, code, decode, initial, (score retained).trans ?_⟩
  exact (Distribution.mass_congr _ original_secret_event).trans retained_mass_false

#print axioms closes
#print axioms command_inverse
#print axioms coded_score_eq_original_secret
#print axioms exists_finite_score
#print axioms exists_fin_extractionGame_winProbability_eq

end Tests.AbstractModelFiniteScore
