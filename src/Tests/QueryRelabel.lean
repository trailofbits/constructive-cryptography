module

public import RandomSystems.Distance.Decision
public import RandomSystems.System.QueryRelabel.Laws
public import RandomSystems.System.Transcript
public import RandomSystems.System.FiniteQueries

/-!
# Query coding on a finite support

A fixed-query observer asks natural number `7` and accepts its Boolean reply.
Coding uses one Boolean query; decoding recovers `7` only on the observer's support.
The original and coded domains admit one query, and the final decision stays `true`.
-/

@[expose] public noncomputable section

namespace Tests.QueryRelabel

open SystemAlgebra

/-- The sole natural-number resource query. -/
def request : Σ _ : Unit, ℕ := ⟨(), 7⟩

/-- Ask `7` once, using the existing fixed-query environment. -/
def queries : DDE (Σ _ : Unit, ℕ) (Σ _ : Unit, Bool) := DDE.ofQueries [request]

/-- Accept after the sole reply. -/
def caller : DDD Unit (fun _ => ℕ) (fun _ => Bool) := envProbe queries (fun _ => True)

lemma caller_isDDD : IsDDD caller := envProbe_isDDD (DDE.ofQueries_queryBounded [request])

/-- Code `7` as `true`; all other natural-number queries share `false`. -/
def code (_ : Unit) (n : ℕ) : Bool := n == 7

/-- Decode the supported query as `7`; the off-support branch chooses `0`. -/
def decode (_ : Unit) (b : Bool) : ℕ := if b then 7 else 0

lemma query_support (ys : List (Σ _ : Unit, Bool)) (x : Σ _ : Unit, ℕ)
    (proposed : x ∈ (ddeOf caller_isDDD).1 ys) : x ∈ ({request} : Set _) := by
  have short := ddeOf_envProbe_queryBounded (DDE.ofQueries_queryBounded [request])
    (fun _ => True) ys (Part.dom_iff_mem.mpr ⟨x, proposed⟩)
  have empty : ys = [] := List.length_eq_zero_iff.mp (by simpa using short)
  subst ys
  change x ∈ envOf (trim (envProbe queries (fun _ => True))) [] at proposed
  rw [envOf_trim_envProbe EFits.nil] at proposed
  exact Part.mem_some_iff.mp proposed

lemma decode_support (x : Σ _ : Unit, ℕ) (member : x ∈ ({request} : Set _)) :
    decode x.1 (code x.1 x.2) = x.2 := by
  obtain rfl := member
  rfl

/-- Finite support comes from the stopping law, although the source query carrier is infinite. -/
example : {x | ∃ ys, x ∈ (ddeOf caller_isDDD).1 ys}.Finite :=
  finite_queries_of_queryBounded _ (ddeOf_bounded caller_isDDD)

/-- The decoder is deliberately not an inverse on the whole natural-number carrier. -/
example : decode () (code () 8) ≠ 8 := by
  change (0 : ℕ) ≠ 8
  omega

/-- The decoded strategy equals the original for every reply history, including stopped ones. -/
lemma decoded_strategy (ys : List (Σ _ : Unit, Bool)) :
    ((ddeOf (IsDDD.relabelQueries caller_isDDD code)).1 ys).map
      (fun x => ⟨x.1, decode x.1 x.2⟩) = (ddeOf caller_isDDD).1 ys :=
  ddeOf_relabelQueries_map_decode caller_isDDD code decode {request}
    query_support decode_support ys

/-- A restricted raw resource answers only its first query, with `false`. -/
def answer : InterfaceSystem Unit (fun _ => ℕ) (fun _ => Bool)
  | [_] => Part.some ⟨(), false⟩
  | _ => Part.none

/-- Transcript transport is the raw law applied to the actual coded observer. -/
example : ((relabel answer (fun x => ⟨x.1, decode x.1 x.2⟩) id).tr
      (ddeOf (IsDDD.relabelQueries caller_isDDD code)).1 3).map
        (Prod.map (fun x => ⟨x.1, decode x.1 x.2⟩) id) =
      answer.tr (ddeOf caller_isDDD).1 3 := by
  rw [System.tr_relabel_input, funext decoded_strategy]

lemma final_decision : caller (dHist [⟨(), false⟩]) = Part.some ⟨.dec, true⟩ := by
  have fits : EFits queries.1 [⟨(), false⟩] :=
    EFits.snoc EFits.nil (show request ∈ queries.1 [] from Part.mem_some _) rfl
  rw [caller, envProbe_dHist fits]
  have stopped : ¬ (queries.1 [⟨(), false⟩]).Dom := Part.not_none_dom
  rw [envReply, dite_eq_right stopped]
  simp only [decide_true]


/-- Coding a query leaves the final decision output unchanged. -/
example : DDD.relabelQueries caller code (dHist [⟨(), false⟩]) = Part.some ⟨.dec, true⟩ := by
  change (caller ((dHist [⟨(), false⟩]).map id)).map _ = _
  rw [List.map_id, final_decision, Part.map_some]

/-- Every DDS on the one-query domain answers the fixed query, after which the caller decides. -/
lemma caller_closes (S : InterfaceSystem Unit (fun _ => ℕ) (fun _ => Bool))
    (_ : IsDDS S) (_ : RepliesAtQueriedInterface S)
    (exactDomain : ∀ xs, (S xs).Dom ↔ xs ≠ [] ∧ xs.length ≤ 1) :
    (close caller S [startIn]).Dom := by
  have defined := (exactDomain [request]).mpr ⟨List.cons_ne_nil _ _, Nat.le_refl 1⟩
  obtain ⟨⟨⟨⟩, b⟩, reply⟩ := Part.dom_iff_mem.mp defined
  have asked : request ∈ envOf caller [] := by
    rw [caller, envOf_envProbe EFits.nil]
    exact Part.mem_some _
  have actual := Transcript.snoc Transcript.nil asked reply
  have fits : EFits queries.1 [⟨(), b⟩] :=
    EFits.snoc EFits.nil (show request ∈ queries.1 [] from Part.mem_some _) rfl
  refine Part.dom_iff_mem.mpr ⟨decOut true, (close_decision true).mpr
    ⟨[request], [⟨(), b⟩], actual, ?_⟩⟩
  rw [caller, envProbe_dHist fits]
  have stopped : ¬ (queries.1 [⟨(), b⟩]).Dom := Part.not_none_dom
  rw [envReply, dite_eq_right stopped]
  simp only [decide_true, Part.mem_some_iff]

/-- The legal-closing contract transfers at the same one-query domain. -/
example :
    (Domain.ofInputs (fun xs : List (Σ _ : Unit, Bool) => xs ≠ [] ∧ xs.length ≤ 1)
      1 (fun _ h => h.2) : Domain (Σ _ : Unit, Bool) (Σ _ : Unit, Bool)).DecisionCompatible
        (DDD.relabelQueries caller code) := by
  apply decisionCompatible_relabelQueries_of_closes code
    ⟨fun h => h.1 rfl, fun hp hn h => ⟨hn, hp.length_le.trans h.2⟩⟩
    ⟨fun h => h.1 rfl, fun hp hn h => ⟨hn, hp.length_le.trans h.2⟩⟩
    (fun xs h => ⟨fun empty => h.1 (List.map_eq_nil_iff.mp empty),
      by simpa only [List.length_map] using h.2⟩) caller caller_isDDD caller_closes

/-- The supported one-query caller keeps its exact bound after a noninjective coding. -/
example : QueryBounded 1 (ddeOf (IsDDD.relabelQueries caller_isDDD code)) :=
  (queryBounded_ddeOf_relabelQueries_iff caller_isDDD code 1).mpr
    (ddeOf_envProbe_queryBounded (DDE.ofQueries_queryBounded [request]) (fun _ => True))

/-- A caller that makes no resource query remains zero-bounded under the same coding. -/
example : QueryBounded 0 (ddeOf (IsDDD.relabelQueries
    (envProbe_isDDD (A := fun _ => True)
      (DDE.ofQueries_queryBounded (X := Σ _ : Unit, ℕ) (Y := Σ _ : Unit, Bool) []))
    code)) :=
  (queryBounded_ddeOf_relabelQueries_iff _ code 0).mpr
    (ddeOf_envProbe_queryBounded (DDE.ofQueries_queryBounded []) (fun _ => True))

#print axioms queryBounded_ddeOf_relabelQueries_iff

#print axioms decoded_strategy
#print axioms final_decision
#print axioms caller_closes
#print axioms decisionCompatible_relabelQueries_of_closes

end Tests.QueryRelabel
