module

public import RandomSystems.System.FiniteQueries
public import RandomSystems.System.QueryRelabel.Laws
public import Tests.FiniteQueries
public import Tests.QueryRelabel

/-!
# Finite query encodings with dependent ports

An adaptive natural-number strategy uses one live port beside an empty query port.
Finite codes preserve its two possible queries. A one-query caller on a restricted domain
uses the same encoding law, retaining its decoded strategy and final decision.
-/

@[expose] public section

namespace Tests.FiniteQueryEncoding

open SystemAlgebra
open Tests.QueryRelabel (caller caller_isDDD caller_closes final_decision)

/-- The live port has natural-number queries; the second port has no query values. -/
def queryAlphabet : Bool → Type
  | false => ℕ
  | true => Empty

/-- Reuse the adaptive `7`, then `23` strategy through the live port. -/
def adaptive : List Bool →. Σ i, queryAlphabet i := fun ys =>
  (Tests.FiniteQueries.adaptive.1 ys).map (fun x => ⟨false, x⟩)

/-- Finite coding retains both adaptive queries and assigns no codes to the empty port. -/
lemma adaptive_encoding :
    ∃ (n : Bool → ℕ) (code : ∀ i, queryAlphabet i → Fin (n i))
      (decode : ∀ i, Fin (n i) ↪ queryAlphabet i),
      n true = 0 ∧ decode false (code false (7 : ℕ)) = (7 : ℕ) ∧
        decode false (code false (23 : ℕ)) = (23 : ℕ) ∧
        code false (7 : ℕ) ≠ code false (23 : ℕ) := by
  obtain ⟨n, code, decode, inverse⟩ := exists_fin_query_encoding adaptive 2
    (fun ys defined => Tests.FiniteQueries.adaptive_bounded ys defined)
  have empty : n true = 0 := Nat.eq_zero_of_not_pos (fun positive =>
    Empty.elim (decode true ⟨0, positive⟩))
  have seven := inverse [] ⟨false, (7 : ℕ)⟩ (Part.mem_map _ (Part.mem_some (7 : ℕ)))
  have twentyThree := inverse [true] ⟨false, (23 : ℕ)⟩ (Part.mem_map _ (Part.mem_some (23 : ℕ)))
  refine ⟨n, code, decode, empty, seven, twentyThree, ?_⟩
  intro same
  have impossible : (7 : ℕ) = 23 :=
    seven.symm.trans ((congrArg (decode false) same).trans twentyThree)
  cases impossible

/-- The existing one-query caller closes on every DDS in its restricted domain. Its finite
encoding preserves that contract through the already-proved query transport. -/
lemma restricted_caller_encoding : ∃ (n : Unit → ℕ) (code : ∀ i, ℕ → Fin (n i))
    (decode : ∀ i, Fin (n i) ↪ ℕ),
    (Domain.ofInputs (fun xs : List (Σ i, Fin (n i)) => xs ≠ [] ∧ xs.length ≤ 1)
      1 (fun _ h => h.2) : Domain (Σ i, Fin (n i)) (Σ _ : Unit, Bool)).DecisionCompatible
        (DDD.relabelQueries caller code) ∧
      (∀ ys, ((ddeOf (IsDDD.relabelQueries caller_isDDD code)).1 ys).map
        (fun x => ⟨x.1, decode x.1 x.2⟩) =
          (ddeOf caller_isDDD).1 ys) ∧
      DDD.relabelQueries caller code (dHist [⟨(), false⟩]) =
        Part.some ⟨.dec, true⟩ := by
  obtain ⟨n, code, decode, inverse⟩ := exists_fin_query_encoding
    (ddeOf caller_isDDD).1
    caller_isDDD.2.1.choose (ddeOf_bounded caller_isDDD)
  refine ⟨n, code, decode, ?_, ?_, ?_⟩
  · apply decisionCompatible_relabelQueries_of_closes code
      ⟨fun h => h.1 rfl, fun hp hn h => ⟨hn, hp.length_le.trans h.2⟩⟩
      ⟨fun h => h.1 rfl, fun hp hn h => ⟨hn, hp.length_le.trans h.2⟩⟩
      (fun xs h => ⟨fun empty => h.1 (List.map_eq_nil_iff.mp empty),
        by simpa only [List.length_map] using h.2⟩)
      caller caller_isDDD caller_closes
  · intro ys
    apply ddeOf_relabelQueries_map_decode caller_isDDD code (fun i => decode i)
      {x | ∃ history, x ∈ (ddeOf caller_isDDD).1 history}
      (fun history x proposed => ⟨history, proposed⟩)
    rintro x ⟨history, proposed⟩
    exact inverse history x proposed
  · change (caller ((dHist [⟨(), false⟩]).map id)).map _ = _
    rw [List.map_id, final_decision, Part.map_some]

#print axioms SystemAlgebra.exists_fin_query_encoding
#print axioms adaptive_encoding
#print axioms restricted_caller_encoding

end Tests.FiniteQueryEncoding
