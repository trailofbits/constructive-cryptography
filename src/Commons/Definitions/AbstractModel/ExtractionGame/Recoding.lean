module

public import Commons.Definitions.AbstractModel.ExtractionGame
public import Commons.Definitions.AbstractModel.FiniteAddresses
public import Commons.Definitions.AbstractModel.ExtractionPresentation.Recoding
public import RandomSystems.Game.Transcript

/-!
# Exact scores under finite register recoding

`extractionGame_winProbability_relabelQueries` equates the coded game's winning probability
with the original raw caller's completed extraction-event mass under the same joint law.
The source register carrier is arbitrary; finite alphabets are required at the coded game.
Source closing is explicit. The proof transports that contract, applies the discrete-game
score law, and uses the transcript correspondence from `ExtractionPresentation.Recoding`.
`exists_fin_extractionGame_winProbability_eq` chooses one capacity and address code from the
caller's bounded support; the same code preserves the score for every joint law.
-/

@[expose] public section

namespace Commons.AbstractModel

open SystemAlgebra Probability Probability.Distribution

/-- Finite-address execution has exactly the raw source caller's extraction-event mass. -/
theorem extractionGame_winProbability_relabelQueries
    -- `M` interprets operations on values `S` using parameters `P`; `ι` and `κ` name registers.
    {S P ι κ : Type} (M : Commons.AbstractModel S P) [DecidableEq ι] [DecidableEq κ]
    -- Values, coded addresses `κ`, ports and replies are finite; `ι` remains arbitrary.
    [Fintype S] [Fintype κ] [Fintype M.Operation] [Fintype M.Query]
    [∀ ρ, Fintype (M.Reply ρ)]
    -- `D` is the original caller; `valid` supplies its bounded interaction discipline.
    (D : DDD (Port M.Operation M.Query) (M.Input ι) M.Output) (valid : IsDDD D)
    -- `input` initially holds the secret; `k` counts ordinary commands before submission.
    (input : ι) (k : ℕ)
    -- Closing is required on every correctly tagged DDS with the exact source domain.
    (closes : ∀ R : InterfaceSystem (Port M.Operation M.Query) (M.Input ι) M.Output,
      IsDDS R → RepliesAtQueriedInterface R →
      (∀ xs, (R xs).Dom ↔ M.Admitted input k xs) → (close D R [startIn]).Dom)
    -- `code` and `decode` retain the initial address and every command the caller may propose.
    (code : ι → κ) (decode : κ ↪ ι) (initial : decode (code input) = input)
    (inverse : ∀ ys q, q ∈ (ddeOf valid).1 ys →
      M.mapCommand decode (M.mapCommand code q) = q)
    -- `μ` is the unchanged joint parameter/secret law; `n` bounds the source caller.
    (μ : ProbDist (P × S)) (n : ℕ) (bounded : QueryBounded n (ddeOf valid)) :
    (M.extractionGame (code input) k μ).1.1.winProbability
      (DDD.relabelQueries D (M.mapInput code))
      (IsDDD.relabelQueries valid (M.mapInput code)) =
    μ.1.mass (fun z =>
      let h := (M.extractionDDS input k z).1.tr (ddeOf valid).1 n
      h ≠ [] ∧ M.submitted (h.map Prod.fst) = some z.2) := by
  let A := M.interface (code input) k
  let : ∀ i, Fintype (M.Input κ i) := A.instFintypeX
  let : ∀ i, Fintype (M.Output i) := A.instFintypeY
  let codedValid := IsDDD.relabelQueries valid (M.mapInput code)
  -- Source closing transfers through the admitted command map.
  have legal : A.inputDomain.DecisionCompatible (DDD.relabelQueries D (M.mapInput code)) :=
    decisionCompatible_relabelQueries_of_closes (M.mapInput code)
      ⟨fun h => h.1 rfl, fun hp hne h => h.prefix hp hne⟩
      ⟨fun h => h.1 rfl, fun hp hne h => h.prefix hp hne⟩
      (fun _ h => h.mapCommand code) D valid closes
  have codedBound : QueryBounded n (ddeOf codedValid) :=
    (queryBounded_ddeOf_relabelQueries_iff valid (M.mapInput code) n).mpr bounded
  have compatible := legal.environment codedValid
    (M.extractionGame (code input) k μ).visible.1
    (M.extractionGame (code input) k μ).visible.2
  -- The coded game is finite, so its score is its retained completed-event mass.
  have score := PDG.winProbability_behavior
    (M.extractionPDG (code input) k μ).1 (M.extractionPDG (code input) k μ).2
    (DDD.relabelQueries D (M.mapInput code)) codedValid compatible codedBound
  refine score.trans ?_
  rw [extractionPDG, ProbDist.map_val, Distribution.mass_fTransform]
  -- Decoding preserves nonemptiness and the first submitted guess for each same sample.
  apply Distribution.mass_congr
  intro z
  have transcript := extractionDDS_tr_relabelQueries M D valid
    code decode input initial inverse k z n
  let h := (M.extractionDDS (code input) k z).1.tr (ddeOf codedValid).1 n
  change (h ≠ [] ∧ M.submitted (h.map Prod.fst) = some z.2) ↔
    ((M.extractionDDS input k z).1.tr (ddeOf valid).1 n ≠ [] ∧
      M.submitted (((M.extractionDDS input k z).1.tr (ddeOf valid).1 n).map Prod.fst) =
        some z.2)
  rw [← transcript]
  change (h ≠ [] ∧ M.submitted (h.map Prod.fst) = some z.2) ↔
    (h.map (Prod.map (M.mapCommand decode) id) ≠ [] ∧
      M.submitted ((h.map (Prod.map (M.mapCommand decode) id)).map Prod.fst) = some z.2)
  refine and_congr (not_congr List.map_eq_nil_iff).symm ?_
  have projected : (h.map (Prod.map (M.mapCommand decode) id)).map Prod.fst =
      (h.map Prod.fst).map (M.mapCommand decode) :=
    (List.map_map (f := Prod.map (M.mapCommand decode) id) (g := Prod.fst) (l := h)).trans
      (List.map_map (f := Prod.fst) (g := M.mapCommand decode) (l := h)).symm
  exact (congrArg (fun x => x = some z.2)
    ((congrArg M.submitted projected).trans (submitted_mapCommand M decode _))).to_iff.symm

/-- One finite register capacity preserves the bounded caller's exact extraction score. -/
theorem exists_fin_extractionGame_winProbability_eq
    -- `M` interprets operations on values `S` using parameters `P`; `ι` names source registers.
    {S P ι : Type} (M : Commons.AbstractModel S P) [DecidableEq ι]
    -- Values, ports and replies are finite; source addresses remain arbitrary.
    [Fintype S] [Fintype M.Operation] [Fintype M.Query]
    [∀ ρ, Fintype (M.Reply ρ)]
    -- `D` is the source caller; `input` holds the original secret and `k` counts ordinary calls.
    (D : DDD (Port M.Operation M.Query) (M.Input ι) M.Output) (valid : IsDDD D)
    (input : ι) (k : ℕ)
    -- `closes` is the source contract on every correctly tagged DDS of the exact domain.
    (closes : ∀ R : InterfaceSystem (Port M.Operation M.Query) (M.Input ι) M.Output,
      IsDDS R → RepliesAtQueriedInterface R →
      (∀ xs, (R xs).Dom ↔ M.Admitted input k xs) → (close D R [startIn]).Dom)
    -- `n` bounds every reply branch; `ddeOf_bounded valid` supplies such a bound.
    (n : ℕ) (bounded : QueryBounded n (ddeOf valid)) :
    -- A single `capacity` and code work for the initial address and all proposed commands.
    ∃ (capacity : ℕ) (code : ι → Fin capacity) (decode : Fin capacity ↪ ι),
      decode (code input) = input ∧
      (∀ ys q, q ∈ (ddeOf valid).1 ys →
        M.mapCommand decode (M.mapCommand code q) = q) ∧
      -- The same code serves every retained joint parameter/secret law `μ`.
      ∀ μ : ProbDist (P × S),
      (M.extractionGame (code input) k μ).1.1.winProbability
        (DDD.relabelQueries D (M.mapInput code))
        (IsDDD.relabelQueries valid (M.mapInput code)) =
      μ.1.mass (fun z =>
        let h := (M.extractionDDS input k z).1.tr (ddeOf valid).1 n
        h ≠ [] ∧ M.submitted (h.map Prod.fst) = some z.2) := by
  -- Reply alphabets do not depend on register addresses; the existing interface certifies them.
  let A := M.interface () k
  let : ∀ i, Fintype (M.Output i) := A.instFintypeY
  obtain ⟨capacity, code, decode, initial, _, inverse⟩ :=
    exists_fin_address_encoding_of_queryBounded input (ddeOf valid) bounded
  exact ⟨capacity, code, decode, initial, inverse,
    fun μ => extractionGame_winProbability_relabelQueries M D valid input k closes
      code decode initial inverse μ n bounded⟩

end Commons.AbstractModel
