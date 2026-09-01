import RandomSystems.Game.Blind
import RandomSystems.Game.Filter

set_option autoImplicit false

/-!
# Blind winning bound for filtered games

This module supplies the generic blind-game bound used after conditional
equivalence. Applications provide only their fixed-query bad-event bound.
-/

noncomputable section

namespace RandomSystems.PDG

open Classical
open Probability

universe u v w

variable {A : Type u} {X : Type v} {Y : Type w}

/-- A uniform bad-event mass bound for every history admitted by a common
prefix-closed filter bounds the maximal winning probability of the filtered
blind game. -/
lemma supWinProb_blind_filterDom_fTransform_le
    (source : Distribution A) (toGame : A → System.DDG X Y)
    (domain : Set (List X))
    (hasDomain : ∀ value, System.dom (toGame value).system = domain)
    (allowed : List X → Prop) (prefixClosed : PrefixClosed allowed)
    (nilAllowed : allowed []) (bad : A → List X → Prop)
    (winImpliesBad : ∀ value queries,
      (toGame value).condition.1 queries = true → bad value queries)
    (sourceNonnegative : source.NonNeg) {bound : ℝ}
    (boundNonnegative : 0 ≤ bound)
    (badMass_le : ∀ queries, allowed queries →
      source.mass (fun value => bad value queries) ≤ bound) :
    supWinProb
        (blind (filterDom allowed prefixClosed
          (Distribution.fTransform toGame source))) ≤ bound := by
  apply supWinProb_le boundNonnegative
  intro winner
  unfold winProb blind filterDom
  rw [Distribution.mass_fTransform, Distribution.mass_fTransform,
    Distribution.mass_fTransform]
  let filteredBlind : A → System.DDG X Unit := fun value =>
    System.DDG.blind
      (System.DDG.filterDom allowed prefixClosed (toGame value))
  change source.mass (fun value => System.Wins winner (filteredBlind value)) ≤
    bound
  by_cases someValueWins : ∃ value, System.Wins winner (filteredBlind value)
  · obtain ⟨referenceValue, referenceWins⟩ := someValueWins
    have system_eq (value : A) :
        (filteredBlind value).system =
          (filteredBlind referenceValue).system := by
      apply Subtype.ext
      funext history
      apply Part.ext'
      · change
          (history ∈ System.dom (toGame value).system ∧ allowed history) ↔
            (history ∈ System.dom (toGame referenceValue).system ∧
              allowed history)
        rw [hasDomain value, hasDomain referenceValue]
      · intro _ _
        exact Subsingleton.elim _ _
    obtain ⟨_, referenceGameMember⟩ := referenceWins
    unfold System.gameTr at referenceGameMember
    obtain ⟨stoppingTranscript, stoppingTranscriptMember, _⟩ :=
      (Part.mem_map_iff _).mp referenceGameMember
    have referenceStops : System.Stops winner
        (filteredBlind referenceValue).system :=
      Part.dom_iff_mem.mpr ⟨stoppingTranscript, stoppingTranscriptMember⟩
    let referenceTranscript :=
      (System.tr winner (filteredBlind referenceValue).system).get
        referenceStops
    have referenceTranscript_eq : referenceTranscript =
        System.trN winner (filteredBlind referenceValue).system
          (Nat.find referenceStops) := by
      exact System.tr_get_eq_trN referenceStops (Nat.find_spec referenceStops)
    let queries := referenceTranscript.map Prod.fst
    have queriesAllowed : allowed queries := by
      rcases System.trN_map_fst_mem_dom_or_nil winner
          (filteredBlind referenceValue).system (Nat.find referenceStops) with
        empty | admitted
      · change allowed (referenceTranscript.map Prod.fst)
        rw [referenceTranscript_eq, empty]
        exact nilAllowed
      · change allowed (referenceTranscript.map Prod.fst)
        rw [referenceTranscript_eq]
        change
          (System.trN winner (filteredBlind referenceValue).system
              (Nat.find referenceStops)).map Prod.fst ∈
            System.dom (System.filterDom allowed prefixClosed
              (toGame referenceValue).system)
          at admitted
        exact (System.mem_dom_filterDom allowed prefixClosed
          (toGame referenceValue).system _).mp admitted |>.2
    have winningSubset : ∀ value,
        System.Wins winner (filteredBlind value) → bad value queries := by
      intro value wins
      obtain ⟨_, gameMember⟩ := wins
      unfold System.gameTr at gameMember
      obtain ⟨transcript, transcriptMember, resultEq⟩ :=
        (Part.mem_map_iff _).mp gameMember
      have transcriptMember' : transcript ∈
          System.tr winner (filteredBlind referenceValue).system := by
        rw [← system_eq value]
        exact transcriptMember
      have transcript_eq : transcript = referenceTranscript :=
        Part.mem_unique transcriptMember' (Part.get_mem referenceStops)
      have conditionTrue : (toGame value).condition.1
          (transcript.map Prod.fst) = true := by
        exact congrArg Prod.snd resultEq
      rw [transcript_eq] at conditionTrue
      exact winImpliesBad value queries conditionTrue
    exact (Distribution.mass_mono sourceNonnegative winningSubset).trans
      (badMass_le queries queriesAllowed)
  · have winningEmpty : ∀ value,
        ¬ System.Wins winner (filteredBlind value) := by
      simpa only [not_exists] using someValueWins
    rw [Distribution.mass_eq_zero_of_forall_not _ winningEmpty]
    exact boundNonnegative

end RandomSystems.PDG
