import RandomSystems.Distance
import RandomSystems.Game.Winning
import RandomSystems.Technique.ConditionalEquivalence

set_option autoImplicit false

/-!
# Conditional equivalence and distinguishing advantage

The not-won part of a game transcript factors through
`ConditionalEquivalence.massYAfalse`. Equal not-won transcript masses therefore
leave only the winning part to distinguish the underlying systems.
-/

noncomputable section

namespace RandomSystems

open Classical
open Probability
open scoped ConditionalEquivalence

universe u v

variable {X : Type u} {Y : Type v}

/-- CR18, Lemma 4.16, on Lanzenberger games: if two normalized games have
equal nonempty not-won transcript masses, then an environment distinguishes
their underlying systems by at most its winning probability against the
right-hand game. -/
lemma statDist_trLaw_le_winProb_of_massYAfalse_eq
    (winner : System.Winner X Y) (left right : PDG X Y)
    (leftProbability : left.isProbDist)
    (rightProbability : right.isProbDist)
    (leftCompatible : PDS.Compatible winner (PDG.underlying left))
    (rightCompatible : PDS.Compatible winner (PDG.underlying right))
    (leftStops : PDS.Stops winner (PDG.underlying left))
    (rightStops : PDS.Stops winner (PDG.underlying right))
    (notWonEqual : ∀ transcript : System.Transcript X Y, transcript ≠ [] →
      ConditionalEquivalence.massYAfalse left transcript =
        ConditionalEquivalence.massYAfalse right transcript) :
    statDist
        (PDS.trLaw winner (PDG.underlying left))
        (PDS.trLaw winner (PDG.underlying right)) ≤
      PDG.winProb winner right := by
  let notWonTrLaw (localWinner : System.Winner X Y)
      (game : PDG X Y) :
      Distribution (Option (System.Transcript X Y)) :=
    Distribution.fTransform
      (fun deterministic =>
        (System.tr localWinner deterministic.system).toOption)
      (game.restrict fun deterministic =>
        ¬ System.Wins localWinner deterministic)
  let wonTrLaw (localWinner : System.Winner X Y)
      (game : PDG X Y) :
      Distribution (Option (System.Transcript X Y)) :=
    Distribution.fTransform
      (fun deterministic =>
        (System.tr localWinner deterministic.system).toOption)
      (game.restrict (System.Wins localWinner))
  have underlying_mem_support_of_mem_support
      {game : PDG X Y} (nonnegative : game.NonNeg)
      {deterministic : System.DDG X Y}
      (supported : deterministic ∈ game.support) :
      deterministic.system ∈ (PDG.underlying game).support := by
    rw [Finsupp.mem_support_iff] at supported ⊢
    rw [PDG.underlying, Distribution.fTransform_apply_eq_mass]
    intro equalZero
    have below : game deterministic ≤ game.mass (fun candidate =>
        candidate.system = deterministic.system) :=
      Distribution.apply_le_mass nonnegative
        (P := fun candidate => candidate.system = deterministic.system)
        (a := deterministic) rfl
    rw [equalZero] at below
    exact supported (le_antisymm below (nonnegative deterministic))
  have not_wins_iff_condition_false_of_observed
      (localWinner : System.Winner X Y) (game : System.DDG X Y)
      (transcript : System.Transcript X Y)
      (observed : (System.tr localWinner game.system).toOption =
        some transcript) :
      (¬ System.Wins localWinner game) ↔
        game.condition.1 (transcript.map Prod.fst) = false := by
    unfold System.Wins System.gameTr
    rw [Part.toOption_eq_some_iff] at observed
    constructor
    · intro notWins
      apply Bool.eq_false_iff.mpr
      intro conditionTrue
      apply notWins
      refine ⟨transcript, ?_⟩
      rw [Part.mem_map_iff]
      exact ⟨transcript, observed, by simp only [conditionTrue]⟩
    · intro conditionFalse ⟨actual, actualMember⟩
      rw [Part.mem_map_iff] at actualMember
      obtain ⟨source, sourceMember, pairEqual⟩ := actualMember
      have sourceEqual : source = transcript :=
        Part.mem_unique sourceMember observed
      subst source
      have conditionTrue :
          game.condition.1 (transcript.map Prod.fst) = true :=
        congrArg Prod.snd pairEqual
      simp [conditionFalse] at conditionTrue
  have trLaw_underlying_eq_notWon_add_won
      (localWinner : System.Winner X Y) (game : PDG X Y) :
      PDS.trLaw localWinner (PDG.underlying game) =
        notWonTrLaw localWinner game + wonTrLaw localWinner game := by
    unfold PDS.trLaw PDG.underlying
    dsimp only [notWonTrLaw, wonTrLaw]
    rw [Distribution.fTransform_fTransform, ← Distribution.fTransform_add]
    congr 1
    ext deterministic
    rw [Finsupp.add_apply]
    by_cases wins : System.Wins localWinner deterministic <;>
      simp [Distribution.restrict_apply, wins]
  have notWonTrLaw_some
      (localWinner : System.Winner X Y) (game : PDG X Y)
      (nonnegative : game.NonNeg)
      (compatible : PDS.Compatible localWinner (PDG.underlying game))
      (transcript : System.Transcript X Y) :
      notWonTrLaw localWinner game (some transcript) =
        PDS.transcriptEnvironmentFactorPartial localWinner transcript *
          ConditionalEquivalence.massYAfalse game transcript := by
    dsimp only [notWonTrLaw]
    rw [Distribution.fTransform_apply_eq_mass, Distribution.mass_restrict]
    unfold PDS.transcriptEnvironmentFactorPartial
    by_cases environmentConsistent :
        System.transcriptEnvironmentEvent localWinner transcript
    · rw [if_pos environmentConsistent, one_mul]
      unfold ConditionalEquivalence.massYAfalse
      apply Distribution.mass_congr_of_support
      intro deterministic supported
      have deterministicCompatible :
          System.Compatible localWinner deterministic.system :=
        compatible deterministic.system
          (underlying_mem_support_of_mem_support nonnegative supported)
      constructor
      · rintro ⟨observed, notWins⟩
        exact ⟨((System.toOption_eq_some_iff_factors
          deterministicCompatible).mp observed).2,
          (not_wins_iff_condition_false_of_observed localWinner deterministic
            transcript observed).mp notWins⟩
      · rintro ⟨systemConsistent, conditionFalse⟩
        have observed :
            (System.tr localWinner deterministic.system).toOption =
              some transcript :=
          (System.toOption_eq_some_iff_factors deterministicCompatible).mpr
            ⟨environmentConsistent, systemConsistent⟩
        exact ⟨observed,
          (not_wins_iff_condition_false_of_observed localWinner deterministic
            transcript observed).mpr conditionFalse⟩
    · rw [if_neg environmentConsistent, zero_mul]
      calc
        game.mass (fun deterministic =>
            (System.tr localWinner deterministic.system).toOption =
                some transcript ∧
              ¬ System.Wins localWinner deterministic) =
            game.mass (fun _ => False) := by
          apply Distribution.mass_congr_of_support
          intro deterministic supported
          have deterministicCompatible :
              System.Compatible localWinner deterministic.system :=
            compatible deterministic.system
              (underlying_mem_support_of_mem_support nonnegative supported)
          constructor
          · rintro ⟨observed, _⟩
            exact environmentConsistent
              ((System.toOption_eq_some_iff_factors
                deterministicCompatible).mp observed).1
          · exact False.elim
        _ = 0 := Distribution.mass_eq_zero_of_forall_not _ (fun _ => id)
  have transcriptSystemFactor_nil (system : PDS X Y) :
      PDS.transcriptSystemFactor system [] = system.weight := by
    unfold PDS.transcriptSystemFactor
    rw [Distribution.mass_congr system
      (Q := fun _ => True) (fun deterministic => by
        simp [System.SystemConsistent])]
    exact Distribution.mass_true system
  have trLaw_nil_eq_of_weight_eq
      (localWinner : System.Winner X Y) (first second : PDS X Y)
      (firstCompatible : PDS.Compatible localWinner first)
      (secondCompatible : PDS.Compatible localWinner second)
      (weightEqual : first.weight = second.weight) :
      PDS.trLaw localWinner first (some []) =
        PDS.trLaw localWinner second (some []) := by
    rw [PDS.trLaw_some_factorization localWinner first firstCompatible [],
      PDS.trLaw_some_factorization localWinner second secondCompatible [],
      transcriptSystemFactor_nil, transcriptSystemFactor_nil, weightEqual]
  have wonTrLaw_nonnegative
      (localWinner : System.Winner X Y) {game : PDG X Y}
      (nonnegative : game.NonNeg) :
      (wonTrLaw localWinner game).NonNeg :=
    (nonnegative.restrict (System.Wins localWinner)).fTransform _
  have wonTrLaw_weight
      (localWinner : System.Winner X Y) (game : PDG X Y) :
      (wonTrLaw localWinner game).weight =
        PDG.winProb localWinner game := by
    dsimp only [wonTrLaw]
    unfold PDG.winProb
    rw [Distribution.weight_fTransform, Distribution.weight_restrict]
  have statDist_trLaw_le_winProb_left
      (localWinner : System.Winner X Y) (first second : PDG X Y)
      (firstNonnegative : first.NonNeg)
      (secondNonnegative : second.NonNeg)
      (weightEqual : first.weight = second.weight)
      (firstCompatible : PDS.Compatible localWinner (PDG.underlying first))
      (secondCompatible : PDS.Compatible localWinner (PDG.underlying second))
      (firstStops : PDS.Stops localWinner (PDG.underlying first))
      (secondStops : PDS.Stops localWinner (PDG.underlying second))
      (notWonEqualLocal :
        ∀ transcript : System.Transcript X Y, transcript ≠ [] →
          ConditionalEquivalence.massYAfalse first transcript =
            ConditionalEquivalence.massYAfalse second transcript) :
      statDist
          (PDS.trLaw localWinner (PDG.underlying first))
          (PDS.trLaw localWinner (PDG.underlying second)) ≤
        PDG.winProb localWinner first := by
    let firstLaw := PDS.trLaw localWinner (PDG.underlying first)
    let secondLaw := PDS.trLaw localWinner (PDG.underlying second)
    let wonLaw := wonTrLaw localWinner first
    let support := (firstLaw - secondLaw).support ∪ wonLaw.support
    rw [statDist_eq_sum_of_support_subset firstLaw secondLaw
      (Finset.subset_union_left :
        (firstLaw - secondLaw).support ⊆ support)]
    rw [← wonTrLaw_weight localWinner first,
      Distribution.weight_eq_sum_of_support_subset wonLaw
        (Finset.subset_union_right : wonLaw.support ⊆ support)]
    apply Finset.sum_le_sum
    intro observation _
    change max (firstLaw observation - secondLaw observation) 0 ≤
      wonLaw observation
    rcases observation with _ | transcript
    · have firstZero : firstLaw none = 0 :=
        PDS.trLaw_none_eq_zero localWinner (PDG.underlying first) firstStops
      have secondZero : secondLaw none = 0 :=
        PDS.trLaw_none_eq_zero localWinner (PDG.underlying second) secondStops
      rw [firstZero, secondZero, sub_self, max_self]
      exact wonTrLaw_nonnegative localWinner firstNonnegative none
    · by_cases empty : transcript = []
      · subst transcript
        have equalAtNil : firstLaw (some []) = secondLaw (some []) := by
          apply trLaw_nil_eq_of_weight_eq localWinner
            (PDG.underlying first) (PDG.underlying second)
            firstCompatible secondCompatible
          simpa only [PDG.underlying, Distribution.weight_fTransform] using
            weightEqual
        rw [equalAtNil, sub_self, max_self]
        exact wonTrLaw_nonnegative localWinner firstNonnegative (some [])
      · have firstSplit := congrArg (fun law :
            Distribution (Option (System.Transcript X Y)) =>
              law (some transcript))
          (trLaw_underlying_eq_notWon_add_won localWinner first)
        have secondSplit := congrArg (fun law :
            Distribution (Option (System.Transcript X Y)) =>
              law (some transcript))
          (trLaw_underlying_eq_notWon_add_won localWinner second)
        have notWonLawEqual :
            notWonTrLaw localWinner first (some transcript) =
              notWonTrLaw localWinner second (some transcript) := by
          rw [notWonTrLaw_some localWinner first firstNonnegative
              firstCompatible,
            notWonTrLaw_some localWinner second secondNonnegative
              secondCompatible,
            notWonEqualLocal transcript empty]
        change max
            (PDS.trLaw localWinner (PDG.underlying first) (some transcript) -
              PDS.trLaw localWinner (PDG.underlying second)
                (some transcript)) 0 ≤
          wonTrLaw localWinner first (some transcript)
        rw [firstSplit, secondSplit, Finsupp.add_apply, Finsupp.add_apply,
          notWonLawEqual]
        apply max_le
        · have secondWonNonnegative :=
            wonTrLaw_nonnegative localWinner secondNonnegative
              (some transcript)
          linarith
        · exact wonTrLaw_nonnegative localWinner firstNonnegative
            (some transcript)
  rw [statDist_symm_of_eq_weight]
  · exact statDist_trLaw_le_winProb_left winner right left
      rightProbability.nonNeg leftProbability.nonNeg
      (rightProbability.weight_eq.trans leftProbability.weight_eq.symm)
      rightCompatible leftCompatible rightStops leftStops
      (fun transcript nonempty => (notWonEqual transcript nonempty).symm)
  · simp only [PDS.trLaw, Distribution.weight_fTransform,
      PDG.underlying, rightProbability.weight_eq, leftProbability.weight_eq]

/-- CR18, Lemma 4.16: equivalent games leave only the winning part available
to distinguish their underlying systems. -/
lemma statDist_trLaw_le_winProb_of_equivalentAsGames
    (winner : System.Winner X Y) (left right : PDG X Y)
    (leftInitiallyFalse : left.InitiallyFalse)
    (rightInitiallyFalse : right.InitiallyFalse)
    (leftProbability : left.isProbDist)
    (rightProbability : right.isProbDist)
    (leftCompatible : PDS.Compatible winner left.underlying)
    (rightCompatible : PDS.Compatible winner right.underlying)
    (leftStops : PDS.Stops winner left.underlying)
    (rightStops : PDS.Stops winner right.underlying)
    (equivalent : left ≡ᵍ right) :
    statDist (PDS.trLaw winner left.underlying)
        (PDS.trLaw winner right.underlying) ≤
      PDG.winProb winner right := by
  apply statDist_trLaw_le_winProb_of_massYAfalse_eq
    winner left right leftProbability rightProbability
    leftCompatible rightCompatible leftStops rightStops
  intro transcript _
  exact PDG.massYAfalse_eq_of_equivalentAsGames
    leftInitiallyFalse rightInitiallyFalse leftProbability rightProbability
    equivalent transcript

end RandomSystems
