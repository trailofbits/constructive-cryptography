import RandomSystems.Game.Winning

set_option autoImplicit false

/-!
# Blind games
-/

noncomputable section

namespace RandomSystems

open Classical
open Probability

universe u v

namespace System.DDE

variable {X : Type u} {Y : Type v}

/-- A deterministic environment is blind when its stopping decision and next
query depend only on the number of answers received. -/
def IsBlind (winner : System.Winner X Y) : Prop :=
  ∀ left right : List Y, left.length = right.length →
    winner.1 left = winner.1 right

end System.DDE

namespace System.DDG

variable {X : Type u} {Y : Type v}

/-- CR18, Definition 4.20: the blind game preserves queries and the monotone
condition while blocking replies. -/
def blind (game : System.DDG X Y) : System.DDG X Unit where
  system :=
    ⟨(fun history : List X =>
        (⟨history ∈ System.dom game.system,
          fun _ => Unit.unit⟩ : Part Unit)),
      ⟨System.empty_not_mem game.system,
        fun isPrefix nonempty admitted =>
          System.prefix_closed game.system isPrefix nonempty admitted⟩⟩
  condition := game.condition

end System.DDG

namespace PDG

variable {X : Type u} {Y : Type v}

/-- The blind version of a probabilistic game. -/
def blind (game : PDG X Y) : PDG X Unit :=
  Distribution.fTransform System.DDG.blind game

/-- A blind winner is bounded by the supremum winning probability of the
blind game. -/
lemma winProb_le_supWinProb_blind {game : PDG X Y}
    (nonnegative : game.NonNeg) (winner : System.Winner X Y)
    (isBlind : System.DDE.IsBlind winner) :
    winProb winner game ≤ ν(PDG.blind game) := by
  let blockedWinner : System.Winner X Unit :=
    ⟨(fun replies : List Unit =>
        if existsAnswers : ∃ answers : List Y,
            answers.length = replies.length then
          winner.1 (Classical.choose existsAnswers)
        else Part.none),
      by
        intro initial final isPrefix finalDefined
        change (if existsAnswers : ∃ answers : List Y,
            answers.length = initial.length then
          winner.1 (Classical.choose existsAnswers)
          else Part.none).Dom
        change (if existsAnswers : ∃ answers : List Y,
            answers.length = final.length then
          winner.1 (Classical.choose existsAnswers)
          else Part.none).Dom at finalDefined
        have finalExists : ∃ answers : List Y,
            answers.length = final.length := by
          by_contra absent
          rw [dif_neg absent] at finalDefined
          exact finalDefined
        rw [dif_pos finalExists] at finalDefined
        let finalAnswers := Classical.choose finalExists
        let initialAnswers := finalAnswers.take initial.length
        change (winner.1 finalAnswers).Dom at finalDefined
        have initialLength : initialAnswers.length = initial.length := by
          dsimp only [initialAnswers]
          rw [List.length_take, min_eq_left]
          exact isPrefix.length_le.trans_eq
            (Classical.choose_spec finalExists).symm
        have initialExists : ∃ answers : List Y,
            answers.length = initial.length := ⟨initialAnswers, initialLength⟩
        rw [dif_pos initialExists]
        have prefixDefined : (winner.1 initialAnswers).Dom := by
          apply winner.2 (List.take_prefix initial.length finalAnswers)
          exact finalDefined
        rw [isBlind (Classical.choose initialExists) initialAnswers
          ((Classical.choose_spec initialExists).trans initialLength.symm)]
        exact prefixDefined⟩
  have blockedWinner_apply (answers : List Y) :
      blockedWinner.1 (answers.map fun _ => Unit.unit) =
        winner.1 answers := by
    change (if existsAnswers : ∃ candidate : List Y,
        candidate.length = (answers.map fun _ => Unit.unit).length then
          winner.1 (Classical.choose existsAnswers)
        else Part.none) = winner.1 answers
    rw [dif_pos ⟨answers, by simp⟩]
    apply isBlind
    simpa using Classical.choose_spec
      (show ∃ candidate : List Y,
        candidate.length = (answers.map fun _ => Unit.unit).length from
        ⟨answers, by simp⟩)
  have trN_blocked (deterministic : System.DDG X Y) (n : Nat) :
      System.trN blockedWinner (System.DDG.blind deterministic).system n =
        (System.trN winner deterministic.system n).map
          (fun pair => (pair.1, Unit.unit)) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [System.trN, ih]
      let transcript := System.trN winner deterministic.system n
      let blockedTranscript : System.Transcript X Unit :=
        transcript.map fun pair => (pair.1, Unit.unit)
      have replyHistory : blockedTranscript.map Prod.snd =
          (transcript.map Prod.snd).map (fun _ => Unit.unit) := by
        simp [blockedTranscript, List.map_map, Function.comp_def]
      have winnerEqual :
          blockedWinner.1 (blockedTranscript.map Prod.snd) =
            winner.1 (transcript.map Prod.snd) := by
        rw [replyHistory, blockedWinner_apply]
      have domainEqual :
          blockedTranscript.map Prod.snd ∈ blockedWinner.1.Dom ↔
            transcript.map Prod.snd ∈ winner.1.Dom := by
        change (blockedWinner.1 (blockedTranscript.map Prod.snd)).Dom ↔
          (winner.1 (transcript.map Prod.snd)).Dom
        rw [winnerEqual]
      rw [System.trExtend, System.trExtend]
      by_cases originalDefined : transcript.map Prod.snd ∈ winner.1.Dom
      · have blockedDefined : blockedTranscript.map Prod.snd ∈
            blockedWinner.1.Dom := domainEqual.mpr originalDefined
        rw [dif_pos blockedDefined, dif_pos originalDefined]
        have queryEqual :
            (blockedWinner.1
                (blockedTranscript.map Prod.snd)).get blockedDefined =
              (winner.1 (transcript.map Prod.snd)).get originalDefined := by
          have blockedQueryMem := Part.get_mem blockedDefined
          have originalQueryMem :
              (blockedWinner.1
                  (blockedTranscript.map Prod.snd)).get blockedDefined ∈
                winner.1 (transcript.map Prod.snd) := by
            rw [← winnerEqual]
            exact blockedQueryMem
          exact (Part.get_eq_of_mem originalQueryMem originalDefined).symm
        have queryHistory : blockedTranscript.map Prod.fst =
            transcript.map Prod.fst := by
          simp [blockedTranscript, List.map_map, Function.comp_def]
        by_cases systemDefined :
            transcript.map Prod.fst ++
                [(winner.1 (transcript.map Prod.snd)).get originalDefined] ∈
              System.dom deterministic.system
        · have blockedSystemDefined :
              blockedTranscript.map Prod.fst ++
                  [(blockedWinner.1
                    (blockedTranscript.map Prod.snd)).get blockedDefined] ∈
                System.dom (System.DDG.blind deterministic).system := by
            change blockedTranscript.map Prod.fst ++
                [(blockedWinner.1
                  (blockedTranscript.map Prod.snd)).get blockedDefined] ∈
              System.dom deterministic.system
            rwa [queryHistory, queryEqual]
          rw [dif_pos blockedSystemDefined, dif_pos systemDefined]
          simp only [List.map_append, List.map_singleton]
          apply congrArg (fun pair : X × Unit =>
            (System.trN winner deterministic.system n).map
              (fun entry => (entry.1, Unit.unit)) ++ [pair])
          apply Prod.ext
          · simpa only [transcript, blockedTranscript] using queryEqual
          · exact Subsingleton.elim _ _
        · have blockedSystemUndefined :
              blockedTranscript.map Prod.fst ++
                  [(blockedWinner.1
                    (blockedTranscript.map Prod.snd)).get blockedDefined] ∉
                System.dom (System.DDG.blind deterministic).system := by
            change blockedTranscript.map Prod.fst ++
                [(blockedWinner.1
                  (blockedTranscript.map Prod.snd)).get blockedDefined] ∉
              System.dom deterministic.system
            rwa [queryHistory, queryEqual]
          rw [dif_neg blockedSystemUndefined, dif_neg systemDefined]
      · have blockedUndefined : blockedTranscript.map Prod.snd ∉
            blockedWinner.1.Dom := by
          exact fun defined => originalDefined (domainEqual.mp defined)
        rw [dif_neg blockedUndefined, dif_neg originalDefined]
  have tr_blocked (deterministic : System.DDG X Y) :
      System.tr blockedWinner (System.DDG.blind deterministic).system =
        (System.tr winner deterministic.system).map
          (fun transcript => transcript.map
            (fun pair => (pair.1, Unit.unit))) := by
    apply Part.ext'
    · constructor
      · rintro ⟨n, stable⟩
        refine ⟨n, ?_⟩
        have mappedStable :
            (System.trN winner deterministic.system (n + 1)).map
                (fun pair => (pair.1, Unit.unit)) =
              (System.trN winner deterministic.system n).map
                (fun pair => (pair.1, Unit.unit)) := by
          rw [← trN_blocked deterministic (n + 1),
            ← trN_blocked deterministic n]
          exact stable
        have lengthEqual := congrArg List.length mappedStable
        simp only [List.length_map] at lengthEqual
        rcases System.trExtend_eq_or_append winner deterministic.system
            (System.trN winner deterministic.system n) with
          unchanged | ⟨pair, appended⟩
        · exact unchanged
        · rw [show System.trN winner deterministic.system (n + 1) =
              System.trExtend winner deterministic.system
                (System.trN winner deterministic.system n) from rfl,
            appended] at lengthEqual
          simp at lengthEqual
      · rintro ⟨n, stable⟩
        refine ⟨n, ?_⟩
        rw [trN_blocked, trN_blocked, stable]
    · intro blockedStops originalStops
      let n := Nat.find originalStops
      have originalStable :
          System.trN winner deterministic.system (n + 1) =
            System.trN winner deterministic.system n :=
        Nat.find_spec originalStops
      have blockedStable :
          System.trN blockedWinner
                (System.DDG.blind deterministic).system (n + 1) =
            System.trN blockedWinner
                (System.DDG.blind deterministic).system n := by
        rw [trN_blocked, trN_blocked, originalStable]
      calc
        (System.tr blockedWinner
            (System.DDG.blind deterministic).system).get blockedStops =
            System.trN blockedWinner
              (System.DDG.blind deterministic).system n :=
          System.tr_get_eq_trN blockedStops blockedStable
        _ = (System.trN winner deterministic.system n).map
            (fun pair => (pair.1, Unit.unit)) := trN_blocked _ _
        _ = ((System.tr winner deterministic.system).map
            (fun transcript => transcript.map
              (fun pair => (pair.1, Unit.unit)))).get originalStops := by
          change (System.trN winner deterministic.system n).map
              (fun pair => (pair.1, Unit.unit)) =
            ((System.tr winner deterministic.system).get originalStops).map
              (fun pair => (pair.1, Unit.unit))
          rw [System.tr_get_eq_trN originalStops originalStable]
  have gameTr_blocked (deterministic : System.DDG X Y) :
      System.gameTr (System.DDG.blind deterministic) blockedWinner =
        (System.gameTr deterministic winner).map fun result =>
          (result.1.map (fun pair => (pair.1, Unit.unit)), result.2) := by
    unfold System.gameTr
    rw [tr_blocked, Part.map_map, Part.map_map]
    apply congrArg
      (fun transform => (System.tr winner deterministic.system).map transform)
    funext transcript
    apply Prod.ext
    · rfl
    · simp [System.DDG.blind, List.map_map, Function.comp_def]
  have wins_blocked (deterministic : System.DDG X Y) :
      System.Wins blockedWinner (System.DDG.blind deterministic) ↔
        System.Wins winner deterministic := by
    constructor
    · rintro ⟨blockedTranscript, blockedMember⟩
      rw [gameTr_blocked] at blockedMember
      obtain ⟨result, resultMember, resultEqual⟩ :=
        (Part.mem_map_iff _).mp blockedMember
      refine ⟨result.1, ?_⟩
      have won : result.2 = true := congrArg Prod.snd resultEqual
      rw [← won]
      exact resultMember
    · rintro ⟨transcript, member⟩
      refine ⟨transcript.map (fun pair => (pair.1, Unit.unit)), ?_⟩
      rw [gameTr_blocked]
      apply (Part.mem_map_iff _).mpr
      exact ⟨(transcript, true), member, rfl⟩
  have winProbEqual :
      winProb blockedWinner (PDG.blind game) = winProb winner game := by
    unfold winProb PDG.blind
    rw [Distribution.mass_fTransform]
    apply Distribution.mass_congr
    exact wins_blocked
  rw [← winProbEqual]
  exact winProb_le_supWinProb (nonnegative.fTransform _) _

end PDG

namespace ConditionalEquivalence

/-- CR18 notation for blocking a game's replies. -/
scoped prefix:max "b " => PDG.blind

end ConditionalEquivalence

end RandomSystems
