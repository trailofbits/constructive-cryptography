import Probability.Conditional
import RandomSystems.Game.Winning
import RandomSystems.Technique.ConditionalEquivalence.InitiallyFalse
import RandomSystems.TranscriptFactor

set_option autoImplicit false

/-!
# Conditional equivalence

CR18, Definition 4.19, adapted to Lanzenberger games. A game is a law over
pairs `(s, A)`, where `s` supplies the visible answers and the monotone
condition `A` is hidden during the interaction.
-/

noncomputable section

namespace RandomSystems

open Classical
open Probability

universe u v

variable {X : Type u} {Y : Type v}

namespace System

/-- CR18, equation (4.39), on Lanzenberger's game carrier: use the target
system for the visible answers and the game's condition for winning. The
combined system is defined exactly where both component systems are. -/
def enhance_with_MBO (target : DDS X Y) (game : DDG X Y) : DDG X Y where
  system :=
    ⟨fun history =>
      ⟨history ∈ dom target ∧ history ∈ dom game.system,
        fun admitted => output target history admitted.1⟩,
      by
        refine ⟨fun empty => empty_not_mem target empty.1, ?_⟩
        intro initial final isPrefix nonempty admitted
        exact ⟨prefix_closed target isPrefix nonempty admitted.1,
          prefix_closed game.system isPrefix nonempty admitted.2⟩⟩
  condition := game.condition

/-- Enhancement changes only the visible system, so it preserves the initial
value of the monotone condition. -/
lemma DDG.initiallyFalse_enhance_with_MBO (target : DDS X Y)
    (game : DDG X Y) (initiallyFalse : game.InitiallyFalse) :
    (enhance_with_MBO target game).InitiallyFalse :=
  initiallyFalse

end System

namespace PDG

/-- CR18, equation (4.39): independently sample the target system and the
source game, then combine the target's visible behavior with the source
game's condition. -/
def enhance_with_MBO (target : PDS X Y) (game : PDG X Y) : PDG X Y :=
  Distribution.fTransform
    (fun pair => System.enhance_with_MBO pair.1 pair.2)
    (Distribution.prod target game)

/-- Independent enhancement preserves the source game's initially-false
condition. -/
lemma initiallyFalse_enhance_with_MBO (target : PDS X Y)
    (game : PDG X Y) (initiallyFalse : game.InitiallyFalse) :
    (enhance_with_MBO target game).InitiallyFalse := by
  apply initiallyFalse_fTransform
  intro pair supported
  obtain ⟨_, gameSupported⟩ := Finset.mem_product.mp
    (Distribution.support_prod_subset target game supported)
  exact pair.2.initiallyFalse_enhance_with_MBO pair.1
    (initiallyFalse pair.2 gameSupported)

/-- CR18, equation (4.39): forgetting the condition of the enhanced target
recovers the target. The common-domain hypotheses make the intersection in
`System.enhance_with_MBO` observationally equal to the sampled target system. -/
lemma underlying_enhance_with_MBO_eq (target : PDS X Y) (game : PDG X Y)
    (domain : Set (List X)) (gameWeight : game.weight = 1)
    (targetDomain : PDS.HasDomain target domain)
    (gameDomain : PDG.HasDomain game domain) :
    PDG.underlying (enhance_with_MBO target game) = target := by
  unfold PDG.underlying enhance_with_MBO
  rw [Distribution.fTransform_fTransform]
  have mapEqual :
      Distribution.fTransform
          (System.DDG.system ∘
            fun pair => System.enhance_with_MBO pair.1 pair.2)
          (Distribution.prod target game) =
        Distribution.fTransform Prod.fst
          (Distribution.prod target game) := by
    apply Distribution.fTransform_congr
    intro pair supported
    obtain ⟨targetSupported, gameSupported⟩ :=
      Finset.mem_product.mp
        (Distribution.support_prod_subset target game supported)
    have targetDomainEqual := targetDomain pair.1 targetSupported
    have gameDomainEqual := gameDomain pair.2 gameSupported
    apply Subtype.ext
    funext history
    apply Part.ext'
    · constructor
      · exact fun admitted => admitted.1
      · intro admitted
        change history ∈ System.dom pair.1 at admitted
        refine ⟨admitted, ?_⟩
        rw [gameDomainEqual, ← targetDomainEqual]
        exact admitted
    · intro _ _
      rfl
  rw [mapEqual, Distribution.fTransform_fst_prod, gameWeight, one_smul]

end PDG

namespace ConditionalEquivalence

/-- CR18, Definition 4.17, writes `Γ(G)` for the maximal winning
probability of a game (printed p. 105). -/
scoped notation:max "Γ(" game ")" => _root_.RandomSystems.PDG.supWinProb game

/-- The mass `p^G_{A_i=0 | X^i}`. -/
def massAfalse (game : PDG X Y) (queries : List X) : ℝ :=
  game.mass fun deterministic =>
    queries ∈ System.dom deterministic.system ∧
      deterministic.condition.1 queries = false

/-- The mass `p^G_{Y^i,A_i=0 | X^i}`. -/
def massYAfalse (game : PDG X Y)
    (transcript : System.Transcript X Y) : ℝ :=
  game.mass fun deterministic =>
    System.SystemConsistent deterministic.system transcript ∧
      deterministic.condition.1 (transcript.map Prod.fst) = false

/-- The mass `p^T_{X^i}`. -/
def massDom (target : PDS X Y) (queries : List X) : ℝ :=
  target.mass fun deterministic => queries ∈ System.dom deterministic

/-- CR18, Definition 4.19: the visible behavior of `game`, conditioned on
not winning, is the behavior of `target`. The certificate includes CR18's
standing convention that the MBO “is initially set to 0” (printed p. 71). -/
structure ConditionallyEquivalent (game : PDG X Y) (target : PDS X Y) : Prop where
  initiallyFalse : game.InitiallyFalse
  mass_eq :
    ∀ transcript : System.Transcript X Y, transcript ≠ [] →
      massAfalse game (transcript.map Prod.fst) ≠ 0 →
      massDom target (transcript.map Prod.fst) ≠ 0 →
        massYAfalse game transcript *
            massDom target (transcript.map Prod.fst) =
          PDS.transcriptSystemFactor target transcript *
            massAfalse game (transcript.map Prod.fst)

@[inherit_doc ConditionallyEquivalent]
scoped notation:50 game " |≡ " target => ConditionallyEquivalent game target

end ConditionalEquivalence

namespace PDG

/-- The event that a transcript is consistent and the game has not yet been
won. -/
def preWinningHistory (game : System.DDG X Y)
    (transcript : System.Transcript X Y) : Prop :=
  System.SystemConsistent game.system transcript ∧
    game.condition.1 (transcript.map Prod.fst) = false

/-- The event that the next answer is produced and the game remains not won. -/
def preWinningAnswer (game : System.DDG X Y)
    (prior : System.Transcript X Y) (query : X) (answer : Y) : Prop :=
  ∃ admitted : prior.map Prod.fst ++ [query] ∈ System.dom game.system,
    System.output game.system (prior.map Prod.fst ++ [query]) admitted = answer ∧
      game.condition.1 (prior.map Prod.fst ++ [query]) = false

/-- CR18, Definition 4.15: the conditional law of the next answer together
with the event that the game has still not been won. -/
def preWinningBehavior (game : PDG X Y)
    (prior : System.Transcript X Y) (query : X) (answer : Y) : Part ℝ :=
  game.cond
    (fun deterministic => preWinningAnswer deterministic prior query answer)
    (fun deterministic => preWinningHistory deterministic prior)

/-- CR18, Definition 4.16: two games are equivalent when their pre-winning
behaviors agree. -/
def EquivalentAsGames (left right : PDG X Y) : Prop :=
  preWinningBehavior left = preWinningBehavior right

@[inherit_doc EquivalentAsGames]
local infix:50 " ≡ᵍ " => EquivalentAsGames

/-- Appending one query-answer pair turns the two one-round pre-winning
events into the cumulative pre-winning transcript event. -/
lemma preWinningAnswer_and_preWinningHistory_iff
    (game : System.DDG X Y) (prior : System.Transcript X Y)
    (query : X) (answer : Y) :
    preWinningAnswer game prior query answer ∧
        preWinningHistory game prior ↔
      preWinningHistory game (prior ++ [(query, answer)]) := by
  rw [preWinningAnswer, preWinningHistory, preWinningHistory,
    System.systemConsistent_snoc_iff]
  simp only [List.map_append, List.map_singleton]
  constructor
  · rintro ⟨⟨admitted, outputEqual, currentFalse⟩,
      priorConsistent, _⟩
    exact ⟨⟨priorConsistent, admitted, outputEqual⟩, currentFalse⟩
  · rintro ⟨⟨priorConsistent, admitted, outputEqual⟩, currentFalse⟩
    refine ⟨⟨admitted, outputEqual, currentFalse⟩,
      priorConsistent, ?_⟩
    apply Bool.eq_false_iff.mpr
    intro priorTrue
    have currentTrue := game.condition.2
      (List.prefix_append (prior.map Prod.fst) [query]) priorTrue
    rw [currentFalse] at currentTrue
    exact Bool.noConfusion currentTrue

/-- Under the `A₀ = 0` convention, the empty not-won transcript has the
full mass of the game law. -/
lemma massYAfalse_nil_eq_weight_of_initiallyFalse
    (game : PDG X Y) (initiallyFalse : game.InitiallyFalse) :
    ConditionalEquivalence.massYAfalse game [] = game.weight := by
  unfold ConditionalEquivalence.massYAfalse
  calc
    game.mass (fun deterministic =>
        System.SystemConsistent deterministic.system [] ∧
          deterministic.condition.1 ([].map Prod.fst) = false) =
        game.mass (fun _ => True) := by
      apply Distribution.mass_congr_of_support
      intro deterministic supported
      constructor
      · intro _
        trivial
      · intro _
        exact ⟨(by intro k hk; simp at hk),
          initiallyFalse deterministic supported⟩
    _ = game.weight := Distribution.mass_true game

/-- The pre-winning conditional is defined exactly when its not-won prefix
has nonzero mass. -/
lemma preWinningBehavior_dom_iff (game : PDG X Y)
    (prior : System.Transcript X Y) (query : X) (answer : Y) :
    (preWinningBehavior game prior query answer).Dom ↔
      ConditionalEquivalence.massYAfalse game prior ≠ 0 := by
  rw [preWinningBehavior, Distribution.cond_dom_iff]
  rfl

/-- The pre-winning conditional is the ratio of the extended and prior
not-won transcript masses. -/
lemma preWinningBehavior_get_eq (game : PDG X Y)
    (prior : System.Transcript X Y) (query : X) (answer : Y)
    (defined : (preWinningBehavior game prior query answer).Dom) :
    (preWinningBehavior game prior query answer).get defined =
      ConditionalEquivalence.massYAfalse game
          (prior ++ [(query, answer)]) /
        ConditionalEquivalence.massYAfalse game prior := by
  unfold preWinningBehavior at defined ⊢
  rw [← Distribution.condProb_eq_cond_get game _ _ defined]
  unfold Distribution.condProb ConditionalEquivalence.massYAfalse
  congr 1
  apply Distribution.mass_congr
  intro deterministic
  simpa only [preWinningHistory] using
    (preWinningAnswer_and_preWinningHistory_iff
      deterministic prior query answer)

/-- Equality of nonempty not-won transcript masses determines equality of
pre-winning behavior for normalized, initially-false games. -/
lemma equivalentAsGames_of_massYAfalse_eq
    {left right : PDG X Y}
    (leftInitiallyFalse : left.InitiallyFalse)
    (rightInitiallyFalse : right.InitiallyFalse)
    (leftProbability : left.isProbDist)
    (rightProbability : right.isProbDist)
    (equal : ∀ transcript : System.Transcript X Y, transcript ≠ [] →
      ConditionalEquivalence.massYAfalse left transcript =
        ConditionalEquivalence.massYAfalse right transcript) :
    left ≡ᵍ right := by
  funext prior query answer
  have prefixEqual :
      ConditionalEquivalence.massYAfalse left prior =
        ConditionalEquivalence.massYAfalse right prior := by
    by_cases nonempty : prior ≠ []
    · exact equal prior nonempty
    · have empty : prior = [] := by simpa using nonempty
      subst prior
      rw [massYAfalse_nil_eq_weight_of_initiallyFalse left leftInitiallyFalse,
        massYAfalse_nil_eq_weight_of_initiallyFalse right rightInitiallyFalse,
        leftProbability.weight_eq, rightProbability.weight_eq]
  apply Part.ext'
  · rw [preWinningBehavior_dom_iff, preWinningBehavior_dom_iff,
      prefixEqual]
  · intro leftDefined rightDefined
    rw [preWinningBehavior_get_eq left prior query answer leftDefined,
      preWinningBehavior_get_eq right prior query answer rightDefined,
      equal (prior ++ [(query, answer)]) (by simp), prefixEqual]

/-- The cumulative not-won mass satisfies the one-round multiplication rule. -/
lemma massYAfalse_snoc (game : PDG X Y) (nonnegative : game.NonNeg)
    (prior : System.Transcript X Y) (query : X) (answer : Y) :
    ConditionalEquivalence.massYAfalse game (prior ++ [(query, answer)]) =
      game.condProb
          (fun deterministic =>
            preWinningAnswer deterministic prior query answer)
          (fun deterministic => preWinningHistory deterministic prior) *
        ConditionalEquivalence.massYAfalse game prior := by
  change game.mass (fun deterministic =>
      preWinningHistory deterministic (prior ++ [(query, answer)])) =
    game.condProb
        (fun deterministic => preWinningAnswer deterministic prior query answer)
        (fun deterministic => preWinningHistory deterministic prior) *
      game.mass (fun deterministic => preWinningHistory deterministic prior)
  rw [Distribution.condProb_mul_mass nonnegative]
  exact Distribution.mass_congr game fun deterministic =>
    (preWinningAnswer_and_preWinningHistory_iff
      deterministic prior query answer).symm

/-- CR18, equation (4.36): equivalent normalized, initially-false games have
the same cumulative not-won transcript masses. -/
lemma massYAfalse_eq_of_equivalentAsGames
    {left right : PDG X Y}
    (leftInitiallyFalse : left.InitiallyFalse)
    (rightInitiallyFalse : right.InitiallyFalse)
    (leftProbability : left.isProbDist)
    (rightProbability : right.isProbDist)
    (equivalent : left ≡ᵍ right) :
    ∀ transcript : System.Transcript X Y,
      ConditionalEquivalence.massYAfalse left transcript =
        ConditionalEquivalence.massYAfalse right transcript := by
  intro transcript
  induction transcript using List.reverseRecOn with
  | nil =>
      rw [massYAfalse_nil_eq_weight_of_initiallyFalse left leftInitiallyFalse,
        massYAfalse_nil_eq_weight_of_initiallyFalse right rightInitiallyFalse,
        leftProbability.weight_eq, rightProbability.weight_eq]
  | append_singleton prior entry inductionHypothesis =>
      rw [massYAfalse_snoc left leftProbability.nonNeg prior entry.1 entry.2,
        massYAfalse_snoc right rightProbability.nonNeg prior entry.1 entry.2]
      by_cases priorZero :
          ConditionalEquivalence.massYAfalse left prior = 0
      · have rightZero :
            ConditionalEquivalence.massYAfalse right prior = 0 := by
          rw [← inductionHypothesis]
          exact priorZero
        rw [priorZero, rightZero, mul_zero, mul_zero]
      · have leftDefined :
            (preWinningBehavior left prior entry.1 entry.2).Dom :=
          (preWinningBehavior_dom_iff left prior entry.1 entry.2).2 priorZero
        have behaviorPoint :
            preWinningBehavior left prior entry.1 entry.2 =
              preWinningBehavior right prior entry.1 entry.2 :=
          congrFun (congrFun (congrFun equivalent prior) entry.1) entry.2
        have rightDefined :
            (preWinningBehavior right prior entry.1 entry.2).Dom := by
          rw [← behaviorPoint]
          exact leftDefined
        have conditionalEqual :
            left.condProb
                (fun deterministic =>
                  preWinningAnswer deterministic prior entry.1 entry.2)
                (fun deterministic => preWinningHistory deterministic prior) =
              right.condProb
                (fun deterministic =>
                  preWinningAnswer deterministic prior entry.1 entry.2)
                (fun deterministic => preWinningHistory deterministic prior) := by
          rw [Distribution.condProb_eq_cond_get left _ _ leftDefined,
            Distribution.condProb_eq_cond_get right _ _ rightDefined]
          exact Part.mem_unique
            (behaviorPoint ▸ Part.get_mem leftDefined)
            (Part.get_mem rightDefined)
        rw [conditionalEqual, inductionHypothesis]

end PDG

namespace ConditionalEquivalence

@[inherit_doc PDG.EquivalentAsGames]
scoped infix:50 " ≡ᵍ " => PDG.EquivalentAsGames

/-- The not-won transcript mass of the enhanced target factors into the
target transcript mass and the source game's not-won mass. -/
lemma massYAfalse_enhance_with_MBO (target : PDS X Y) (game : PDG X Y)
    (transcript : System.Transcript X Y) (nonempty : transcript ≠ []) :
    massYAfalse (PDG.enhance_with_MBO target game) transcript =
      PDS.transcriptSystemFactor target transcript *
        massAfalse game (transcript.map Prod.fst) := by
  have queryHistoryPrefix (k : Nat) (hk : k < transcript.length) :
      List.IsPrefix
        ((transcript.take k).map Prod.fst ++ [transcript[k].1])
        (transcript.map Prod.fst) := by
    have takeEqual : transcript.take k ++ [transcript[k]] =
        transcript.take (k + 1) := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk]
      simp only [Option.toList_some]
    have historyPrefix : List.IsPrefix (transcript.take k ++ [transcript[k]])
        transcript := takeEqual ▸ List.take_prefix (k + 1) transcript
    simpa only [List.map_append, List.map_singleton] using
      historyPrefix.map (fun entry : X × Y => entry.1)
  unfold massYAfalse
  rw [PDG.enhance_with_MBO, Distribution.mass_fTransform]
  rw [Distribution.mass_congr (Distribution.prod target game)
    (Q := fun pair =>
      System.SystemConsistent pair.1 transcript ∧
        ((transcript.map Prod.fst ∈ System.dom pair.2.system) ∧
          pair.2.condition.1 (transcript.map Prod.fst) = false)) ?_]
  · simpa only [PDS.transcriptSystemFactor, massAfalse] using
      Distribution.mass_prod_and target game
        (fun deterministic =>
          System.SystemConsistent deterministic transcript)
        (fun deterministic =>
          transcript.map Prod.fst ∈ System.dom deterministic.system ∧
            deterministic.condition.1 (transcript.map Prod.fst) = false)
  · intro pair
    constructor
    · rintro ⟨consistent, conditionFalse⟩
      refine ⟨?_, ?_, conditionFalse⟩
      · intro k hk
        obtain ⟨admitted, answer⟩ := consistent k hk
        exact ⟨admitted.1, answer⟩
      · rcases System.systemConsistent_queries_admitted
            (System.enhance_with_MBO pair.1 pair.2).system transcript consistent with
          empty | admitted
        · exact (nonempty (List.map_eq_nil_iff.mp empty)).elim
        · exact admitted.2
    · rintro ⟨consistent, gameAdmitted, conditionFalse⟩
      refine ⟨?_, conditionFalse⟩
      intro k hk
      obtain ⟨targetAdmitted, answer⟩ := consistent k hk
      refine ⟨⟨targetAdmitted,
        System.prefix_closed pair.2.system
          (queryHistoryPrefix k hk) (by simp) gameAdmitted⟩, answer⟩

/-- CR18, equation (4.39): conditional equivalence makes the enhanced target
and the source game agree on one nonempty not-won transcript. The displayed
normalizer hypothesis is the exact target-domain fact used at this
transcript. -/
lemma massYAfalse_enhance_with_MBO_eq_of_conditionallyEquivalent
    (target : PDS X Y) (game : PDG X Y)
    (nonnegative : game.NonNeg) (equivalent : game |≡ target)
    (transcript : System.Transcript X Y) (nonempty : transcript ≠ [])
    (targetDefined : massDom target (transcript.map Prod.fst) = 1) :
    massYAfalse (PDG.enhance_with_MBO target game) transcript =
      massYAfalse game transcript := by
  have massYAfalseLeMassAfalse :
      massYAfalse game transcript ≤
        massAfalse game (transcript.map Prod.fst) := by
    apply Distribution.mass_mono nonnegative
    intro deterministic notWon
    refine ⟨?_, notWon.2⟩
    rcases System.systemConsistent_queries_admitted deterministic.system transcript
        notWon.1 with empty | admitted
    · exact (nonempty (List.map_eq_nil_iff.mp empty)).elim
    · exact admitted
  rw [massYAfalse_enhance_with_MBO target game transcript nonempty]
  by_cases gameNotWon : massAfalse game (transcript.map Prod.fst) = 0
  · rw [gameNotWon, mul_zero]
    apply le_antisymm (nonnegative.mass_nonneg _)
    exact massYAfalseLeMassAfalse.trans_eq gameNotWon
  · have conditional := equivalent.mass_eq transcript nonempty gameNotWon
      (by rw [targetDefined]; exact one_ne_zero)
    rw [targetDefined, mul_one] at conditional
    exact conditional.symm

/-- CR18, equation (4.39), for two probability laws with one common domain. -/
lemma massYAfalse_enhance_with_MBO_eq_of_conditionallyEquivalent_of_hasDomain
    (target : PDS X Y) (game : PDG X Y) (domain : Set (List X))
    (targetProbability : target.isProbDist)
    (gameProbability : game.isProbDist)
    (targetDomain : PDS.HasDomain target domain)
    (gameDomain : PDG.HasDomain game domain)
    (equivalent : game |≡ target)
    (transcript : System.Transcript X Y) (nonempty : transcript ≠ []) :
    massYAfalse (PDG.enhance_with_MBO target game) transcript =
      massYAfalse game transcript := by
  by_cases admitted : transcript.map Prod.fst ∈ domain
  · apply massYAfalse_enhance_with_MBO_eq_of_conditionallyEquivalent target game
      gameProbability.nonNeg equivalent transcript nonempty
    unfold massDom
    calc
      target.mass (fun deterministic =>
          transcript.map Prod.fst ∈ System.dom deterministic) =
          target.mass (fun _ => True) := by
        apply Distribution.mass_congr_of_support
        intro deterministic supported
        simp only [iff_true]
        rw [targetDomain deterministic supported]
        exact admitted
      _ = target.weight := Distribution.mass_true target
      _ = 1 := targetProbability.weight_eq
  · have gameHistoryZero :
        massAfalse game (transcript.map Prod.fst) = 0 := by
      unfold massAfalse
      calc
        game.mass (fun deterministic =>
            transcript.map Prod.fst ∈ System.dom deterministic.system ∧
              deterministic.condition.1 (transcript.map Prod.fst) = false) =
            game.mass (fun _ => False) := by
          apply Distribution.mass_congr_of_support
          intro deterministic supported
          apply iff_false_intro
          intro member
          apply admitted
          rw [← gameDomain deterministic supported]
          exact member.1
        _ = 0 := Distribution.mass_eq_zero_of_forall_not _ fun _ => id
    have gameTranscriptZero : massYAfalse game transcript = 0 := by
      apply le_antisymm
      · apply (Distribution.mass_mono gameProbability.nonNeg _).trans_eq
          gameHistoryZero
        intro deterministic notWon
        refine ⟨?_, notWon.2⟩
        rcases System.systemConsistent_queries_admitted deterministic.system transcript
            notWon.1 with empty | historyAdmitted
        · exact (nonempty (List.map_eq_nil_iff.mp empty)).elim
        · exact historyAdmitted
      · exact gameProbability.nonNeg.mass_nonneg _
    rw [massYAfalse_enhance_with_MBO target game transcript nonempty,
      gameHistoryZero, mul_zero, gameTranscriptZero]

/-- CR18, equation (4.39): conditional equivalence makes the source game
equivalent as a game to the independently MBO-enhanced target. -/
lemma equivalentAsGames_enhance_with_MBO_of_conditionallyEquivalent
    (game : PDG X Y) (target : PDS X Y) (domain : Set (List X))
    (gameProbability : game.isProbDist)
    (targetProbability : target.isProbDist)
    (gameDomain : PDG.HasDomain game domain)
    (targetDomain : PDS.HasDomain target domain)
    (equivalent : game |≡ target) :
    game ≡ᵍ PDG.enhance_with_MBO target game := by
  apply PDG.equivalentAsGames_of_massYAfalse_eq
    equivalent.initiallyFalse
    (PDG.initiallyFalse_enhance_with_MBO target game
      equivalent.initiallyFalse)
    gameProbability
    (Distribution.fTransform_isProbDist _
      (Distribution.prod_isProbDist target game
        targetProbability gameProbability))
  intro transcript nonempty
  exact
    (massYAfalse_enhance_with_MBO_eq_of_conditionallyEquivalent_of_hasDomain
      target game domain targetProbability gameProbability targetDomain
      gameDomain equivalent transcript nonempty).symm

end ConditionalEquivalence

end RandomSystems
