import Informalization.Semantics.CanonicalRandomSystems

/-!
Focused structural tests for the canonical claim layer.  These declarations
mirror the relevant signatures under their fully qualified names; the test is
standalone and does not make the informalization package depend on a Random
Systems implementation.
-/

namespace Probability.Distribution

def fTransform (f : Nat → Nat) (distribution : Nat) : Nat := f distribution
def NonNeg (_distribution : Nat) : Prop := True
def weight (distribution : Nat) : Nat := distribution

end Probability.Distribution

namespace Probability.Counting

theorem birthday_bound (N q : Nat) (_h_le : q ≤ N) (_h_pos : 0 < N) :
    q ≤ N := _h_le

end Probability.Counting

namespace ENNReal

def ofReal (value : Nat) : Nat := value

end ENNReal

namespace EDist

def edist (left right : Nat) : Nat := left + right

end EDist

namespace RandomSystems

def filterQueries (q : Nat) (system : Nat) : Nat := q + system

namespace System

def filterQueries (q : Nat) (system : Nat) : Nat := q + system

end System

namespace PDS

def urf (_inputSpace _outputSpace : Type) : Nat := 1
def urp (_alphabet : Type) : Nat := 2

def adjoin (system : Nat) (_condition : Nat → Bool) : {_game : Nat // True} :=
  ⟨system, True.intro⟩

def advFullyDefined (source _target : Nat) : Nat := source

end PDS

namespace PDG

def forget (game : Nat) : Nat := game
def CondEquiv (_game _target : Nat) : Prop := True
def supWinProb (game : Nat) : Nat := game
def blindSupWinProb (game : Nat) : Nat := game

theorem condEquiv_filterQueries (q : Nat) {G T : Nat}
    (_sourceTotal : True) (_targetTotal : True) (_hCE : CondEquiv G T) :
    CondEquiv
      (Probability.Distribution.fTransform (System.filterQueries q) G)
      (Probability.Distribution.fTransform (System.filterQueries q) T) := by
  trivial

theorem advFullyDefined_forget_le_blindSupWinProb_of_condEquiv {G T : Nat}
    (_sourceNonnegative : Probability.Distribution.NonNeg G)
    (_targetNonnegative : Probability.Distribution.NonNeg T)
    (_equalWeight : Probability.Distribution.weight G =
      Probability.Distribution.weight T)
    (_hCE : CondEquiv G T) :
    PDS.advFullyDefined (forget G) T ≤
      ENNReal.ofReal (blindSupWinProb G) := by
  exact Nat.le_refl G

end PDG

namespace Switching

def limit (q : Nat) (system : Nat) : Nat := q + system
def limitGame (q : Nat) (game : Nat) : Nat := q + game

theorem uniform_function_collision_on_finset_le
    (X : Type) [Nonempty X] (S : Nat) : 0 ≤ S := Nat.zero_le S

theorem blindSupWinProb_limit_urf_collision_le
    (X : Type) [Nonempty X] (q : Nat) : 0 ≤ q := Nat.zero_le q

theorem limit_urf_collision_condEquiv_limit_urp
    (X : Type) [Nonempty X] (q : Nat) : PDG.CondEquiv q q := by
  trivial

theorem urf_collision_condEquiv_urp
    (X : Type) [Nonempty X] : PDG.CondEquiv 0 0 := by
  trivial

end Switching

def collisionCondition (_system : Nat) : Bool := false

end RandomSystems

namespace FormulaFixture

def attach (blockForm limit system : Nat) : Nat := blockForm + limit + system

theorem attachment (blockForm limit system : Nat) :
    attach blockForm limit system = blockForm + limit + system := rfl

theorem misleading (blockForm limit system : Nat) : True := by
  have _ := blockForm + limit + system
  trivial

end FormulaFixture

namespace Tests.Canonical

open Lean Meta Elab Command
open Informalization.Semantics.Canonical
open Informalization.Semantics.Canonical.RandomSystemsProfile

theorem restrictedAugmentedCE (q : Nat) :
    RandomSystems.PDG.CondEquiv
      (RandomSystems.Switching.limitGame q
        (RandomSystems.PDS.adjoin
          (RandomSystems.PDS.urf Nat Nat)
          RandomSystems.collisionCondition).1)
      (RandomSystems.Switching.limit q (RandomSystems.PDS.urp Nat)) := by
  trivial

private def requireClaim (expression : Expr) : MetaM Claim := do
  let some claim ← decodeClaim? expression
    | throwError "canonical claim was not decoded"
  return claim

private def requireDerivation (expression : Expr) : MetaM DerivationApplication := do
  let some derivation ← decodeDerivation? expression
    | throwError "canonical derivation was not decoded"
  return derivation

private def requireDerivationWith (decoderProfile : DecoderProfile)
    (expression : Expr) : MetaM DerivationApplication := do
  let some derivation ←
      Informalization.Semantics.Canonical.decodeDerivation? decoderProfile expression
    | throwError "canonical derivation was not decoded"
  return derivation

run_cmd liftTermElabM do
  let q := mkNatLit 7
  let theoremProof ← mkAppM ``restrictedAugmentedCE #[q]
  let claim ← requireClaim (← inferType theoremProof)
  match claim with
  | .conditionalEquivalence _ game target =>
      let some restricted := game.restrictedEnhancement?
        | throwError "restricted MBO enhancement was not exposed structurally"
      unless restricted.budget == q do
        throwError "the game query budget was not retained"
      match restricted.baseSystem with
      | .uniformRandomFunction _ inputSpace outputSpace =>
          unless inputSpace.isConstOf ``Nat && outputSpace.isConstOf ``Nat do
            throwError "the URF input/output spaces were not retained"
      | _ => throwError "the enhanced game's base system was not decoded as a URF"
      match restricted.condition with
      | .named _ declaration _ =>
          unless declaration == ``RandomSystems.collisionCondition do
            throwError "the MBO condition declaration was not retained"
      | _ => throwError "the MBO condition was not decoded"
      match target with
      | .queryRestriction _ targetBudget
          (.uniformRandomPermutation _ alphabet) =>
          unless targetBudget == q && alphabet.isConstOf ``Nat do
            throwError "the restricted URP operands were not retained"
      | _ => throwError "the CE target was not decoded as a restricted URP"
  | _ => throwError "the theorem conclusion was not decoded as conditional equivalence"

  let game := mkNatLit 3
  let target := mkNatLit 4
  let trueProof := mkConst ``True.intro
  let ceProof := mkAppN (mkConst ``RandomSystems.PDG.condEquiv_filterQueries)
    #[q, game, target, trueProof, trueProof, trueProof]
  let ceDerivation ← requireDerivation ceProof
  unless ceDerivation.rule == .preserveConditionalEquivalence do
    throwError "filtering was not decoded as preservation of conditional equivalence"
  unless ceDerivation.obligations.map (·.slot) ==
      #[.sourceTotal, .targetTotal, .conditionalEquivalence] do
    throwError "filtering obligations were not kept in their canonical slots"
  match ceDerivation.conclusion.claim? with
  | some (.conditionalEquivalence _ (.queryRestriction _ gameBudget _)
      (.queryRestriction _ targetBudget _)) =>
      unless gameBudget == q && targetBudget == q do
        throwError "the two transformed CE operands lost their shared query budget"
  | _ => throwError "fTransform/filterQueries did not normalize to query restrictions"

  let sourceNonnegative := mkConst ``True.intro
  let targetNonnegative := mkConst ``True.intro
  -- Choose equal operands so that the equality witness elaborates directly.
  let equalGame := mkNatLit 3
  let equalWeight ← mkAppM ``Eq.refl #[equalGame]
  let reductionProof := mkAppN (mkConst
    ``RandomSystems.PDG.advFullyDefined_forget_le_blindSupWinProb_of_condEquiv)
    #[equalGame, equalGame, sourceNonnegative, targetNonnegative, equalWeight, trueProof]
  let reduction ← requireDerivation reductionProof
  unless reduction.rule == .conditionalEquivalenceToBlindWinning do
    throwError "the CE-to-blind transition was not classified canonically"
  unless reduction.obligations.map (·.slot) == #[
      .sourceNonnegative,
      .targetNonnegative,
      .equalWeight,
      .conditionalEquivalence
    ] do
    throwError "CE-to-blind proof obligations were collapsed or reordered"
  match reduction.conclusion.claim? with
  | some (.advantageBound _ .fullyDefined (.forgetGame _ _) _ upper) =>
      unless upper.blindWinningGame?.isSome do
        throwError "the coerced blind-winning upper bound was not recovered"
  | _ => throwError "the reduction conclusion lost its fully-defined advantage operands"

  let natType := mkConst ``Nat
  let nonemptyNatType ← mkAppM ``Nonempty #[natType]
  let nonemptyNat ← synthInstance nonemptyNatType
  let queriedSet := mkNatLit 5
  let collisionProof := mkAppN
    (mkConst ``RandomSystems.Switching.uniform_function_collision_on_finset_le)
    #[natType, nonemptyNat, queriedSet]
  let collision ← requireDerivation collisionProof
  unless collision.rule == .custom `collisionProbabilityBound do
    throwError "the collision estimate was not assigned its canonical rule"
  unless collision.operands.map (·.slot) == #[`alphabet, `queriedSet] do
    throwError "the collision rule did not retain alphabet/set operand slots"
  unless collision.operands[0]!.value == natType &&
      collision.operands[1]!.value == queriedSet do
    throwError "the collision rule retained the wrong checked operands"
  unless collision.operands.all (·.type?.isSome) do
    throwError "canonical collision operands lost their checked types"
  unless collision.obligations.isEmpty do
    throwError "a typeclass assumption was exposed as a proof obligation"

  let one := mkNatLit 1
  let hle ← mkAppM ``Nat.le_refl #[one]
  let hpos ← mkAppM ``Nat.zero_lt_succ #[mkNatLit 0]
  let birthdayProof := mkAppN (mkConst ``Probability.Counting.birthday_bound)
    #[one, one, hle, hpos]
  let birthday ← requireDerivation birthdayProof
  unless birthday.rule == .custom `birthdayBound do
    throwError "the birthday estimate was not assigned its canonical rule"
  unless birthday.operands.map (·.slot) ==
      #[`sampleSpaceCardinality, `sampleSize] do
    throwError "the birthday rule did not retain cardinality/sample-size slots"
  unless birthday.operands.all (·.value == one) do
    throwError "the birthday operands did not retain N and q"
  unless birthday.obligations.map (·.slot) == #[.queryBudget, .sideCondition] do
    throwError "the birthday side conditions lost their canonical slots"
  unless birthday.obligations.map (·.key) == #[
      { telescopePosition := 2, proofOrdinal := 0 },
      { telescopePosition := 3, proofOrdinal := 1 }
    ] do
    throwError "birthday obligations lost their stable telescope identities"

  -- Positional maps are accepted only when their expected telescope binders
  -- still agree with the checked declaration signature.
  let positionalRule : RuleDeclarationProfile := {
    declaration := `RandomSystems.Switching.uniform_function_collision_on_finset_le
    rule := .custom `collisionProbabilityBound
    operands := #[
      { selector := .position 0 `X, slot := `alphabet },
      { selector := .position 2 `S, slot := `queriedSet }
    ]
  }
  let positionalProfile : DecoderProfile := {
    profile with rules := #[positionalRule]
  }
  let positional ← requireDerivationWith positionalProfile collisionProof
  unless positional.operands.map (·.slot) == #[`alphabet, `queriedSet] do
    throwError "validated positional operand selection failed"
  let invalidRule : RuleDeclarationProfile := {
    positionalRule with operands := #[
      { selector := .position 0 `notX, slot := `alphabet }
    ]
  }
  let invalidProfile : DecoderProfile := {
    profile with rules := #[invalidRule]
  }
  let rejected ← try
    let _ ← requireDerivationWith invalidProfile collisionProof
    pure false
  catch _ => pure true
  unless rejected do
    throwError "a positional operand map accepted the wrong expected binder"

  let attachmentRule : RuleDeclarationProfile := {
    declaration := `FormulaFixture.attachment
    rule := .custom `restrictionAttachment
    operands := #[
      { selector := .binder `blockForm, slot := `blockForm },
      { selector := .binder `limit, slot := `blockLimit },
      { selector := .binder `system, slot := `system }
    ]
    formula? := some .restrictionAttachment
  }
  let attachmentProfile : DecoderProfile := { rules := #[attachmentRule] }
  let attachmentProof ← mkAppM ``FormulaFixture.attachment
    #[mkNatLit 2, mkNatLit 3, mkNatLit 5]
  let attachment ← requireDerivationWith attachmentProfile attachmentProof
  match attachment.formula? with
  | some (.restrictionAttachment source blockForm limit system) =>
      unless source == attachment.conclusion.source && blockForm == mkNatLit 2 &&
          limit == mkNatLit 3 && system == mkNatLit 5 do
        throwError "the restriction formula lost its checked proposition or operands"
  | _ => throwError "a registered equality did not produce its formula AST"

  let misleadingRule : RuleDeclarationProfile := {
    attachmentRule with declaration := `FormulaFixture.misleading
  }
  let misleadingProfile : DecoderProfile := { rules := #[misleadingRule] }
  let misleadingProof ← mkAppM ``FormulaFixture.misleading
    #[mkNatLit 2, mkNatLit 3, mkNatLit 5]
  if (← Informalization.Semantics.Canonical.decodeDerivation?
      misleadingProfile misleadingProof).isSome then
    throwError "a registered formula schema accepted the wrong proposition genre"

  -- Unknown scalar leaves keep local aliases, even though head recognition
  -- zeta-expands them internally.
  withLetDecl `N natType (mkNatLit 17) fun localN => do
    let bound ← Informalization.Semantics.Canonical.decodeBound profile localN
    match bound with
    | .expression source =>
        unless source == localN do
          throwError "unknown scalar decoding expanded away its checked local alias"
    | _ => throwError "an unknown scalar alias was assigned guessed structure"

  -- The polymorphic `edist` symbol is not by itself Random Systems evidence.
  -- Its operands must inhabit a carrier named by the selected profile.
  withLocalDeclD `x (mkConst ``Nat) fun x =>
    withLocalDeclD `y (mkConst ``Nat) fun y => do
      let distance ← mkAppM ``EDist.edist #[x, y]
      let inequality ← mkAppM ``LE.le #[distance, distance]
      match ← Informalization.Semantics.Canonical.decodeClaim? profile inequality with
      | some (.distanceBound ..) =>
          throwError "an arbitrary pseudo-emetric distance was classified as Random Systems security"
      | _ => pure ()
end Tests.Canonical
