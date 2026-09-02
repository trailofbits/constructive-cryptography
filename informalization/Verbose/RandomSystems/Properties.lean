import Verbose.RandomSystems.Declarations

/-!
# Superseded Random Systems property prototype

This module is not imported by `Verbose`. The “by construction; call this
fact” form is retained only as negative migration evidence and is rejected by
public rendering/help. Canonical source omits routine constructor properties;
when such a property is needed internally, `rs_routine` records a checked
receipt. `Fact NAME:` is reserved for wrapping a registered mathematical
assertion, never for a raw proposition or this legacy form.
-/

open Lean Elab Tactic
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Rules
open CryptoLanguage.LanguageDesign.Ontology

namespace CryptoLanguage.Verbose.RandomSystems.Properties

def restrictedEnhancedURFGameNonnegative :=
  descriptor `rs.property `restrictedEnhancedURFGameNonnegative
    rsRestrictedEnhancedURFGameNonnegative .assertion
    (.addLocalFact (typedBinding (role `fact) Ontology.proposition))
    Relations.nonnegativity #[
      explicitOperand (role `game) Ontology.probabilisticGame]
    "record nonnegativity of a query-restricted game obtained by adjoining an MBO to a uniform random function"
    `CryptoLanguage.Verbose.RandomSystems.Properties.Backend.restrictedEnhancedURFGameNonnegative

namespace Backend

def restrictedEnhancedURFGameNonnegative
    (name : Ident) (game : Term) : TacticM Unit := do
  evalTactic (← `(tactic|
    have $name : Probability.Distribution.NonNeg $game :=
      (RandomSystems.PDS.nonNeg_adjoin
        (RandomSystems.PDS.isProbDist_urf _ _).nonNeg _).fTransform _))

end Backend
end CryptoLanguage.Verbose.RandomSystems.Properties

open CryptoLanguage.Verbose
open CryptoLanguage.Verbose.RandomSystems.Properties

elab "crypto_verbose_rs_restricted_enhanced_urf_game_nonnegative "
    game:verboseReference ", " name:ident : tactic => do
  let gameRef ← decodeReference game
  let statement ←
    `(term| Probability.Distribution.NonNeg $(gameRef.term))
  runSentenceWithBindings (← getRef) restrictedEnhancedURFGameNonnegative
      (.addLocals #[name.getId]) #[⟨role `game, gameRef⟩] #[
        ⟨role `fact, name.getId, some statement⟩] #[] <|
    backendAction Backend.restrictedEnhancedURFGameNonnegative
      (name, gameRef.term)

namespace CryptoVerbose

scoped macro &"The" &"game" game:verboseReference &"is" &"nonnegative"
    &"by" &"construction" ";" &"call" &"this" &"fact" name:ident : tactic =>
  `(tactic|
    crypto_verbose_rs_restricted_enhanced_urf_game_nonnegative $game, $name)

end CryptoVerbose
