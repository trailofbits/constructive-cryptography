import Verbose.Core

/-!
# Presentation-only guidance

These wrappers execute an ordinary tactic unchanged and attach typed reader
guidance to the checked transition.  The strings are never passed to Lean as
proof evidence.
-/

open Lean Elab Tactic
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Annotations
open CryptoLanguage.Verbose

elab (name := internalPresentationLabel)
    "crypto_verbose_presentation_label " label:str " => " step:tactic : tactic => do
  runPresentation (← getRef) #[⟨Annotations.label, label.getString⟩] <| evalTactic step

elab (name := internalPresentationParagraph)
    "crypto_verbose_presentation_paragraph " label:str ", " paragraph:ident
    " => " step:tactic : tactic => do
  let value := paragraph.getId.toString
  unless value == "true" || value == "false" do
    throwErrorAt paragraph "paragraphBefore must be `true` or `false`"
  runPresentation (← getRef)
      #[⟨Annotations.label, label.getString⟩,
        ⟨Annotations.paragraphBefore, value⟩] <|
    evalTactic step

namespace CryptoVerbose

scoped macro &"With" &"presentation" "(" &"label" ":=" label:str ")"
    &"in" ppLine step:tactic : tactic =>
  `(tactic| crypto_verbose_presentation_label $label => $step)

scoped macro &"With" &"presentation" "(" &"label" ":=" label:str ","
    &"paragraphBefore" ":=" paragraph:ident ")" &"in" ppLine
    step:tactic : tactic =>
  `(tactic| crypto_verbose_presentation_paragraph $label, $paragraph => $step)

end CryptoVerbose
