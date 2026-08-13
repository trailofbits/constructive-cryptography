/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import AbstractCryptography.Tactics.ProofAutomation

/-!
# Controlled natural language for Abstract Cryptography

This module is the paper-facing syntax layer above
`AbstractCryptography.Tactics.ProofAutomation`.  Its design follows the three-layer
separation used by Patrick Massot's Verbose Lean:

1. existing proof-producing tactics implement one mathematical step;
2. the controlled language gives those steps rigid, readable sentences;
3. diagnostics and future suggestion providers remain a separate layer.

The sentences below add no theorem search and no cryptographic semantics.
Every sentence expands to one existing `ac_*` command, so the ideal resource,
simulator, intermediate specification, error budget, and proof route remain
explicit.

The syntax is scoped.  Importing `AbstractCryptography` makes the implementation
available, but users opt in with:

```lean
open scoped CryptoControlledNaturalLanguage
```

The neutral scope name is intentional.  A downstream `ConstructiveCryptography` or
`RandomSystemsCC` controlled-language module may add scoped sentences to the
same namespace and lower them through `crypto_cnl_sentence`.  This preserves
the import direction: concrete layers extend the language without adding
concrete vocabulary to AC.

## Corpus-derived language profile

The wording is taken from the recurring proof prose of the AC, CC, and random-
systems papers themselves.  Verbose Lean and ForTheL/Naproche motivate the
separation between mathematical sentences and proof-producing tactics, but
they do not supply this module's vocabulary.

The source corpus consistently uses direct mathematical assertions:

* `A ... is ...`, `For ..., define ...`, and `We say that ... if ...` for
  definitions;
* `Let ...`, `Fix ...`, `Consider ...`, and `Define ...` to introduce objects;
* `We have ...`, `We obtain ...`, `It follows that ...`, and `This implies ...`
  to state consequences;
* `We use the following simulator ... to prove ...` to introduce the simulator
  that witnesses a construction;
* `It suffices to show ...` and `It remains to prove/analyze ...` to expose the
  remaining obligation; and
* `By Lemma ...`, `Using ...`, or a reason attached to a calculation step to
  justify an inference.

The controlled sentences below follow that usage.  They name mathematical
objects such as a construction, equality, protocol, bound, or simulator.  They
do not rename a proof as a generic `certificate`, and they do not describe
equality replacement as `transport`.  Those words have different domain
meanings in cryptographic papers.

Serial composition is written in the order in which its two construction
proofs are listed.  The goal still displays the resulting converter product,
so Lean checks the paper's function-composition convention rather than hiding
it in prose.

A cited object may carry an optional quoted annotation, for example
`firstConstruction ("authentication leaves the encryption key unchanged")`.
The annotation is retained for the reader but is not elaborated and is not
passed to the proof tactic.  Ordinary Lean comments remain available between
any two proof steps.  Thus explanatory prose can be added freely without ever
being mistaken for mathematical evidence.

The end of the tactic line terminates a controlled sentence.  The syntax does
not require a final full stop: Lean reads a full stop immediately after a term
as field notation, while requiring a space before it would produce unnatural
technical prose.
-/

open Lean Elab Tactic

/-- A prose-word parser that can also admit Lean keywords such as `have`.
The enclosing sentence validates the word after parsing, which gives a useful
controlled-language diagnostic instead of a low-level parser failure. -/
declare_syntax_cat cryptoCnlWord
syntax ident : cryptoCnlWord
syntax "have" : cryptoCnlWord

/-- A named object in a controlled sentence, optionally followed by free
explanatory prose.  The string is retained in the source and ignored by the
elaborator; only the preceding Lean term is passed to the proof backend. -/
declare_syntax_cat cryptoCnlReference
syntax term:max ("(" str ")")? : cryptoCnlReference

namespace CryptoControlledNaturalLanguage

/-- Check a prose word without installing it as a parser keyword.  This keeps
common cryptographic identifiers such as `construction`, `certificate`, and
`simulator` available while the controlled-language scope is open. -/
def expectWord (word : Ident) (expected : String) : MacroM Unit := do
  unless word.getId.toString = expected do
    Macro.throwErrorAt word s!"expected `{expected}` in this controlled-language sentence"

/-- Validate a `cryptoCnlWord`, including words that Lean reserves as
keywords. -/
def expectCnlWord (word : TSyntax `cryptoCnlWord)
    (expected : String) : MacroM Unit := do
  let actual ← match word with
    | `(cryptoCnlWord| $identifier:ident) => pure identifier.getId.toString
    | `(cryptoCnlWord| have) => pure "have"
    | _ => Macro.throwErrorAt word "invalid controlled-language word"
  unless actual = expected do
    Macro.throwErrorAt word s!"expected `{expected}` in this controlled-language sentence"

/-- Remove the optional human annotation from a controlled-language object
reference. -/
def referenceTerm (reference : TSyntax `cryptoCnlReference) : MacroM Term :=
  match reference with
  | `(cryptoCnlReference| $value:term $[( $_annotation:str )]?) => pure value
  | _ => Macro.throwErrorAt reference "invalid controlled-language object reference"

/-- Trace a controlled-language sentence only after its backend tactic has
elaborated successfully.  Sentence identifiers are stable, layer-prefixed
names such as `ac.construction.by_composition`; downstream extensions should
use `cc.` or `rs.` prefixes. -/
initialize Lean.registerTraceClass `CryptoControlledNaturalLanguage.sentence

/-- Shared lowering boundary for AC, CC, and concrete controlled-language
sentences.  It provides observability but deliberately performs no rule
selection of its own. -/
syntax (name := cryptoCnlSentence)
  "crypto_cnl_sentence " str " => " tactic : tactic

elab_rules : tactic
  | `(tactic| crypto_cnl_sentence $label:str => $backend:tactic) => do
      evalTactic backend
      trace[CryptoControlledNaturalLanguage.sentence] "{label.getString}"

/-- Close a construction or protocol-action equality from one explicitly
named fact.  The noun selects the corresponding deterministic AC rule; no
library search is performed. -/
scoped macro (name := cnlFollowsFrom)
    "The" subject:ident followsWord:ident "from"
      fact:cryptoCnlReference : tactic => do
  expectWord followsWord "follows"
  let fact ← referenceTerm fact
  match subject.getId.toString with
  | "construction" =>
      `(tactic|
        crypto_cnl_sentence "ac.construction.follows_from" =>
          ac_construct using $fact)
  | "equality" =>
      `(tactic|
        crypto_cnl_sentence "ac.equality.follows_from" =>
          ac_transport using $fact)
  | _ =>
      Macro.throwErrorAt subject
        "expected `construction` or `equality` in this controlled-language sentence"

/-- Replace the protocol label in one supplied exact or approximate
construction using one supplied protocol equality.  This follows the wording
"Replacing ... using ..." and "we obtain ..." used in MauRen11's composition
proofs. -/
scoped macro (name := cnlReplaceProtocol)
    "Replacing" "the" protocolWord:ident "in"
      construction:cryptoCnlReference "using"
      equation:cryptoCnlReference "," "we"
      "obtain" "the" requiredWord:ident
      constructionWord:ident : tactic => do
  expectWord protocolWord "protocol"
  expectWord requiredWord "required"
  expectWord constructionWord "construction"
  let construction ← referenceTerm construction
  let equation ← referenceTerm equation
  `(tactic|
    crypto_cnl_sentence "ac.construction.replace_protocol" =>
      ac_transport $construction using $equation)

/-- Apply exact or scalar-metric serial composition to two supplied
construction proofs.  Their written order is their execution order. -/
scoped macro (name := cnlComposeConstruction)
    "The" constructionWord:ident followsWord:ident "by"
      composingWord:ident firstConstruction:cryptoCnlReference "and"
      secondConstruction:cryptoCnlReference : tactic => do
  expectWord constructionWord "construction"
  expectWord followsWord "follows"
  expectWord composingWord "composing"
  let firstConstruction ← referenceTerm firstConstruction
  let secondConstruction ← referenceTerm secondConstruction
  `(tactic|
    crypto_cnl_sentence "ac.construction.by_composition" =>
      ac_compose $firstConstruction, $secondConstruction)

/-- Introduce a named intermediate fact together with its proof.  This is the
controlled-language counterpart of Lean's `have`, following Verbose Lean's
named `Fact`/`Claim` pattern.  The name is explicit so later construction
steps can cite it deterministically. -/
scoped macro (name := cnlHaveFact)
    "We" haveWord:cryptoCnlWord name:ident ":" statement:term "by"
      colGt proof:tacticSeq : tactic => do
  expectCnlWord haveWord "have"
  `(tactic|
    crypto_cnl_sentence "ac.argument.named_fact" =>
      have $name : $statement := by
        $proof)

/-- Introduce a named intermediate fact from one explicit proof term.  This is
the single-line counterpart of `cnlHaveFact`; it performs no proof search. -/
scoped macro (name := cnlHaveFactFrom)
    "We" haveWord:cryptoCnlWord name:ident ":" statement:term
      "from" proof:cryptoCnlReference : tactic => do
  expectCnlWord haveWord "have"
  let proof ← referenceTerm proof
  `(tactic|
    crypto_cnl_sentence "ac.argument.named_fact" =>
      have $name : $statement := $proof)

/-- Introduce one explicitly named simulator for a star-relaxed ideal
specification.  The wording follows MaRuTa12's recurring sentence "We use the
following simulator ... to prove ..."; the shorter controlled form avoids
pretending that Lean will infer which simulator the proof needs.  Admission in
the simulator class and the distance estimate remain as visible goals. -/
scoped macro (name := cnlUseSimulator)
    "We" useWord:ident simulator:cryptoCnlReference "to" proveWord:ident
      "the" constructionWord:ident : tactic => do
  expectWord useWord "use"
  expectWord proveWord "prove"
  expectWord constructionWord "construction"
  let simulator ← referenceTerm simulator
  `(tactic|
    crypto_cnl_sentence "ac.construction.from_simulator" =>
      ac_simulator $simulator)

/-- Extend one supplied construction by a fixed parallel resource.  The side
word describes where the resource context appears: a right context gives the
converter `protocol ∥ 1`, while a left context gives `1 ∥ protocol`.
MauRen11 describes exactly these resource constructions as making a system
available "in parallel (on the right side)" or analogously on the left. -/
scoped macro (name := cnlParallelContext)
    "With" context:cryptoCnlReference "as" "the" sideWord:ident
      parallelWord:ident contextWord:ident "," "the"
      constructionWord:ident followsWord:ident "from"
      construction:cryptoCnlReference : tactic => do
  expectWord parallelWord "parallel"
  expectWord contextWord "context"
  expectWord constructionWord "construction"
  expectWord followsWord "follows"
  let context ← referenceTerm context
  let construction ← referenceTerm construction
  match sideWord.getId.toString with
  | "right" =>
      `(tactic|
        crypto_cnl_sentence "ac.construction.right_parallel_context" =>
          ac_context_left $context using $construction)
  | "left" =>
      `(tactic|
        crypto_cnl_sentence "ac.construction.left_parallel_context" =>
          ac_context_right $context using $construction)
  | _ =>
      Macro.throwErrorAt sideWord
        "expected `left` or `right` in this controlled-language sentence"

end CryptoControlledNaturalLanguage
