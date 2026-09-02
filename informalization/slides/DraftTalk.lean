/-
Copyright (c) 2026 Trail of Bits. Apache 2.0.

Verso-native Swiss Crypto Day 2026 talk. The proof slide mounts the current
informalization document with the same renderer as the standalone reader; it
is not a second, hand-authored representation of the proof.
-/
import VersoSlides
import Verso.Doc.Elab

open Lean
open Verso Doc Elab
open Verso.Output
open Lean.Doc.Syntax
open VersoSlides

private def hText (value : String) : Html := .text true value

private def hElem (tag className : String) (children : Array Html) : Html :=
  let attrs := if className.isEmpty then #[] else #[("class", className)]
  .tag tag attrs (.seq children)

private def hElemAttrs (tag className : String) (attrs : Array (String × String))
    (children : Array Html) : Html :=
  let attrs := if className.isEmpty then attrs else #[("class", className)] ++ attrs
  .tag tag attrs (.seq children)

private def expectEmpty (contents : Array (TSyntax `block)) : DocElabM Unit :=
  unless contents.isEmpty do
    throwErrorAt contents[0]! "This draft directive does not accept body content"

private def definitionHtml : Html :=
  hElem "div" "draft-definition-visual" #[
    hElem "div" "draft-direction-row formalization" #[
      hElem "span" "draft-direction-object" #[hText "human mathematical explanation"],
      hElem "span" "draft-direction-track points-right" #[
        hElem "span" "draft-direction-label" #[hText "formalization"]
      ],
      hElem "span" "draft-direction-object proof" #[hText "Lean proof"]
    ],
    hElem "div" "draft-direction-row informalization" #[
      hElem "span" "draft-direction-object" #[hText "human-oriented, navigable view"],
      hElem "span" "draft-direction-track points-left" #[
        hElem "span" "draft-direction-label" #[hText "informalization"]
      ],
      hElem "span" "draft-direction-object proof" #[hText "Lean proof"]
    ]
  ]

private def spectrumHtml : Html :=
  hElem "div" "draft-spectrum" #[
    hElem "div" "draft-spectrum-label intuition" #[hText "human intuition"],
    hElem "div" "draft-spectrum-line" #[
      hElem "span" "draft-spectrum-marker" #[]
    ],
    hElem "div" "draft-spectrum-label certainty" #[hText "checked certainty"],
    hElem "div" "draft-spectrum-caption" #[hText "configurable detail"]
  ]

private def provenanceHtml : Html :=
  hElem "div" "draft-provenance" #[
    hElem "div" "draft-provenance-source formal" #[
      hElem "span" "draft-provenance-name" #[hText "checked CBC theorem"]
    ],
    hElem "div" "draft-provenance-wire formal-to-generated" #[],
    hElem "div" "draft-provenance-generated" #[
      hElem "span" "draft-provenance-name" #[hText "semantic proof plan"],
      hElem "span" "draft-provenance-sub" #[hText "claims · relations · evidence"]
    ],
    hElem "div" "draft-provenance-wire generated-to-result" #[],
    hElem "div" "draft-provenance-source authored" #[
      hElem "span" "draft-provenance-name" #[hText "language design"],
      hElem "span" "draft-provenance-sub" #[hText "ontology · grammar · reader controls"]
    ],
    hElem "div" "draft-provenance-wire authored-to-result" #[],
    hElem "div" "draft-provenance-result" #[hText "navigable explanation"]
  ]

/- MainDraftTalk replaces these tokens with the current `.tex` files at build
   time. This keeps TikZ independently editable without Lean recompilation. -/
def cbcPrimitiveTikzToken : String := "@@CBC_PRIMITIVE_TIKZ@@"
def cbcConverterTikzToken : String := "@@CBC_CONVERTER_TIKZ@@"
def cbcComparisonTikzToken : String := "@@CBC_COMPARISON_TIKZ@@"
def cbcInformalizationDataToken : String := "@@CBC_INFORMALIZATION_DATA@@"

private def tikzPicture (source : String) : Html :=
  .tag "script" #[("type", "text/tikz")] (.text false source)

private def draftConstructionHtml : Html :=
  hElem "div" "tikz-cbc-stage" #[
    hElemAttrs "div" "tikz-cbc-frame fragment fade-out"
      #[("data-fragment-index", "1")] #[tikzPicture cbcPrimitiveTikzToken],
    hElemAttrs "div" "tikz-cbc-frame fragment fade-in"
      #[("data-fragment-index", "1")] #[tikzPicture cbcConverterTikzToken],
    hElemAttrs "div" "tikz-cbc-frame fragment fade-in"
      #[("data-fragment-index", "2")] #[tikzPicture cbcComparisonTikzToken]
  ]

private def draftInformalizationHtml : Html :=
  hElemAttrs "div" "informalization-native-host"
    #[("data-informalization-reader", "true")] #[
      hElemAttrs "div" "informalization-mount"
        #[("data-informalization-mount", "true")] #[],
      hElemAttrs "script" "informalization-document"
        #[("type", "application/json"), ("data-informalization-data", "true")]
        #[.text false cbcInformalizationDataToken]
    ]

private def htmlBlock (html : Html) : Block Slides :=
  .other (.ofHtml html) #[]

@[directive]
public meta def draftDefinition : DirectiveExpanderOf Unit
  | (), contents => do
      expectEmpty contents
      ``(htmlBlock definitionHtml)

@[directive]
public meta def draftSpectrum : DirectiveExpanderOf Unit
  | (), contents => do
      expectEmpty contents
      ``(htmlBlock spectrumHtml)

@[directive]
public meta def draftProvenance : DirectiveExpanderOf Unit
  | (), contents => do
      expectEmpty contents
      ``(htmlBlock provenanceHtml)

@[directive]
public meta def draftConstruction : DirectiveExpanderOf Unit
  | (), contents => do
      expectEmpty contents
      ``(htmlBlock draftConstructionHtml)

@[directive]
public meta def draftInformalization : DirectiveExpanderOf Unit
  | (), contents => do
      expectEmpty contents
      ``(htmlBlock draftInformalizationHtml)

#doc (Slides) "Informalizing a cryptographic proof — Swiss Crypto Day 2026" =>

# Informalizing a cryptographic proof

%%%
backgroundColor := "#0f1011"
state := "title"
%%%

## A checked proof, presented for humans

Marc Ilunga · Swiss Crypto Day 2026

:::notes
Hi, my name is Marc Ilunga, and I want to talk about informalizing a cryptographic proof.

Because I only have ten minutes, I will begin with the proof itself. The example is a familiar one: the security of the CBC construction as a pseudorandom function.

Transcript: section 1, “Opening — a familiar proof.”
:::

# Randomness Expansion with CBC

:::draftConstruction
:::

:::notes
Let our primitive be a random function from a block space to itself. For a message m = (m₁, …, mₗ), CBC feeds m₁ directly to the random function. Each later block is XORed with the previous chaining value before the random function is applied again. The final chaining value is the output.

We can express the same construction in the random-systems framework. The CBC converter attaches to the random-function interface. The result is a new system accepting variable-length messages.

The question is whether this construction behaves like the ideal object: a random function directly defined on the message space.

Transcript: section 2, “The CBC construction.”

Sources: CR18 Theorem 6.1; exact theorem fixture.
:::

# CBC proof

%%%
state := "informalization-reader"
%%%

:::draftInformalization
:::

:::notes
This is the generated reader for the checked theorem—not a second slide copy of
the argument. Verso mounts the generated explanation document using the same
renderer as the standalone page. The theorem heading and inputs come from the elaborated
declaration; the collapsed proof is the semantic proof plan rendered in the
language of random systems.

I can now ask what supports any particular sentence. Each dot opens the claim's
own mathematical justification. The small mark on the right reaches the full
concrete proof tree and its Lean contexts and goals. We can therefore move from
the paper-level argument to the precise checked evidence without leaving this
proof.

The key route is visible in the collapsed text: introduce the relevant systems
and game, use conditional equivalence to reduce distinguishing to blind
winning, and bound the collision probability. The audience controls how much
of that route to inspect.

Transcript: sections 3 and 4, “The proof, already in informalized form” and
“Reveal — what did I ask you to trust?”

Source: generated `preview/cbc-mac.html` from the live CBC theorem.
:::

# Informalization reverses the usual direction

:::draftDefinition
:::

:::notes
Formalization usually begins with a human mathematical explanation and translates it into a form that a proof assistant can check.

Here we move in the other direction. We begin with a checked formal proof and construct a human-oriented presentation of it. I call this informalization.

The aim is not to regenerate one fixed piece of prose. Different readers need different levels of detail. A cryptographer may want the game transition. A formalizer may want the exact theorem and proof state. An implementer may need the definition hidden behind a symbol. The same checked proof should support all of these views, with detail on demand.

Transcript: section 5, “What ‘informalization’ means here.”

Sources: Kyle Miller, ICERM informalization talk; Massot–Miller informalization prototype.
:::

# Correctness and explanation are different guarantees

:::draftSpectrum
:::

Formal verification answers whether a theorem follows from its definitions.

Readers still need to understand whether those definitions express the intended concept—and why the argument works.

:::notes
Formal verification gives us strong guarantees, but a Lean proof is not automatically a good explanation. It does not by itself communicate why a definition is meaningful, where the conceptual joints of an argument are, or which intuition a human should retain.

This tension is becoming more visible as language models produce more formal code. In this experiment, most of the Lean development was written with language-model assistance. Checking tells us whether the proof term satisfies the stated theorem. It does not tell us whether the statement captures the concept we intended, or whether another human can understand the argument.

Informalization is an attempt to preserve both sides: machine-checked certainty and human mathematical intuition.

And this is useful even without AI. In industry, the same result must often be communicated to researchers, reviewers, protocol designers, and implementers. Those readers need different explanations, but they should remain connected to the same formal source.

Transcript: section 6, “Why this matters.”

Sources: no quantitative AI claim is made on this slide.
:::

# The prototype keeps provenance visible

:::draftProvenance
:::

Checked structure and evidence determine the claims. A licensed mathematical language determines how they are said.

:::notes
This experiment adapts work by Kyle Miller and Patrick Massot on turning Lean proofs into interactive, structured explanations. The implementation first recovers checked entities, relations, and proof dependencies. It then forms a semantic proof plan and realizes that plan using a registered mathematical ontology and grammar.

The author can still provide a theorem title, preferred terminology, emphasis, and reader guidance. Those controls shape the presentation, but they cannot change a checked claim or supply missing proof evidence. The prototype does not yet promise polished prose for an arbitrary Lean theorem; unsupported semantics fail closed instead of being assigned a plausible story.

Transcript: section 7, “The experiment and invitation.”

Sources: local Talk Backend; Miller ICERM talk.
:::

# One checked proof

%%%
backgroundColor := "#0f1011"
state := "close"
%%%

## Different readers. Detail on demand.

*Communication is part of the formalization problem.*

:::notes
My invitation is therefore not that everyone should use this particular library. It is that we should treat communication as part of the formalization problem. If more mathematics and cryptography become formally verified, we should also invest in ways to keep those results inspectable, teachable, and human.

One checked proof; different readers; detail on demand.

Thank you.

Transcript: section 7, “The experiment and invitation.”
:::
