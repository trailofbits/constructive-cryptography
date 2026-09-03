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

/- The headline poses the question the spectrum answers: the two columns of
   the tension table are not the only options. -/
private def spectrumHtml : Html :=
  hElem "div" "draft-spectrum-block" #[
    hElem "div" "draft-spectrum-headline" #[hText "Must we choose?"],
    hElem "div" "draft-spectrum" #[
      hElem "div" "draft-spectrum-label intuition" #[hText "human intuition"],
      hElem "div" "draft-spectrum-line" #[
        hElem "span" "draft-spectrum-marker" #[]
      ],
      hElem "div" "draft-spectrum-label certainty" #[hText "checked certainty"],
      hElem "div" "draft-spectrum-caption" #[hText "configurable tradeoff"]
    ]
  ]

private def flowStage (className name : String) (parts : Array String) : Html :=
  hElem "div" className #[
    hElem "span" "draft-flow-name" #[hText name],
    hElem "span" "draft-flow-parts"
      (parts.map fun part => hElem "span" "draft-flow-part" #[hText part])
  ]

/- The informalizer as a flow: each stage is built from the previous one, and
   the authored language design enters at the semantic plan and the rendering.
   Labels follow the pipeline boundary documented in the project README. -/
private def pipelineHtml : Html :=
  hElem "div" "draft-flow" #[
    flowStage "draft-flow-stage" "checked source"
      #["Lean theorem", "proof term", "InfoTrees"],
    hElem "div" "draft-flow-wire" #[],
    flowStage "draft-flow-stage" "proof tree"
      #["evidence graph", "proof dependencies", "goals and contexts"],
    hElem "div" "draft-flow-wire" #[],
    flowStage "draft-flow-stage" "semantic plan"
      #["entities and relations", "applied rules", "canonical proof plan"],
    hElem "div" "draft-flow-wire" #[],
    flowStage "draft-flow-stage" "rendering"
      #["discourse and realization", "Explanation JSON", "interactive reader"],
    hElem "div" "draft-flow-rise into-plan" #[],
    hElem "div" "draft-flow-rise into-rendering" #[],
    flowStage "draft-flow-input" "language design"
      #["Random Systems ontology · grammar · presentation rules"]
  ]

/- MainDraftTalk replaces these tokens with the current `.tex` files at build
   time. This keeps TikZ independently editable without Lean recompilation. -/
def cbcPrimitiveTikzToken : String := "@@CBC_PRIMITIVE_TIKZ@@"
def cbcConverterTikzToken : String := "@@CBC_CONVERTER_TIKZ@@"
def cbcComparisonTikzToken : String := "@@CBC_COMPARISON_TIKZ@@"
def cbcInformalizationDataToken : String := "@@CBC_INFORMALIZATION_DATA@@"

private def tikzPicture (source : String) : Html :=
  .tag "script" #[("type", "text/tikz")] (.text false source)

private def proofMilestoneStep (fragmentIndex order : String) : Html :=
  hElemAttrs "span" "fragment proof-milestone-step"
    #[("data-fragment-index", fragmentIndex),
      ("data-proof-milestone-step", order)] #[]

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
        #[.text false cbcInformalizationDataToken],
      proofMilestoneStep "0" "2",
      proofMilestoneStep "1" "3",
      proofMilestoneStep "2" "4",
      proofMilestoneStep "3" "5"
    ]

/- A second view of the same document. It reuses the JSON embedded by the
   main proof slide and opts out of the milestone highlights. -/
private def draftInformalizationBareHtml : Html :=
  hElemAttrs "div" "informalization-native-host"
    #[("data-informalization-reader", "true"),
      ("data-informalization-milestones", "false")] #[
      hElemAttrs "div" "informalization-mount"
        #[("data-informalization-mount", "true")] #[]
    ]

private def htmlBlock (html : Html) : Block Slides :=
  .other (.ofHtml html) #[]

/-! ## Footnotes

Verso's own footnote syntax (`[^1]` in the text, `[^1]: …` as a definition)
renders as an inline disclosure widget, which is wrong on a slide. The pass
below runs before rendering. Each reference becomes a superscript marker, and
the notes referenced on a slide are collected, in order of first use, into a
footer block at the end of that slide. Everything stays ordinary genre data,
so links and emphasis inside a note render through the usual pipeline. -/

private def footnoteMarker (label : String) : Inline Slides :=
  .other (.styled #[("class", "draft-footnote-ref")]) #[.text label]

private abbrev FootnoteM := StateM (Array (String × Array (Inline Slides)))

private def recordFootnote (label : String) (content : Array (Inline Slides)) :
    FootnoteM Unit :=
  modify fun notes =>
    if notes.any (·.1 == label) then notes else notes.push (label, content)

private partial def hoistInline : Inline Slides → FootnoteM (Inline Slides)
  | .footnote label content => do
      recordFootnote label content
      pure (footnoteMarker label)
  | .emph content => .emph <$> content.mapM hoistInline
  | .bold content => .bold <$> content.mapM hoistInline
  | .link content url => (.link · url) <$> content.mapM hoistInline
  | .concat content => .concat <$> content.mapM hoistInline
  | .other container content => .other container <$> content.mapM hoistInline
  | inline => pure inline

private partial def hoistBlock : Block Slides → FootnoteM (Block Slides)
  | .para content => .para <$> content.mapM hoistInline
  | .ul items => .ul <$> items.mapM hoistItem
  | .ol start items => .ol start <$> items.mapM hoistItem
  | .dl items => .dl <$> items.mapM fun item => do
      pure ⟨← item.term.mapM hoistInline, ← item.desc.mapM hoistBlock⟩
  | .blockquote content => .blockquote <$> content.mapM hoistBlock
  | .concat content => .concat <$> content.mapM hoistBlock
  | .other container content => .other container <$> content.mapM hoistBlock
  | block => pure block
where
  hoistItem (item : ListItem (Block Slides)) : FootnoteM (ListItem (Block Slides)) :=
    (⟨·⟩) <$> item.contents.mapM hoistBlock

private def footnoteFooter (notes : Array (String × Array (Inline Slides))) : Block Slides :=
  .other (.wrap #[("class", "draft-footnotes")]) <|
    notes.map fun (label, content) =>
      .para (#[footnoteMarker label, .text " "] ++ content)

private instance : Inhabited (Part Slides) := ⟨⟨#[], "", none, #[], #[]⟩⟩

/-- Rewrites every slide so its footnote references become markers and the
referenced notes appear as a footer on that same slide. -/
partial def hoistFootnotes (part : Part Slides) : Part Slides :=
  let (content, notes) := (part.content.mapM hoistBlock).run #[]
  let content := if notes.isEmpty then content else content.push (footnoteFooter notes)
  { part with content, subParts := part.subParts.map hoistFootnotes }

private def emptyHtml : Html := .seq #[]

/-- Source-only content: the body is parsed but renders nothing. -/
@[directive]
public meta def comment : DirectiveExpanderOf Unit
  | (), _contents => ``(htmlBlock emptyHtml)

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
public meta def draftPipeline : DirectiveExpanderOf Unit
  | (), contents => do
      expectEmpty contents
      ``(htmlBlock pipelineHtml)

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

@[directive]
public meta def draftInformalizationBare : DirectiveExpanderOf Unit
  | (), contents => do
      expectEmpty contents
      ``(htmlBlock draftInformalizationBareHtml)

#doc (Slides) "Informalizing Cryptographic Proofs — Swiss Crypto Day 2026" =>

# Informalizing Cryptographic Proofs

%%%
backgroundColor := "#0f1011"
state := "title"
%%%

:::comment
## A checked proof, presented for humans
:::

Marc Ilunga · Swiss Crypto Day · 4 September 2026

:::notes
(30 s)

Hi. Today I'd like to talk about a security proof, and to do so I will review a classic result: Maurer's proof of the CBC MAC in the random systems framework.
:::

# Randomness Expansion with CBC

:::draftConstruction
:::

:::notes
(30 s)

We start with a random function, a random system whose probabilistic behavior is shown on screen.

CBC can be seen as a converter attached to the random system: it uses a block former to create an output.

What we'd like to know is whether CBC is as good as the system on the right, which in practice is usually a variable-input-length random function.
:::

# CBC proof

%%%
state := "informalization-reader"
%%%

:::draftInformalization
:::

:::notes
(1.5 min)

Let me briefly go through the proof. How much time do I have? Only 5 minutes left, so I'll have to skim over it!

We want to establish the following distinguishing advantage.

Note the theta on both sides: it restricts the input space to values producing q blocks with CBC. And the filter \[q\] restricts the random function R to q queries.

First, given that theta, the \[q\] filter is unnecessary.

Next, define a game with a binary output that starts at 0 and becomes 1 if there is a non-trivial collision at the input of any call to R.

Conditioned on the game bit being zero, the two systems have the same behavior.

The conditional-equivalence lemma then lets us focus on bounding the advantage of winning the collision game blindly, that is, non-adaptively.

One can work out that this is at most the value shown.

Gluing everything together gives the intended result.
:::

# Correctness  vs Presentation

:::::class "draft-tension"
:::table +colHeaders
*
  * Intuition
  * Complete correctness
*
  * Human-written paper
  * Formalization in a proof assistant
*
  * Can be slightly incorrect, usually readable
  * Machine checked, mostly unreadable
:::
:::::

:::::fragment fadeUp
:::draftSpectrum
:::
:::::

:::notes
I have just done a bad job of explaining a proof, which I could blame on having only 10 minutes.

Regardless of the medium and of how much time one is given, there is an inherent tension between being thorough and conveying intuition.

On one hand, hand-written proofs present material at an abstraction level chosen by the author. At the risk of being ambiguous or slightly incorrect, they are well suited to conveying ideas and intuition.

On the other hand, formalizing in a proof assistant gives very strong guarantees but produces artifacts that are extremely difficult to read.

So I wanted to explore whether there is a configurable lever to get the best of both worlds.
:::

# CBC proof, bare

%%%
state := "informalization-reader"
%%%

:::draftInformalizationBare
:::

:::notes
In fact, the text I skimmed over before is a semi-automated rendering of a Lean proof.

You can hover over an element to see its definition, inspect the current goal, expand parts of the proof for more detail, and expand the whole proof if you need every detail.
:::

# How it works

- Adaptation of the Lean informalization[^1] by Patrick Massot and Kyle Miller.
- Own formalization of Random Systems[^2] in Lean.
- LLM driven implementation, variable level of manual scrutiny.

:::::fragment fadeUp
:::draftPipeline
:::
:::::

[^1]: Kyle Miller, From Lean to Natural Language and Back, ICERM 2025. [https://kmill.github.io/informalization/icerm\_talk.pdf](https://kmill.github.io/informalization/icerm_talk.pdf)

[^2]: Ueli Maurer, Cryptography Foundations, lecture notes, ETH Zürich, Spring 2018.

:::notes
This is an adaptation of the informalization project by Massot and Miller. The project seems abandoned, but there are rendered examples, so I used Miller's slides as the specification for the implementation.

There is also my own experimental formalization of random systems in Lean.

The code is LLM-generated but manually reviewed, with a variable level of scrutiny.

Overall, a pipeline goes from Lean 4 code and user-defined linguistic rules to the rendered output.
:::

# Why do I care?

- AI-generated maths and crypto
  - Increasingly trustworthy thanks to formal verification
  - Currently unsuitable for human consumers
  - Informalization: enforce a presentation style decided by humans.

:::::fragment fadeUp
- Consumers of cryptographic literature have different needs
  - Advancing science, implementation considerations
  - Informalization would let each reader pick their level of detail.
:::::

:::notes
AI-generated math and cryptographic content is on the rise. AI's growing use of proof assistants makes these results more trustworthy, but at the cost of understanding.

I am positive about this trend but do not expect everyone to be. Nevertheless, there is a world where non-trivial results are produced and formalized by AI, and humans verify that the statement is meaningful without gaining insight from the proof. A human-defined way to render formalized results could be one of many approaches to staying deeply connected to a field we care about.

\[click\]

Besides AI, there are various consumers of cryptographic literature: some advancing science, others implementing. Each could benefit from a rendering at the level of detail they need.
:::

# Informal or Fully Correct? Why not both.

:::::class "draft-links"
- Random Systems in Lean: [github.com/trailofbits/constructive-cryptography/RandomSystems](https://github.com/trailofbits/constructive-cryptography/tree/categorical/RandomSystems)
- CBC-MAC proof: [github.com/trailofbits/cbc-mac-cc](https://github.com/trailofbits/cbc-mac-cc)
- CBC-MAC informalization: [github.com/trailofbits/constructive-cryptography/informalization](https://github.com/trailofbits/constructive-cryptography/tree/categorical/informalization)
- Informal Lean (Massot & Miller): [kmill.github.io/informalization/ContinuousFrom.html](https://kmill.github.io/informalization/ContinuousFrom.html)
- Get in touch: [marc.ilunga@trailofbits.com](mailto:marc.ilunga@trailofbits.com)
:::::

:::notes
My invitation is therefore not that everyone should use this particular library. It is that we should treat communication as part of the formalization problem. If more mathematics and cryptography become formally verified, we should also invest in ways to keep those results inspectable, teachable, and human.

One checked proof; different readers; detail on demand.

Thank you.

Transcript: section 7, “The experiment and invitation.”
:::
