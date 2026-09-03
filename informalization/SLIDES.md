# Slide authoring guide

This is the self-contained authoring guide for the Swiss Crypto Day Verso deck.
The slide source is ordinary Verso markup inside Lean, with a small set of
project-specific directives for the CBC figures and generated proof reader.

## Quick start

For a live editing session, run this from the repository root:

```sh
./scripts/watch-swiss-crypto-day.sh --serve --port 8766
```

Then open <http://127.0.0.1:8766>. The watcher rebuilds the deck after changes
and reloads the browser only after a successful build.

To rebuild only the slides against the existing generated proof document:

```sh
./scripts/build-swiss-crypto-day.sh --slides-only
```

To regenerate the informalization from the live CBC theorem and then rebuild
the deck:

```sh
./scripts/build-swiss-crypto-day.sh
```

The complete build is fail-closed: it does not replace checked proof evidence
with hand-authored slide content when the source proof is incomplete.

## Which files to edit

| Purpose | File or directory |
| --- | --- |
| Slide order, visible copy, and speaker notes | `slides/DraftTalk.lean` |
| Global dimensions, theme, CSS/JS assets, and output | `slides/MainDraftTalk.lean` |
| CBC construction stages | `slides/tikz/*.tex` |
| Deck-specific layout and typography | `slides/static/draft-talk.css` |
| Trail of Bits theme | `slides/static/tob-tangerine.css` |
| TikZ container geometry | `slides/static/tikz-cbc.css` |
| Embedded proof-reader layout | `slides/static/informalization-native.css` |
| Embedded proof-reader lifecycle | `slides/static/informalization-slide.js` |
| Spoken transcript | `slides/TRANSCRIPT.md` |

Do not edit these generated outputs:

- `slides/_draft_talk/`
- `preview/cbc-mac.html`
- `preview/cbc-mac.document.json`
- `preview/cbc-mac.semantic.json`

The CBC proof slide is generated from the checked theorem. Do not copy the
proof into `DraftTalk.lean` or maintain a second hand-written proof tree.

## Minimal Verso deck

A presentation is a Verso document with the `Slides` genre. Every top-level
heading is one horizontal slide.

```lean
import VersoSlides
import Verso.Doc.Elab

open VersoSlides

#doc (Slides) "My presentation" =>

# First slide

One idea, expressed briefly.

# Second slide

The next idea.
```

The document is imported by a small executable that calls `slidesMain`:

```lean
import VersoSlides
import MyPresentation

open VersoSlides

def main : IO UInt32 :=
  slidesMain
    (config := { outputDir := "_slides", slideNumber := true })
    (doc := %doc MyPresentation)
```

In this repository, `DraftTalk.lean` owns the document and
`MainDraftTalk.lean` owns the executable.

## Ordinary text and structure

Verso accepts familiar Markdown-like markup:

```text
Plain paragraph with *emphasis*, **strong text**, and `inline code`.

* First bullet
* Second bullet

1. First numbered item
2. Second numbered item

[Link text](https://example.com)
```

Keep visible slide content audience-facing. Timing, talk tracks, production
comments, and source details belong in speaker notes.

## Speaker notes

Use `:::notes` at the end of a slide. Press `S` while presenting to open the
reveal.js speaker view.

```text
:::notes
Explain why this transition matters.

Sources: CR18, Theorem 6.1.
:::
```

Put sources for non-trivial claims and external assets in the notes. Notes are
not visible on the audience slide.

## Slide metadata

Place a `%%%` block immediately after a slide heading:

```text
# Dark title slide

%%%
backgroundColor := "#0f1011"
transition := "none"
state := "title"
%%%
```

Common fields are:

| Field | Meaning |
| --- | --- |
| `vertical` | Treat `##` subsections as vertical sub-slides |
| `transition` | Slide transition such as `none`, `fade`, or `zoom` |
| `transitionSpeed` | Transition speed |
| `backgroundColor` | CSS background color |
| `backgroundImage` | Background image URL |
| `backgroundSize` | CSS background size |
| `backgroundPosition` | CSS background position |
| `backgroundRepeat` | CSS background repeat |
| `backgroundOpacity` | Background opacity |
| `backgroundVideo` | Background video URL |
| `backgroundVideoLoop` | Loop the background video |
| `backgroundVideoMuted` | Mute the background video |
| `backgroundIframe` | Background page URL; avoid for interactive project content |
| `backgroundGradient` | CSS background gradient |
| `backgroundTransition` | Background transition |
| `backgroundInteractive` | Permit interaction with a background iframe |
| `autoAnimate` | Animate matching elements across adjacent slides |
| `autoAnimateId` | Group auto-animated slides |
| `autoAnimateEasing` | CSS easing for auto-animation |
| `autoAnimateDuration` | Auto-animation duration |
| `autoAnimateUnmatched` | Animate elements without matches |
| `autoAnimateRestart` | Restart an auto-animation sequence |
| `timing` | Expected slide duration |
| `visibility` | reveal.js slide visibility |
| `state` | CSS/JavaScript state class for the current slide |
| `autoSlide` | Per-slide auto-advance interval in milliseconds |

The fields are optional. The local sources normally use direct values, while
explicit `some` values are also valid where the field type is an `Option`.

### Vertical slides

```text
# Main topic

%%%
vertical := true
%%%

The first vertical slide.

## Supporting detail

Navigate down to reach this slide.
```

Without `vertical := true`, `##` headings remain content inside the current
slide rather than creating navigable sub-slides.

## Progressive reveals

### Block fragments

```text
:::fragment fadeUp (index := 2)
This block appears at fragment step 2.
:::
```

If one `:::fragment` contains several paragraphs, each child block becomes a
separate fragment. Wrap each intended reveal separately when exact grouping
matters.

Useful styles include:

- `fadeIn`, `fadeOut`
- `fadeUp`, `fadeDown`, `fadeLeft`, `fadeRight`
- `currentVisible`
- `highlightRed`, `highlightGreen`, `highlightBlue`
- `fadeInThenOut`, `grow`, and `shrink`

An explicit `index` coordinates several fragments. Fragments with the same
index activate together.

### Inline fragments

```text
This is {fragment (style := highlightRed) (index := 2)}[revealed inline].
```

### Layer replacement

Use `stack` with matching fragment indices when one visual should replace
another without moving the layout:

```text
:::::stack
:::fragment fadeOut (index := 1)
First visual.
:::

:::fragment fadeIn (index := 1)
Replacement visual.
:::
:::::
```

## Layout utilities

### Fit, stretch, and frame

```text
:::fitText
Text scaled to the available width.
:::

:::stretch
Content that fills the remaining slide height.
:::

:::frame
Content with the reveal.js frame style.
:::
```

Only one element per slide should use reveal.js stretching. If several Lean
code blocks share a slide, add `-stretch` to all but one.

### Horizontal, vertical, and overlay layouts

```text
:::hstack
Left item.

Right item.
:::

:::vstack
Top item.

Bottom item.
:::

:::stack
Layer one.

Layer two.
:::
```

`hstack` lays out children horizontally, `vstack` lays them out vertically,
and `stack` overlays them.

## CSS classes, IDs, and attributes

Block forms push attributes onto each child block:

```text
:::class "important" "wide"
Styled content.
:::

:::id "main-claim"
Identified content.
:::

:::attr («data-id» := "shared-title") (style := "color: red")
Attributed content.
:::
```

Hyphenated attribute names use guillemets, as in `«data-id»`.

Inline counterparts use roles:

```text
This is {class "important"}[styled], {id "term"}[identified], and
{attr («data-id» := "term")}[tracked].
```

Matching `data-id` values are useful for `autoAnimate` transitions.

### Nesting directives

Use a longer outer fence when directives are nested:

```text
:::::fitText
:::attr («data-id» := "title")
Scaled and tracked text.
:::
:::::
```

## Mathematics

Inline and display mathematics use LaTeX rendered by KaTeX:

```text
Inline: $`e^{i\pi}+1=0`.

$$`\Delta(R,S) \leq \varepsilon`
```

The backticks are required. Use inline math inside sentences and display math
only for expressions that deserve their own visual line.

Recurring macros can be installed once through `Config.mathPrelude`:

```lean
let config : Config := {
  mathPrelude :=
    "\\def\\RR{\\mathbb{R}}\n\\newcommand{\\Adv}{\\operatorname{Adv}}\n"
}
```

KaTeX is bundled, so mathematics works offline.

## Images

Use the image role. Paths are relative to the Lean source file:

```text
{image "static/images/example.png" (width := "600px")}[Useful alt text]
```

The alt text belongs between brackets. Prefer explicit width or height and
inspect the resulting crop in the browser.

## Tables

The `table` directive consumes a nested list. Every row must have the same
number of cells.

```text
:::table +colHeaders +stripedRows +rowSeps +border
*
  * Claim
  * Meaning
*
  * Conditional equivalence
  * Equal behavior until the bad event
*
  * Blind winning
  * The query list is fixed before replies
:::
```

Available flags include `+colHeaders`, `+rowHeaders`, `+stripedRows`,
`+stripedCols`, `+rowSeps`, `+colSeps`, `+headerSep`, and `+border`. Customize
cell padding with `(cellGap := "0.4em 0.6em")`.

## Lean and other code

### Elaborated Lean

````text
```lean
theorem example : True := by
  trivial
```
````

Lean blocks are elaborated during the build and retain syntax information. By
default, a code block stretches to fill the remaining slide and includes an
interactive information panel. Code information is opened by clicking a token,
not by hovering over it, so pointing at code during a talk does not obscure the
slide.

Useful flags are:

- `-stretch`: size the box to its content.
- `-panel`: hide the interactive information panel.
- `-show`: elaborate setup code but do not display it.
- `+panel` or `+stretch`: explicitly re-enable a disabled default.

To disable panels for the whole deck and opt in only where useful, put this
before the `#doc` command:

```lean
set_option verso.slides.panel false
```

Inline Lean expressions use `{lean}`:

```text
The declaration {lean}`Nat.add_comm` is checked while building the deck.
```

A single command can be rendered with `{leanCommand}`:

```text
{leanCommand}`#check Nat.add_comm`
```

### Progressive Lean-code reveal

Special comments inside an elaborated Lean block control fragments:

```lean
theorem example : True := by
  -- !fragment
  trivial
```

The main controls are:

- `-- !fragment`: start a new line-level fragment.
- `-- !fragment fadeUp 3`: fragment with style and index.
- `-- ^ !click`: make the token above the caret a click target.
- `/- !fragment -/ ... /- !end fragment -/`: inline fragment.
- `/- !hide -/ ... /- !end hide -/`: elaborate but omit a region.
- `/- !replace ... -/ ... /- !end replace -/`: show replacement text while
  elaborating the real expression.

### Modules and library excerpts

Use `leanModule` for a complete elaborated module and `leanModules` to group
several modules:

````text
```leanModule
module
import Std

def answer := 42
```
````

For several related modules, assign their names inside `leanModules`:

````text
:::leanModules (moduleRoot := Lib)
```leanModule (moduleName := Lib.A) -stretch
module

def a := 1
```

```leanModule (moduleName := Lib.B) -stretch
module
import Lib.A

#check a
```
:::
````

Add `+lakefile` to a `leanModule` when its contents are a small Lake project
configuration rather than an ordinary Lean module.

Use `leanLibCode` to pin displayed source to a declaration or line range in a
dependency:

````text
```leanLibCode MyLib.Foo (decl := MyLib.Foo.bar)
def bar : Nat := 42
```
````

The expected body must match the library. Library highlighting facets must be
listed in the slides Lake target's `needs` field when the dependency is not
Lean's prelude or `Std`.

`leanLibCode` accepts either `(decl := Name)` or a paired 1-based inclusive
`(startLine := n) (endLine := m)` range. `(package := name)` disambiguates a
module supplied by more than one package. Omitting the declaration and range
shows the whole module. The `panel` and `stretch` flags work as they do on
ordinary Lean blocks.

For a dependency named `mypkg`, arrange for Lake to produce highlighted source
before the slide module is elaborated:

```lean
lean_lib MySlides where
  needs := #[`@mypkg:highlighted]
```

For one module only, use `` `@mypkg/+MyLib.Foo:highlighted ``. A missing facet
fails the build instead of silently triggering a large dependency build.

### Other languages

````text
```code rust
fn main() { println!("hello"); }
```
````

Non-Lean code is highlighted but not type-checked.

## Trusted HTML and programmatic visuals

For controlled local markup, use an `html` block or role:

````text
```html
<div class="custom-widget">Content</div>
```

Inline {html}`<span class="custom-widget">HTML</span>` is also available.
````

This HTML is trusted and unsanitized. Never insert untrusted input.

Verso also provides `diagram` and `animate` code blocks through Illuminate.
They evaluate Lean code that returns a diagram or animation. This deck instead
uses TikZ for its CBC construction because the figure is maintained as a
mathematical diagram and rendered in the browser.

## Footnotes

Use Verso's own footnote syntax. A reference is `[^1]` immediately after the
word it annotates; the definition is a `[^1]:` line at the top level of the
slide, anywhere in it:

```text
- Adaptation of the Lean informalization[^1] by Patrick Massot and Kyle Miller.

[^1]: Kyle Miller, From Lean to Natural Language and Back, ICERM 2025. [kmill.github.io/…](https://kmill.github.io/informalization/icerm_talk.pdf)
```

Stock Verso renders each reference as an inline disclosure widget. The deck's
`hoistFootnotes` pass (in `slides/DraftTalk.lean`, applied by
`MainDraftTalk.lean` before rendering) rewrites every slide instead: each
reference becomes a superscript marker (`.draft-footnote-ref`), and the notes a
slide uses are collected, in order of first use, into a `.draft-footnotes`
footer at the end of that slide. Note text is ordinary inline markup, so links
and emphasis work; escape underscores in link text (`icerm\_talk.pdf`) or
Verso reads them as emphasis. Names are free-form, but digits keep the markers
readable.

## This deck's custom directives

`slides/DraftTalk.lean` defines five body-less directives:

| Directive | Result |
| --- | --- |
| `:::draftConstruction` | Three staged TikZ views of the CBC construction |
| `:::draftInformalization` | Native mount point for the generated checked proof reader |
| `:::draftDefinition` | Formalization/informalization direction visual |
| `:::draftSpectrum` | Intuition-to-certainty spectrum visual |
| `:::draftProvenance` | Checked-evidence and language-design provenance visual |

Use them like this:

```text
# Randomness Expansion with CBC

:::draftConstruction
:::

# CBC proof

%%%
state := "informalization-reader"
%%%

:::draftInformalization
:::
```

These directives reject body content. Their HTML structures are defined above
the `#doc` block in `DraftTalk.lean`, while CSS controls their layout.

### Adding a custom directive

For a new reusable visual:

1. Build its `Verso.Output.Html` value above the `#doc` block.
2. Wrap it in `htmlBlock`.
3. Register a `public meta def` with `@[directive]`.
4. Put geometry and styling in a named CSS class rather than inline styles.
5. Use the directive in the document body.
6. Rebuild and inspect every fragment state in the browser.

The existing `draftDefinition` directive is the shortest complete example.

## TikZ workflow

The CBC construction uses three source files:

- `slides/tikz/cbc-primitive.tex`
- `slides/tikz/cbc-converter.tex`
- `slides/tikz/cbc-comparison.tex`

`draftConstruction` places tokens in the Verso document. After Verso writes
the HTML, `MainDraftTalk.lean` reads the current `.tex` files and replaces
those tokens. Therefore a TikZ edit does not require copying SVG or PDF
artifacts into the deck.

Prefer semantic TikZ geometry:

- Name important nodes.
- Position new nodes relative to named nodes.
- Join exact anchors such as `.east`, `.west`, `.north`, and `.south`.
- Keep interface lines straight unless a bend communicates real structure.
- Use filled switch contacts and connect wires to their boundaries.
- Avoid accumulating unrelated numerical offsets to repair alignment.
- Inspect all fragment stages, not only the final comparison.

The containing figure size and placement live in
`slides/static/tikz-cbc.css`; internal diagram geometry belongs in the `.tex`
files.

## Theme, CSS, JavaScript, and assets

`MainDraftTalk.lean` constructs a custom theme and a `Config`:

```lean
let config : Config := {
  theme := .custom tangerineDraftTheme
  center := false
  width := 1600
  height := 900
  margin := 0.025
  slideNumber := true
  transition := "none"
  outputDir := "_draft_talk"
  extraCss := #[tangerineCss, draftCss, tikzCbcCss, informalizationNativeCss]
  extraJs := #["tikzjax-loader.js", "massot-miller.js",
    "informalization-slide.js"]
}
```

Important document-wide configuration fields include `theme`, `transition`,
`width`, `height`, `margin`, `controls`, `progress`, `slideNumber`, `hash`,
`center`, `navigationMode`, `autoSlide`, `autoSlideStoppable`,
`autoSlideMethod`, `highlightTheme`, `extraCss`, `extraJs`, `mathPrelude`, and
`outputDir`.

### Automatic advance

`autoSlide := 0` disables automatic advance. A positive value is the interval
in milliseconds and adds a play/pause control. A slide-level `autoSlide` value
overrides the global interval. `autoSlideStoppable := true` pauses after user
interaction; use `false` only for unattended playback.

`autoSlideMethod` determines the movement: `.next` advances through fragments
and slides, `.right` moves horizontally, and `.down` moves vertically. The
escape hatch `.js "() => Reveal.left()"` accepts a JavaScript function.

### Built-in and custom themes

A string such as `theme := "white"` selects a bundled reveal.js theme. The
standard themes plus `black-contrast` and `white-contrast` are bundled, and
their fonts are available offline. A project-owned stylesheet can replace the
theme:

```lean
import VersoUtil.BinFiles

open Verso.BinFiles

def myThemeCss : CssFile where
  filename := "theme/my-theme.css"
  contents := ⟨include_str "static/my-theme.css"⟩

def myTheme : CustomTheme where
  stylesheet := myThemeCss
  assets := ThemeAsset.fromDir (include_bin_dir "static/theme-assets")
```

Pass it as `theme := .custom myTheme`. Asset URLs inside the CSS remain normal
paths relative to the emitted stylesheet. For one binary asset, use
`include_bin`; for a directory tree, use `include_bin_dir`.

Non-Lean code uses highlight.js. Bundled highlighting themes include
`monokai`, `github`, `githubDark`, `atomOneLight`, `atomOneDark`, `tomorrow`,
`solarizedLight`, and `solarizedDark`. Set, for example,
`highlightTheme := .githubDark`, or supply a `CssFile` as a custom highlighting
theme. An explicit `Config.highlightTheme` overrides the theme default.

CSS files are loaded in `extraCss` order, after the theme. Later styles can
override earlier styles. Keep responsibilities separate:

- Brand variables and global typography belong in `tob-tangerine.css`.
- Deck-specific composition belongs in `draft-talk.css`.
- TikZ host sizing belongs in `tikz-cbc.css`.
- Proof-reader integration belongs in `informalization-native.css`.

Theme assets are bundled with `include_bin` or `include_bin_dir`. Extra
JavaScript filenames name files written into the output directory. The build
currently copies the shared reader and project adapter explicitly.

All theme assets and extra stylesheets share the output directory. Reusing a
filename with identical bytes is deduplicated. Reusing it with different
contents is a build error, and the output is left untouched; fix the filenames
rather than depending on write order.

The `state` metadata field is useful for narrowly scoped CSS and lifecycle
behavior. The proof slide uses `state := "informalization-reader"` so its
interactive reader is mounted only when Reveal has made that slide current.

## Navigation while presenting

Common reveal.js controls are:

| Key | Action |
| --- | --- |
| Right arrow or Space | Advance a fragment or slide |
| Left arrow | Go backward |
| Up/Down arrows | Navigate vertical slides |
| `S` | Open speaker view |
| `Esc` | Show slide overview |
| `Home` / `End` | First / last slide |
| `?` | Show keyboard help |

The URL hash records the current slide. A path such as `#/1/0/2` identifies a
horizontal slide, vertical sub-slide, and fragment state.

## Project presentation rules

- Keep slides and illustrations extremely minimal.
- Give each slide one purpose and one primary claim.
- Use direct, audience-facing titles rather than production labels.
- Put detail in speaker notes before adding dense visible prose.
- Shorten copy or change the layout before shrinking text.
- Use one composition rather than a grid of UI-like cards.
- Use fragments only when the sequence helps the explanation.
- Keep mathematical notation proportional to the surrounding text.
- Put external claims and asset sources in speaker notes.
- Keep the CBC proof generated from the checked declaration.
- Review the rendered deck in the browser before declaring a change complete.

## Visual verification checklist

After every visible change:

1. Rebuild successfully.
2. Open the deck over HTTP, not from a stale `file://` tab.
3. Inspect every changed slide at its initial fragment state.
4. Advance through every fragment and inspect each state.
5. Check for clipping, overflow, accidental scrollbars, and wrapped titles.
6. Check arrow endpoints, straightness, alignment, and label spacing.
7. Check speaker notes with `S` when notes changed.
8. On the proof slide, test local expansion, Expand all, Collapse all, hovers,
   proof-state selection, scrolling, and navigation to another slide.
9. Refresh once from a new page load and confirm the proof slide is responsive.
10. Run `git diff --check` before committing.

## Common mistakes

- Editing `_draft_talk/index.html`: it is overwritten by the next build.
- Opening a stale `file://` copy: use the watcher and localhost server.
- Copying the proof into the slide source: the generated reader is the only
  proof-slide source.
- Adding visible source attribution such as “Following CR18”: attribution
  belongs in notes or provenance unless the audience needs it.
- Putting several paragraphs in one fragment: they reveal separately.
- Stretching more than one element: reveal.js computes the heights badly.
- Using a background iframe for interactive content: it can capture keyboard
  navigation; use a native Verso block when integration is required.
- Styling generic `.controls`: this can accidentally capture the proof
  reader's controls as well as Reveal's controls.
- Fixing TikZ with many unrelated numeric offsets: use named nodes and anchors.
- Checking only the final fragment: intermediate stages can have different
  bends, overlaps, or labels.

## Upstream references

This guide contains the authoring surface needed for this project. The pinned
dependency also includes the full upstream reference and an executable demo:

- `slides/.lake/packages/verso-slides/README.md`
- `slides/.lake/packages/verso-slides/Demo.lean`

Those paths are dependency-cache material and may be regenerated; this
top-level guide is the stable project documentation.
