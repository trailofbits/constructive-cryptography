# System diagrams

`Rendering` is an optional Lean infoview integration. It derives diagrams from
elaborated Lean expressions and their inferred types. The renderer is independent
of CC theory; the adapters register the declarations whose meanings it displays.
No additional VS Code extension or external rendering service is required.

```lean
import Rendering

-- Show relevant elaborated objects and proof goals at the editor cursor (the default):
set_option cc.diagram.auto true

-- Optional explicit views accept a system, converter, proposition, or applied theorem:
#cc_diagram_show c • (d • R)
#cc_diagram_show ResourceTheory.attach_serial c d R
#cc_diagram_show distance (c • R) S ≤ ε

-- Export the same view with selectable source text:
#cc_diagram_export c • R to "diagram.html"
```

Move the editor cursor onto a system, converter, interface, or recognized statement to see
its view. Ordinary definitions, references to imported objects, and local variables work;
no `@[cc_diagram]` attribute or `#cc_diagram_show` command is required. Applied terms use the
actual arguments recorded by Lean. A parameterized DSL declaration without a complete
application shows its original pseudocode when available, without choosing argument values.
Unrelated terms and unresolved expressions produce no automatic object view.

Put `set_option cc.diagram.auto false` after the imports to turn automatic views off in that
file. Standard Lean sections and `set_option cc.diagram.auto false in …` also work. Explicit
`#cc_diagram_show` and `#cc_pseudocode_show` commands remain available with automatic views
disabled; they produce only one panel. Automatic calculation navigation takes precedence
inside a `calc`; otherwise a recognized object under the cursor takes precedence over the
surrounding proof goal. Lean's usual goals and diagnostics remain available.

The examples assume the corresponding interfaces, resources, converters and
instances in scope. [Gallery.lean](../Tests/Rendering/Gallery.lean) is a complete,
compilable gallery, including live tactic goals and a navigable `calc` proof.
Import `Rendering.Widget` for the abstract CC adapter alone, or
`Rendering.Instances` for the current interface instances. `Rendering.Export`
adds standalone HTML export. These imports leave the mathematical library unchanged.

## Proof views

`Rendering` also displays registered proof objects at the cursor, using the same
`cc.diagram.auto` option. [ProofGallery.lean](../Tests/Rendering/ProofGallery.lean) contains
complete examples of calculations, implication witnesses and H-coefficient arguments.
[HMethodGallery.lean](../Tests/Rendering/HMethodGallery.lean) is a focused H-coefficient example:
place the cursor on `argument` or on the theorem application to see the corresponding view.

- In a recognized `calc`, arrows and the compact `⋯` overview select a step. Each step retains
  its actual elaborated statement, source link and supplied justification. Open the
  justification to inspect its source. Failed or unfinished proofs show their recorded goals;
  there is no inferred success badge.
- A substitution witness shows each assumption use in its recorded direction, under its actual
  converter. `⇝` means an oriented use of a premise; it does not assert that premise. Endpoint
  and join equalities have a separate disclosure. Repeated assumptions retain separate positions.
  A registered `distance_le` application also shows its actual per-position bounds and proofs;
  budgets are neither identified with multiplicities nor silently added to a bare witness.
- An H-coefficient application draws its actual conclusion using the same system, interface,
  relation and budget components as a `calc` step. Its `H` justification opens one transient
  inspector with the supplied argument, fields and proof. Inside a calculation, this inspector
  belongs to the recorded step; it adds no steps or navigation. A bare argument shows its two
  systems without a relation. Reveals, classes, quantified bounds and signed budget conversions
  remain exact Lean terms in the inspector; no good/bad partition is inferred.

Small literal implication chains have at most twelve displayed positions. Symbolic or larger
chains show their actual index binder and parameterized step instead of inventing a finite
list or dropping steps. Only registered witness constructors and finite-index selection reduce;
component definitions and probability laws retain their names. Opaque or cast-dependent fields
remain exact projections in the source inspector. Implication fields also retain their
individual disclosures. No technique is inferred from a
name, a proof's conclusion alone, or an unrelated theorem that happens to mention a witness.

Explicit commands are optional:

```lean
#cc_proof_show chain
#cc_proof_show chain.distance_le errors localBounds
#cc_proof_show Interface.distance_le_of_hCoefficient argument
#cc_proof_export argument to "proof.html"
```

Exports use the same projection, with native disclosures for each position and selectable Lean
text. Infoview views additionally provide Lean hovers and definition navigation. The optional
`Rendering.Proofs` adapter registers existing declarations; `Rendering.ProofView` contains the
presentation engine and does not import CC or systems theory. New upstream contracts need a
checked adapter and tests before they acquire a specialized view.

## DSL pseudocode

DSL components have an expandable label in their diagram. Open it to show the original
declaration in a Penpot-style card, with procedure headings and whitespace between blocks.
Initialization and all procedures stay inside one component, including components with shared
state across several ports. The card wraps into one column in a narrow infoview.

```lean
import Rendering
import Examples.DSL.Components

#cc_pseudocode_show DSLExamples.Arithmetic
#cc_pseudocode_export DSLExamples.Arithmetic to "pseudocode.html"
#cc_diagram_show DSLExamples.BoundedCounter 7 (budget := 2)
```

The card labeled `Declaration` shows parameters **as declared**. The diagram label still
shows the applied term; opening it does not substitute arguments into pseudocode. Source
keywords, types, calls, sampling laws, assignments, conditions, loops, matches, comments,
requirements and domains remain literal DSL text. Explicit trailing proofs are available
under `by`, and `Lean` exposes the complete original declaration for selection and copying.
Interface declarations, filters and `system Name ≔ expression` also have source views.
An assembly is displayed as its written expression, without inventing a procedural body.

The compiler records exact source slices at parser boundaries after checking for elaboration
errors. The metadata travels with the compiled module, so the viewer never reads a possibly
stale source file or decompiles a generated function. Concatenating the slices recovers the
source byte for byte. Synthetic commands without original tokens get no source record.
Ordinary Lean aliases and generated helpers such as `.program`, `.perPort` and `.exact` remain
opaque. Explicit pseudocode commands report missing metadata rather than guessing a body;
modules compiled before source recording was added need rebuilding. Source availability is
not a proof-status indicator; Lean's diagnostics remain authoritative.

## Reading a diagram

Blue rectangles denote resources. Rounded green boxes denote converters. Double
borders denote specifications. Thin undirected lines denote attachment at the
interface written beside them. Each wire joins two components; exposed ports
use type labels without wire stubs. Parallel groups have one continuous frame;
nested groups retain their order and brackets. A serial converter group retains
the order of `≫`. Both sides of a comparison expose ports in the same orientation.
Unknown subterms remain literal Lean text, with their full inferred type in the
tooltip. `Lean` reveals the complete, selectable original expression. Aggregate
interface labels are shown on connections; branch labels identify the individual
interfaces inside a parallel group. Operator labels sit inside the group frame.

Object and interface names use Lean's native hover information, including explicit
`#cc_diagram_show` commands and display aliases. Ctrl/Cmd-click or the context menu's
`Go to Definition` follows the actual Lean object. The `ⓘ` beside an interface opens its
type information. For the concrete `Interface` adapter this includes labels `I`, query and
reply alphabets `X`, `Y`, and the exact history predicate `D`. Converters expose both their
outside and inside interfaces. Hover opens a temporary preview; leaving it closes it promptly,
even after a single click. Double-click `ⓘ` to pin it. Click empty space, press Escape, or use
`×` to dismiss it. Tab opens a keyboard preview; Enter or Space pins it. Only one inspector is
visible at a time, and a pin is not replaced by merely hovering another trigger. Its underlined
trigger identifies its origin; the title retains the interface name. Changing the inspected
object or moving focus out of the infoview also dismisses it. It sits outside the diagram layout, so
connections stay attached when information opens.

The inspector and its **Port / Query / Reply** table size themselves to their contents, with
viewport limits and wrapping for long types. Opening the source may grow the popover; closing
it restores the compact view. Literal enum labels get one row
per declared constructor, with query and reply types computed from their alphabet projections.
This replaces implementation lambdas and matches with their actual values. Other label types
use the symbolic row `i ∈ I`, `X(i)`, `Y(i)`; each entry retains its original Lean hover.
Empty enumeration types show `Ports ∅`. No `Fintype` is evaluated to invent a port list. An
abstract category object has only its actual type; it acquires no concrete alphabets or domain.
Expanded interface constructors (query budgets, per-port budgets and anonymous records) show
only `ⓘ` at their boundary. Their ports, types, domains and complete expressions remain in the
inspector. Named interfaces and abstract labels stay visible; no system name is invented for
an unnamed interface. Standalone exports bundle the same small interaction controller without
external dependencies; with scripting disabled, native disclosures retain all fields. Lean hovers and
source navigation operate in the infoview.

Query and reply types use familiar notation for exact core constructors:

| Lean type | Display |
| --- | --- |
| `Nat`, `Int`, `Bool` | `ℕ`, `ℤ`, `𝔹` |
| `Unit`, `PUnit` | `{⋆}` |
| `Empty`, `PEmpty`, `Fin 0` | `∅` |
| `Fin 1`, `Fin 2`, `Fin 16` | `{0}`, `{0,1}`, `{0,…,15}` |
| `Prod A B`, `Sum A B`, `A → B` | `A × B`, `A ⊕ B`, `A → B` |

These are display abbreviations; the original Lean types remain distinct and inspectable.
Nested symbols have individual native hovers; an operator's hover shows the full original type.
Parentheses preserve grouping. Named alphabets, dependent function types, symbolic `Fin` bounds
and unknown types keep their Lean spelling. Numeral bounds are checked against their actual
selected `OfNat` instance before displaying a finite range. No algebraic structure is inferred.

Domains use set notation, for example `{ h | h ≠ ε ∧ |h| ≤ 3 }`. Here `ε` is the empty history
and `|h|` its length; the notation has a tooltip and the exact predicate remains under `Lean`.
This printer recognizes core expression constructors, beta-reduces literal function applications,
and preserves connective scope and every restriction. It performs no logical simplification.
Unsupported syntax keeps Lean's printer. The source disclosure retains full alphabet functions,
interface types and the original domain predicate without repeating them beside the table.

For `c : A ⟶ B`, `d : B ⟶ D` and `R : Phi D`, the chain is
`A  c —[B]— d —[D]— R`. The converter nearest `R` attaches first. An abstract
interface is not a query direction or a list of parties. Labels such as
`simulator`, `Eve`, or `adversary` do not confer a semantic role.

Native MathML typesets identifiers and registered interface tensors. Arbitrary
Lean syntax remains literal text; it is never interpreted as LaTeX, HTML, or
JavaScript. Container queries adapt to the infoview's width: comparisons stack,
then chains turn vertically. Large expressions retain local horizontal scrolling
and selectable text. Light, dark, and forced-color themes share the same tree.
Vertical labels sit beside continuous wires. Construction arrows carry the
converter and error as `π; ε`; calculation navigation uses `1 / n` and `↗`.

## Interpretation contract

A diagram displays expression structure, not proof status. Lean's diagnostics
remain the authority for whether a statement has been proved. Only fully applied,
explicitly registered declarations are decomposed. The projection performs no
algebraic rewriting, definition unfolding, reassociation, commutation, inferred
simulation, or probability simplification. In particular:

- `(c ≫ d) • R` and `c • (d • R)` have distinct trees, related only when the
  displayed Lean expression contains their equality.
- `(c ⊗ₘ d) • (R ∥ S)` retains its tensor and parallel groups.
- `Δ R S = 0` remains a distance equation. It does not become `R = S`.
- `=`, `≤`, and `<`, scalar budgets, infinity, sums, and specification relaxations
  remain exactly as supplied. No error is truncated or silently added.
- Quantified statements retain their full source under `Lean`. Existential witnesses
  are never chosen. Unrecognized goals leave the ordinary infoview in place;
  explicit check/show/export commands report an unrecognized expression.
- Abstract resources require the explicit `ResourceTheory` capability. A
  categorical arrow must use that capability's selected category. Concrete arrow
  types may reduce through their selected instance to a registered converter type;
  the source expression itself is never unfolded.
- Registered interface projections may reduce by definitional computation to expose their
  values. Domain conditions and both query limits remain intact. There is no theorem rewriting,
  history enumeration or inference from names. Unknown label carriers stay symbolic.
- A recursion limit leaves the complete remaining subterm visible.

The semantic adapters are the trust boundary: registration asserts an operation's
meaning and must be reviewed against its live declaration and documentation.
The renderer checks declaration existence, full application and argument positions;
it cannot prove that an incorrectly registered operation has the intended meaning.
Current registrations follow [the CC algebra](../ConstructiveCryptography/README.md)
and [its interface instances](../../THEORY.md#interface-instance-table).

## Labels and extension

Registered identity converters display `𝟙`. The interface argument remains in the
interface inspector and the original Lean expression; the identity node is never removed.

Authors can name declarations or specific applied terms:

```lean
attribute [cc_diagram "BC"] DSLExamples.BoundedCounter
-- BoundedCounter 7 is labeled BC 7; printed arguments are retained.

cc_diagram_name "Counter₃" := DSLExamples.Counter (budget := 3)
-- Only this exact application is named; budget 4 keeps its ordinary label.

section
local cc_diagram_name "WT₃" := DSLExamples.WriteThrough (budget := 3)
#cc_diagram_show DSLExamples.WriteThrough (budget := 3)
end
```

Declaration nicknames match resolved constant names, never suffixes. The nickname replaces only
the printed head, preserving Lean's argument printing. `cc_diagram_name` matches an exact closed,
fully elaborated expression, including implicit arguments; it does not unfold aliases or match
definitionally equal terms such as `3` and `3 + 0`. Later names for the same expression take
precedence; `local` restores the previous name at the end of the section. Open expressions with
local variables or unresolved types are rejected. Global names persist through imports.

Both forms apply to component and interface labels. An explicit interface name remains visible
beside `ⓘ`. Named compositions show their name on the group and keep their component structure
and connections. The full Lean expression, types, source navigation and original DSL pseudocode
are preserved. Display strings are plain text, never executable markup.

Add semantic roles at an optional adapter boundary. Use resolved declaration
names and argument positions counted from the end (`0` is the final argument).
Each role needs a visible purpose, a positive test, an unrelated negative case,
source-position checks and a representative rendering. Register concrete carriers
instead of recognizing their pretty-printed names. Add new algebraic laws in their
mathematical owner; visualization never supplies a missing law.

## Scenario matrix

This matrix partitions the supported grammar and its failure boundaries. Lean
terms are unbounded; a finite test suite does not enumerate every possible term.

| Scenario | Required behavior | Check |
|---|---|---|
| Calculation justifications and unfinished tactic blocks | Use the actual proof or recorded remaining goals | Info-tree tests, live infoview |
| Repeated or reversed implication uses | Preserve positions, directions and exact joins | Proof projection tests |
| Symbolic or long implication families | Keep the index binder; do not truncate a list | Proof projection tests, gallery |
| Bare implication versus a bound theorem | Keep premises, multiplicities and supplied errors distinct | Proof projection tests |
| Local H-coefficient parameters and concrete arguments | Shared system diagrams, exact source fields, conclusion only at a registered application | Proof tests, focused H-method gallery |
| Signed and oversized errors; raw systems; cast-dependent fields | Preserve budget conversion, domain and source terms | Proof tests |
| Changed budget or real system | Reject fields inconsistent with the supplied argument | Adversarial proof tests |
| H inside a calculation | Keep the actual number of steps and each supplied justification | Info-tree tests, browser proof-layout checks |
| Narrow H-method panel and transient definitions | Use the shared responsive diagram, dismiss on pointer exit | Browser proof-layout checks |
| Unrelated proof mentioning a witness | No technique classification | Negative proof tests |
| Cursor on a system, converter, interface, theorem or local variable | Use its elaborated expression and context | Info-tree tests, live infoview |
| File, section and command-local automatic options | Read the option at the cursor | Info-tree tests, live infoview |
| Explicit show command with automatic views enabled or disabled | One panel | Info-tree tests, live infoview |
| Unresolved or unrelated cursor term, comments or whitespace | No invented object view | Negative info-tree tests |
| DSL declaration name | Resolve the actual declaration and recorded source | Info-tree tests |
| Nested attachment | Preserve order and each inferred interface | Projection, gallery |
| Serial composition versus nested attachment | Keep distinct syntax trees and exact equality | Projection, gallery, live goal |
| Left/right nested parallel | Keep ordered binary grouping and aggregate tensor | Projection, gallery |
| Tensor converter on a parallel resource | Keep both groups; no distribution | Projection, gallery |
| Identity converters and unit interfaces | Remain visible | Projection, live calculation |
| Repeated converter occurrences | Preserve every occurrence and its source location | Projection, gallery |
| Concrete interface instances | Match the direct system operations and CC notation | Instance tests |
| Exact and approximate construction | Preserve converter, source, target, and error | Projection, gallery |
| Specification maps and relaxations | Preserve map order and both relaxations | Projection |
| Distance `=`, `≤`, `<` | Preserve the comparison operator | Projection |
| Zero, infinity, and arithmetic bounds | Keep the original bound and distance | Projection, gallery |
| Simulator/adversary-like names | Remain ordinary converters | Projection |
| Unrelated multiplication, action, family, category or set | Receive no CC meaning | Negative projection |
| Alternative category on the same object type | Receive no role from the other category | Negative projection |
| Partially applied registered declaration | Remain opaque | Negative projection |
| Unknown application or named definition | Preserve the complete term | Projection |
| Existential statement | Do not fabricate a witness | Negative projection |
| Depth limit | Preserve the entire remaining term | Projection |
| Namespace collisions and display aliases | Use exact names; preserve applied arguments | Projection, label tests |
| Applied-term names and local overrides | Match the exact expression; restore names on scope exit | Label tests, gallery |
| Identity converters | Display `𝟙`; retain interfaces, node and original source | Label tests, gallery |
| Invalid registration indices | Reject missing or duplicate positions | Elaboration guards |
| Repeated projection | Produce identical serialized trees | Projection |
| Every projected node | Resolve to its actual original subexpression | Projection |
| Long identifiers and markup-like text | Wrap safely; never execute markup | Gallery, browser |
| Narrow/wide widths and light/dark/forced colors | Preserve text and order, avoid page overflow | Browser matrix |
| Keyboard collapse and expansion | Preserve content and focusability | Browser matrix |
| Mathematical operators, system bodies and budgets | Share a visual axis; keep relation and bound together when wrapping | Browser matrix, live VS Code |
| Connection endpoints and vertical labels | Join actual components without gaps or obscured strokes | Browser matrix |
| Parallel and serial group frames | Keep uninterrupted boundaries and internal operator labels | Browser matrix |
| Source disclosure | Keep exact selectable Lean available by keyboard | Browser matrix |
| Tactic goals, code hover, calculation navigation | Use actual infoview RPC and source locations | Live VS Code |
| Unrecognized bookkeeping goal | Mark the enclosing statement as `Context` | Live VS Code |
| Static HTML export | Same component tree; escape text, refuse RPC-only components | Export, browser |
| Imported and local DSL declarations | Recover the exact source compiled into the module | Source tests |
| Initialization versus procedure sampling | Preserve scope and explicit sampling laws | Source tests, cards |
| Tuples, reassignment, branches, loops and matches | Preserve syntax, nesting and order | Source tests, cards |
| Named outside ports with shared state | Keep initialization and handlers in one card | Source tests, cards |
| Explicit types, parameters, requirements, domains and proofs | Retain all written clauses | Source tests, cards |
| Applied DSL components | Retain the application and show generic declaration separately | Projection, live view |
| Filters, interfaces and system assemblies | Show only their written source | Source tests, cards |
| Aliases, generated helpers, failed or synthetic declarations | Do not invent pseudocode | Negative source tests |
| Comments, multiline terms, Unicode and markup-like literals | Preserve source and escape markup | Source tests, browser |
| Expanded diagram leaves | Keep real connections attached; support keyboard disclosure | Browser, live view |
| Interfaces, alphabets and domain predicates | Display actual registered projections and their types | Interface tests, live inspector |
| Restricted, aggregate and per-port budgets | Preserve all domain conditions and actual arguments | Interface tests, gallery |
| Enum ports, empty labels and payload-carrying labels | List literal enum constructors only; otherwise stay symbolic | Interface tests |
| Function-valued alphabets | Retain the parentheses in Lean's arrow type | Interface tests, gallery |
| Compact predicate notation | Preserve logical scope, all restrictions and unsupported syntax | Notation tests |
| Alphabet symbols | Match exact type constructors; retain grouping, bounds and source identity | Type notation tests |
| Symbolic alphabet families | Keep `X(i)` and `Y(i)` linked to the actual projections | Interface tests |
| Aliased names and quantified statements | Keep real RPC identity and the correct local context | Interface tests, live hover |
| Interface disclosure | Fit the viewport without moving diagram components | Browser matrix, live popover |
| Hover, double-click pinning, empty-space click and Escape | Keep one inspector; never pin via incidental focus | Native/export lifecycle tests |

The projection tests are in [Widget.lean](../Tests/Rendering/Widget.lean) and
[Instances.lean](../Tests/Rendering/Instances.lean). Run:

```sh
lake build Rendering Tests.Rendering.Widget Tests.Rendering.Instances Tests.Rendering.Gallery
node src/Tests/Rendering/check-layout.cjs
```

The browser check needs Playwright available to Node. Set `CC_CHROME_EXECUTABLE`
to use an existing Chromium executable. It generates the gallery from Lean, tests
280, 320, 460, 480, 760, 800, 1024 and 1440px widths in three themes, and writes
HTML, screenshots and machine-readable results under ignored
`Scratch/CCWidgetVisual/`. It checks content stability, node overlap, label
clipping, page overflow, markup escaping, keyboard disclosure and network silence.
Visually inspect the final rebuilt examples in both standalone HTML and the actual Lean
infoview at narrow and wide widths in light and dark themes. Check the mathematical axis,
interface placement, spacing, wrapping, contrast and connections, then exercise navigation
and disclosures. Repeat this inspection after the last visual edit. Geometry assertions
complement this review; they cannot establish visual quality or test native Lean interactions.

The pseudocode gallery and its source checks are in
[PseudocodeGallery.lean](../Tests/Rendering/PseudocodeGallery.lean) and
[Pseudocode.lean](../Tests/Rendering/Pseudocode.lean). Run
`lake build Tests.Rendering.PseudocodeGallery`, then
`node src/Tests/Rendering/check-pseudocode.cjs` with the same Playwright setup.
This checks the source partition, responsive cards, expanded connections, escaping and
keyboard access in all three themes; artifacts go under `Scratch/CCPseudocodeVisual/`.

[InterfaceGallery.lean](../Tests/Rendering/InterfaceGallery.lean) covers concrete domains,
per-port types, symbolic interfaces and aliases. After building
`Tests.Rendering.InterfaceGallery`, run
`CC_GALLERY=InterfaceGallery.lean node src/Tests/Rendering/check-layout.cjs` to check the same
layout invariants and every interface disclosure across widths and themes. Its artifacts go
under `Scratch/CCInterfaceVisual/`. Check hover, definition navigation and the popover's keyboard
behavior in the live infoview as well.

`node src/Tests/Rendering/check-inspector.cjs` tests the actual inspector JavaScript with the
Lean extension's React runtime. Set `CC_INFOVIEW_DIR` to that extension's
`dist/lean4-infoview` directory, alongside the Playwright/Chromium settings above. It exercises
hover departure, single versus double clicks, keyboard pinning, repeated switching, empty-space
dismissal, context changes and viewport changes in light, dark and forced-color modes. The same
checks run against the native React component, independently loaded copies of that component,
and the standalone controller. Iframe tests cover leaving the view and clicking in the editor.
