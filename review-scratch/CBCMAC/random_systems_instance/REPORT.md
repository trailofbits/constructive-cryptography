# Random Systems as the abstract resource/converter instance

## Result

The experiment succeeded without changing the repository.

Four scratch files compile against the repository's real dependencies:

- `TypedCategoryInstance.lean`: actual valid Random Systems DDC programs
  compose heterogeneously with `*` and act directly on typed PDS resources
  with `•`.  The serial action law is proved once from the existing
  `Converter.apply_toDDC_comp` theorem.
- `HomogeneousACInstance.lean`: at one fixed signature, `Phi` is literally
  `PDS X Y`, and `DDC` is a free monoid over valid concrete DDC programs.
  The abstract `Monoid` and `MulAction` requirements are inherited, and both
  `cbcDDC bf * cbcDDC bg` and `cbcDDC bf • Rnn X` compile.
- `UniversalACInstance.lean`: at the actual top-level universal carrier,
  `Phi` is `RandomSystems.Phi = PDS Uni Uni`; `SigmaDDC` is a free monoid over
  valid universal-alphabet DDC programs, not a subtype of `Phi → Phi`.
  A single action instance makes the following compile directly:

  ```lean
  cbcDDC bf • Rnn X
  cbcDDC bf * cbcDDC bf
  ```

  The same file defines `SigmaPDC` as free serial syntax over concrete PDC
  laws and compiles direct PDC composition and PDC-on-PDS application.
- `ProbabilisticInstance.lean`: typed CR18 PDCs are literally distributions
  over valid DDC programs.  Independent product plus pushforward supplies
  PDC composition and PDC-on-PDS application once, after which `*` and `•`
  work directly.

Compilation commands, all successful:

```text
lake env lean .../TypedCategoryInstance.lean
lake env lean .../HomogeneousACInstance.lean
lake env lean .../UniversalACInstance.lean
lake env lean .../ProbabilisticInstance.lean
```

## Existing definitions that already support this design

The repository already contains most of the desired lower-level model:

- `RandomSystems/Converter/Converter.lean:67`: `Converter.DDC U V X Y` is
  genuinely a Random Systems DDS at the converter alphabets.
- `RandomSystems/Converter/Converter.lean:211`: `Converter.DDC.apply` applies
  a concrete DDC directly to a DDS.
- `RandomSystems/System/ProbabilisticSystem.lean:108`: `PDS.applyLaw` lifts
  deterministic DDC application to PDS by pushforward.
- `RandomSystems/System/ProbabilisticSystem.lean:133`: `PDS.Protocol X Y` is
  already a free monoid over valid concrete converter programs.
- `RandomSystems/System/ProbabilisticSystem.lean:139` and `:143`: its action
  homomorphism and `MulAction` instance already interpret the concrete
  programs once at the model boundary.
- `RandomSystems/Converter/Cascade.lean:2945`: `apply_toDDC_comp` is the
  deterministic serial action law.
- `RandomSystems/Converter/Cascade.lean:3414`:
  `serial_composition_is_ddc` proves closure of valid DDC programs.
- `RandomSystems/System/Phi.lean:56`: the universal carrier is already
  `PDS Uni Uni`; `ofTyped` and its coercion are at lines 325 and 329.
- `RandomSystems/System/ProbabilisticConverter.lean:75`: a PDC is already a
  law over deterministic engine systems; `attachLawAt` at line 89 is the
  independent-product/pushforward interpretation needed for PDC action.

Thus the core problem is not absence of DDC/PDC objects or application.  It is
that the newer universal/CBC-facing API bypasses this typed converter layer
and exposes the semantic image as the converter carrier.

## Why there are two honest algebraic presentations

### Typed signatures: a category, not one monoid

A DDC has four alphabets:

```text
DDC U V X Y : converts PDS X Y into PDS U V
```

Consequently, signature-changing DDCs compose only when the middle signatures
match.  They form a category/typed algebra:

```text
DDC W Z U V × DDC U V X Y → DDC W Z X Y
DDC U V X Y × PDS X Y       → PDS U V
```

Lean's `HMul` and `HSMul` express this directly, and the typed scratch file
does so.  A single ordinary `Monoid Sigma` cannot express the changing source
and target indices without first fixing a signature, moving to `Uni`, or
changing the abstract interface from a monoid action to a categorical action.

### Abstract AC surface: one homogeneous monoid action

The present abstract layer requires `[Monoid Sigma] [MulAction Sigma Phi]`.
For that surface, the smallest faithful Random Systems instance is:

```text
Phi      := PDS Uni Uni
DDCAtom  := {nu : ProtocolFn Uni Uni Uni Uni // IsDDC nu}
SigmaDDC := FreeMonoid DDCAtom
```

`SigmaDDC` remains concrete converter syntax; it is not an endomorphism
subtype.  Only the `MulAction` implementation interprets the syntax on `Phi`.
The free monoid provides exact identity and associativity required by the
abstract layer, while keeping concrete DDCs as its atoms.

This choice is not cosmetic.  The repository itself documents counterexamples
to raw equality laws for protocol functions: off-trace junk prevents using raw
DDCs directly as an equality-level monoid.  There are two principled repairs:

1. free serial syntax over valid DDC atoms (the compiled prototype and the
   existing `PDS.Protocol` approach); or
2. quotient valid DDCs by trace/action equivalence, then prove composition and
   application descend to the quotient.

The first is the smallest change.  The second better supports paper-level
equality of composed converters but is a larger proof project.

## PDC variant and the paper's `Sigma`

CR18 Definition 3.17's PDC is a distribution over DDCs.  In the scratch model:

```text
PDCAtom  := Distribution DDCAtom
SigmaPDC := FreeMonoid PDCAtom
```

A PDC letter acts on a PDS by sampling the PDC and resource independently and
pushing their product law through deterministic DDC application.  A DDC enters
this probabilistic converter class as a point mass.  This is the variant that
matches a top-level `Sigma` intended to include probabilistic converters.
`SigmaDDC` is its deterministic sublanguage.

Typed PDCs also compose directly by independent product and pushforward, as
shown in `ProbabilisticInstance.lean`.  As with raw DDCs, making raw PDC values
themselves an exact homogeneous monoid requires either quotient laws or free
serial syntax.  The universal prototype uses free syntax so the abstract laws
are immediate and the PDC data remain primary.

## Required repository changes

1. Introduce one public Random Systems instantiation module defining the
   abstract carrier and converter carrier, preferably the universal free
   syntax design above (or the larger trace quotient design).
2. Install the `MulAction` once using the existing DDC/PDC application:
   `PDS.applyLaw` for deterministic atoms and the existing
   product/pushforward construction (`attachLawAt`) for probabilistic atoms.
3. Define CBC's operational object as a valid `ProtocolFn M X X X`/DDC (or
   provide a one-time bridge from `cbcRound`/`converterEngine` to that object).
   Reuse `cbcRound_innerTotal` and `cbcRound_requestsBounded` to discharge the
   corresponding validity/finite-query obligations.
4. Make the public `cbcDDC` an element of the selected concrete `Sigma` at its
   definition boundary.  Then CBC statements use `cbcDDC bf • Rnn X` directly.
5. Define public `Rnn` and `Vn` in the selected `Phi`; keep `ofTyped` inside
   those definitions.  Typed counting lemmas can continue using private or
   explicitly named typed versions.
6. Re-express filters, blocking, parallel frames, and simulators as concrete
   DDC/PDC atoms or as explicit constructors in the free converter syntax.
   Do not reintroduce arbitrary endomorphisms as the public converter type.
7. Move the existing non-expansion proofs from membership in
   `converterMonoidAt` to generator lemmas, then extend them by free-monoid
   induction.  The mathematical absorption arguments are reusable; only the
   carrier of the proof changes.

After this, `Applications/CBCMAC.lean` should no longer construct:

```text
attachAt ... (converterEngine ...) : Phi → Phi
⟨..., proof of membership in converterMonoidAt⟩
```

at lines 375–378.  That interpretation/package belongs in the Random Systems
instance, not in an application.

## Remaining blockers and design decisions

- **Exact converter equality.** Free words give exact monoid laws but retain
  syntactically different words with the same behavior.  If the theory needs
  converter equality rather than action equality, use the trace/action
  quotient instead.
- **Signature preservation.** `Phi = PDS Uni Uni` forgets intended typed
  signatures.  The existing `TypedAt X Y` specifications must remain the
  applicability discipline, and each typed converter needs a theorem mapping
  its input `TypedAt` to its output `TypedAt`.
- **`Phi` as a literal dependent sum.** `Sigma X, Sigma Y, PDS X Y` retains
  the signature as data, but signature-changing converters then act
  heterogeneously; it cannot support the current ordinary `MulAction` without
  changing the abstract layer.  `PDS Uni Uni` is therefore the practical
  homogeneous carrier, while the dependent-sum view is the indexed model.
- **Non-DDC converter families.** The present `converterMonoidAt` contains
  filter and parallel-frame generators as well as engine attachment.  Each
  must either be realized as an actual DDC/PDC or represented as a separate
  concrete syntax constructor with a proved interpretation.
- **Probability side conditions.** PDC action on a signed distribution is
  definable, but probability/non-negativity and non-expansion require the
  existing support and weight hypotheses.
- **Universes.** `Uni.{u} : Type (u+1)`, so universal `Phi`, DDC atoms, and
  PDC atoms live in `Type (u+1)`.  The scratch files compile at that level.
  Cross-universe alphabets would require lifts or a fixed universe policy.

## Recommendation

Use the universal free-concrete model as the first repository change:

```text
Phi      = PDS Uni Uni
SigmaDDC = FreeMonoid valid-universal-DDC
SigmaPDC = FreeMonoid (Distribution valid-universal-DDC)
```

Install their actions once, hide typed inclusion inside named resource and
converter definitions, and make CBC consume only `*` and `•`.  In parallel,
retain the typed `HMul`/`HSMul` interface for proofs that naturally change
signatures.  Consider a trace/action quotient later only if paper-level
converter equality cannot be stated adequately through the free syntax and
its interpreted action.
