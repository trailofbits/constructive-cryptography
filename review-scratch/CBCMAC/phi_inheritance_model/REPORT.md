# Universal-carrier / typed-PDS experiment

## Scope and build

The experiment uses the repository at
`/Users/marcilunga/Documents/tob/research/abstract-crypto` and Lean 4.29.0.
No repository, dependency, or project file was changed.

The smallest imports used for the real carrier experiment are:

```lean
import RandomSystems.System.RandomObjects
import RandomSystems.System.AttachEngineFully
```

They provide the real definitions needed here:

- `PDS X Y := Distribution (System.DDS X Y)`;
- `Uni := Σ X : Type u, X`;
- `Phi := PDS Uni Uni`;
- `RandomSystems.ofTyped : PDS X Y → Phi` and its `CoeTC` instance;
- `PDS.urf` for the typed `Vn` test object;
- `converterMonoidAt`, whose subtype already acts homogeneously on `Phi`.

`ExactCBCSyntax.lean` imports `Applications.CBCMAC` and checks the exact real
expression rather than toy names.

Both files compile successfully with:

```text
lake env lean .../Prototype.lean
lake env lean .../ExactCBCSyntax.lean
```

## What the current representation actually is

The current `Phi` is **not definitionally a dependent sum** of `PDS X Y`.
It is the full, larger space `PDS Uni Uni`.  A universal DDS may accept mixed
type tags in one history and may emit different tags; such a behavior need not
be the image of any single `PDS X Y` under `ofTyped`.

The literal untagged union/image is already separately defined in
`RandomSystems/System/Phi.lean` as:

```lean
typed : Set Phi := ⋃ X Y, TypedAt X Y
```

Thus:

- `Phi` is the universal ambient behavior space;
- `typed` is the untagged union of all canonical typed images inside it;
- `ofTyped` is the canonical inclusion of one typed fiber into the ambient
  space.

`ofTyped` is injective for a fixed signature (proved in `ParFace.lean`).  Across
different signatures the image need not determine a unique signature: for
example, behavior with no accepted queries carries no observable query/output
tags.  The `typed` set intentionally stores only existence of a signature,
whereas a dependent sum stores a chosen signature as data.

## Current failure

The registered coercion works when Lean already has an expected `Phi`:

```lean
thetaToy • (VnTyped M X : Phi)
```

The completely bare expression does not elaborate with the current API:

```lean
thetaToy • VnTyped M X
```

The failure is instance synthesis for `HSMul Sigma (PDS M X) ...`.  A coercion
is not itself an operator instance.  This is also true for a genuine Lean
`Subtype`: ambient operator instances are not automatically inherited when
closure and result-type choices are involved.

## Alternative A: family + canonical heterogeneous action

The following local instance compiles:

```lean
instance {M X : Type u} :
    HSMul (↥converterMonoidAt) (PDS M X) Phi where
  hSMul sigma resource := sigma • (resource : Phi)
```

With it, both of these compile:

```lean
theta bf r • Vn M X
thetaToy • (thetaToy • VnTyped M X)
```

`ExactCBCSyntax.lean` verifies the first expression against the actual
`Applications.CBCMAC` definitions.

Properties and limitations:

- This uses the canonical inclusion and exposes exactly the desired syntax.
- The result of the first action is `Phi`; subsequent actions use the existing
  homogeneous `MulAction` on `Phi`.
- It does not claim `PDS M X = Phi` or turn the indexed family into a subtype.
- It is a heterogeneous action, so the typed fiber itself is not a carrier of
  the existing `MulAction`: identity is equality only after inclusion into
  `Phi`.
- It is a very small API completion and does not disturb typed reasoning about
  `PDS M X`.

## Alternative B: universal-first public objects

Defining the public object in the ambient carrier also compiles directly:

```lean
def VnPhi ... : Phi := ofTyped (PDS.urf M X)

example : Phi := thetaToy • VnPhi M X
```

This is the cleanest homogeneous abstract-algebra surface: named resources and
converters already share the carrier `Phi`.  It places `ofTyped` once inside
the object definition.  However, changing the existing `Vn` and `Rnn` this way
would make the many typed lemmas less direct.  A practical version is to keep
typed implementation objects and add `Phi`-facing aliases or paper notation.

## Alternative C1: literal dependent sum

This carrier compiles:

```lean
def TaggedPDS := Σ M : Type u, Σ X : Type u, PDS M X
```

It is a **tagged disjoint union**, not an untagged union.  It retains the input
and output types as data, so identical embedded behavior with two signature
witnesses remains two different elements.

A converter on this carrier must be an endomorphism of the whole dependent sum
and must choose an output signature.  The existing converter is only an
endomorphism of `Phi`; after acting on an embedded resource, it generally does
not supply a small typed output witness.  Universal converter composition and
parallel/interface attachment can also create mixed-tag behavior.  Therefore
the existing converter monoid cannot be transferred to this carrier merely by
coercion.  Doing so would require redesigning converters as signature-indexed
dependent morphisms and would no longer model the current universal
endomorphism monoid directly.

There is also a universe issue: the canonical fallback output signature
`(Uni, Uni)` lives one universe above the `Type u` fibers being summed, so an
arbitrary universal result cannot simply be repackaged in the same dependent
sum without enlarging the hierarchy.

## Alternative C2: literal untagged image/subtype

This carrier also compiles:

```lean
def ImagePhi := {R : Phi // R ∈ typed}
```

It is the literal untagged union/image: signature is a proposition, not stored
data.  But an ambient converter acts on it only after proving closure:

```lean
structure ImageConverter where
  toFun : Phi → Phi
  preserves_typed : ∀ R ∈ typed, toFun R ∈ typed
```

For the CBC `theta` filter, a closure proof is available in substance from the
existing `filterDom_ofTyped` / `theta_smul_ofTyped` crossing.  It is not a
property of arbitrary `converterMonoidAt` elements: attachment and parallel
framing are designed to produce general universal, potentially multi-interface
behavior.  Consequently `ImagePhi` is too small to replace the current
abstract carrier without restricting/redesigning the converter monoid.

## Recommendation

Keep the current universal ambient carrier.  The smallest principled API
change is to add the canonical heterogeneous action from every small typed PDS
fiber to `Phi`, with a reduction theorem stating that it is exactly homogeneous
action after `ofTyped`.  This realizes the intended inclusion at converter use
sites and makes `theta bf r • Vn M X` compile while preserving all existing
typed definitions and proofs.

For the paper-facing layer, optionally also add `Phi`-valued aliases/notation
for `Rnn` and `Vn`.  Do not replace `Phi` by the dependent sum or `typed`
subtype unless the project intends a much larger redesign of converter
signatures, composition, parallel attachment, and universe management.
