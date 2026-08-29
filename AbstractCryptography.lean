/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import AbstractCryptography.Categorical.ResourceAlgebra.ConstructorClass
import AbstractCryptography.Categorical.ResourceAlgebra.ConverterTuple
import AbstractCryptography.Categorical.ResourceAlgebra.CostBounded
import AbstractCryptography.Categorical.ResourceAlgebra.Endomorphism
import AbstractCryptography.Categorical.ResourceAlgebra.Filtered
import AbstractCryptography.Categorical.ResourceAlgebra.Outbound
import AbstractCryptography.Tactics.ProofAutomation
import AbstractCryptography.Tactics.ControlledNaturalLanguage

/-!
# Abstract Cryptography

This is the MR16-track, carrier-independent theory. It exports one
interface-indexed presentation, centered on
`AbstractCryptography.Categorical.ResourceAlgebra`.

For a category `C` of interfaces and converters and a contravariant functor
`Phi : Cᵒᵖ ⥤ Type` of resources, `ResourceAlgebra C Phi` supplies:

* ordered parallel composition of interfaces and converters;
* the corresponding ordered parallel operation on resources;
* attachment as the functor action `Phi.map`;
* a pseudo-emetric on every resource fibre;
* non-expansion of attachment and parallel composition.

Maurer--Renner 2016, Section 3.3 (printed p. 7), says that a converter
“induces a function `Φ → Φ`” and states
“`(β ◦ α)ⁱR = βⁱ(αⁱR)`.” In the interface-indexed presentation these are
respectively
the functor map and its composition law. An endomorphism at one interface is
therefore a specialization of that theory, not a second algebra.

Specifications are sets in one resource fibre. Exact construction is image
inclusion under attachment; approximate construction uses the fibre distance.
The exported modules prove identity, serial composition, ordered parallel
composition, finite converter tuples, scalar relaxation, star closure,
filtered and outbound specifications, admitted converter classes, and
cost-bounded subclasses.

The ordered tensor does not assert symmetry. Concrete carriers may provide an
explicit routing equivalence, and may prove commutation for attachments at
disjoint interfaces. This matches Jost's interface-indexed treatment: his
local connection and commutation results are concrete consequences, not a
generic symmetric-monoidal axiom. Liu's homogeneous endomorphism presentation
is recovered by fixing one interface through
`Categorical.ResourceAlgebra.Endomorphism`.

`RandomSystems` owns fixed-interface DDS, DDE, and PDS mathematics.
`RandomSystems.Converter` owns the concrete DDC category, and
`RandomSystemsCC` installs the single selected `ResourceAlgebra` instance.
None of those concrete modules is imported here.

`AbstractCryptography.Tactics.ProofAutomation` and
`AbstractCryptography.Tactics.ControlledNaturalLanguage` are deterministic
frontends over this same interface-indexed surface; they introduce no
additional theory.

The systematic public setup is:

```lean
import AbstractCryptography
open AbstractCryptography
open scoped AbstractCryptography
```

This makes both the scoped notation and the `ac_*` proof commands available.
A narrow file may instead import `AbstractCryptography.Tactics.ProofAutomation` with
the same two `open` commands.

Controlled-language sentences are opt-in even through the public root:

```lean
open scoped CryptoControlledNaturalLanguage
```

`AbstractCryptography.EventAlgebra` is **not a rung of this ladder.**  It is
GegMau26, an orthogonal axis: §1.4 says event algebras are "a priori
incomparable to the abstract theory of systems of [MauRen11]; the two
theories are compatible on a more concrete level (satisfying both sets
of axioms)."  A concrete interaction instantiates both.
-/
