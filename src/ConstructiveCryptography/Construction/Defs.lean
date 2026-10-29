import Mathlib.Data.Set.Defs

set_option autoImplicit false

/-!
# Constructor-indexed judgments

MR16, Section 2.1, writes `R —γ→ S` for “constructor `γ` constructs `S` from `R`”, and
`R → S` for “some constructor in a chosen set `Γ` (Gamma) does so”. This module keeps that
statement abstract. A construction judgment is any predicate

```text
judgment : Constructor → Source → Target → Prop
judgment γ R S   reads   R —γ→ S     (γ builds the target S from the source R)
```

with no structure assumed on the carriers. `Constructible judgment constructors R S` is MR16's
`R → S` relative to `Γ = constructors`, and `Unconstructible` is its negation `R ↛ S`. The
laws relating these predicates are in `ConstructiveCryptography.Construction.Basic`.
-/

namespace ConstructiveCryptography.Construction

universe u v w

variable
    -- `Constructor` is the type of candidate constructors `γ`; it is opaque here, with no
    -- composition, identity or efficiency assumed.
    {Constructor : Type u}
    -- `Source` contains the objects `R` constructed from; `Target` contains the objects `S`
    -- constructed. The two types may differ.
    {Source : Type v} {Target : Type w}

/-- Existence of an admitted constructor satisfying the construction judgment:

```text
Constructible judgment Γ R S  :⇔  ∃ γ ∈ Γ, judgment γ R S        (MR16: R → S)
```

MR16, Section 2.1 (printed p. 4): “Typically one considers a certain set Γ of
constructors, possibly restricted in terms of efficiency or implementation cost.”
Jost, Section 2.2.2 (printed p. 17), instead keeps converters explicit; a
constructor class is an optional restriction of that presentation. -/
def Constructible
    -- `judgment γ R S` is the statement “`γ : Constructor` constructs `S : Target` from
    -- `R : Source`”, MR16's `R —γ→ S`.
    (judgment : Constructor → Source → Target → Prop)
    -- `constructors` is MR16's Γ (Gamma), the admitted subset of `Constructor`, possibly empty
    -- (then the predicate is false); efficiency enters only through the caller's choice of Γ.
    (constructors : Set Constructor)
    -- `source : Source` is `R` and `target : Target` is `S`; the witnessing `γ` need not be
    -- unique.
    (source : Source) (target : Target) : Prop :=
  ∃ constructor ∈ constructors, judgment constructor source target

/-- Non-constructibility within a selected constructor class: no admitted `γ ∈ constructors`
satisfies `judgment γ source target`. A constructor outside `Γ` may still satisfy it.

MR16, Section 2.1 (printed p. 4): “R ↛ S :⇐⇒ ¬∃ γ ∈ Γ : R —γ→ S.” -/
def Unconstructible
    -- `judgment γ R S` reads `R —γ→ S`, as in `Constructible`.
    (judgment : Constructor → Source → Target → Prop)
    -- `constructors` is the admitted class Γ (Gamma); constructors outside it are ignored.
    (constructors : Set Constructor)
    -- `source : Source` is `R` and `target : Target` is `S`, claimed unconstructible from `R`.
    (source : Source) (target : Target) : Prop :=
  ¬ Constructible judgment constructors source target

end ConstructiveCryptography.Construction
