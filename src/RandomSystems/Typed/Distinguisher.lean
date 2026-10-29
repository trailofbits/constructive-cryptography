import RandomSystems.Typed.Interface
import RandomSystems.Distance.Distinguisher

/-!
# Typed distinguishers and absorption

A typed distinguisher on interface `A` is the decision behavior of a stopping distinguisher
compatible with `A`'s domain: the map `R ↦ Pr[d(R) = 1]` on typed systems.
`TypedDistinguisher A` abbreviates the existing `A.inputDomain.DistinguisherBehavior`; it adds
no carrier and no equivalence. Absorbing a typed converter `α : TypedConverter A B` gives a
distinguisher on `B`:

```text
dα ── R   =   d ── α ── R          (dα)(R) = d(αR)
```

## Main definitions

* `TypedDistinguisher A`: compatible stopping decision behaviors on `A`
* `TypedDistinguisher.absorb d α`: the distinguisher `dα` on `B`

## Main results

* `TypedDistinguisher.probability_absorb`: `(dα)(R) = d(αR)`, by definition
* `TypedDistinguisher.absorb_id`, `TypedDistinguisher.absorb_comp`: absorbing the identity
  leaves `d` unchanged, and `d(αβ) = (dα)β` for `αβ = TypedConverter.comp α β`; both follow from
  the identity and serial attachment laws

These laws are about the action only; a selected subset of typed distinguishers need not be
closed under absorption.
-/

namespace SystemAlgebra

/-- The output-1 behavior `R ↦ Pr[d(R) = 1]` of a stopping distinguisher compatible with the
input domain of interface `A`. -/
abbrev TypedDistinguisher (A : Interface) := A.inputDomain.DistinguisherBehavior

namespace TypedDistinguisher

/-- Absorb `α : TypedConverter A B` into `d` on `A`: the distinguisher `dα` on `B` that runs
`d` on `α` attached to the tested system, `(dα)(R) = d(αR)`. -/
noncomputable def absorb {A B : Interface} (d : TypedDistinguisher A)
    (α : TypedConverter A B) : TypedDistinguisher B :=
  Domain.DistinguisherBehavior.absorb B.nonempty_prefix A.nonempty_prefix α d

/-- Absorption leaves the probability of the connected experiment unchanged:
`(dα)(R) = d(αR)`. -/
lemma probability_absorb {A B : Interface} (d : TypedDistinguisher A)
    (α : TypedConverter A B) (R : TypedSystem B) :
    (absorb d α).1 R = d.1 (α • R) := rfl

/-- Absorbing the identity leaves the decision behavior unchanged, since `𝟙 • R = R`. -/
lemma absorb_id {A : Interface} (d : TypedDistinguisher A) :
    absorb d (TypedConverter.id A) = d := by
  apply Subtype.ext
  funext R
  exact congrArg d.1 (TypedConverter.identity_attach R)

/-- Serial absorption retains physical order: `d(αβ) = (dα)β` for
`αβ = TypedConverter.comp α β`, where `α` sits next to `d` and `β` next to the tested system. -/
lemma absorb_comp {A B C : Interface} (d : TypedDistinguisher A)
    (α : TypedConverter A B) (β : TypedConverter B C) :
    absorb d (TypedConverter.comp α β) = absorb (absorb d α) β :=
  Domain.DistinguisherBehavior.absorb_comp C.nonempty_prefix A.nonempty_prefix
    B.nonempty_prefix α β d

end TypedDistinguisher

end SystemAlgebra
