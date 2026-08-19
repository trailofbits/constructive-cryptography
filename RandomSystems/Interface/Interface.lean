/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.StarFullyDefined

/-!
# Interface roles, and the arbitrary resource at one of them

CR18 §5.3.1 (printed p. 117) types the interfaces of a resource: a **party**
interface, an **adversary** interface, and a third role — the paper's *free*
interface — which models the **environment's own access**, for example the
forwarding trigger of an authenticated channel.  §7.2.1 (printed p. 133) then
uses a device built on the second role: `Φ_E`, the specification of an
*arbitrary* resource at `E`, which is how "we do not care what the constructed
resource gives Eve, including an arbitrarily powerful computer" is said at the
specification level.

Both are addressing, and addressing on this carrier is exogenous (PHI-SPEC R3):
an interface is a set of queries, `Set Uni`.  So a role assignment is three
pairwise-disjoint query sets, and everything below is the algebra those three
sets induce on the *landed* converter classes — no new converter object, no new
relaxation machinery.

## The name of the third role

The third role is `environmentInterface`.  It is **not** called a free
interface here: `AbstractCryptography/Algebra/Indexed.lean` already uses "free
interface" for the *exposed interface index type* of a resource (MMPRT18
Definition 3.1), an unrelated concept, and LEDGER FLAG F-4 records the
collision.

## What the roles buy

* `InterfaceRoles.admittedConverters` — the converters that may be attached at
  all: `converterMonoidWithin` the complement of the environment's interface.
  The environment's access is the one place nothing is attached; the protocol
  class (at the party interface) and the simulator class (at the adversary
  interface) both sit inside it, by `converterMonoidWithin_mono`.
* the commutations — a protocol at the party interface commutes with a
  simulator at the adversary interface, and anything admitted commutes with
  anything at the environment's interface — by `commute_converterMonoidWithin`,
  which is `attachAt_comm` lifted along the closures.
* `constructs_PhiAt` — MauRen16 §4.1 Lemma 3 read at the role split: a protocol
  at the party interface carries a construction through `Φ_E`.

`Φ_E` itself is `RandomSystems.PhiAt`, and it is *not* a new object: it is
`Relaxation.star (converterMonoidWithin E)`, whose eliminator
`mem_star_converterMonoidWithin_iff` is restated here as `mem_PhiAt_iff`.
-/

namespace RandomSystems

open AbstractCryptography (Specification Constructs Relaxation)

open scoped AbstractCryptography

universe u

noncomputable section

/-! ## CR18 §5.3.1's interface typing -/

/-- **CR18 §5.3.1's three interface roles**, as query sets (PHI-SPEC R3):
the party interface, the adversary interface, and the environment's own access
— the paper's *free* interface, renamed per LEDGER FLAG F-4.

Only pairwise disjointness is imposed.  The paper types the interfaces of one
resource, so its three sets also cover that resource's interface set; covering
is deliberately not a field, because on this carrier the query universe is
`Uni` and a resource's face is derived from its behaviour
(`RandomSystems.support`) rather than declared. -/
structure InterfaceRoles where
  /-- The honest parties' interface — where a protocol attaches. -/
  partyInterface : Set Uni.{u}
  /-- The adversary's interface — where a simulator attaches, and the `E` of
  §7.2.1's `Φ_E`. -/
  adversaryInterface : Set Uni.{u}
  /-- The environment's own access.  CR18 §5.3.1's *free* interface, renamed
  (FLAG F-4). -/
  environmentInterface : Set Uni.{u}
  /-- The party and adversary interfaces are disjoint. -/
  partyInterface_disjoint_adversaryInterface : Disjoint partyInterface adversaryInterface
  /-- The party and environment interfaces are disjoint. -/
  partyInterface_disjoint_environmentInterface : Disjoint partyInterface environmentInterface
  /-- The adversary and environment interfaces are disjoint. -/
  adversaryInterface_disjoint_environmentInterface :
    Disjoint adversaryInterface environmentInterface

namespace InterfaceRoles

variable (I : InterfaceRoles.{u})

/-- **The converters a role assignment admits**: those attached anywhere except
the environment's own access.

MauRen16 §3.4's class `converterMonoidWithin A` is "the admitted converters at
`A`"; the role split says which `A` that may be.  The environment's interface
is the one the protocol and the simulator must both leave alone — it is the
distinguisher's, not theirs — so the admitted class is the class at its
complement, and both the protocol class and the simulator class lie inside
it. -/
def admittedConverters : Submonoid ↥converterMonoidAt.{u} :=
  converterMonoidWithin I.environmentInterfaceᶜ

theorem admittedConverters_eq :
    I.admittedConverters = converterMonoidWithin I.environmentInterfaceᶜ := rfl

/-- The protocol class is admitted: the party interface misses the
environment's. -/
theorem converterMonoidWithin_partyInterface_le_admittedConverters :
    converterMonoidWithin I.partyInterface ≤ I.admittedConverters :=
  converterMonoidWithin_mono
    (Set.subset_compl_iff_disjoint_right.mpr I.partyInterface_disjoint_environmentInterface)

/-- The simulator class is admitted: the adversary interface misses the
environment's. -/
theorem converterMonoidWithin_adversaryInterface_le_admittedConverters :
    converterMonoidWithin I.adversaryInterface ≤ I.admittedConverters :=
  converterMonoidWithin_mono
    (Set.subset_compl_iff_disjoint_right.mpr I.adversaryInterface_disjoint_environmentInterface)

/-! ### The commutations the roles supply

MauRen16 §3.3's `(αR)β = α(Rβ)` needs disjoint interfaces and confined
requests; the role split is exactly a supply of disjointness, so each of these
is `commute_converterMonoidWithin` at one field. -/

/-- A protocol at the party interface commutes with a simulator at the
adversary interface. -/
theorem commute_partyInterface_adversaryInterface
    {π β : ↥converterMonoidAt.{u}} (hπ : π ∈ converterMonoidWithin I.partyInterface)
    (hβ : β ∈ converterMonoidWithin I.adversaryInterface) : π * β = β * π :=
  commute_converterMonoidWithin I.partyInterface_disjoint_adversaryInterface hπ hβ

/-- Everything admitted commutes with everything at the environment's own
access: no admitted converter is attached there, so the two never meet.  The
disjointness is `disjoint_compl_left` and costs no field. -/
theorem commute_admittedConverters_environmentInterface
    {π β : ↥converterMonoidAt.{u}} (hπ : π ∈ I.admittedConverters)
    (hβ : β ∈ converterMonoidWithin I.environmentInterface) : π * β = β * π :=
  commute_converterMonoidWithin disjoint_compl_left hπ hβ

end InterfaceRoles

/-! ## CR18 §7.2.1's `Φ_E` -/

/-- **CR18 §7.2.1's `Φ_E`** — the arbitrary resource at the interface `E`,
as a relaxation: `Φ_E 𝓢` is `𝓢` with an arbitrary admitted converter at `E`
attached, which is what "we do not care what the constructed resource gives
Eve" says about a specification.

It is `Relaxation.star` at MauRen16 §3.4's class `converterMonoidWithin E`, and
so is not a new object: every `∗` fact of `StarFullyDefined.lean` is a `Φ_E`
fact.  The name exists because the source uses the device by name and the
`∗`-relaxation is written at a class, not at an interface. -/
def PhiAt (E : Set Uni.{u}) : Relaxation Phi.{u} :=
  Relaxation.star (converterMonoidWithin E)

theorem PhiAt_eq_star (E : Set Uni.{u}) :
    PhiAt E = (Relaxation.star (converterMonoidWithin E) : Relaxation Phi.{u}) := rfl

/-- The eliminator, cross-referenced: `mem_star_converterMonoidWithin_iff` at
`Φ_E`.  A law is an arbitrary resource at `E` over `𝓡` exactly when some
admitted converter at `E`, applied to some law of `𝓡`, produces it. -/
theorem mem_PhiAt_iff {E : Set Uni.{u}} {𝓡 : Specification Phi.{u}} {L : Phi.{u}} :
    L ∈ PhiAt E 𝓡 ↔
      ∃ σ ∈ converterMonoidWithin E, ∃ R ∈ 𝓡, (σ : Function.End Phi.{u}) R = L :=
  mem_star_converterMonoidWithin_iff

/-- `𝓡 ⊆ Φ_E 𝓡` — the device only ever weakens the specification, which is what
makes "we do not care what Eve gets" a sound relaxation.  MauRen16 eq. (1) at
this class. -/
theorem subset_PhiAt (E : Set Uni.{u}) (𝓡 : Specification Phi.{u}) : 𝓡 ⊆ PhiAt E 𝓡 :=
  subset_star_converterMonoidWithin E 𝓡

namespace InterfaceRoles

variable (I : InterfaceRoles.{u})

/-- **MauRen16 §4.1 Lemma 3 at the role split**: a protocol at the party
interface carries a construction through `Φ_E` at the adversary interface —
`𝓡 —π→ 𝓢` gives `Φ_E 𝓡 —π→ Φ_E 𝓢`.

The single premise the abstract theorem spends is that the protocol commute
with the whole class the relaxation ranges over, and the role split supplies it
from one field: `partyInterface_disjoint_adversaryInterface`. -/
theorem constructs_PhiAt {π : ↥converterMonoidAt.{u}}
    (hπ : π ∈ converterMonoidWithin I.partyInterface)
    {𝓡 𝓢 : Specification Phi.{u}} (h : Constructs π 𝓡 𝓢) :
    Constructs π (PhiAt I.adversaryInterface 𝓡) (PhiAt I.adversaryInterface 𝓢) :=
  constructs_star_converterMonoidWithin I.partyInterface_disjoint_adversaryInterface hπ h

end InterfaceRoles

end

end RandomSystems
