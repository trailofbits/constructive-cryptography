/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Submonoid.MulAction
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Order.SetNotation
import Mathlib.Topology.EMetricSpace.Lipschitz
import AbstractCryptography.Refinement.Basic
import AbstractCryptography.Metric.Nonexpansion

/-!
# The selected cryptographic algebra (MauRen11 §6)

This is the public, equality-level rendering of the algebra after behavioral
equivalence has been absorbed into the resource carrier. Serial converter
composition is a standard `Monoid`; converter application is a `MulAction`;
parallel compatibility and metric non-expansion are independent mixins.

For interface-indexed converters `Γ : I → Type*`, one protocol is a tuple
`∀ i, Γ i`. The single-interface operations of MauRen11 Definition 14 are
therefore the singleton-supported actions `Pi.mulSingle i α • R`. The generic
`mulActionOfAttach` constructor is retained only for concrete models that
already prove exact unit, serial, and distinct-interface commutation laws.

The obsolete raw modulo-`Equiv` compatibility structures have been deleted.
Random-systems integration must absorb behavioral equivalence into its carrier
and instantiate this selected surface directly.

Specifications and the construction relation are in
`AbstractCryptography.Specification.Basic` and `AbstractCryptography.Specification.Parallel`;
relaxations and metric composition are in `AbstractCryptography.Specification.Relaxation`,
`AbstractCryptography.Metric.Epsilon`, and `AbstractCryptography.Algebra.Star`;
distinguisher-induced metrics are in
`AbstractCryptography.Metric.Distinguisher`.
-/

namespace AbstractCryptography

universe u v w

/-! ## The selected public typeclass rendering of Definitions 14 and 3 -/

/-!
# Converter attachment at interfaces (MauRen11 §6.1–6.3)

Definition 14's mapping "`Σ × Φ × I ↦ Φ` defining the resource obtained
when converter `α` is attached to interface `i` of resource `R`, denoted
as `αⁱR`", and §6.1's vectors: "We will often consider vectors
`α = (αᵢ)_{i∈I}` of converters, one for each interface of a resource …
Applying `α` to `R` is defined naturally: `αR = α₁α₂⋯αₙR`.  For a vector
`α = (α₁, …, αₙ)` of converter systems and for a subset `P ⊂ I` of the
interfaces, we denote by `αᴾ` the vector `α` with components only `P`,
and `αᴾR` is understood as the resource resulting when for every
`i ∈ P`, `αᵢ` is attached to interface `i` of `R`."

We model this differently from the paper, in two ways:

* **Attachment is a monoid action of the tuple monoid `∀ i, Γ i` on
  `Φ`.**  `αⁱR` is the action of `Pi.mulSingle i α` — the tuple that is
  `α` at `i` and `1` elsewhere — and `αᴾR` is the action of
  `P.piecewise π 1`.  Definition 14's axioms then become theorems about
  disjoint-support tuples, in the order they appear below: (ii) is
  `attach_one`, §6.2's serial law is `attach_mul`, (i) is
  `attach_attach_comm`.  (iii) and (iv) hold by construction, the
  carrier being taken up to `≈`.
* **The converter monoids may differ per interface** (`Γ : I → Type*`).
  The paper has one `Σ` for all of `I`; that is the constant-family
  special case.  A per-interface family is what the interface-typed
  resource layer below produces, its converter monoids depending on the
  signature at `i`.

`supportedOn P H` is the submonoid of tuples trivial outside `P` with
components in the unital classes `H i`.  Identity and serial closure make it
the carrier for optional, repeatable star/adversary/simulator action.  It is
not Definition 17's efficient converter class `Σe`: that class need not
contain the neutral converter and is represented on the selected feasible
carrier by `Subsemigroup M`.  `supportedOn` feeds the `*`-relaxation and the
choice-free local-simulator theorem.
-/

/-- **Ours**: the mixin that makes the specification layer
context-insensitive in the abstract monoid-action model, where the
concrete model's "`π` acts only on `ℛ`'s interfaces" is not available.

Its content is not ours: at Layer C it is the *definition* of parallel
converter composition, MauRen11 §6.2 — "`(α|β)ⁱ(R‖S) := αⁱR ‖ βⁱS`". -/
class SMulParClass (M Φ : Type*) [SMul M Φ] [Par M] [Par Φ] : Prop where
  smul_par (α β : M) (R S : Φ) : (α ∥ β) • (R ∥ S) = (α • R) ∥ (β • S)

export SMulParClass (smul_par)

/-- A supplied protocol equality acts identically on every resource.  This is
the canonical equality-transport boundary between converter algebra and the
resource action; it requires no action law beyond `SMul`. -/
theorem smul_congr_protocol {M Φ : Type*} [SMul M Φ] {π π' : M}
    (same : π = π') (R : Φ) :
    π • R = π' • R :=
  congrArg (fun protocol => protocol • R) same

/-! ### The tuple `MulAction`, built from per-interface attachment

This constructor is the total equality-level specialization used after resource
and converter equivalences have been quotiented and the carrier is closed under
attachment.  Install the returned action locally with `letI` to avoid instance
diamonds.  Every concrete bridge must supply these exact quotient-level laws. -/

/-- **The tuple action, built from per-interface attachment.**  Given attach
operations satisfying the interface-`i` action laws (`attach_one`/`attach_mul`)
and commuting at distinct interfaces (`attach_comm`), the product monoid
`∀ i, Γ i` acts on `Φ` — via `MonoidHom.noncommPiCoprod` (a family of
per-interface homs into `Function.End Φ` whose images pairwise commute) fed to
`MulAction.compHom`.  A finite interface set suffices. -/
@[implicit_reducible]
noncomputable def mulActionOfAttach {I : Type*} [Fintype I] [DecidableEq I]
    {Γ : I → Type*} [∀ i, Monoid (Γ i)] {Φ : Type*}
    (attach : (i : I) → Γ i → Φ → Φ)
    (attach_one : ∀ i s, attach i 1 s = s)
    (attach_mul : ∀ i a b s, attach i (a * b) s = attach i a (attach i b s))
    (attach_comm : ∀ i j, i ≠ j → ∀ a b s,
      attach i a (attach j b s) = attach j b (attach i a s)) :
    MulAction (∀ i, Γ i) Φ :=
  let φ : ∀ i, Γ i →* Function.End Φ := fun i =>
    { toFun := attach i
      map_one' := funext (attach_one i)
      map_mul' := fun a b => funext (attach_mul i a b) }
  MulAction.compHom Φ (MonoidHom.noncommPiCoprod φ
    (fun i j hij a b => funext (attach_comm i j hij a b)))

/-- A singleton-supported converter tuple acts as the supplied attachment at
that interface in the tuple action constructed by `mulActionOfAttach`. -/
theorem mulActionOfAttach_mulSingle_smul
    {I : Type*} [Fintype I] [DecidableEq I]
    {Γ : I → Type*} [∀ i, Monoid (Γ i)] {Φ : Type*}
    (attach : (i : I) → Γ i → Φ → Φ)
    (attach_one : ∀ i s, attach i 1 s = s)
    (attach_mul : ∀ i a b s, attach i (a * b) s = attach i a (attach i b s))
    (attach_comm : ∀ i j, i ≠ j → ∀ a b s,
      attach i a (attach j b s) = attach j b (attach i a s))
    (i : I) (a : Γ i) (s : Φ) :
    letI := mulActionOfAttach attach attach_one attach_mul attach_comm
    (Pi.mulSingle i a : ∀ j, Γ j) • s = attach i a s := by
  let φ : ∀ i, Γ i →* Function.End Φ := fun i =>
    { toFun := attach i
      map_one' := funext (attach_one i)
      map_mul' := fun a b => funext (attach_mul i a b) }
  let hcomm : Pairwise fun i j => ∀ x y, Commute (φ i x) (φ j y) :=
    fun i j hij a b => funext (attach_comm i j hij a b)
  change (MonoidHom.noncommPiCoprod φ hcomm (Pi.mulSingle i a)) s =
    attach i a s
  rw [MonoidHom.noncommPiCoprod_mulSingle]
  rfl

variable {I : Type*} {Γ : I → Type*} {Φ : Type*}

/-! ### Single-interface attachment: Definition 14, as theorems -/

section Single

variable [∀ i, Monoid (Γ i)] [MulAction (∀ i, Γ i) Φ] [DecidableEq I]

/-- Def 14 (ii): "Attaching no converter is defined as a special neutral
converter `1 ∈ Σ`: `1ⁱR ≈ R` for all `i ∈ I` and `R ∈ Φ`." -/
theorem attach_one (i : I) (R : Φ) : (Pi.mulSingle i (1 : Γ i)) • R = R := by
  rw [Pi.mulSingle_one, one_smul]

/-- §6.2: "serial composition: `αβ` (or `α ∘ β`) is defined by
`(αβ)ⁱR := αⁱβⁱR` for all `i` and `R`."

In the paper this *defines* the composition on `Σ`; here `Γ i`'s
multiplication comes first and this certifies that it and the tuple
action package the same algebra. -/
theorem attach_mul (i : I) (α β : Γ i) (R : Φ) :
    (Pi.mulSingle i (α * β)) • R
      = (Pi.mulSingle i α) • (Pi.mulSingle i β) • R := by
  rw [Pi.mulSingle_mul, mul_smul]

/-- Def 14 (i): "Converter application at different interfaces commutes:
`αⁱβʲR ≈ βʲαⁱR` for all `i ≠ j`, `R ∈ Φ`, and `α ∈ Σ`." -/
theorem attach_attach_comm {i j : I} (h : i ≠ j) (α : Γ i) (β : Γ j) (R : Φ) :
    (Pi.mulSingle i α) • (Pi.mulSingle j β) • R
      = (Pi.mulSingle j β) • (Pi.mulSingle i α) • R := by
  have hc : (Pi.mulSingle i α : ∀ k, Γ k) * Pi.mulSingle j β
      = Pi.mulSingle j β * Pi.mulSingle i α :=
    (Pi.mulSingle_commute h α β).eq
  rw [← mul_smul, ← mul_smul, hc]

end Single

/-! ### `αᴾ`: attachment along a vector with "components only `P`" -/

section Pattern

variable [∀ i, Monoid (Γ i)]

/-- Tuples of converters with pointwise-disjoint effective support commute
in the tuple monoid — how Def 14 (i) reaches vectors, and the engine of
Theorem 2. -/
theorem commute_of_forall_eq_one {f g : ∀ i, Γ i} (h : ∀ i, f i = 1 ∨ g i = 1) :
    Commute f g := by
  show f * g = g * f
  funext i
  rcases h i with h1 | h1 <;> simp [h1]

/-- `αᴾ` and `βᴽ` commute when `P` and `Q` are disjoint — Def 14 (i)
again, "if two converters are connected to distinct interfaces, then the
order in which these operations are performed is irrelevant." -/
theorem piecewise_commute_of_disjoint {P Q : Set I}
    [∀ j, Decidable (j ∈ P)] [∀ j, Decidable (j ∈ Q)]
    (h : Disjoint P Q) (f g : ∀ i, Γ i) :
    Commute (P.piecewise f 1) (Q.piecewise g 1) :=
  commute_of_forall_eq_one fun i => by
    by_cases hi : i ∈ P
    · exact Or.inr (Set.piecewise_eq_of_notMem _ _ _ (Set.disjoint_left.mp h hi))
    · exact Or.inl (Set.piecewise_eq_of_notMem _ _ _ hi)

/-- The converter tuples that are `αᴾ`-shaped for some `α` with
components in the classes `H i`: "the vector `α` with components only
`P`", i.e. trivial outside `P`, in `H` inside.  The `Submonoid` records the
neutral and serial closure required by star/adversary/simulator action; it is
deliberately stronger than Definition 17's non-unital efficient class `Σe`. -/
def supportedOn (P : Set I) (H : ∀ i, Submonoid (Γ i)) : Submonoid (∀ i, Γ i) where
  carrier := {f | (∀ i ∈ P, f i ∈ H i) ∧ ∀ i ∉ P, f i = 1}
  one_mem' := ⟨fun i _ => one_mem (H i), fun _ _ => rfl⟩
  mul_mem' {a b} ha hb :=
    ⟨fun i hi => mul_mem (ha.1 i hi) (hb.1 i hi),
     fun i hi => by rw [Pi.mul_apply, ha.2 i hi, hb.2 i hi, one_mul]⟩

theorem mem_supportedOn {P : Set I} {H : ∀ i, Submonoid (Γ i)} {f : ∀ i, Γ i} :
    f ∈ supportedOn P H ↔ (∀ i ∈ P, f i ∈ H i) ∧ ∀ i ∉ P, f i = 1 := Iff.rfl

theorem piecewise_mem_supportedOn {P : Set I} [∀ j, Decidable (j ∈ P)]
    {H : ∀ i, Submonoid (Γ i)} {f : ∀ i, Γ i}
    (hf : ∀ i ∈ P, f i ∈ H i) : P.piecewise f 1 ∈ supportedOn P H :=
  ⟨fun i hi => by rw [Set.piecewise_eq_of_mem _ _ _ hi]; exact hf i hi,
   fun _ hi => Set.piecewise_eq_of_notMem _ _ _ hi⟩

/-- `αᴾ` commutes with anything supported on `Pᶜ` — the disjointness at
the heart of Theorem 2's proof, where the protocol sits at `P` and the
simulators at `P̄`. -/
theorem commute_piecewise_supportedOn {P : Set I} [∀ j, Decidable (j ∈ P)]
    {H : ∀ i, Submonoid (Γ i)} {γ : ∀ i, Γ i}
    (hγ : γ ∈ supportedOn Pᶜ H) (f : ∀ i, Γ i) : Commute (P.piecewise f 1) γ :=
  commute_of_forall_eq_one fun i => by
    by_cases hi : i ∈ P
    · exact Or.inr (hγ.2 i (Set.notMem_compl_iff.mpr hi))
    · exact Or.inl (Set.piecewise_eq_of_notMem _ _ _ hi)

open Classical in
/-- `πᴾ`: "the vector `π` with components only `P`" — `π` inside `P`, `1`
outside.  One canonical (classical) `Decidable` instance, so that
statements built from it are definitionally coherent across files. -/
noncomputable def patternAttach (P : Set I) (π : ∀ i, Γ i) :
    ∀ i, Γ i :=
  P.piecewise π 1

/-- Paper-facing restriction of a converter tuple to an interface pattern.
`protocol ⇂ P` expands to `patternAttach P protocol`; in particular,
`protocol ⇂ Pᶜ` keeps complement-heavy CC expressions readable. -/
scoped notation:90 protocol " ⇂ " P:91 => patternAttach P protocol

section PatternAttach

/-- Inside the pattern, `πᴾ` is `π`.  Stated on `patternAttach` directly so
that callers never touch the canonical classical `Decidable` instance baked
into the definition (`Set.piecewise_eq_of_mem` demands that instance by
synthesis and fails without `open Classical`). -/
theorem patternAttach_apply_of_mem {P : Set I} {i : I} (π : ∀ i, Γ i)
    (hi : i ∈ P) : patternAttach P π i = π i := by
  simp [patternAttach, Set.piecewise, hi]

/-- Outside the pattern, `πᴾ` is neutral. -/
theorem patternAttach_apply_of_notMem {P : Set I} {i : I} (π : ∀ i, Γ i)
    (hi : i ∉ P) : patternAttach P π i = 1 := by
  simp [patternAttach, Set.piecewise, hi]

/-- A singleton pattern recovers one-interface attachment. -/
theorem patternAttach_singleton [DecidableEq I] (i : I) (π : ∀ i, Γ i) :
    patternAttach ({i} : Set I) π = Pi.mulSingle i (π i) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [patternAttach]
  · simp [patternAttach, hji]

open Classical in
/-- Pattern attachments on disjoint interface sets commute. This is MauRen11
Definition 14(i) lifted to the paper's restricted converter vectors. -/
theorem commute_patternAttach_of_disjoint {P Q : Set I}
    (h : Disjoint P Q) (f g : ∀ i, Γ i) :
    Commute (patternAttach P f) (patternAttach Q g) :=
  piecewise_commute_of_disjoint h f g

open Classical in
theorem patternAttach_mem_supportedOn {P : Set I} {H : ∀ i, Submonoid (Γ i)}
    {f : ∀ i, Γ i} (hf : ∀ i ∈ P, f i ∈ H i) :
    patternAttach P f ∈ supportedOn P H :=
  piecewise_mem_supportedOn hf

open Classical in
theorem commute_patternAttach_supportedOn {P : Set I} {H : ∀ i, Submonoid (Γ i)}
    {γ : ∀ i, Γ i} (hγ : γ ∈ supportedOn Pᶜ H) (f : ∀ i, Γ i) :
    Commute (patternAttach P f) γ :=
  commute_piecewise_supportedOn hγ f

theorem patternAttach_mul (P : Set I) (f g : ∀ i, Γ i) :
    patternAttach P (f * g) = patternAttach P f * patternAttach P g := by
  funext i
  by_cases hi : i ∈ P <;>
    simp [patternAttach, Set.piecewise, hi]

/-- Attaching the neutral converter along any pattern is the neutral
converter: `1ᴾ = 1`.  Def 14 (ii) at the vector level. -/
theorem patternAttach_one (P : Set I) : patternAttach P (1 : ∀ i, Γ i) = 1 := by
  funext i
  by_cases hi : i ∈ P <;>
    simp [patternAttach, Set.piecewise, hi]

end PatternAttach

end Pattern



end AbstractCryptography
