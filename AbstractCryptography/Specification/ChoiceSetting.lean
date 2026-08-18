/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import AbstractCryptography.Algebra.Attachment

/-!
# Choice settings and abstraction of filtered specifications (MauRen11 §§4–5, 7)

**MR11-DEFERRED (provenance fence, 2026-08-17): MauRen11 constructs
quarantined pending the MR11 reconciliation task.  No MR16-track file may
import this module — enforced by `scripts/ledgerAudit.sh`.  See `LEDGER.md`
PROVENANCE FENCE.**

The choice-setting / complete-factorizable-relation layer of MauRen11 and its
central theorem: local ongoing simulation proves filtered-specification
abstraction, `R_φ ⊑^π S_ψ` (§7.4, Theorem 2, p. 15, proof pp. 15–16).

## Source, by page

* **Definition 1 (p. 6).**  "An `(A, B)`-relation `ρ` is called *complete* if
  it has full domain (i.e., `∀a ∈ A ∃b ∈ B : a ρ b`) and full range (i.e.,
  `∀b ∈ B ∃a ∈ A : a ρ b`)."  Rendered by `RelCompleteOn`.
* **Lemma 1 (p. 6).**  `⨂ᵢ (ρᵢ ∪ σᵢ) = ⋃_{M ⊆ {1..n}} (⨂_{j∈M} ρⱼ ×
  ⨂_{j∉M} σⱼ)` — the union/product exchange behind Theorem 2's proof.  Not a
  separate statement here: on the factored representation it is the pointwise
  branch split `P := {i | left branch}` inside the main proof.
* **Definition 4 (p. 7) and §4.2 (p. 9).**  Isomorphism of choice settings via
  a CFR: `R ≅^ρ S :⟺ (∀i : aᵢ ρᵢ bᵢ) → R(a₁, …, aₙ) ≃ S(b₁, …, bₙ)`.
  Rendered by `ChoiceSetting.IsomorphicVia` (one direction, as in the paper).
* **Definition 8 (p. 8) and §7.1 (p. 14).**  An `n`-choice setting is a
  function `R : A₁ × ⋯ × Aₙ → Ω`; §7.1 specializes: "each party's choice
  space is `Σ` (or a subset of `Σ`), and a resource system `R` corresponds to
  the function `Σⁿ → Φ` defined by `α ↦ αR` … the effect space `Ω` is the
  resource set `Φ`, equipped with the equivalence relation `≈`."  Rendered by
  `ChoiceSetting` (resource plus actual domains); the effect map is `α • R`.
* **Definition 9 (p. 9).**  A relation is *factorizable* if `ρ = ρ₁ × ⋯ × ρₙ`;
  a complete factorizable relation is a *CFR*.  Factorizability is by
  construction here: relations enter as per-interface families
  `ρ : (i : I) → Γ i → Γ i → Prop`, the product being
  `∀ i, ρ i (α i) (β i)`.
* **Definition 10 (p. 10).**  An `n`-specification is a set of `n`-choice
  settings with guaranteed choice domains `Âᵢ` contained in every member's
  `i`th domain.  Rendered by `ChoiceSpec`.
* **Definition 11 (p. 10).**  `𝓢` is a `π`-abstraction of `𝓡`, `𝓡 ⊑^π 𝓢`,
  for `πᵢ : B̂ᵢ → Âᵢ`, if for every `R ∈ 𝓡` there are `S ∈ 𝓢` and a CFR `ρ`
  with (i) `R ≅^ρ S` and (ii) `πᵢ⁻¹ ⊆ ρᵢ` for all `i`.  (Fn. 14: only the
  `πᵢ`-part of `ρᵢ` is common to all `R`.)  Rendered by
  `ChoiceSpec.Abstraction`.
* **§7.2, eq. (4) and Definition 18 (pp. 14–15).**  Guaranteed space
  `Σφᵢ = {αφᵢ : α ∈ Σ}`, possible space `Σ`, `Σφᵢ ⊆ Aᵢ ⊆ Σ`; `R_φ` is the
  specification of all settings with underlying resource `R` whose domains
  satisfy (4).  Rendered by `guaranteedChoices` and `filteredSpec`.
* **§7.3 (p. 15).**  For filtered specifications the abstraction map is
  induced by a converter `πᵢ`: `Σψᵢ → Σφᵢ : αψᵢ ↦ απᵢφᵢ`, and condition (ii)
  becomes `{(γπᵢφᵢ, γψᵢ) : γ ∈ Σ} ⊆ ρᵢ`.  Rendered by
  `FilteredAbstraction`; the bridge back to Definition 11's function form is
  `FilteredAbstraction.exists_abstraction`.
* **§7.4, Theorem 2 (p. 15), proof (pp. 15–16).**  "`∀𝒫 ⊆ 𝓘 : π_𝒫 φ_𝒫 R ≈
  σ_𝒫̄ ψ_𝒫 S ⟹ R_φ ⊑^π S_ψ`."  The proof's objects, both explicit below in
  `filteredAbstraction_of_local_simulators`'s plan: ideal domain
  `Bᵢ = Σψᵢ ∪ Aᵢσᵢ` and relation
  `ρᵢ′ = {(γπᵢφᵢ, γψᵢ) : γ ∈ Σ} ∪ {(γ, γσᵢ) : γ ∈ Aᵢ}`.

## Reading the rendering

* `≈` is `=`: the carrier is already quotiented, so Definition 14 (iii)'s
  congruence of attachment with `≈` is automatic.
* Only the §7.1 specialization of Definition 8 is rendered — a setting is a
  resource together with its domains, the effect being `α • R`.
* Converter monoids are per-interface (`Γ : I → Type*`); the paper's single
  `Σ` is the constant family, and eq. (4)'s bound `Aᵢ ⊆ Σ` is the typing
  `Set (Γ i)`.
* The paper's `ρᵢ ⊆ Aᵢ × Bᵢ` is a total `Γ i → Γ i → Prop` used only through
  membership-guarded statements (`RelCompleteOn`, `IsomorphicVia`), and
  Definition 11's `πᵢ : B̂ᵢ → Âᵢ` is a total `Γ i → Γ i` whose typing on the
  guaranteed domains is a clause of `ChoiceSpec.Abstraction`.
* `I` is arbitrary: a choice tuple is an element of `∀ i, Γ i` and the
  premise quantifies over all `P : Set I`; the paper's `{1, …, n}` is the
  finite case.
* Not represented: `ε`-extensions and approximate abstraction (Definition 12,
  Lemma 3 — Theorem 2 is exact in the paper as well), the
  reduction/composability reading of `⊑^π` (§5.3, Theorem 1), and
  efficiency/feasibility classes (Definition 17).
-/

namespace AbstractCryptography

/-- MauRen11 §2.1, **Definition 1**, relative to actual domains: "An
`(A, B)`-relation `ρ` is called *complete* if it has full domain (i.e.,
`∀a ∈ A ∃b ∈ B : a ρ b`) and full range (i.e., `∀b ∈ B ∃a ∈ A : a ρ b`)."
(p. 6.)  The relation is total on the ambient types; `Adom` and `Bdom` are
the paper's `A` and `B`. -/
def RelCompleteOn {α β : Type*} (Adom : Set α) (Bdom : Set β)
    (ρ : α → β → Prop) : Prop :=
  (∀ a ∈ Adom, ∃ b ∈ Bdom, ρ a b) ∧ (∀ b ∈ Bdom, ∃ a ∈ Adom, ρ a b)

/-- MauRen11 §4.1, **Definition 8** (p. 8) in the §7.1 specialization
(p. 14): a choice setting whose choices are converters and whose effect is
the converted resource — "a resource system `R` corresponds to the function
`Σⁿ → Φ` defined by `α ↦ αR`, where `α = (α₁, …, αₙ)` and `αᵢ` is party
`i`'s choice", here restricted to the actual domains `choiceDom i ⊆ Γ i`.
The effect map itself is `α • resource` and is not stored. -/
structure ChoiceSetting {I : Type*} (Γ : I → Type*) (Φ : Type*) where
  /-- The underlying resource; the effect of choices `α` is `α • resource`. -/
  resource : Φ
  /-- The actual choice domain at each interface (`Aᵢ ⊆ Σ` of eq. (4)). -/
  choiceDom : (i : I) → Set (Γ i)

/-- MauRen11 §5.1, **Definition 10** (p. 10): "An *`n`-choice setting
specification* (or simply *`n`-specification*) `𝓡` is a set of `n`-choice
settings, together with an `n`-tuple of sets, `(Â₁, …, Âₙ)`, such that for
all `i`, `Âᵢ` is a subset of the `i`th choice domain of every setting in
`𝓡`.  The set `Âᵢ` is called the *`i`th guaranteed choice domain* of `𝓡`." -/
structure ChoiceSpec {I : Type*} (Γ : I → Type*) (Φ : Type*) where
  /-- The settings contained in the specification. -/
  settings : Set (ChoiceSetting Γ Φ)
  /-- The guaranteed choice domain `Âᵢ` at each interface. -/
  guaranteed : (i : I) → Set (Γ i)
  /-- Guaranteed choices are available in every member setting. -/
  guaranteed_subset : ∀ X ∈ settings, ∀ i, guaranteed i ⊆ X.choiceDom i

variable {I : Type*} {Γ : I → Type*} {Φ : Type*}
  [∀ i, Monoid (Γ i)] [MulAction (∀ i, Γ i) Φ]

/-- MauRen11 §4.2 (p. 9), lifting **Definition 4** (p. 7): "`R ≅^ρ S :⟺
(∀i : aᵢ ρᵢ bᵢ) → R(a₁, …, aₙ) ≃ S(b₁, …, bₙ)`" — whenever each interface
picks related choices from the actual domains, the effects agree.  The CFR
`ρ` enters in factored form (Definition 9, p. 9), and `≃` is equality on the
quotiented carrier.  One direction only, as in the paper. -/
def ChoiceSetting.IsomorphicVia (X Y : ChoiceSetting Γ Φ)
    (ρ : (i : I) → Γ i → Γ i → Prop) : Prop :=
  ∀ α β : ∀ i, Γ i,
    (∀ i, α i ∈ X.choiceDom i) → (∀ i, β i ∈ Y.choiceDom i) →
    (∀ i, ρ i (α i) (β i)) →
    α • X.resource = β • Y.resource

/-- MauRen11 §5.2, **Definition 11** (p. 10): "We say that `𝓢` is a
*`π`-abstraction* of `𝓡`, denoted `𝓡 ⊑^π 𝓢`, if for every `R ∈ 𝓡` there
exists an `S ∈ 𝓢` and a CFR `ρ = (ρ₁, …, ρₙ)`, such that (i) `R ≅^ρ S`,
(ii) `πᵢ⁻¹ ⊆ ρᵢ` for all `i`."

Here `Abstraction real ideal π` is `real ⊑^π ideal`.  The paper's
`πᵢ : B̂ᵢ → Âᵢ` is a total `Γ i → Γ i`; its guaranteed-domain typing is the
first conjunct of the final clause, and `πᵢ⁻¹ ⊆ ρᵢ` — the graph inclusion
`{(πᵢ b, b) : b ∈ B̂ᵢ} ⊆ ρᵢ` — is the second.  Completeness of `ρᵢ` is
required on the matched settings' actual domains, per Definitions 1 and 9.
Fn. 14 (p. 10): only this `πᵢ`-part of `ρᵢ` is common to all `R`. -/
def ChoiceSpec.Abstraction (real ideal : ChoiceSpec Γ Φ)
    (π : (i : I) → Γ i → Γ i) : Prop :=
  ∀ X ∈ real.settings, ∃ Y ∈ ideal.settings,
    ∃ ρ : (i : I) → Γ i → Γ i → Prop,
      (∀ i, RelCompleteOn (X.choiceDom i) (Y.choiceDom i) (ρ i)) ∧
      X.IsomorphicVia Y ρ ∧
      ∀ i, ∀ b ∈ ideal.guaranteed i, π i b ∈ real.guaranteed i ∧ ρ i (π i b) b

/-- MauRen11 §7.2, eq. (4) (pp. 14–15): the guaranteed choice space
`Σφᵢ = {αφᵢ : α ∈ Σ}` — "a guaranteed choice `αᵢφᵢ ∈ Σφᵢ` is specified by
the converter `αᵢ`."  Constructor multiplication is function-composition
order, so `αφᵢ` is `α * φ i` (the filter innermost, at the resource). -/
def guaranteedChoices (φ : ∀ i, Γ i) (i : I) : Set (Γ i) :=
  {c | ∃ γ : Γ i, c = γ * φ i}

/-- MauRen11 §7.2, **Definition 18** (p. 15): "Let `φ₁, …, φₙ` be converters
and let `φ = (φ₁, …, φₙ)`.  Then `R_φ` denotes the `n`-specification defined
as the set of all resources `R`, where at each interface `i` the choice
domain `Aᵢ` satisfies (4) [`Σφᵢ ⊆ Aᵢ ⊆ Σ`].  An `n`-specification of this
form will be called *filtered*."

The members are the settings with underlying resource `R` (the carrier is
quotiented, so "the same resource" is equality) and any domains above the
guaranteed spaces; the upper bound `Aᵢ ⊆ Σ` is the typing `Set (Γ i)`. -/
def filteredSpec (R : Φ) (φ : ∀ i, Γ i) : ChoiceSpec Γ Φ where
  settings :=
    {X | X.resource = R ∧ ∀ i, guaranteedChoices φ i ⊆ X.choiceDom i}
  guaranteed := guaranteedChoices φ
  guaranteed_subset := fun _ hX => hX.2

omit [MulAction (∀ i, Γ i) Φ] in
theorem mem_filteredSpec_iff {R : Φ} {φ : ∀ i, Γ i}
    {X : ChoiceSetting Γ Φ} :
    X ∈ (filteredSpec R φ).settings
      ↔ X.resource = R ∧ ∀ i, guaranteedChoices φ i ⊆ X.choiceDom i :=
  Iff.rfl

/-- MauRen11 §7.3 (p. 15): abstraction specialized to filtered
specifications, the conclusion form of Theorem 2 — `R_φ ⊑^π S_ψ` "if for
every `R′ ∈ R_φ` there exists `S′ ∈ S_ψ` and a CFR `ρ = ρ₁ × ⋯ × ρₙ`
between the choice spaces `A₁ × ⋯ × Aₙ` of `R′` and `B₁ × ⋯ × Bₙ` of `S′`
such that `R′ ≅^ρ S′` and, for all `i`,
`{(γπᵢφᵢ, γψᵢ) : γ ∈ Σ} ⊆ ρᵢ`."

The final clause is the converter-induced form of Definition 11 (ii): the
abstraction map `Σψᵢ → Σφᵢ : αψᵢ ↦ απᵢφᵢ` is used only through its graph,
which sidesteps choosing a representation `γ` for each `γψᵢ`.
`FilteredAbstraction.exists_abstraction` recovers the function form. -/
def FilteredAbstraction (φ ψ π : ∀ i, Γ i) (R S : Φ) : Prop :=
  ∀ X ∈ (filteredSpec R φ).settings,
    ∃ Y ∈ (filteredSpec S ψ).settings,
      ∃ ρ : (i : I) → Γ i → Γ i → Prop,
        (∀ i, RelCompleteOn (X.choiceDom i) (Y.choiceDom i) (ρ i)) ∧
        X.IsomorphicVia Y ρ ∧
        ∀ i (γ : Γ i), ρ i (γ * π i * φ i) (γ * ψ i)

open Classical in
/-- MauRen11 §7.4, **Theorem 2** (p. 15, proof pp. 15–16): "Let
`⟨Φ, Σ, ≈⟩` be a cryptographic algebra and, for any `i ∈ 𝓘`, let
`φᵢ, ψᵢ, πᵢ, σᵢ ∈ Σ` be converters.  Then

  `∀𝒫 ⊆ 𝓘 : π_𝒫 φ_𝒫 R ≈ σ_𝒫̄ ψ_𝒫 S ⟹ R_φ ⊑^π S_ψ`."

"What is crucial is that the simulation can be performed **locally** (rather
than jointly) and … the simulation must be ongoing, not only for the final
transcript (or view)" (§7.4): one simulator tuple `σ` is fixed before the
quantification over honesty patterns `P`.

The settings range over every actual-domain family `Σφᵢ ⊆ Aᵢ ⊆ Σ`, the
matched ideal setting has domains `Bᵢ = Σψᵢ ∪ Aᵢσᵢ`, and the conclusion is a
single abstraction covering all corruption patterns at once. -/
theorem filteredAbstraction_of_local_simulators
    {φ ψ π σ : ∀ i, Γ i} {R S : Φ}
    (h : ∀ P : Set I,
      patternAttach P π • patternAttach P φ • R
        = patternAttach Pᶜ σ • patternAttach P ψ • S) :
    FilteredAbstraction φ ψ π R S := by
  rintro X ⟨hres, hdom⟩
  -- The proof's ideal setting has domains `Bᵢ = Σψᵢ ∪ Aᵢσᵢ` (p. 16), and its
  -- relation is `ρᵢ′ = {(γπᵢφᵢ, γψᵢ) : γ ∈ Σ} ∪ {(γ, γσᵢ) : γ ∈ Aᵢ}`.
  refine ⟨⟨S, fun i => guaranteedChoices ψ i ∪ (· * σ i) '' X.choiceDom i⟩,
      ⟨rfl, fun i => Set.subset_union_left⟩,
      fun i a b => (∃ γ, a = γ * π i * φ i ∧ b = γ * ψ i)
        ∨ (a ∈ X.choiceDom i ∧ b = a * σ i),
      fun i => ⟨?_, ?_⟩, ?_, fun i γ => Or.inl ⟨γ, rfl, rfl⟩⟩
  · -- Full domain: `a ↦ aσᵢ` lands in the second branch of `Bᵢ` and `ρᵢ′`.
    exact fun a ha =>
      ⟨a * σ i, Set.mem_union_right _ (Set.mem_image_of_mem _ ha),
        Or.inr ⟨ha, rfl⟩⟩
  · -- Full range: `γψᵢ ↦ γπᵢφᵢ ∈ Σφᵢ ⊆ Aᵢ`, and `aσᵢ ↦ a`.
    rintro b (⟨γ, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact ⟨γ * π i * φ i, hdom i ⟨γ * π i, rfl⟩, Or.inl ⟨γ, rfl, rfl⟩⟩
    · exact ⟨a, ha, Or.inr ⟨ha, rfl⟩⟩
  · -- Isomorphism.  Lemma 1's branch split: `P` is the set of interfaces
    -- whose related pair took the `(γπᵢφᵢ, γψᵢ)` branch; choose a common
    -- leftmost `γ` there and keep `γ i = α i` elsewhere.
    intro α β _ _ hρ
    have key : ∀ j, ∃ g : Γ j,
        (α j = g * π j * φ j ∧ β j = g * ψ j) ∨
          (¬(∃ g' : Γ j, α j = g' * π j * φ j ∧ β j = g' * ψ j) ∧ g = α j) := by
      intro j
      by_cases hj : ∃ g' : Γ j, α j = g' * π j * φ j ∧ β j = g' * ψ j
      · obtain ⟨g, hg⟩ := hj
        exact ⟨g, Or.inl hg⟩
      · exact ⟨α j, Or.inr ⟨hj, rfl⟩⟩
    choose γ hγ using key
    set P : Set I := {j | ∃ g : Γ j, α j = g * π j * φ j ∧ β j = g * ψ j}
      with hPdef
    have hαfac : α = γ * patternAttach P π * patternAttach P φ := by
      funext j
      rcases hγ j with ⟨h1, h2⟩ | ⟨hj, hγj⟩
      · have hjP : j ∈ P := ⟨γ j, h1, h2⟩
        rw [Pi.mul_apply, Pi.mul_apply, patternAttach_apply_of_mem _ hjP,
          patternAttach_apply_of_mem _ hjP]
        exact h1
      · have hjP : j ∉ P := hj
        rw [Pi.mul_apply, Pi.mul_apply, patternAttach_apply_of_notMem _ hjP,
          patternAttach_apply_of_notMem _ hjP, mul_one, mul_one, hγj]
    have hβfac : β = γ * patternAttach Pᶜ σ * patternAttach P ψ := by
      funext j
      rcases hγ j with ⟨h1, h2⟩ | ⟨hj, hγj⟩
      · have hjP : j ∈ P := ⟨γ j, h1, h2⟩
        rw [Pi.mul_apply, Pi.mul_apply,
          patternAttach_apply_of_notMem _ (Set.notMem_compl_iff.mpr hjP),
          patternAttach_apply_of_mem _ hjP, mul_one]
        exact h2
      · have hjP : j ∉ P := hj
        have hσj : β j = α j * σ j := by
          rcases hρ j with hL | ⟨_, hs⟩
          · exact absurd hL hj
          · exact hs
        rw [Pi.mul_apply, Pi.mul_apply,
          patternAttach_apply_of_mem _ (Set.mem_compl hjP),
          patternAttach_apply_of_notMem _ hjP, mul_one, hγj]
        exact hσj
    show α • X.resource = β • S
    calc α • X.resource
        = α • R := by rw [hres]
      _ = (γ * patternAttach P π * patternAttach P φ) • R := by rw [← hαfac]
      _ = γ • patternAttach P π • patternAttach P φ • R := by
          rw [mul_smul, mul_smul]
      _ = γ • patternAttach Pᶜ σ • patternAttach P ψ • S := by rw [h P]
      _ = (γ * patternAttach Pᶜ σ * patternAttach P ψ) • S := by
          rw [← mul_smul, ← mul_smul]
      _ = β • S := by rw [← hβfac]

open Classical in
/-- The §7.3 filtered abstraction implies the Definition 11 function form:
"This mapping is achieved by means of a converter `πᵢ`, as follows:
`Σψᵢ → Σφᵢ : αψᵢ ↦ απᵢφᵢ`.  …  If we understand `πᵢ` as a function, just as
described, then `S_ψ` is a `π`-abstraction of `R_φ`" (p. 15).

The function is obtained by one global classical choice of a representation
`γ` for each guaranteed ideal choice `γψᵢ`; it is independent of the concrete
setting, as Definition 11 requires (fn. 14, p. 10). -/
theorem FilteredAbstraction.exists_abstraction
    {φ ψ π : ∀ i, Γ i} {R S : Φ}
    (h : FilteredAbstraction φ ψ π R S) :
    ∃ ab : (i : I) → Γ i → Γ i,
      ChoiceSpec.Abstraction (filteredSpec R φ) (filteredSpec S ψ) ab := by
  -- One global choice of a representation `γ` for each `γψᵢ`, independent of
  -- the concrete setting (fn. 14: only the `πᵢ`-part of `ρᵢ` is common).
  refine ⟨fun i b =>
      if hb : ∃ γ : Γ i, b = γ * ψ i then hb.choose * π i * φ i else b, ?_⟩
  intro X hX
  obtain ⟨Y, hY, ρ, hcomp, hiso, hgraph⟩ := h X hX
  refine ⟨Y, hY, ρ, hcomp, hiso, fun i b hb => ?_⟩
  have hbex : ∃ γ : Γ i, b = γ * ψ i := hb
  have hab : (if hb' : ∃ γ : Γ i, b = γ * ψ i then hb'.choose * π i * φ i else b)
      = hbex.choose * π i * φ i := dif_pos hbex
  constructor
  · show (if hb' : ∃ γ : Γ i, b = γ * ψ i then hb'.choose * π i * φ i else b)
        ∈ guaranteedChoices φ i
    rw [hab]
    exact ⟨hbex.choose * π i, rfl⟩
  · show ρ i
        (if hb' : ∃ γ : Γ i, b = γ * ψ i then hb'.choose * π i * φ i else b) b
    rw [hab]
    have hg := hgraph i hbex.choose
    rwa [← hbex.choose_spec] at hg

end AbstractCryptography
