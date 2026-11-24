module

public import ConstructiveCryptography.Construction.Basic
public import ConstructiveCryptography.Notation.Basic
public import ConstructiveCryptography.Substitution.Basic

/-!
# Two-party algebraic construction obstruction

For a two-party protocol `π = (π₁, π₂)` constructing a target resource `S` from a neutral channel
`R`, the three simulation equations (honest availability and security against each dishonest
party) force `S γ S ≈ S` for the composite bridge `γ = σ₂ σ₁` formed from the two simulators
[1, Appendix C, Theorem 4, pp. 18–19]:

```text
S ≃ π₁ R π₂                      symmetry of honest availability (eq. 1)
  ═ plugRight π₂ • (π₁ R)        plug_honest
  ≃ plugRight π₂ • (S σ₂)        dishonest right party (eq. 3), preserved by plugRight π₂
  ═ plugLeft S σ₂ • (R π₂)       plug_assoc (neutral-channel associativity)
  ≃ plugLeft S σ₂ • (σ₁ S)       dishonest left party (eq. 2), preserved by plugLeft S σ₂
  ═ S (composeBridge σ₂ σ₁) S    plug_compose
```

Here `═` marks an exact two-ended plugging equation supplied explicitly in `TwoPartyPlugging`, and
`≃` marks one substitution step transported by `SubstitutionRelation.substitutes_of_hybrid` (or,
quantitatively, `SubstitutionRelation.distance_hybrid_le`). When the simulator classes are closed
under `composeBridge` into an admitted bridge class `bridges`, any resource `S` separated from
`S γ S` for every `γ ∈ bridges` is `Unconstructible` from `R`.

No base-category axioms, resource carriers or separating arguments are introduced here: two-ended
plugging, bridge composition closure and separation from `bridges` are explicit inputs.

## Main definitions

* `TwoPartySetup`: honest and dishonest-party resource evaluations, together with the qualitative
  (`Constructs`) and quantitative (`ConstructsWithin`) three-equation construction judgments
* `TwoPartyPlugging`: the two-ended plugging converters, bridge composition and the three plugging
  equations at a fixed source resource

## Main results

* `bridge_substitutes_of_equations`, `twoParty_bridge_substitutes`: three simulation equations
  imply `S γ S ≈ S` for an admitted composite bridge `γ`
* `unconstructible_of_bridge_separation`: separation from every admitted bridge rules out
  two-party construction (`Unconstructible`)
* `bridge_distance_le_of_bounds`, `twoParty_bridge_distance_le`,
  `unconstructible_of_bridge_distance_gt`: quantitative pseudo-metric counterparts

## References

1. U. Maurer and R. Renner. *Abstract Cryptography*. In *Innovations in Computer Science
   (ICS 2011)*, pp. 1–21, 2011. Appendix C, Theorem 4, pp. 18–19.
-/

@[expose] public section

set_option autoImplicit false

namespace ConstructiveCryptography.Construction

open CategoryTheory
open ConstructiveCryptography.CryptographicAlgebra
open scoped SystemAlgebra

universe u v w u₁ u₂ u₃ u₄ u₅ u₆ u₇

/-- The resource-level evaluations of a two-party protocol `π = (π₁, π₂)` and its two simulators
`(σ₁, σ₂)` on a resource theory `Phi`.

The three interfaces `A`, `ALeft`, `ARight` may coincide (untyped two-party algebra) or differ
(typed interfaces where a dishonest party directly accesses the source interface instead of
running its protocol component). -/
structure TwoPartySetup
    -- `C` is the category of interfaces; `A ⟶ B` is a converter from outside `A` to inside `B`.
    (C : Type u) [Category.{v} C]
    -- `Phi A` is the fibre of resources at interface `A`, with attachment `attach`.
    {Phi : C → Type w} [ResourceTheory C Phi]
    -- `A` is the honest two-party interface; `ALeft` exposes dishonest party 1; `ARight` exposes
    -- dishonest party 2.
    (A ALeft ARight : C)
    -- `Source` carries candidate source resources `R`; `LeftProtocol`, `RightProtocol` carry
    -- protocol components `π₁`, `π₂`; `LeftSimulator`, `RightSimulator` carry `σ₁`, `σ₂`.
    (Source : Type u₁) (LeftProtocol : Type u₂) (RightProtocol : Type u₃)
    (LeftSimulator : Type u₄) (RightSimulator : Type u₅) where
  /-- Both parties honest: `π₁ R π₂` at interface `A`. -/
  realHonest : LeftProtocol → RightProtocol → Source → Phi A
  /-- Party 1 dishonest, party 2 honest: `R π₂` at interface `ALeft`. -/
  realRight : RightProtocol → Source → Phi ALeft
  /-- Party 1 honest, party 2 dishonest: `π₁ R` at interface `ARight`. -/
  realLeft : LeftProtocol → Source → Phi ARight
  /-- Ideal resource with simulator `σ₁` at dishonest party 1: `σ₁ S` at interface `ALeft`. -/
  simulatedLeft : LeftSimulator → Phi A → Phi ALeft
  /-- Ideal resource with simulator `σ₂` at dishonest party 2: `S σ₂` at interface `ARight`. -/
  simulatedRight : Phi A → RightSimulator → Phi ARight

namespace TwoPartySetup

variable {C : Type u} [Category.{v} C] {Phi : C → Type w} [ResourceTheory C Phi]
variable {A ALeft ARight : C}
variable {Source : Type u₁} {LeftProtocol : Type u₂} {RightProtocol : Type u₃}
variable {LeftSimulator : Type u₄} {RightSimulator : Type u₅}

/-- Qualitative two-party construction judgment [1, Appendix C, pp. 18–19]: protocol `(π₁, π₂)`
constructs `target` from `source` under `relation` with simulators in `leftSimulators` and
`rightSimulators` when honest availability (`π₁ R π₂ ≈ S`) and both single-party simulation
equations (`R π₂ ≈ σ₁ S` and `π₁ R ≈ S σ₂`) hold. -/
def Constructs
    -- `setup` supplies the five honest/dishonest resource evaluations.
    (setup : TwoPartySetup C A ALeft ARight Source LeftProtocol RightProtocol
      LeftSimulator RightSimulator)
    -- `relation` is the selected substitution relation `≈` in every resource fibre.
    (relation : SubstitutionRelation C)
    -- `leftSimulators` and `rightSimulators` are the admitted simulator classes for parties 1, 2.
    (leftSimulators : Set LeftSimulator) (rightSimulators : Set RightSimulator)
    -- `protocol = (π₁, π₂)` is the candidate two-party protocol.
    (protocol : LeftProtocol × RightProtocol)
    -- `source = R` is the assumed resource and `target = S` is the target resource.
    (source : Source) (target : Phi A) : Prop :=
  relation.substitutes A (setup.realHonest protocol.1 protocol.2 source) target ∧
    (∃ σ₁ ∈ leftSimulators,
      relation.substitutes ALeft (setup.realRight protocol.2 source)
        (setup.simulatedLeft σ₁ target)) ∧
    (∃ σ₂ ∈ rightSimulators,
      relation.substitutes ARight (setup.realLeft protocol.1 source)
        (setup.simulatedRight target σ₂))

/-- Quantitative two-party construction judgment in a compatible pseudo-metric: protocol
`(π₁, π₂)` constructs `target` from `source` within honest error `εHonest` and dishonest-party
simulation errors `εLeft`, `εRight` using simulators in `leftSimulators` and `rightSimulators`. -/
def ConstructsWithin [MonoidalCategory C] [CompatiblePseudoMetric C Phi]
    -- `setup` supplies the five honest/dishonest resource evaluations.
    (setup : TwoPartySetup C A ALeft ARight Source LeftProtocol RightProtocol
      LeftSimulator RightSimulator)
    -- `εHonest`, `εLeft`, `εRight` are the untruncated `ENNReal` budgets for the three equations.
    (εHonest εLeft εRight : ENNReal)
    -- `leftSimulators` and `rightSimulators` are the admitted simulator classes for parties 1, 2.
    (leftSimulators : Set LeftSimulator) (rightSimulators : Set RightSimulator)
    -- `protocol = (π₁, π₂)` is the candidate two-party protocol.
    (protocol : LeftProtocol × RightProtocol)
    -- `source = R` is the assumed resource and `target = S` is the target resource.
    (source : Source) (target : Phi A) : Prop :=
  Δ (setup.realHonest protocol.1 protocol.2 source) target ≤ εHonest ∧
    (∃ σ₁ ∈ leftSimulators,
      Δ (setup.realRight protocol.2 source) (setup.simulatedLeft σ₁ target) ≤ εLeft) ∧
    (∃ σ₂ ∈ rightSimulators,
      Δ (setup.realLeft protocol.1 source) (setup.simulatedRight target σ₂) ≤ εRight)

end TwoPartySetup

/-- Explicit two-ended plugging structure at a fixed source resource `source` (the neutral channel
of [1, Appendix C, Theorem 4, pp. 18–19]).

The plugging equations are indexed by `source` rather than all of `Source`: `plug_assoc` captures
neutrality of `source` under inserting `source` between `S σ₂` and `π₂`, which holds for a
neutral channel and fails for nontrivial setup resources. -/
structure TwoPartyPlugging
    -- `C` is the interface category and `Phi` its resource theory.
    {C : Type u} [Category.{v} C] {Phi : C → Type w} [ResourceTheory C Phi]
    -- `A`, `ALeft`, `ARight` are the honest and two dishonest-party interfaces.
    {A ALeft ARight : C}
    -- `Source`, protocol and simulator carriers match `setup`; `Bridge` carries composite bridges.
    {Source : Type u₁} {LeftProtocol : Type u₂} {RightProtocol : Type u₃}
    {LeftSimulator : Type u₄} {RightSimulator : Type u₅}
    (setup : TwoPartySetup C A ALeft ARight Source LeftProtocol RightProtocol
      LeftSimulator RightSimulator)
    (source : Source) (Bridge : Type u₆) where
  /-- Converter plugging right protocol `π₂` onto a resource at `ARight` to produce `A`. -/
  plugRight : RightProtocol → (A ⟶ ARight)
  /-- Converter plugging `S σ₂` on the left of a resource at `ALeft` to produce `A`. -/
  plugLeft : Phi A → RightSimulator → (A ⟶ ALeft)
  /-- Compose a right-party simulator `σ₂` with a left-party simulator `σ₁` into a bridge `σ₂ σ₁`.
  -/
  composeBridge : RightSimulator → LeftSimulator → Bridge
  /-- Plug two copies of a two-party resource through a bridge: `S γ S'`. -/
  plugBridge : Phi A → Bridge → Phi A → Phi A
  /-- Plugging `π₂` on the right of `π₁ R` produces the honest execution `π₁ R π₂`. -/
  plug_honest : ∀ (π₁ : LeftProtocol) (π₂ : RightProtocol),
    plugRight π₂ • setup.realLeft π₁ source = setup.realHonest π₁ π₂ source
  /-- Two-ended associativity across the neutral channel `source`: `(S σ₂) · π₂ = (S σ₂) · (R π₂)`.
  -/
  plug_assoc : ∀ (π₂ : RightProtocol) (σ₂ : RightSimulator) (S : Phi A),
    plugRight π₂ • setup.simulatedRight S σ₂ =
      plugLeft S σ₂ • setup.realRight π₂ source
  /-- Plugging `σ₁ S` on the right of `S σ₂` yields the bridged double resource `S (σ₂ σ₁) S`. -/
  plug_compose : ∀ (σ₁ : LeftSimulator) (σ₂ : RightSimulator) (S : Phi A),
    plugLeft S σ₂ • setup.simulatedLeft σ₁ S = plugBridge S (composeBridge σ₂ σ₁) S

section Qualitative

variable {C : Type u} [Category.{v} C] {Phi : C → Type w} [ResourceTheory C Phi]
variable {A ALeft ARight : C}
variable {Source : Type u₁} {LeftProtocol : Type u₂} {RightProtocol : Type u₃}
variable {LeftSimulator : Type u₄} {RightSimulator : Type u₅} {Bridge : Type u₆}

/-- **Algebraic neutral-channel equation** [1, Appendix C, Theorem 4, pp. 18–19]:
“if there exists a protocol `π = (π₁, π₂)` that constructs `S` from a neutral channel, then
there exists a converter `γ` such that `S γ S ≈ S`.”

Here the three simulation equations for `(π₁, π₂)` and `(σ₁, σ₂)` imply
`S (composeBridge σ₂ σ₁) S ≈ S` via a three-step `SubstitutionRelation.substitutes_of_hybrid`
chain through `plugRight π₂` and `plugLeft S σ₂`. -/
theorem bridge_substitutes_of_equations
    -- `setup` gives the five evaluations; `source` is the neutral channel; `plug` gives the
    -- three two-ended plugging equations at `source`.
    {setup : TwoPartySetup C A ALeft ARight Source LeftProtocol RightProtocol
      LeftSimulator RightSimulator}
    {source : Source} (plug : TwoPartyPlugging setup source Bridge)
    -- `relation` is the chosen substitution relation `≈`.
    (relation : SubstitutionRelation C)
    -- `π₁`, `π₂` are the protocol components; `σ₁`, `σ₂` are the two simulators; `target = S`.
    {π₁ : LeftProtocol} {π₂ : RightProtocol} {σ₁ : LeftSimulator} {σ₂ : RightSimulator}
    {target : Phi A}
    -- The three simulation equations: honest availability, dishonest left, dishonest right.
    (honest : relation.substitutes A (setup.realHonest π₁ π₂ source) target)
    (dishonestLeft :
      relation.substitutes ALeft (setup.realRight π₂ source) (setup.simulatedLeft σ₁ target))
    (dishonestRight :
      relation.substitutes ARight (setup.realLeft π₁ source) (setup.simulatedRight target σ₂)) :
    relation.substitutes A (plug.plugBridge target (plug.composeBridge σ₂ σ₁) target) target := by
  -- Assemble the three-step hybrid chain:
  --   target ≈ π₁ R π₂ = plugRight π₂ • (π₁ R) ≈ plugRight π₂ • (S σ₂)
  --          = plugLeft S σ₂ • (R π₂) ≈ plugLeft S σ₂ • (σ₁ S) = S (σ₂ σ₁) S.
  let iface : Fin 3 → C
    | ⟨0, _⟩ => A
    | ⟨1, _⟩ => ARight
    | ⟨2, _⟩ => ALeft
  let left : ∀ i : Fin 3, Phi (iface i)
    | ⟨0, _⟩ => target
    | ⟨1, _⟩ => setup.realLeft π₁ source
    | ⟨2, _⟩ => setup.realRight π₂ source
  let right : ∀ i : Fin 3, Phi (iface i)
    | ⟨0, _⟩ => setup.realHonest π₁ π₂ source
    | ⟨1, _⟩ => setup.simulatedRight target σ₂
    | ⟨2, _⟩ => setup.simulatedLeft σ₁ target
  let transform : ∀ i : Fin 3, A ⟶ iface i
    | ⟨0, _⟩ => 𝟙 A
    | ⟨1, _⟩ => plug.plugRight π₂
    | ⟨2, _⟩ => plug.plugLeft target σ₂
  have step : ∀ i : Fin 3, relation.substitutes (iface i) (left i) (right i)
    | ⟨0, _⟩ => (relation.symmetric A).symm _ _ honest
    | ⟨1, _⟩ => dishonestRight
    | ⟨2, _⟩ => dishonestLeft
  have link : ∀ i : Fin 2,
      transform i.castSucc • right i.castSucc = transform i.succ • left i.succ
    | ⟨0, _⟩ => (attach_identity (setup.realHonest π₁ π₂ source)).trans
        (plug.plug_honest π₁ π₂).symm
    | ⟨1, _⟩ => plug.plug_assoc π₂ σ₂ target
  have chain := relation.substitutes_of_hybrid left right transform step link
  -- Identify the endpoints `𝟙 A • S = S` and `plugLeft S σ₂ • (σ₁ S) = S (σ₂ σ₁) S`, then flip.
  rw [show transform 0 = 𝟙 A from rfl, show left 0 = target from rfl, attach_identity,
    show transform (Fin.last 2) = plug.plugLeft target σ₂ from rfl,
    show right (Fin.last 2) = setup.simulatedLeft σ₁ target from rfl] at chain
  change relation.substitutes A target
    (plug.plugLeft target σ₂ • setup.simulatedLeft σ₁ target) at chain
  rw [plug.plug_compose σ₁ σ₂ target] at chain
  exact (relation.symmetric A).symm _ _ chain

/-- Any admitted two-party construction from a neutral channel produces an admitted composite
bridge `γ ∈ bridges` with `S γ S ≈ S` [1, Appendix C, Theorem 4, pp. 18–19]. -/
theorem twoParty_bridge_substitutes
    -- `setup` gives the five evaluations; `source` is the neutral channel; `plug` supplies the
    -- two-ended plugging equations at `source`.
    {setup : TwoPartySetup C A ALeft ARight Source LeftProtocol RightProtocol
      LeftSimulator RightSimulator}
    {source : Source} (plug : TwoPartyPlugging setup source Bridge)
    -- `relation` is the substitution relation `≈`.
    (relation : SubstitutionRelation C)
    -- `protocols` is the admitted protocol class; `leftSimulators`, `rightSimulators` are the
    -- admitted simulator classes; `bridges` is the admitted composite-bridge class.
    {protocols : Set (LeftProtocol × RightProtocol)}
    {leftSimulators : Set LeftSimulator} {rightSimulators : Set RightSimulator}
    {bridges : Set Bridge}
    -- Composition closure: composing admitted `σ₂ ∈ rightSimulators` and `σ₁ ∈ leftSimulators`
    -- lands in `bridges`.
    (closed : ∀ σ₂ ∈ rightSimulators, ∀ σ₁ ∈ leftSimulators, plug.composeBridge σ₂ σ₁ ∈ bridges)
    -- `target = S` is constructible from `source` by some admitted protocol in `protocols`.
    {target : Phi A}
    (construction : Constructible (setup.Constructs relation leftSimulators rightSimulators)
      protocols source target) :
    ∃ γ ∈ bridges, relation.substitutes A (plug.plugBridge target γ target) target := by
  obtain ⟨⟨π₁, π₂⟩, -, honest, ⟨σ₁, hσ₁, dishonestLeft⟩, ⟨σ₂, hσ₂, dishonestRight⟩⟩ :=
    construction
  exact ⟨plug.composeBridge σ₂ σ₁, closed σ₂ hσ₂ σ₁ hσ₁,
    bridge_substitutes_of_equations plug relation honest dishonestLeft dishonestRight⟩

/-- **Two-party algebraic construction obstruction** [1, Appendix C, Theorem 4, pp. 18–19]:
if `S` is separated from `S γ S` for every admitted bridge `γ ∈ bridges`, then `S` is
`Unconstructible` from the neutral channel `source` by any protocol in `protocols` with
simulators in `leftSimulators` and `rightSimulators`. -/
theorem unconstructible_of_bridge_separation
    -- `setup` gives the five evaluations; `source` is the neutral channel; `plug` supplies the
    -- two-ended plugging equations at `source`.
    {setup : TwoPartySetup C A ALeft ARight Source LeftProtocol RightProtocol
      LeftSimulator RightSimulator}
    {source : Source} (plug : TwoPartyPlugging setup source Bridge)
    -- `relation` is the substitution relation `≈`.
    (relation : SubstitutionRelation C)
    -- `protocols`, `leftSimulators`, `rightSimulators` and `bridges` are the admitted classes.
    {protocols : Set (LeftProtocol × RightProtocol)}
    {leftSimulators : Set LeftSimulator} {rightSimulators : Set RightSimulator}
    {bridges : Set Bridge}
    -- Bridge composition closure for admitted simulators.
    (closed : ∀ σ₂ ∈ rightSimulators, ∀ σ₁ ∈ leftSimulators, plug.composeBridge σ₂ σ₁ ∈ bridges)
    -- `target = S` is separated from every bridged double copy `S γ S` with `γ ∈ bridges`.
    {target : Phi A}
    (separated : ∀ γ ∈ bridges, ¬ relation.substitutes A (plug.plugBridge target γ target) target) :
    Unconstructible (setup.Constructs relation leftSimulators rightSimulators)
      protocols source target := by
  intro construction
  obtain ⟨γ, admitted, equiv⟩ := twoParty_bridge_substitutes plug relation closed construction
  exact separated γ admitted equiv

end Qualitative

section Quantitative

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : C → Type w} [ResourceTheory C Phi] [CompatiblePseudoMetric C Phi]
variable {A ALeft ARight : C}
variable {Source : Type u₁} {LeftProtocol : Type u₂} {RightProtocol : Type u₃}
variable {LeftSimulator : Type u₄} {RightSimulator : Type u₅} {Bridge : Type u₆}

/-- Quantitative counterpart of `bridge_substitutes_of_equations`: the three simulation distance
bounds add across the three-step hybrid chain to bound `Δ (S (σ₂ σ₁) S) S` by
`εHonest + εRight + εLeft`. -/
theorem bridge_distance_le_of_bounds
    -- `setup`, `source` and `plug` supply the two-party evaluations and plugging equations.
    {setup : TwoPartySetup C A ALeft ARight Source LeftProtocol RightProtocol
      LeftSimulator RightSimulator}
    {source : Source} (plug : TwoPartyPlugging setup source Bridge)
    -- `π₁`, `π₂` are the protocol components; `σ₁`, `σ₂` are the simulators; `target = S`.
    {π₁ : LeftProtocol} {π₂ : RightProtocol} {σ₁ : LeftSimulator} {σ₂ : RightSimulator}
    {target : Phi A}
    -- `εHonest`, `εLeft`, `εRight` are the untruncated `ENNReal` distance bounds.
    {εHonest εLeft εRight : ENNReal}
    (honest : Δ (setup.realHonest π₁ π₂ source) target ≤ εHonest)
    (dishonestLeft : Δ (setup.realRight π₂ source) (setup.simulatedLeft σ₁ target) ≤ εLeft)
    (dishonestRight :
      Δ (setup.realLeft π₁ source) (setup.simulatedRight target σ₂) ≤ εRight) :
    Δ (plug.plugBridge target (plug.composeBridge σ₂ σ₁) target) target ≤
      εHonest + εRight + εLeft := by
  -- Run the same three-step chain quantitatively through `distance_hybrid_le`.
  let iface : Fin 3 → C
    | ⟨0, _⟩ => A
    | ⟨1, _⟩ => ARight
    | ⟨2, _⟩ => ALeft
  let left : ∀ i : Fin 3, Phi (iface i)
    | ⟨0, _⟩ => target
    | ⟨1, _⟩ => setup.realLeft π₁ source
    | ⟨2, _⟩ => setup.realRight π₂ source
  let right : ∀ i : Fin 3, Phi (iface i)
    | ⟨0, _⟩ => setup.realHonest π₁ π₂ source
    | ⟨1, _⟩ => setup.simulatedRight target σ₂
    | ⟨2, _⟩ => setup.simulatedLeft σ₁ target
  let transform : ∀ i : Fin 3, A ⟶ iface i
    | ⟨0, _⟩ => 𝟙 A
    | ⟨1, _⟩ => plug.plugRight π₂
    | ⟨2, _⟩ => plug.plugLeft target σ₂
  let err : Fin 3 → ENNReal
    | ⟨0, _⟩ => εHonest
    | ⟨1, _⟩ => εRight
    | ⟨2, _⟩ => εLeft
  have step : ∀ i : Fin 3, Δ (left i) (right i) ≤ err i
    | ⟨0, _⟩ => (distance_comm _ _).trans_le honest
    | ⟨1, _⟩ => dishonestRight
    | ⟨2, _⟩ => dishonestLeft
  have link : ∀ i : Fin 2,
      transform i.castSucc • right i.castSucc = transform i.succ • left i.succ
    | ⟨0, _⟩ => (attach_identity (setup.realHonest π₁ π₂ source)).trans
        (plug.plug_honest π₁ π₂).symm
    | ⟨1, _⟩ => plug.plug_assoc π₂ σ₂ target
  have chain := SubstitutionRelation.distance_hybrid_le left right transform err step link
  rw [show transform 0 = 𝟙 A from rfl, show left 0 = target from rfl, attach_identity,
    show transform (Fin.last 2) = plug.plugLeft target σ₂ from rfl,
    show right (Fin.last 2) = setup.simulatedLeft σ₁ target from rfl,
    Fin.sum_univ_three] at chain
  change Δ target (plug.plugLeft target σ₂ • setup.simulatedLeft σ₁ target) ≤
    εHonest + εRight + εLeft at chain
  rw [plug.plug_compose σ₁ σ₂ target] at chain
  exact (distance_comm _ _).trans_le chain

/-- Any quantitative two-party construction within `(εHonest, εLeft, εRight)` yields an admitted
composite bridge `γ ∈ bridges` with `Δ (S γ S) S ≤ εHonest + εRight + εLeft`. -/
theorem twoParty_bridge_distance_le
    -- `setup`, `source` and `plug` supply the two-party evaluations and neutral-channel plugging.
    {setup : TwoPartySetup C A ALeft ARight Source LeftProtocol RightProtocol
      LeftSimulator RightSimulator}
    {source : Source} (plug : TwoPartyPlugging setup source Bridge)
    -- `εHonest`, `εLeft`, `εRight` are the three simulation distance budgets.
    {εHonest εLeft εRight : ENNReal}
    -- `protocols`, `leftSimulators`, `rightSimulators` and `bridges` are the admitted classes.
    {protocols : Set (LeftProtocol × RightProtocol)}
    {leftSimulators : Set LeftSimulator} {rightSimulators : Set RightSimulator}
    {bridges : Set Bridge}
    -- Bridge composition closure for admitted simulators.
    (closed : ∀ σ₂ ∈ rightSimulators, ∀ σ₁ ∈ leftSimulators, plug.composeBridge σ₂ σ₁ ∈ bridges)
    -- `target = S` is quantitatively constructible from `source` by some protocol in `protocols`.
    {target : Phi A}
    (construction : Constructible
      (setup.ConstructsWithin εHonest εLeft εRight leftSimulators rightSimulators)
      protocols source target) :
    ∃ γ ∈ bridges, Δ (plug.plugBridge target γ target) target ≤
      εHonest + εRight + εLeft := by
  obtain ⟨⟨π₁, π₂⟩, -, honest, ⟨σ₁, hσ₁, dishonestLeft⟩, ⟨σ₂, hσ₂, dishonestRight⟩⟩ :=
    construction
  exact ⟨plug.composeBridge σ₂ σ₁, closed σ₂ hσ₂ σ₁ hσ₁,
    bridge_distance_le_of_bounds plug honest dishonestLeft dishonestRight⟩

/-- Quantitative two-party obstruction: if every admitted bridge `γ ∈ bridges` stays strictly
farther than `εHonest + εRight + εLeft` from `S`, then `S` is `Unconstructible` from `source`
within `(εHonest, εLeft, εRight)`. -/
theorem unconstructible_of_bridge_distance_gt
    -- `setup`, `source` and `plug` supply the two-party evaluations and neutral-channel plugging.
    {setup : TwoPartySetup C A ALeft ARight Source LeftProtocol RightProtocol
      LeftSimulator RightSimulator}
    {source : Source} (plug : TwoPartyPlugging setup source Bridge)
    -- `εHonest`, `εLeft`, `εRight` are the three simulation distance budgets.
    {εHonest εLeft εRight : ENNReal}
    -- `protocols`, `leftSimulators`, `rightSimulators` and `bridges` are the admitted classes.
    {protocols : Set (LeftProtocol × RightProtocol)}
    {leftSimulators : Set LeftSimulator} {rightSimulators : Set RightSimulator}
    {bridges : Set Bridge}
    -- Bridge composition closure for admitted simulators.
    (closed : ∀ σ₂ ∈ rightSimulators, ∀ σ₁ ∈ leftSimulators, plug.composeBridge σ₂ σ₁ ∈ bridges)
    -- `target = S` stays strictly farther than `εHonest + εRight + εLeft` from every `S γ S`.
    {target : Phi A}
    (separated : ∀ γ ∈ bridges,
      εHonest + εRight + εLeft < Δ (plug.plugBridge target γ target) target) :
    Unconstructible (setup.ConstructsWithin εHonest εLeft εRight leftSimulators rightSimulators)
      protocols source target := by
  intro construction
  obtain ⟨γ, admitted, bound⟩ := twoParty_bridge_distance_le plug closed construction
  exact (separated γ admitted).not_ge bound

end Quantitative

end ConstructiveCryptography.Construction
