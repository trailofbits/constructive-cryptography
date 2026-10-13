import ConstructiveCryptography.Notation
import RandomSystems.Typed.Game
import RandomSystems.Typed.PresentedGame

/-!
# Games on interfaces

Interfaces are an instance of `Games`, the abstraction of CR18, §4.4.3, §4.5.1 and §4.7.2, and
of `DistinctionGames`, the abstraction of CR18, §§4.10–4.11; the instance is where these
abstractions meet random systems. Its field `Game A` is the typed games `TypedGame A`, MBO random
systems as CR18 instantiates games (§3.7.1). Winners and solvers are probabilistic distinguishers,
through their behaviors `Domain.SolverBehavior`: a winner does not see the MBO
(`DDE.blindMBO`).

For `Games`, the field `attachGame` is `TypedConverter.attachGame`, the attachment of the
MBO-forwarding lift `PDCBehavior.liftMBO`, and `winners` are the winning probabilities of the
solver behaviors.
The axiom `attachGame_identity` is discharged by `PDCBehavior.liftMBO_id` and
`PDCBehavior.attach_id`, `attachGame_serial` by `PDCBehavior.liftMBO_comp` and
`PDCBehavior.attach_comp`, and `closed_attach` by `Domain.SolverBehavior.absorb`.

For `DistinctionGames`, the field `solvers` is the pairs of the solver behaviors, `visible` is
`TypedGame.visible`, the visible system `RandomSystem.visible`, and `ConditionallyEquivalent` is
`RandomSystem.ConditionallyEquivalent`. The axiom `solvers_winner` holds by the definition of the
winners, `solvers_closed_attach` is discharged by `Domain.SolverBehavior.absorb`,
`visible_attachGame` by `RandomSystem.visible_attach_liftMBO`, and `advantage_le_win` by
`Domain.Distinguisher.advantage_le_winProbability`.

Conditional equivalence then bounds the distance of the visible system of a game by the
probability that its MBO is set on fixed queries (CR18, Theorem 4.17), through
`RandomSystem.transcriptDistance_visible_le_of_unsetProbability`. For a game presented by a
discrete game (`TypedGame.ofPDG`), the bound on the condition bounds the distance from the
presented typed system.

## Main definitions

* `Interface.winners A`, `Interface.solvers A`: the winners and solvers on `A`
* `Interface.games`, `Interface.distinctionGames`: the instances

## Main results

* `Interface.win_le`: a bound on winning by every distinguisher bounds winning by every winner
* `Interface.dist_visible_le`: conditional equivalence bounds the distance of the visible
  typed system
* `Interface.conditionallyEquivalent_ofPDG_iff`: the conditional equivalence of a presented game
  is that of the game on random systems
* `Interface.game_dist_le`, `Interface.game_dist_ofSingleFunction_le`: the distance bound for a
  presented game and for a single-label sampled-function game
-/

namespace SystemAlgebra.Interface

open CategoryTheory ConstructiveCryptography Probability
open scoped SystemAlgebra NNReal

/-- The winners on `A`: the winning probabilities of the solver behaviors on the input domain of
`A`. -/
def winners (A : Interface) : Set (TypedGame A → ℝ) :=
  Set.range fun s : Domain.SolverBehavior (Y := A.Y) A.domain A.bound A.length_le =>
    fun G => s.1.2 ⟨G.1.1, G.1.2, G.2⟩

/-- The solvers on `A`: the solver behaviors on the input domain of `A`. -/
def solvers (A : Interface) : Set ((TypedSystem A → ℝ) × (TypedGame A → ℝ)) :=
  Set.range fun s : Domain.SolverBehavior (Y := A.Y) A.domain A.bound A.length_le =>
    (fun R => s.1.1 R, fun G => s.1.2 ⟨G.1.1, G.1.2, G.2⟩)

/-- **Interfaces are an instance of `Games`**: attachment is the attachment of the lift, and the
winners are the winning probabilities of the solver behaviors. -/
noncomputable instance games : Games Interface TypedGame where
  -- Field `attachGame`: the systems-level attachment `PDCBehavior.attach` of the lift
  -- `PDCBehavior.liftMBO α` to the game's random system.
  attachGame := TypedConverter.attachGame
  -- Axiom `attachGame_identity`, discharged by the systems-level theorems
  -- `PDCBehavior.liftMBO_id` (the lift of the identity PDC is the identity PDC) and
  -- `PDCBehavior.attach_id` (attaching the identity PDC leaves a random system unchanged,
  -- used here as `TypedConverter.identity_attach`).
  attachGame_identity {A} G := by
    -- Two games are equal when their typed systems are.
    apply Subtype.ext
    change TypedConverter.attach (PDCBehavior.liftMBO (𝟙 A)) G.1 = G.1
    -- The lift of the identity converter is the identity converter on `A.withMBO`.
    rw [show PDCBehavior.liftMBO (𝟙 A) = TypedConverter.id A.withMBO from
      PDCBehavior.liftMBO_id _]
    -- Attaching the identity converter leaves the game's typed system unchanged.
    exact TypedConverter.identity_attach G.1
  -- Axiom `attachGame_serial`, discharged by the systems-level theorems
  -- `PDCBehavior.liftMBO_comp` (the lift of `α ≫ β` is the composition of the lifts) and
  -- `PDCBehavior.attach_comp` (attaching a serial composition is nested attachment, used
  -- here as `TypedConverter.comp_smul`).
  attachGame_serial {A B C} α β G := by
    -- Two games are equal when their typed systems are.
    apply Subtype.ext
    change TypedConverter.attach (PDCBehavior.liftMBO (α ≫ β)) G.1 =
      TypedConverter.attach (A := A.withMBO) (PDCBehavior.liftMBO α)
        (TypedConverter.attach (A := B.withMBO) (PDCBehavior.liftMBO β) G.1)
    -- The lift is functorial: lift (α ≫ β) = lift α ≫ lift β.
    rw [show PDCBehavior.liftMBO (α ≫ β) = TypedConverter.comp (A := A.withMBO) (B := B.withMBO)
      (C := C.withMBO) (PDCBehavior.liftMBO α) (PDCBehavior.liftMBO β) from
      PDCBehavior.liftMBO_comp α β]
    -- (lift α ≫ lift β) • G = lift α • (lift β • G): attach the inner converter first.
    exact TypedConverter.comp_smul _ _ G.1
  -- Field `winners`: the winning probabilities of the systems-level solver behaviors
  -- `Domain.SolverBehavior` on the input domain.
  winners := winners
  -- Axiom `closed_attach`, discharged by the systems-level construction
  -- `Domain.SolverBehavior.absorb` (a solver behavior with a PDC absorbed).
  closed_attach {A B} α := by
    -- The winner on `A` is the winning probability of a solver behavior `s`.
    rintro _ ⟨s, rfl⟩
    -- Absorb `α` into `s`: a solver behavior on `B`, which wins `G` as `s` wins the lift of
    -- `α` attached to `G`, by definition of the absorbed solver (`rfl`). The winner `s` does
    -- not see the MBO `a`:
    --
    --   ┌───────────────────────────┐
    --   │ ┌───┐ ──x────▶ ┌────────┐ │ ──u────▶ ┌───┐
    --   │ │ s │          │ lift α │ │          │ G │
    --   │ └───┘ ◀─(y,a)─ └────────┘ │ ◀─(v,a)─ └───┘
    --   └───────────────────────────┘
    exact ⟨Domain.SolverBehavior.absorb B.nonempty_prefix A.nonempty_prefix α s, rfl⟩

/-- **Interfaces are an instance of `DistinctionGames`** with carrier `TypedSystem` and games
`TypedGame`: the solvers are the solver behaviors, `visible` is `TypedGame.visible`, the visible
system, and conditional equivalence is that of the game's random system and the typed system's
random system. -/
noncomputable instance distinctionGames : DistinctionGames Interface TypedSystem TypedGame where
  toGames := games
  -- Field `solvers`: the pairs (decision probabilities, winning probabilities) of the
  -- systems-level solver behaviors `Domain.SolverBehavior`.
  solvers := solvers
  -- Axiom `solvers_winner`: the second component of a solver behavior is, by the definition
  -- of `winners`, a winner.
  solvers_winner := by
    rintro _ _ ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  -- Axiom `solvers_closed_attach`, discharged by the systems-level construction
  -- `Domain.SolverBehavior.absorb`: `s` with `α` absorbed decides on `R` as `s` decides on
  -- `α • R`, and wins `G` as `s` wins the lift of `α` attached to `G` (both by `rfl`).
  solvers_closed_attach {A B} α := by
    rintro _ ⟨s, rfl⟩
    exact ⟨Domain.SolverBehavior.absorb B.nonempty_prefix A.nonempty_prefix α s, rfl⟩
  -- Field `visible`: the systems-level visible system `RandomSystem.visible` (`S⁻`).
  visible := TypedGame.visible
  -- Axiom `visible_attachGame`, discharged by the systems-level theorem
  -- `RandomSystem.visible_attach_liftMBO`: `(lift α • G)⁻ = α • G⁻`.
  visible_attachGame {A B} α G :=
    Subtype.ext (RandomSystem.visible_attach_liftMBO B.nonempty_prefix A.nonempty_prefix α G.1.1
      G.1.2)
  -- Field `ConditionallyEquivalent`: the systems-level `RandomSystem.ConditionallyEquivalent`
  -- of the game's random system and the typed system's random system.
  ConditionallyEquivalent G T := G.1.1.ConditionallyEquivalent T.1
  -- Axiom `advantage_le_win`, discharged by the systems-level theorem
  -- `Domain.Distinguisher.advantage_le_winProbability` for the probabilistic distinguisher
  -- behind the solver behavior.
  advantage_le_win := by
    -- The solver is a solver behavior `s`.
    rintro A G T _ hc ⟨s, rfl⟩
    -- `s` comes from one probabilistic distinguisher `P`: its decisions are `P`'s decision
    -- probabilities (`hP`) and its winning probabilities are `P`'s (`hW`).
    obtain ⟨P, hP, hW⟩ := s.2
    change |s.1.1 G.visible - s.1.1 T| ≤ s.1.2 ⟨G.1.1, G.1.2, G.2⟩
    -- Rewrite the goal in terms of `P`:
    --   |Pr[P → 1 on G⁻] − Pr[P → 1 on T]| ≤ Pr[P sets the MBO of G]
    rw [hP G.visible, hP T, hW ⟨G.1.1, G.1.2, G.2⟩]
    -- Conditional equivalence `G |≡ T` bounds `P`'s advantage by its winning probability.
    exact P.advantage_le_winProbability G.1.2 T.2 G.2 hc

/-- **Winning by every distinguisher bounds winning by every winner**: a bound on the winning
probability of every distinguisher for the game's system bounds the winning probability of
every winner. -/
lemma win_le {A : Interface} {G : TypedGame A} {ε : ℝ}
    (hW : ∀ P : A.inputDomain.Distinguisher, P.winProbability G.1.1 ≤ ε)
    {winner : TypedGame A → ℝ} (hw : winner ∈ Games.winners A) : winner G ≤ ε := by
  -- The winner is the winning probability of a solver behavior `s`, which is that of one
  -- probabilistic distinguisher `P` (`hP`).
  obtain ⟨s, rfl⟩ := hw
  obtain ⟨P, -, hP⟩ := s.2
  change s.1.2 ⟨G.1.1, G.1.2, G.2⟩ ≤ ε
  -- So the winner wins `G` with `P`'s winning probability, which `hW` bounds.
  rw [hP]
  exact hW P

/-- **Conditional equivalence bounds the distance of the visible system** (CR18,
Theorem 4.17): a game on an interface conditionally equivalent to a typed system `T`, whose MBO
stays unset with probability at least `1 - ε` on the queries of each transcript of `T`, has its
visible typed system within `ε` of `T`. -/
theorem dist_visible_le {A : Interface} {G : TypedGame A} {T : TypedSystem A}
    (hc : DistinctionGames.ConditionallyEquivalent G T) {ε : ℝ≥0}
    (hε : ∀ h, T.1 h ≠ 0 → 1 - ε ≤ G.1.1.unsetProbability (h.map Prod.fst)) :
    CryptographicAlgebra.distance (DistinctionGames.visible G) T ≤ ε := by
  -- The distance of `CompatiblePseudoMetric` (its field `fibreMetric`) on interfaces is the
  -- systems-level transcript distance of the random systems.
  rw [cc_distance_eq]
  -- The systems-level bound: Δ(G⁻, T) ≤ ε when `G |≡ T` and the MBO of `G` stays unset with
  -- probability at least `1 - ε` on the queries of each transcript of `T`.
  exact RandomSystem.transcriptDistance_visible_le_of_unsetProbability G.1.2 T.2 G.2 hc hε

/-- The game a probabilistic discrete game presents is conditionally equivalent to a typed system
exactly when its game on random systems is conditionally equivalent to the typed system's random
system. -/
lemma conditionallyEquivalent_ofPDG_iff {A : Interface}
    (G : PDG (Σ i, A.X i) (Σ i, A.Y i) A.inputDomain) (hG : G.isProbDist) {R : TypedSystem A}
    (visible : R.1 = PDS.behavior G.underlying (PDG.underlying_probability hG))
    (S : TypedSystem A) :
    TypedGame.ofPDG G hG visible |≡ S ↔ (G.behavior hG).ConditionallyEquivalent S.1 :=
  -- The field `ConditionallyEquivalent` of `DistinctionGames` on interfaces is the
  -- systems-level `RandomSystem.ConditionallyEquivalent`, so both sides agree by definition.
  Iff.rfl

/-- **Conditional equivalence bounds the distance of a presented game**: if the visible systems
of a probabilistic discrete game `G` present `R`, the game it presents is conditionally
equivalent to `S`, and the condition holds with probability at most `ε` on the empty and on
every admitted query sequence, then `R` and `S` are at most `ε` apart. -/
theorem game_dist_le {A : Interface}
    {G : PDG (Σ i, A.X i) (Σ i, A.Y i) A.inputDomain} {hG : G.isProbDist} {R S : TypedSystem A}
    (visible : R.1 = PDS.behavior G.underlying (PDG.underlying_probability hG))
    (equiv : TypedGame.ofPDG G hG visible |≡ S) {ε : ℝ≥0}
    (hbad : ∀ xs, xs = [] ∨ A.domain xs → G.badProbability xs ≤ ε) :
    Δ R S ≤ ε := by
  --   Δ(R, S) = Δ((ofPDG G)⁻, S)   (`R` is the visible system of the presented game)
  --           ≤ ε                 (`ofPDG G |≡ S`, MBO unset with probability ≥ 1 - ε)
  --
  -- The bound on the condition gives the bound on the unset MBO on the queries of each
  -- transcript of `S` (`PDG.one_sub_le_unsetProbability_behavior`); `dist_visible_le` then
  -- bounds the distance of the visible system.
  have bound := dist_visible_le equiv
    (PDG.one_sub_le_unsetProbability_behavior hG A.nonempty_prefix hbad)
  -- The visible system of the presented game is `R` (`TypedGame.visible_ofPDG`).
  rwa [show DistinctionGames.visible (TypedGame.ofPDG G hG visible) = R from
    TypedGame.visible_ofPDG G hG visible] at bound

/-- **Conditional equivalence bounds the distance of a sampled-function game**: the typed system
sampling the function is at most `ε` from a typed system conditionally equivalent to the game
when the sampled condition holds with probability at most `ε` on the empty and on every admitted
query sequence. -/
lemma game_dist_ofSingleFunction_le {I K X Y : Type}
    [Unique I] [Fintype X] [Fintype Y] {D : List (Σ _ : I, X) → Prop}
    {hD : ¬ D [] ∧ ∀ {p h}, p <+: h → p ≠ [] → D h → D p} {bound : ℕ}
    {hb : ∀ h, D h → h.length ≤ bound}
    {P : Distribution K} [Distribution.IsProbability P] {f : K → X → Y} {bad : K → MC X}
    {R S : TypedSystem ⟨I, fun _ => X, fun _ => Y, D, hD, bound, hb⟩}
    (equiv : TypedGame.ofSingleFunction D hD bound hb P f bad |≡ S)
    (visible : R = TypedSystem.sample P (fun k => TypedSystem.ofFunction (fun _ => f k)))
    {ε : ℝ≥0}
    (hbad : ∀ xs, xs = [] ∨ D xs → P.mass (fun k => (bad k).1 (xs.map Sigma.snd)) ≤ ε) :
    Δ R S ≤ ε := by
  -- `R` is the typed system sampling the function.
  subst visible
  -- The distance bound for a presented game: `R` is presented by the visible systems of the
  -- sampled-function game, which is conditionally equivalent to `S`.
  refine game_dist_le (TypedSystem.sample_ofFunction_eq_behavior D hD bound hb P f bad) equiv
    fun xs hxs => ?_
  -- The condition holds on `xs` with the `P`-probability of a key whose condition holds on
  -- the values of `xs`, which `hbad` bounds by `ε`.
  rw [PDG.ofSingleFunction, PDG.ofFunction_badProbability]
  exact hbad xs hxs

end SystemAlgebra.Interface
