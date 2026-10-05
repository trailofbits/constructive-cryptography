import RandomSystems.Game.FunctionGame
import ConstructiveCryptography.InterfaceGame
import ConstructiveCryptography.Functional
import ConstructiveCryptography.Notation

/-!
# Games presented by discrete games

A probabilistic discrete game whose visible systems present a resource `R` presents a game on
the interface of `R`, the behavior of its deterministic games with the MBO, and the visible
resource of that game is `R`. Its conditional equivalence to a resource, the field of the
instance of `DistinctionGames`, is that of the game it presents on random systems. The bound of
conditional equivalence on games (`Interface.dist_visible_le`, CR18 Theorem 4.17) then bounds
the distance from `R` to a resource `S` conditionally equivalent to the game by any bound on the
condition on the empty and on every admitted query sequence. A single-label sampled function
with a hidden condition presents a game on its interface, conditionally equivalent to the
resource sampling the ideal function once the answers with the condition unset factor through
the ideal answers.

## Main definitions

* `G |≡ T`: conditional equivalence of a game to a resource
* `Interface.Game.ofPDG`: the game a probabilistic discrete game presents
* `Interface.Game.ofSingleFunction`: the game of a single-label sampled function

## Main results

* `Interface.Game.visible_ofPDG`: its visible resource is the presented resource
* `Interface.Game.conditionallyEquivalent_ofPDG_iff`: its conditional equivalence is that of the
  game on random systems
* `Interface.game_dist_le`: the distance bound for a presented game
* `Interface.Resource.sample_ofFunction_eq_behavior`: the resource sampling a single-label
  function is presented by the sampled-function game
* `Interface.ofSingleFunction_conditionallyEquivalent`: a single-label sampled-function game is
  conditionally equivalent to the resource sampling the ideal function, from the fixed-query
  factorization
* `Interface.game_dist_ofSingleFunction_le`: the distance bound for a single-label
  sampled-function game
-/

namespace SystemAlgebra

open Probability ConstructiveCryptography
open scoped SystemAlgebra

/-- Conditional equivalence `G |≡ T` of a game on an interface to a resource (CR18,
Definition 4.19): the field of the instance of `DistinctionGames`. -/
scoped notation:50 G:51 " |≡ " T:51 =>
  ConstructiveCryptography.DistinctionGames.ConditionallyEquivalent G T

namespace Interface

namespace Game

variable {A : Interface}

/-- **The game a probabilistic discrete game presents**: when the visible systems of `G` present
the resource `R`, the behavior of its deterministic games with the MBO is a game on the interface
of `R`. -/
noncomputable def ofPDG (G : PDG (Σ i, A.X i) (Σ i, A.Y i) A.inputDomain) (hG : G.isProbDist)
    {R : Resource A} (visible : R.1 = PDS.behavior G.underlying (PDG.underlying_probability hG)) :
    Game A :=
  ⟨⟨G.behavior hG, PDG.repliesAtQueriedInterface_behavior hG (visible ▸ R.2)⟩,
    PDG.monotoneMBO_behavior hG⟩

/-- The visible resource of the game a probabilistic discrete game presents is the resource its
visible systems present. -/
theorem visible_ofPDG (G : PDG (Σ i, A.X i) (Σ i, A.Y i) A.inputDomain) (hG : G.isProbDist)
    {R : Resource A} (visible : R.1 = PDS.behavior G.underlying (PDG.underlying_probability hG)) :
    DistinctionGames.visible (ofPDG G hG visible) = R :=
  Subtype.ext ((PDG.visible_behavior hG).trans visible.symm)

/-- The game a probabilistic discrete game presents is conditionally equivalent to a resource
exactly when its game on random systems is conditionally equivalent to the resource's random
system. -/
theorem conditionallyEquivalent_ofPDG_iff (G : PDG (Σ i, A.X i) (Σ i, A.Y i) A.inputDomain)
    (hG : G.isProbDist) {R : Resource A}
    (visible : R.1 = PDS.behavior G.underlying (PDG.underlying_probability hG)) (S : Resource A) :
    ofPDG G hG visible |≡ S ↔ (G.behavior hG).ConditionallyEquivalent S.1 :=
  Iff.rfl

end Game

/-- **Conditional equivalence bounds the distance of a presented game**: if the visible systems
of a probabilistic discrete game `G` present `R`, the game it presents is conditionally
equivalent to `S`, and the condition holds with probability at most `ε` on the empty and on
every admitted query sequence, then `R` and `S` are at most `ε` apart. -/
theorem game_dist_le {A : Interface}
    {G : PDG (Σ i, A.X i) (Σ i, A.Y i) A.inputDomain} {hG : G.isProbDist} {R S : Resource A}
    (visible : R.1 = PDS.behavior G.underlying (PDG.underlying_probability hG))
    (equiv : Game.ofPDG G hG visible |≡ S) {ε : ℝ}
    (hbad : ∀ xs, xs = [] ∨ A.domain xs → G.badProbability xs ≤ ε) :
    Δ R S ≤ ENNReal.ofReal ε := by
  have bound := dist_visible_le equiv
    (PDG.one_sub_le_unsetProbability_behavior hG A.nonempty_prefix hbad)
  rwa [Game.visible_ofPDG] at bound

/-- **The resource sampling a single-label function** is the behavior of the visible systems of
the sampled-function game. -/
theorem Resource.sample_ofFunction_eq_behavior {I K X Y : Type} [Unique I] [Fintype X]
    [Fintype Y] (D : List (Σ _ : I, X) → Prop)
    (hD : ¬ D [] ∧ ∀ {p h}, p <+: h → p ≠ [] → D h → D p) (bound : ℕ)
    (hb : ∀ h, D h → h.length ≤ bound) (P : Distribution K) [Distribution.IsProbability P]
    (f : K → X → Y) (bad : K → MC X) :
    (Resource.sample (A := ⟨I, fun _ => X, fun _ => Y, D, hD, bound, hb⟩) P
        (fun k => Resource.ofFunction (fun _ => f k))).1 =
      PDS.behavior (PDG.ofSingleFunction D hD bound hb P f bad).underlying
        (PDG.underlying_probability (PDG.ofFunction_isProbDist D hD bound hb
          (Distribution.IsProbability.isProbDist P) _ _)) := by
  apply RandomSystem.ext
  intro h
  rw [Resource.sample_ofFunction_mass]
  change _ = behaviorMass _ _ _
  rw [PDG.ofSingleFunction, PDG.ofFunction_underlying]
  simp only [behaviorMass, PDS.ofFunction, Distribution.mass_fTransform]

/-- **The game of a single-label sampled function** with a hidden condition: the game it presents
on its interface, whose visible resource samples the function. -/
noncomputable def Game.ofSingleFunction {I K X Y : Type} [Unique I] [Fintype X] [Fintype Y]
    (D : List (Σ _ : I, X) → Prop) (hD : ¬ D [] ∧ ∀ {p h}, p <+: h → p ≠ [] → D h → D p)
    (bound : ℕ) (hb : ∀ h, D h → h.length ≤ bound) (P : Distribution K)
    [Distribution.IsProbability P] (f : K → X → Y) (bad : K → MC X) :
    Game ⟨I, fun _ => X, fun _ => Y, D, hD, bound, hb⟩ :=
  Game.ofPDG (PDG.ofSingleFunction D hD bound hb P f bad)
    (PDG.ofFunction_isProbDist D hD bound hb (Distribution.IsProbability.isProbDist P) _ _)
    (Resource.sample_ofFunction_eq_behavior D hD bound hb P f bad)

open Classical in
/-- **A single-label sampled-function game is conditionally equivalent to the resource sampling
the ideal function** when, on every fixed query sequence, the answers jointly with the unset
condition factor through the ideal answers. -/
theorem ofSingleFunction_conditionallyEquivalent {I K X Y : Type} [Unique I] [Fintype X]
    [Fintype Y] (D : List (Σ _ : I, X) → Prop)
    (hD : ¬ D [] ∧ ∀ {p h}, p <+: h → p ≠ [] → D h → D p) (bound : ℕ)
    (hb : ∀ h, D h → h.length ≤ bound)
    (P : Distribution K) [Distribution.IsProbability P]
    (f : K → X → Y) (bad : K → MC X)
    (Q : Distribution (X → Y)) [Distribution.IsProbability Q]
    (factor : ∀ xs (answers : X → Y),
      P.mass (fun k => (∀ x ∈ xs, f k x = answers x) ∧ ¬ (bad k).1 xs) =
        Q.mass (fun g => ∀ x ∈ xs, g x = answers x) *
          P.mass (fun k => ¬ (bad k).1 xs)) :
    Game.ofSingleFunction D hD bound hb P f bad |≡
      Resource.sample (A := ⟨I, fun _ => X, fun _ => Y, D, hD, bound, hb⟩)
        Q (fun g => Resource.ofFunction (fun _ => g)) := by
  refine (Game.conditionallyEquivalent_ofPDG_iff _ _
    (Resource.sample_ofFunction_eq_behavior D hD bound hb P f bad) _).mpr ?_
  unfold PDG.ofSingleFunction
  let tagged := fun g : X → Y => fun x : Σ _ : I, X => (⟨x.1, g x.2⟩ : Σ _ : I, Y)
  let taggedLaw := Distribution.fTransform tagged Q
  have hQ := Distribution.IsProbability.isProbDist taggedLaw
  have hP := Distribution.IsProbability.isProbDist P
  have equiv := PDG.ofFunction_conditionallyEquivalent D hD bound hb P (fun k => tagged (f k))
    (fun k => ⟨fun xs => (bad k).1 (xs.map Sigma.snd),
      fun {_ _} hp => (bad k).2 (hp.map Sigma.snd)⟩)
    (hG := by exact PDG.ofFunction_isProbDist D hD bound hb hP _ _) taggedLaw hQ (by
      intro xs answers
      dsimp only [taggedLaw]
      rw [Distribution.mass_fTransform]
      simp only [tagged, single_interface_answers_iff]
      have he := factor (xs.map Sigma.snd) (fun x => (answers ⟨default, x⟩).2)
      have complement := Distribution.mass_add_compl P
        (fun k => (bad k).1 (xs.map Sigma.snd))
      rw [Distribution.IsProbability.weight_eq_one (X := P)] at complement
      have good : P.mass (fun k => ¬ (bad k).1 (xs.map Sigma.snd)) =
          1 - P.mass (fun k => (bad k).1 (xs.map Sigma.snd)) := by linarith
      rw [good, mul_comm] at he
      exact he)
  intro h
  convert equiv h using 2
  rw [Resource.sample_ofFunction_mass]
  change _ = behaviorMass _ _ _
  simp only [behaviorMass, PDS.ofFunction, taggedLaw, Distribution.mass_fTransform]
  rfl

/-- **Conditional equivalence bounds the distance of a sampled-function game**: the resource
sampling the function is at most `ε` from a resource conditionally equivalent to the game when
the sampled condition holds with probability at most `ε` on the empty and on every admitted
query sequence. -/
theorem game_dist_ofSingleFunction_le {I K X Y : Type}
    [Unique I] [Fintype X] [Fintype Y] {D : List (Σ _ : I, X) → Prop}
    {hD : ¬ D [] ∧ ∀ {p h}, p <+: h → p ≠ [] → D h → D p} {bound : ℕ}
    {hb : ∀ h, D h → h.length ≤ bound}
    {P : Distribution K} [Distribution.IsProbability P] {f : K → X → Y} {bad : K → MC X}
    {R S : Resource ⟨I, fun _ => X, fun _ => Y, D, hD, bound, hb⟩}
    (equiv : Game.ofSingleFunction D hD bound hb P f bad |≡ S)
    (visible : R = Resource.sample P (fun k => Resource.ofFunction (fun _ => f k))) {ε : ℝ}
    (hbad : ∀ xs, xs = [] ∨ D xs → P.mass (fun k => (bad k).1 (xs.map Sigma.snd)) ≤ ε) :
    Δ R S ≤ ENNReal.ofReal ε := by
  subst visible
  refine game_dist_le (Resource.sample_ofFunction_eq_behavior D hD bound hb P f bad) equiv
    fun xs hxs => ?_
  rw [PDG.ofSingleFunction, PDG.ofFunction_badProbability]
  exact hbad xs hxs

end Interface

end SystemAlgebra
