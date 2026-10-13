import RandomSystems.Game.FunctionGame
import RandomSystems.Typed.Game
import RandomSystems.Typed.Functional

/-!
# Typed games presented by discrete games

A probabilistic discrete game whose visible systems present a typed system `R` presents a typed
game on the interface of `R`, the behavior of its deterministic games with the MBO, and the
visible typed system of that game is `R`. A single-label sampled function with a hidden
condition presents a typed game on its interface, conditionally equivalent to the typed system
sampling the ideal function once the answers with the condition unset factor through the ideal
answers.

## Main definitions

* `TypedGame.ofPDG`: the typed game a probabilistic discrete game presents
* `TypedGame.ofSingleFunction`: the typed game of a single-label sampled function

## Main results

* `TypedGame.visible_ofPDG`: its visible typed system is the presented typed system
* `TypedSystem.sample_ofFunction_eq_behavior`: the typed system sampling a single-label function
  is presented by the sampled-function game
* `TypedGame.ofSingleFunction_conditionallyEquivalent`: a single-label sampled-function game is
  conditionally equivalent to the typed system sampling the ideal function, from the
  fixed-query factorization
-/

namespace SystemAlgebra

open Probability

namespace TypedGame

variable {A : Interface}

/-- **The typed game a probabilistic discrete game presents**: when the visible systems of `G`
present the typed system `R`, the behavior of its deterministic games with the MBO is a typed game
on the interface of `R`. -/
noncomputable def ofPDG (G : PDG (Σ i, A.X i) (Σ i, A.Y i) A.inputDomain) (hG : G.isProbDist)
    {R : TypedSystem A}
    (visible : R.1 = PDS.behavior G.underlying (PDG.underlying_probability hG)) : TypedGame A :=
  -- The random system is the behavior of `G` with the MBO. It replies at the queried interface
  -- because its visible system, `R`, does, and its MBO once set stays set.
  ⟨⟨G.behavior hG, PDG.repliesAtQueriedInterface_behavior hG (visible ▸ R.2)⟩,
    PDG.monotoneMBO_behavior hG⟩

/-- The visible typed system of the typed game a probabilistic discrete game presents is the
typed system its visible systems present. -/
lemma visible_ofPDG (G : PDG (Σ i, A.X i) (Σ i, A.Y i) A.inputDomain) (hG : G.isProbDist)
    {R : TypedSystem A}
    (visible : R.1 = PDS.behavior G.underlying (PDG.underlying_probability hG)) :
    (ofPDG G hG visible).visible = R :=
  -- The visible system of the behavior of `G` is the behavior of its visible systems
  -- (`PDG.visible_behavior`), which is `R`.
  Subtype.ext ((PDG.visible_behavior hG).trans visible.symm)

end TypedGame

/-- **The typed system sampling a single-label function** is the behavior of the visible systems
of the sampled-function game. -/
lemma TypedSystem.sample_ofFunction_eq_behavior {I K X Y : Type} [Unique I] [Fintype X]
    [Fintype Y] (D : List (Σ _ : I, X) → Prop)
    (hD : ¬ D [] ∧ ∀ {p h}, p <+: h → p ≠ [] → D h → D p) (bound : ℕ)
    (hb : ∀ h, D h → h.length ≤ bound) (P : Distribution K) [Distribution.IsProbability P]
    (f : K → X → Y) (bad : K → MC X) :
    (TypedSystem.sample (A := ⟨I, fun _ => X, fun _ => Y, D, hD, bound, hb⟩) P
        (fun k => TypedSystem.ofFunction (fun _ => f k))).1 =
      PDS.behavior (PDG.ofSingleFunction D hD bound hb P f bad).underlying
        (PDG.underlying_probability (PDG.ofFunction_isProbDist D hD bound hb
          (Distribution.IsProbability.isProbDist P) _ _)) := by
  -- Compare the two random systems transcript by transcript.
  apply RandomSystem.ext
  intro h
  -- The typed system sampling the function gives `h` the probability that the DDS answering
  -- with the sampled function replies with `h`.
  rw [TypedSystem.sample_ofFunction_mass]
  change _ = behaviorMass _ _ _
  -- The visible systems of the sampled-function game are the sampled function
  -- (`PDG.ofFunction_underlying`), with its answers tagged with the single label.
  rw [PDG.ofSingleFunction, PDG.ofFunction_underlying]
  -- Both sides are the probability, over `k ∼ P`, that the DDS of `f k` replies with `h`.
  simp only [behaviorMass, PDS.ofFunction, Distribution.mass_fTransform]

/-- **The typed game of a single-label sampled function** with a hidden condition: the typed game
it presents on its interface, whose visible typed system samples the function. -/
noncomputable def TypedGame.ofSingleFunction {I K X Y : Type} [Unique I] [Fintype X] [Fintype Y]
    (D : List (Σ _ : I, X) → Prop) (hD : ¬ D [] ∧ ∀ {p h}, p <+: h → p ≠ [] → D h → D p)
    (bound : ℕ) (hb : ∀ h, D h → h.length ≤ bound) (P : Distribution K)
    [Distribution.IsProbability P] (f : K → X → Y) (bad : K → MC X) :
    TypedGame ⟨I, fun _ => X, fun _ => Y, D, hD, bound, hb⟩ :=
  TypedGame.ofPDG (PDG.ofSingleFunction D hD bound hb P f bad)
    (PDG.ofFunction_isProbDist D hD bound hb (Distribution.IsProbability.isProbDist P) _ _)
    (TypedSystem.sample_ofFunction_eq_behavior D hD bound hb P f bad)

open Classical in
/-- **A single-label sampled-function game is conditionally equivalent to the typed system
sampling the ideal function** when, on every fixed query sequence, the answers jointly with the
unset condition factor through the ideal answers. -/
lemma TypedGame.ofSingleFunction_conditionallyEquivalent {I K X Y : Type} [Unique I] [Fintype X]
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
    (TypedGame.ofSingleFunction D hD bound hb P f bad).1.1.ConditionallyEquivalent
      (TypedSystem.sample (A := ⟨I, fun _ => X, fun _ => Y, D, hD, bound, hb⟩)
        Q (fun g => TypedSystem.ofFunction (fun _ => g))).1 := by
  -- Plan:
  --   1. The typed game's random system is the behavior of the sampled-function game.
  --   2. Apply the systems-level `PDG.ofFunction_conditionallyEquivalent` with the ideal law
  --      `taggedLaw` (`Q`, its answers tagged with the single label); its factorization
  --      hypothesis follows from `factor`.
  --   3. Identify the ideal random system of step 2 with the typed system sampling `Q`.
  --
  -- Step 1: the typed game's random system is the behavior of the sampled-function game.
  change ((PDG.ofSingleFunction D hD bound hb P f bad).behavior
    (PDG.ofFunction_isProbDist D hD bound hb (Distribution.IsProbability.isProbDist P) _ _)
    ).ConditionallyEquivalent _
  unfold PDG.ofSingleFunction
  -- Step 2: a function `X → Y` as a function on the single interface, and the ideal law.
  let tagged := fun g : X → Y => fun x : Σ _ : I, X => (⟨x.1, g x.2⟩ : Σ _ : I, Y)
  let taggedLaw := Distribution.fTransform tagged Q
  have hQ := Distribution.IsProbability.isProbDist taggedLaw
  have hP := Distribution.IsProbability.isProbDist P
  -- The sampled-function game, its condition read on the values of the queries, is
  -- conditionally equivalent to the function sampled from `taggedLaw`.
  have equiv := PDG.ofFunction_conditionallyEquivalent D hD bound hb P (fun k => tagged (f k))
    (fun k => ⟨fun xs => (bad k).1 (xs.map Sigma.snd),
      fun {_ _} hp => (bad k).2 (hp.map Sigma.snd)⟩)
    (hG := by exact PDG.ofFunction_isProbDist D hD bound hb hP _ _) taggedLaw hQ (by
      -- The factorization on a fixed query sequence `xs`, with `xs' = xs.map Sigma.snd`:
      --
      --   P[f k = answers on xs' ∧ ¬ bad k xs']
      --     = Q[g = answers on xs'] · P[¬ bad k xs']           (`factor`)
      --     = (1 - P[bad k xs']) · Q[g = answers on xs']       (complement, commute)
      intro xs answers
      -- The mass of `taggedLaw` is the `Q`-mass of the tagged event.
      dsimp only [taggedLaw]
      rw [Distribution.mass_fTransform]
      -- At the single label, a tagged reply equals an answer exactly when its value does.
      simp only [tagged, single_interface_answers_iff]
      have he := factor (xs.map Sigma.snd) (fun x => (answers ⟨default, x⟩).2)
      -- P[bad] + P[¬ bad] = 1, since `P` is a probability distribution.
      have complement := Distribution.mass_add_compl P
        (fun k => (bad k).1 (xs.map Sigma.snd))
      rw [Distribution.IsProbability.weight_eq_one (X := P)] at complement
      have good : P.mass (fun k => ¬ (bad k).1 (xs.map Sigma.snd)) =
          1 - P.mass (fun k => (bad k).1 (xs.map Sigma.snd)) := by linarith
      -- Rewrite `factor` into the required form.
      rw [good, mul_comm] at he
      exact he)
  -- Step 3: on each transcript `h`, the game sides agree by definition; it remains to show
  -- that the typed system sampling `Q` is the behavior of the PDS sampling from `taggedLaw`.
  intro h
  convert equiv h using 2
  rw [TypedSystem.sample_ofFunction_mass]
  change _ = behaviorMass _ _ _
  -- Both are the `Q`-probability that the DDS of the tagged function replies with `h`.
  simp only [behaviorMass, PDS.ofFunction, taggedLaw, Distribution.mass_fTransform]
  rfl

end SystemAlgebra
