import RandomSystems.Game.FunctionGame
import ConstructiveCryptography.Functional
import ConstructiveCryptography.Notation

/-!
# Conditional equivalence bounds the resource distance

The bound of conditional equivalence on random systems (CR18, Theorem 4.17,
`RandomSystem.transcriptDistance_visible_le_of_unsetProbability`), on resources presented by
probabilistic discrete games: a resource presented by the visible systems of a discrete game
whose game is conditionally equivalent to a resource `S` is within `ε` of `S` when the condition
holds with probability at most `ε` on the empty and on every admitted query sequence.

## Main results

* `RandomSystem.ConditionallyEquivalent.game_dist_le`: the distance bound
* `PDG.ofSingleFunction_conditionallyEquivalent`: a single-label sampled-function game is
  conditionally equivalent to the resource sampling the ideal function, from the fixed-query
  factorization
* `RandomSystem.ConditionallyEquivalent.game_dist_ofSingleFunction_le`: the bound for a
  single-label sampled-function game
-/

namespace SystemAlgebra

open Probability
open scoped SystemAlgebra

open Lean Elab Term Meta in
/-- Conditional equivalence `G |≡ R` of a game to the named resource (CR18, Definition 4.19).
The resource is elaborated first, so its interface is the one determined by its own arrows. -/
scoped elab:50 G:term:51 " |≡ " R:term:51 : term => do
  let A ← mkFreshExprMVar (mkConst ``Interface)
  let R ← withSynthesize (elabTerm R (mkApp (mkConst ``Interface.Resource) A))
  let G ← elabTerm G none
  mkAppM ``RandomSystem.ConditionallyEquivalent #[G, ← mkAppM ``Subtype.val #[R]]

namespace PDG

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
    {hG : (ofSingleFunction D hD bound hb P f bad).isProbDist}
    (Q : Distribution (X → Y)) [Distribution.IsProbability Q]
    (factor : ∀ xs (answers : X → Y),
      P.mass (fun k => (∀ x ∈ xs, f k x = answers x) ∧ ¬ (bad k).1 xs) =
        Q.mass (fun g => ∀ x ∈ xs, g x = answers x) *
          P.mass (fun k => ¬ (bad k).1 xs)) :
    (ofSingleFunction D hD bound hb P f bad).behavior hG |≡
      Interface.Resource.sample (A := ⟨I, fun _ => X, fun _ => Y, D, hD, bound, hb⟩)
        Q (fun g => Interface.Resource.ofFunction (fun _ => g)) := by
  unfold ofSingleFunction
  let tagged := fun g : X → Y => fun x : Σ _ : I, X => (⟨x.1, g x.2⟩ : Σ _ : I, Y)
  let taggedLaw := Distribution.fTransform tagged Q
  have hQ := Distribution.IsProbability.isProbDist taggedLaw
  have equiv := ofFunction_conditionallyEquivalent D hD bound hb P (fun k => tagged (f k))
    (fun k => ⟨fun xs => (bad k).1 (xs.map Sigma.snd),
      fun {_ _} hp => (bad k).2 (hp.map Sigma.snd)⟩) (hG := by exact hG) taggedLaw hQ (by
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
  rw [Interface.Resource.sample_ofFunction_mass]
  change _ = behaviorMass _ _ _
  simp only [behaviorMass, PDS.ofFunction, taggedLaw, Distribution.mass_fTransform]
  rfl

end PDG

/-- **Conditional equivalence bounds the resource distance**: if the game a probabilistic discrete
game `G` presents is conditionally equivalent to `S`, `R` is the behavior of the visible systems
of `G`, and the condition holds with probability at most `ε` on the empty and on every admitted
query sequence, then `R` and `S` are at most `ε` apart. -/
theorem RandomSystem.ConditionallyEquivalent.game_dist_le {A : Interface}
    {G : PDG (Σ i, A.X i) (Σ i, A.Y i) A.inputDomain} {hG : G.isProbDist}
    {R S : Interface.Resource A} (equiv : G.behavior hG |≡ S)
    (visible : R.1 = PDS.behavior G.underlying (PDG.underlying_probability hG)) {ε : ℝ}
    (hbad : ∀ xs, xs = [] ∨ A.domain xs → G.badProbability xs ≤ ε) :
    Δ R S ≤ ENNReal.ofReal ε := by
  rw [Interface.cc_distance_eq, visible, ← PDG.visible_behavior hG]
  exact RandomSystem.transcriptDistance_visible_le_of_unsetProbability
    (PDG.repliesAtQueriedInterface_behavior hG (visible ▸ R.2)) S.2 (PDG.monotoneMBO_behavior hG)
    equiv (PDG.one_sub_le_unsetProbability_behavior hG A.nonempty_prefix hbad)

/-- **Conditional equivalence bounds the distance of a sampled-function game**: the resource
sampling the function is at most `ε` from a resource conditionally equivalent to the game when
the condition holds with probability at most `ε` on the empty and on every admitted query
sequence. -/
theorem RandomSystem.ConditionallyEquivalent.game_dist_ofSingleFunction_le {I K X Y : Type}
    [Unique I] [Fintype X] [Fintype Y] {D : List (Σ _ : I, X) → Prop}
    {hD : ¬ D [] ∧ ∀ {p h}, p <+: h → p ≠ [] → D h → D p} {bound : ℕ}
    {hb : ∀ h, D h → h.length ≤ bound}
    {P : Distribution K} [Distribution.IsProbability P]
    {f : K → X → Y} {bad : K → MC X} {hG : (PDG.ofSingleFunction D hD bound hb P f bad).isProbDist}
    {R S : Interface.Resource ⟨I, fun _ => X, fun _ => Y, D, hD, bound, hb⟩}
    (equiv : (PDG.ofSingleFunction D hD bound hb P f bad).behavior hG |≡ S)
    (visible : R = Interface.Resource.sample P
      (fun k => Interface.Resource.ofFunction (fun _ => f k))) {ε : ℝ}
    (hbad : ∀ xs, xs = [] ∨ D xs →
      (PDG.ofSingleFunction D hD bound hb P f bad).badProbability xs ≤ ε) :
    Δ R S ≤ ENNReal.ofReal ε := by
  have underlying : R.1 = PDS.behavior _ (PDG.underlying_probability hG) := by
    rw [visible]
    apply RandomSystem.ext
    intro h
    rw [Interface.Resource.sample_ofFunction_mass]
    change _ = behaviorMass _ _ _
    rw [PDG.ofSingleFunction, PDG.ofFunction_underlying]
    simp only [behaviorMass, PDS.ofFunction, Distribution.mass_fTransform]
  exact equiv.game_dist_le underlying hbad

end SystemAlgebra
