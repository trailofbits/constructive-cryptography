import RandomSystems.Game.FunctionGame
import ConstructiveCryptography.Functional
import ConstructiveCryptography.Notation

/-!
# Game equivalence bounds the resource distance

The game-equivalence bound on random systems (`GameEquivalent.transcriptDistance_le_blind`,
CR18 Theorem 4.17) gives a bound on the distance of resources: a resource presented by the
visible systems of a game is at most the game's blind winning probability away from an
equivalent resource.

## Main results

* `GameEquivalent.game_dist_le`: the distance bound
* `PDG.ofSingleFunction_gameEquivalent`: a sampled-function game is equivalent to the resource
  sampling the ideal function, from the fixed-query factorization
* `GameEquivalent.game_dist_ofSingleFunction_le`: the bound for a sampled-function game
-/

namespace SystemAlgebra

open Probability
open scoped SystemAlgebra

open Lean Elab Term Meta in
/-- One-sided game equivalence to the named visible resource. The resource is
elaborated first, so its interface is the one determined by its own arrows. -/
scoped elab:50 G:term:51 " |≡ " R:term:51 : term => do
  let A ← mkFreshExprMVar (mkConst ``Interface)
  let R ← withSynthesize (elabTerm R (mkApp (mkConst ``Interface.Resource) A))
  let G ← elabTerm G none
  mkAppM ``GameEquivalent #[G, ← mkAppM ``Subtype.val #[R]]

namespace PDG

open Classical in
/-- **A single-label sampled-function game is equivalent to the resource sampling the ideal
function** when, on every fixed query sequence, the answers jointly with the unset condition
factor through the ideal answers. -/
theorem ofSingleFunction_gameEquivalent {I K X Y : Type} [Unique I] [Fintype X] [Fintype Y]
    (D : List (Σ _ : I, X) → Prop)
    (hD : ¬ D [] ∧ ∀ {p h}, p <+: h → p ≠ [] → D h → D p) (bound : ℕ)
    (hb : ∀ h, D h → h.length ≤ bound)
    (P : Distribution K) [Distribution.IsProbability P]
    (f : K → X → Y) (bad : K → MC X)
    (Q : Distribution (X → Y)) [Distribution.IsProbability Q]
    (factor : ∀ xs (answers : X → Y),
      P.mass (fun k => (∀ x ∈ xs, f k x = answers x) ∧ ¬ (bad k).1 xs) =
        Q.mass (fun g => ∀ x ∈ xs, g x = answers x) *
          P.mass (fun k => ¬ (bad k).1 xs)) :
    GameEquivalent
      (ofSingleFunction D hD bound hb P f bad)
      (Interface.Resource.sample (A := ⟨I, fun _ => X, fun _ => Y, D, hD, bound, hb⟩)
        Q (fun g => Interface.Resource.ofFunction (fun _ => g))).1 := by
  unfold ofSingleFunction
  let tagged := fun g : X → Y => fun x : Σ _ : I, X => (⟨x.1, g x.2⟩ : Σ _ : I, Y)
  let taggedLaw := Distribution.fTransform tagged Q
  have hQ := Distribution.IsProbability.isProbDist taggedLaw
  have equiv := ofFunction_gameEquivalent D hD bound hb P (fun k => tagged (f k))
    (fun k => ⟨fun xs => (bad k).1 (xs.map Sigma.snd),
      fun {_ _} hp => (bad k).2 (hp.map Sigma.snd)⟩) taggedLaw hQ (by
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
  convert equiv h using 1
  congr 1
  rw [Interface.Resource.sample_ofFunction_mass]
  change _ = behaviorMass _ _ _
  simp only [behaviorMass, PDS.ofFunction, taggedLaw, Distribution.mass_fTransform]
  rfl

end PDG

namespace GameEquivalent

/-- **Game equivalence bounds the resource distance**: if the game `G` is equivalent to `S`
and `R` is the behavior of its visible systems, then `R` and `S` are at most the blind
winning probability of `G` apart. -/
theorem game_dist_le {A : Interface}
    {G : PDG (Σ i, A.X i) (Σ i, A.Y i) A.inputDomain} {R S : Interface.Resource A}
    (equiv : GameEquivalent G S.1) (hG : G.isProbDist)
    (visible : R.1 = PDS.behavior G.underlying (PDG.underlying_probability hG)) :
    Δ R S ≤ ENNReal.ofReal (G.blind A.nonempty_prefix).supWinProbability := by
  rw [Interface.cc_distance_eq, visible]
  exact equiv.transcriptDistance_le_blind hG A.nonempty_prefix (visible ▸ R.2) S.2

/-- A sampled-function game is compared directly with its visible resource. -/
theorem game_dist_ofSingleFunction_le {I K X Y : Type} [Unique I] [Fintype X]
    [Fintype Y] {D : List (Σ _ : I, X) → Prop}
    {hD : ¬ D [] ∧ ∀ {p h}, p <+: h → p ≠ [] → D h → D p} {bound : ℕ}
    {hb : ∀ h, D h → h.length ≤ bound}
    {P : Distribution K} [Distribution.IsProbability P]
    {f : K → X → Y} {bad : K → MC X}
    {R S : Interface.Resource ⟨I, fun _ => X, fun _ => Y, D, hD, bound, hb⟩}
    (equiv : GameEquivalent (PDG.ofSingleFunction D hD bound hb P f bad) S.1)
    (visible : R = Interface.Resource.sample P
      (fun k => Interface.Resource.ofFunction (fun _ => f k))) :
    Δ R S ≤
      ENNReal.ofReal ((PDG.ofSingleFunction D hD bound hb P f bad).blind hD).supWinProbability := by
  let tagged := fun k (x : Σ _ : I, X) => (⟨x.1, f k x.2⟩ : Σ _ : I, Y)
  let condition := fun k => (⟨fun xs => (bad k).1 (xs.map Sigma.snd),
    fun {_ _} hp => (bad k).2 (hp.map Sigma.snd)⟩ : MC (Σ _ : I, X))
  let hG := PDG.ofFunction_isProbDist D hD bound hb
    (Distribution.IsProbability.isProbDist P) tagged condition
  have underlying : R.1 = PDS.behavior _ (PDG.underlying_probability hG) := by
    rw [visible]
    apply RandomSystem.ext
    intro h
    rw [Interface.Resource.sample_ofFunction_mass]
    change _ = behaviorMass _ _ _
    rw [PDG.ofFunction_underlying]
    simp only [behaviorMass, PDS.ofFunction, Distribution.mass_fTransform]
    rfl
  exact equiv.game_dist_le hG underlying

end GameEquivalent
end SystemAlgebra
