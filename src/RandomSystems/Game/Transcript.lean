module

public import RandomSystems.Game.DiscreteMBO
public import RandomSystems.Distance.Coupling

/-!
# Transcripts of games with a hidden condition

`DDG.forgetMBOs_tr_withMBO` identifies the visible transcript of a deterministic game
with the transcript of its underlying system: the environment chooses each query after
forgetting the hidden bits. `DDG.finalMBO_tr_withMBO_iff` then identifies the last bit with
the game's condition on the completed input history, provided at least one reply occurred.
`PDG.winProbability_behavior` transports the winning event through the sampled-game law.
The condition may hold initially; a win still requires a reply [1, p. 71]:
"Winner w wins game g if aᵢ = 1 for some i ≥ 1."

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

@[expose] public section

namespace SystemAlgebra

-- `I` selects the ports and `X`, `Y` their query and visible reply alphabets.
variable {I : Type} {X Y : I → Type}

/-- Forgetting hidden bits gives exactly the transcript seen by the original environment. -/
lemma DDG.forgetMBOs_tr_withMBO
    -- `g` contains a DDS and its monotone condition; `e` chooses queries from visible replies.
    (g : DDG (Σ i, X i) (Σ i, Y i)) (e : DDE (Σ i, X i) (Σ i, Y i))
    -- `n` is the finite observation horizon; either participant may stop earlier.
    (n : ℕ) :
    forgetMBOs ((DDG.withMBO g).1.tr (DDE.blindMBO e).1 n) = g.1.1.tr e.1 n := by
  simpa only [DDG.relabel_withMBO, forgetMBOs, DDE.blindMBO, Prod.map_def, id_eq] using
    (System.tr_relabel_output (DDG.withMBO g).1 forgetMBO e.1 n).symm

/-- The final hidden bit holds exactly when a reply occurred and the game's condition holds
on the visible input history. The condition may already hold before the first query. -/
lemma DDG.finalMBO_tr_withMBO_iff
    -- `g` contains the DDS and its condition; `e` reacts to its visible replies.
    (g : DDG (Σ i, X i) (Σ i, Y i)) (e : DDE (Σ i, X i) (Σ i, Y i))
    -- `n` bounds the transcript length, allowing either participant to stop sooner.
    (n : ℕ) :
    finalMBO ((DDG.withMBO g).1.tr (DDE.blindMBO e).1 n) = true ↔
      g.1.1.tr e.1 n ≠ [] ∧ g.2.1 ((g.1.1.tr e.1 n).map Prod.fst) := by
  classical
  have replies := System.replies_tr (s := (DDG.withMBO g).1)
    (σ := (DDE.blindMBO e).1) n
  -- Express both sides on the tagged transcript, whose final reply carries the condition.
  rw [← DDG.forgetMBOs_tr_withMBO g e n, map_fst_forgetMBOs]
  generalize (DDG.withMBO g).1.tr (DDE.blindMBO e).1 n = h at replies ⊢
  rcases List.eq_nil_or_concat h with rfl | ⟨h, z, rfl⟩
  · simp only [finalMBO, List.getLast?_nil, Option.map_none, Option.getD_none,
      Bool.false_eq_true, forgetMBOs, List.map_nil, ne_eq, not_true_eq_false, false_and]
  · rw [List.concat_eq_append] at replies ⊢
    simp only [List.map_append, List.map_singleton] at replies
    have last := (replies_snoc.mp replies).2
    have bit := (map_tagMBO_eq_some_iff.mp last).2
    simp only [finalMBO, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.map_some, Option.getD_some, forgetMBOs, ne_eq,
      List.append_eq_nil_iff, List.cons_ne_nil, and_false, not_false_eq_true, true_and,
      List.map_append, List.map_singleton]
    rw [bit]
    exact decide_eq_true_iff

open Probability

/-- Winning is the sampled-game mass whose completed visible transcript is nonempty and
satisfies its hidden condition. Each reply carries the bit, so an immediate stop has score zero. -/
theorem PDG.winProbability_behavior
    -- `P` samples a deterministic game on the common input domain `E`, bounded by `m`.
    [Fintype I] [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    {E : List (Σ i, X i) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
    (P : PDG (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE)) (hP : P.isProbDist)
    -- `D` is a legal winner; `hC` certifies that its visible queries are admitted.
    (D : DDD I X Y) (hD : IsDDD D)
    (hC : (P.behavior hP).visible.Compatible (ddeOf hD).1)
    -- `n` is any bound beyond the winner's last possible query.
    {n : ℕ} (hn : QueryBounded n (ddeOf hD)) :
    (P.behavior hP).winProbability D hD = P.mass (fun g =>
      g.1.1.1.tr (ddeOf hD).1 n ≠ [] ∧
        g.1.2.1 ((g.1.1.1.tr (ddeOf hD).1 n).map Prod.fst)) := by
  -- Evaluate at `n`, then expose the sampled deterministic games by the PDS transcript law.
  rw [RandomSystem.winProbability_eq_mass_at_bound _ _ _ hn, PDG.behavior,
    PDS.sLaw_behavior_eq_fTransform _ _ ((P.behavior hP).compatible_blindMBO hC),
    Distribution.mass_fTransform, PDG.withMBO, Distribution.mass_fTransform]
  -- For each retained sample, the final bit is its condition after at least one reply.
  exact Distribution.mass_congr _ fun g => DDG.finalMBO_tr_withMBO_iff g.1 (ddeOf hD) n

end SystemAlgebra
