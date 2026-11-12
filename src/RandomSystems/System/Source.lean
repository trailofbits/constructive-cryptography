module

public import RandomSystems.System.Source.Defs
public import RandomSystems.System.Memoryless
public import RandomSystems.Cumulative.FiniteCuts

/-!
# An unlimited fresh source and its bounded presentations

`sourceMass_isRandomSystem` normalizes the product of fresh reply masses on the domain admitting
every query. `sourceMass_ofFn` identifies its finite reply vectors with `ProbDist.pi`.
`RandomSystem.memoryless_eq_cut_sourceMass` identifies each finite observation cut with the
existing memoryless system on any domain admitting exactly that many queries.
-/

@[expose] public section

namespace SystemAlgebra

open Probability Probability.Distribution

-- `A` carries triggers, `B` replies, and `ν` is the law of each independent reply.
variable {A B : Type} (ν : ProbDist B)

/-- The empty transcript has mass one. -/
lemma sourceMass_nil : sourceMass (A := A) ν [] = 1 := rfl

/-- One additional reply multiplies the transcript mass by its probability under `ν`. -/
lemma sourceMass_snoc (h : List (A × B)) (x : A) (y : B) :
    sourceMass ν (h ++ [(x, y)]) = sourceMass ν h * ν.1 y := by
  simp only [sourceMass, List.map_append, List.map_singleton, List.prod_append,
    List.prod_singleton]

/-- Fresh replies normalize on the domain admitting every next query. -/
theorem sourceMass_isRandomSystem :
    IsRandomSystem (fun (_ : List (A × B)) _ => True) (sourceMass ν) := by
  refine ⟨sourceMass_nil ν, ?_, ?_⟩
  · intro h
    exact List.prod_nonneg (fun x hx => by
      obtain ⟨xy, _, rfl⟩ := List.mem_map.mp hx
      exact ν.2.1 xy.2)
  · intro h x
    -- The incoming transcript mass scales the normalized next-reply law.
    refine ⟨sourceMass ν h • ν.1, ?_, ?_⟩
    · intro y
      rw [Finsupp.smul_apply, smul_eq_mul, sourceMass_snoc]
    · simp only [weight_smul, ν.2.2, mul_one, ite_true]

/-- Finite reply vectors have the mass of the existing independent product law. -/
lemma sourceMass_ofFn {n : ℕ}
    -- `xs` fixes the queries and `ys` the replies in the first `n` exchanges.
    (xs : Fin n → A) (ys : Fin n → B) :
    sourceMass ν (List.ofFn fun i => (xs i, ys i)) =
      (ProbDist.pi fun _ : Fin n => ν).1 ys := by
  simp only [sourceMass, ProbDist.pi_val, Distribution.pi_apply, List.map_ofFn,
    List.prod_ofFn, Function.comp_apply]

namespace RandomSystem

/-- A memoryless system on a complete finite horizon is the corresponding source cut. -/
lemma memoryless_eq_cut_sourceMass [Fintype A] [Fintype B]
    -- `E` admits exactly the histories shorter than `q`, as certified by `hE`.
    (E : Domain A B) (q : ℕ) (hE : ∀ h x, E h x ↔ h.length < q) :
    (memoryless E (fun _ => ν) : List (A × B) → ℝ) = cutMass (sourceMass ν) q := by
  -- Domain presentation changes only the normalization predicate of the same cut masses.
  have domains : E.admits = (cutDomain (fun (_ : List (A × B)) _ => True) q).admits := by
    funext h x
    exact propext (by simpa only [cutDomain, true_and] using hE h x)
  have normalized : IsRandomSystem E (cutMass (sourceMass ν) q) := by
    rw [domains]
    exact IsRandomSystem.cutMass _ _ (sourceMass_isRandomSystem ν) q
  -- The source's product equation is exactly the admitted-query memoryless contract.
  have same : (⟨cutMass (sourceMass ν) q, normalized⟩ : RandomSystem A B E) =
      memoryless E (fun _ => ν) := by
    apply eq_memoryless_of_snoc
    intro h x y hd
    have hq := (hE h x).mp hd
    change cutMass (sourceMass ν) q (h ++ [(x, y)]) = cutMass (sourceMass ν) q h * ν.1 y
    rw [cutMass, cutMass, List.length_append, List.length_singleton,
      ite_eq_left (Nat.succ_le_of_lt hq), ite_eq_left (Nat.le_of_lt hq), sourceMass_snoc]
  exact (congrArg Subtype.val same).symm

end RandomSystem

end SystemAlgebra
