module

public import Commons.Definitions.EvaluationSharing
public import RandomSystems.Typed.Context

/-!
# Conditional reconstruction of a retained random function

`observe F` exposes one latent function and its pointwise observation. `reconstruct κ` instead
exposes a conditional lookup and the observed function. The direct assembly shares one latent
table. Reconstruction shares one observed table and retains an independent private table.

```text
direct access:                  reconstructed access:
latent(z) ──────┐               lookup(z) ──► g(z) ──► ψ(z,g(z))
observe(z) ─F───┴─ retained f    observe(z) ───┘        retained private ψ
                                      retained observed g
```

`reconstruct_eq_observe` in `ConditionalRandomFunction.Laws` identifies these assemblies
from the coordinate joint-law contract.

## References

1. G. Herold, D. Khovratovich, M. Kudinov, S. Tessaro, and B. Wagner.
   Aborting Random Oracles: How to Build them, How to Use them.
   Cryptology ePrint Archive, Paper 2026/016, July 17, 2026.
-/

@[expose] public section

namespace Commons.ConditionalRandomFunction

open SystemAlgebra Probability Probability.Distribution CategoryTheory
open scoped SystemAlgebra CategoryTheory

-- `D` contains inputs, `X` latent replies, and `O` observations; all three alphabets are finite.
variable (D X O : Type) [Fintype D] [Fintype X] [Fintype O]

/-- Query the observed table at `z`, then the private table at `(z,o)`.
[1, Theorem 3, p. 17]: "Query h := H⊥(z)." The second call selects its conditional entry. -/
converter lookupCalls (D X O : Type) [Fintype D] [Fintype X] [Fintype O] : Evaluation D X
  inside observed : Evaluation D O
  inside privateTable : Evaluation (D × O) X
  on eval(z : D) → X
    o ← observed.eval(z)
    x ← privateTable.eval((z, o))
    return x

/-- The observed oracle is the protected left port of the lookup. -/
abbrev observedPort : Evaluation.Port → Option (Evaluation.Port ⊕ Evaluation.Port) :=
  fun _ => some (.inl .eval)

/-- The observed call occurs once; the private lookup is outside the protected-port image. -/
lemma lookupCalls_preserves : (lookupCalls.body D X O).PortPreserving observedPort := by
  intro state port z
  cases port
  rcases state with _ | ⟨⟩ <;> simp only [lookupCalls.body]
  all_goals
    apply DSL.preservesAt_call_self
    · intro o
      apply DSL.avoids_call
      · intro x
        exact DSL.avoids_return _ _
      · intro port impossible
        cases impossible
    · intro port _
      cases port
      rfl

/-- Protected counts admit observed histories; total cost admits the private projection. -/
lemma lookup_domain (q : ℕ) :
    ∀ ys, ys ≠ [] → ys.length ≤ 2 * q →
      (∀ o j, observedPort o = some j → (SystemAlgebra.restrict j ys).length ≤ q) →
      ((Evaluation D O q).tensor (Evaluation (D × O) X (2 * q))).domain ys := by
  intro ys nonempty length counts
  apply Interface.perPort_tensor_admits
    (A := Evaluation D O q) (B := Evaluation (D × O) X (2 * q))
    (fun _ => q)
    (fun xs hne hc => ⟨hne, by
      have total := length_eq_sum_restrict xs
      rw [Finset.sum_eq_single Evaluation.Port.eval] at total
      · exact total.trans_le (hc .eval)
      · intro i _ different
        cases i
        exact False.elim (different rfl)
      · intro absent
        exact False.elim (absent (Finset.mem_univ _))⟩)
    (fun _ hne hl => ⟨hne, hl⟩) ys nonempty length
  intro port
  cases port
  exact counts .eval (.inl .eval) rfl

/-- On input `z`, return `ψ(z,f(z))` by calling the observed table and then the private table.
The observed allowance is `q`; the private allowance is `2q`, including pending calls. -/
noncomputable def lookup (q : ℕ) :
    TypedConverter (Evaluation D X q)
      ((Evaluation D O q).tensor (Evaluation (D × O) X (2 * q))) :=
  TypedConverter.ofPreservingProgram none (lookupCalls.body D X O)
    (lookupCalls.bound_spec D X O) observedPort (lookupCalls_preserves D X O)
    (fun _ => q)
    (fun xs admitted port => (length_restrict_le port xs).trans admitted.2)
    (lookup_domain D X O q)

variable {D X O}

/-- On `z`, query the latent function once and return its observation `F z x`. -/
noncomputable def observeReply (r : ℕ) (F : D → X → O) :
    TypedConverter (Evaluation D O r) (Evaluation D X r) :=
  TypedConverter.routingAt id (fun u x => F u.2 x)
    (fun xs admitted => by simpa only [List.map_id] using admitted)

/-- The observed arm and direct latent arm share one retained latent function. -/
noncomputable def observe (q r : ℕ) (F : D → X → O) :
    TypedConverter ((Evaluation D X q).tensor (Evaluation D O r))
      (Evaluation D X (q + r)) :=
  ((𝟙 (Evaluation D X q)) ⊗ₘ observeReply r F) ≫ Evaluation.share D X q r

/-- Keep one private table in the converter; both evaluation callers share its observed table. -/
noncomputable def reconstruct (q r : ℕ)
    (κ : D → O → ProbDist X) :
    TypedConverter ((Evaluation D X q).tensor (Evaluation D O r))
      (Evaluation D O (q + r)) :=
  ((lookup D X O q ≫ TypedConverter.rightContext (Evaluation D O q)
      (randomFunction (Evaluation (D × O) X (2 * q)) (fun _ zo => κ zo.1 zo.2)))
    ⊗ₘ (𝟙 (Evaluation D O r))) ≫ Evaluation.share D O q r

end Commons.ConditionalRandomFunction
