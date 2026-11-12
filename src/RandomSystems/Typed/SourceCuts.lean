module

public import RandomSystems.Typed.Memoryless
public import RandomSystems.System.Source

/-!
# Finite observations of the typed fresh source

`TypedSystem.source_eq_cutMass` identifies the existing table-based source with a finite cut
of the unlimited cumulative source. The proof uses `source_eq_memoryless` and the memoryless
cut contract; the single port tags the reply law by `Sigma.mk ()`.
-/

@[expose] public section

namespace SystemAlgebra.TypedSystem

open Probability.Distribution RandomSystem

/-- The source of `q` fresh replies is the `q`-cut of the unlimited source's tagged law. -/
lemma source_eq_cutMass
    -- `B` carries replies, `ν` is sampled independently, and `q` is the query allowance.
    {B : Type} [Fintype B] (ν : ProbDist B) (q : ℕ)
    -- `h` is a transcript at the existing source's single trigger port.
    (h : List ((Σ _ : Unit, Unit) × (Σ _ : Unit, B))) :
    (source ν q).1 h = cutMass (sourceMass (ν.map (Sigma.mk ()))) q h := by
  rw [source_eq_memoryless]
  -- Every query uses the same single-port tagging of the reply law.
  have tagged : portLaw (fun (_ : Unit) (_ : Unit) => ν) =
      fun (_ : Σ _ : Unit, Unit) => ν.map (Sigma.mk ()) := by
    funext ⟨⟨⟩, ⟨⟩⟩
    rfl
  rw [tagged]
  exact congrFun (memoryless_eq_cut_sourceMass _ _ q
    (fun _ _ => Interface.queryBudget_inputDomain_iff)) h

end SystemAlgebra.TypedSystem
