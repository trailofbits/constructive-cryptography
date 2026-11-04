module

public import Commons.Definitions.Ideal
public import RandomSystems.Typed.QueryRouting

/-!
# Transforming evaluation replies

`mapReplies f q` forwards an `eval(())` query once and returns `f x` on the inside reply `x`.
The per-port allowance `q` is unchanged. `mapReplies_smul_memorylessSource` identifies the attached fresh
source with the source of the mapped probability law.

```text
caller ── eval(()) ──► [mapReplies f] ── eval(()) ──► source P
       ◄──── f x ────              ◄────── x ─────
```
-/

@[expose] public section

namespace Commons.Evaluation

open SystemAlgebra Probability.Distribution

/-- Forward each `eval(())` once and return `f x`; keep no state between calls. -/
noncomputable def mapReplies
    -- `X`, `Y` are the inside and outside reply alphabets; `f` transforms one reply.
    {X Y : Type} [Fintype X] [Fintype Y] (f : X → Y)
    -- `q` permits the same number of evaluations at both interfaces.
    (q : Evaluation.Port → ℕ) :
    TypedConverter (Evaluation.perPort Unit Y q) (Evaluation.perPort Unit X q) :=
  TypedConverter.mapReplies (Evaluation.perPort Unit X q) (fun _ => f)

/-- Mapping fresh replies from `P` by `f` gives fresh replies from `P.map f`. -/
lemma mapReplies_smul_memorylessSource
    -- `f` transforms each inside reply from `X` into an outside reply in `Y`.
    {X Y : Type} [Fintype X] [Fintype Y] (f : X → Y)
    -- `P` is the fresh inside law; `q` is the shared query allowance.
    (P : ProbDist X) (q : Evaluation.Port → ℕ) :
    mapReplies f q • MemorylessSource.perPort X P (budget := q) =
      MemorylessSource.perPort Y (P.map f) (budget := q) := by
  rw [MemorylessSource.eq_ofMemoryless, MemorylessSource.eq_ofMemoryless]
  exact TypedConverter.mapReplies_smul_ofMemoryless _ _ _

end Commons.Evaluation
