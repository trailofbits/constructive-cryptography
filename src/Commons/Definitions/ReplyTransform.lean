module

public import Commons.Definitions.Ideal
public import RandomSystems.Typed.QueryRouting
public import RandomSystems.Typed.ReplyTransform

/-!
# Transforming evaluation replies

`mapReplies f q` forwards an `eval(())` query once and returns `f x` on the inside reply `x`.
The per-port allowance `q` is unchanged. `mapReplies_smul_memorylessSource` identifies
the attached source with the source of the mapped probability law. `sampleReplies P f q`
additionally draws `k ∼ P` independently on each call and returns `f k x`;
`sampleReplies_smul_memorylessSource` gives the fresh reply law
`(prodProbDist P Q).map (fun kx => f kx.1 kx.2)` on a source with law `Q`.

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

/-- Draw `k ∼ P` afresh, request one inside reply `x`, and return `f k x`. -/
noncomputable def sampleReplies
    -- `X`, `Y` carry inside and outside replies; `K` carries the auxiliary sample.
    {X Y K : Type} [Fintype X] [Fintype Y] [Fintype K]
    -- `P` is sampled independently on every call; `f` computes the outside reply.
    (P : ProbDist K) (f : K → X → Y)
    -- `q` gives the same evaluation allowance on both public interfaces.
    (q : Evaluation.Port → ℕ) :
    TypedConverter (Evaluation.perPort Unit Y q) (Evaluation.perPort Unit X q) :=
  TypedConverter.sampleReplies Evaluation.Port (fun _ => Unit) (fun _ => X) q P (fun _ => f)

/-- Independent fresh `k ∼ P` and `x ∼ Q` give fresh replies with the mapped product law. -/
lemma sampleReplies_smul_memorylessSource
    -- `X`, `Y`, `K` carry resource replies, outside replies and auxiliary samples.
    {X Y K : Type} [Fintype X] [Fintype Y] [Fintype K]
    -- `P`, `Q` are the two independent laws; `f` combines their draws and `q` bounds calls.
    (P : ProbDist K) (f : K → X → Y) (Q : ProbDist X) (q : Evaluation.Port → ℕ) :
    sampleReplies P f q • MemorylessSource.perPort X Q (budget := q) =
      MemorylessSource.perPort Y ((prodProbDist P Q).map (fun kx => f kx.1 kx.2))
        (budget := q) := by
  rw [MemorylessSource.eq_ofMemoryless, MemorylessSource.eq_ofMemoryless]
  exact TypedConverter.sampleReplies_smul_ofMemoryless _ _ _ _

end Commons.Evaluation
