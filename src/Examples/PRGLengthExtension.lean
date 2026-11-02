module

public import Commons.Definitions.Ideal
public import ConstructiveCryptography.Tactics.Substitution

/-!
# PRG length extension

The 2-wise sequential composition of a length-doubling PRG `G : S → S × S` [1, §3.4.2, p. 59],

```
  H(s) = (A, C, D)     where (A, B) := G(s) and (C, D) := G(B),
```

is a secure PRG when `G` is, here with a fresh seed for every query: `prg-real^G` answers each
`eval(())` with `G(s)` for a fresh uniform seed `s`, and `prg-rand` is the beacon of uniform
samples [2, Example 3.2, p. 56], the memoryless source `MemorylessSource 𝒰[R]`.

`PRGReal G` is the mapped source of `G_* 𝒰[S]`. The converters `𝓡₁` and `𝓡₂` transform
memoryless sources by their one-invocation reply laws (`𝓡₁_smul_source`, `𝓡₂_smul_source`).
`inline` applies the typed program contracts from explicit memorylessness certificates.

```text
 system                 law of one reply to eval(())       (U = 𝒰[S])
 prg-real^H             H_* U
 = 𝓡₁ • prg-real^G      (a, G b)_* (G_* U)                  prgReal_H_eq
 ≃ 𝓡₁ • prg-rand        (a, G b)_* U²                        security of G
 = 𝓡₂ • prg-real^G      U ⊗ G_* U                           𝓡₁_smul_prgRand
 ≃ 𝓡₂ • prg-rand        U ⊗ U²                              security of G
 = prg-rand             U³                                  𝓡₂_smul_prgRand
```

`prg_length_extension` combines these equalities and two uses of `PRGSamples G ε`.
At a distinguisher `D`, the losses are `ε(D𝓡₁)` and `ε(D𝓡₂)`. The selected class of admitted
distinguishers is closed under absorbing each of these two converters.

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
2. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

@[expose] public section

namespace Examples.PRGLengthExtension

open ConstructiveCryptography
open Commons Probability Probability.Distribution SystemAlgebra SystemAlgebra.DSL
  SystemAlgebra.Interface RandomSystem
open scoped SystemAlgebra SystemAlgebra.DSL

/-- **The 2-wise sequential composition** of `G` [1, §3.4.2]: `H(s) = (A, C, D)` for
`(A, B) := G(s)` and `(C, D) := G(B)`. -/
def H {S : Type} (G : S → S × S) (seed : S) : S × S × S :=
  let (A, B) := G seed
  let (C, D) := G B
  (A, C, D)

-- `S` carries the seeds and `R` the replies, both finite alphabets.
variable {S R : Type} [Fintype S] [Fintype R]

/-- On each admitted `eval(())`, return `G(s)` for a fresh uniform seed `s`.
The reply law is `G_* 𝒰[S]`, with at most `budget` calls. -/
noncomputable def PRGReal (G : S → R) [Nonempty S] {budget : ℕ} :
    TypedSystem (Evaluation Unit R budget) :=
  MemorylessSource R (ProbDist.map G 𝒰[S])

/-- The same reply law `G_* 𝒰[S]` on the per-port domain selected by `budget`. -/
noncomputable def PRGReal.perPort (G : S → R) [Nonempty S]
    {budget : Evaluation.Port → ℕ} : TypedSystem (Evaluation.perPort Unit R budget) :=
  MemorylessSource.perPort R (ProbDist.map G 𝒰[S])

/-! Query `(a, b) ← prg.eval(())` and return `(a, G(b))`. -/
converter 𝓡₁(G : S → S × S) : Evaluation Unit (S × S × S)
  inside prg : Evaluation Unit (S × S)
  on eval(_input : Unit) → S × S × S
    (A, B) ← prg.eval(())
    return (A, G B)

/-! Return `(a, c, d)` for independent `a ← 𝒰[S]` and `(c, d) ← prg.eval(())`.

```text
  eval(()) ──► 𝓡₂ ── randomness(()) ──► source(𝒰[S]), fresh a
                  └─ prg.eval(()) ─────► inside source, reply (c, d)
           ◄── (a, c, d)
``` -/
converter 𝓡₂(S : Type) [Fintype S] [Nonempty S] : Evaluation Unit (S × S × S)
  inside prg : Evaluation Unit (S × S)
  on eval(_input : Unit) → S × S × S
    A ←$ 𝒰[S]
    CD ← prg.eval(())
    return (A, CD)

noncomputable section

-- `q .eval` bounds the outer queries in each component equation.
variable {q : Evaluation.Port → ℕ}

/-! ### The systems of the proof are memoryless sources -/

/-- `prg-real^G` is defined by the source of `G_* 𝒰[S]`. -/
lemma prgReal_eq_source [Nonempty S] (G : S → R) :
    PRGReal.perPort G (budget := q) = MemorylessSource.perPort R (ProbDist.map G 𝒰[S]) := rfl

/-- **`𝓡₁` on the memoryless source** of `(A, B)` is the memoryless source of `(A, G(B))`. -/
lemma 𝓡₁_smul_source (G : S → S × S) (ν : ProbDist (S × S)) :
    𝓡₁.perPort G (budget := q) • MemorylessSource.perPort (S × S) ν =
      MemorylessSource.perPort (S × S × S) (ProbDist.map (fun AB => (AB.1, G AB.2)) ν) := by
  -- The program maps one reply `(a, b) ← ν` to `(a, G b)` in either invocation state.
  conv_rhs => rw [MemorylessSource.eq_ofMemoryless]
  inline using (MemorylessSource.eq_ofMemoryless ν _)
  all_goals rfl

/-- **`𝓡₂` on the memoryless source** of `(C, D)` is the memoryless source of `(A, C, D)` for a
uniform `A`. -/
lemma 𝓡₂_smul_source [Nonempty S] (ν : ProbDist (S × S)) :
    𝓡₂.perPort S (budget := q) • MemorylessSource.perPort (S × S) ν =
      MemorylessSource.perPort (S × S × S) (prodProbDist 𝒰[S] ν) := by
  -- The program's own uniform draw is independent of the source reply.
  conv_rhs => rw [MemorylessSource.eq_ofMemoryless]
  inline using (MemorylessSource.eq_ofMemoryless ν _), (TypedSystem.source_eq_ofMemoryless _ _)
  all_goals
    -- Read the two port laws; their independent sequential draws have the product law.
    simp only [parallelLaw, 𝓡₂.law1]
    exact (prod_eq_bindK _ _).symm

/-! ### The hops -/

variable [Nonempty S]

/-- `(A, G(B))` for a uniform `(A, B)` is a uniform `A` beside `G(s)` for a uniform `s`. -/
lemma map_uniform_eq_prod (G : S → S × S) :
    ProbDist.map (fun AB => (AB.1, G AB.2)) 𝒰[S × S] =
      prodProbDist 𝒰[S] (ProbDist.map G 𝒰[S]) := by
  -- Equality of normalized laws reduces to equality of their mass functions.
  apply Subtype.ext
  -- `(a, b) ↦ (a, G b)` is the product map `id × G`.
  change fTransform (Prod.map id G) (Distribution.uniform (S × S)) = _
  -- A uniform pair has independent uniform coordinates.
  rw [← prod_uniform]
  -- The product map pushes each coordinate law forward separately.
  rw [fTransform_prod]
  -- The first coordinate is unchanged by `id`.
  rw [fTransform_id]
  rfl

/-- **The first hop**, factoring out the first call of `G`: `prg-real^H` is `𝓡₁` on
`prg-real^G`. -/
lemma prgReal_H_eq (G : S → S × S) (q : Evaluation.Port → ℕ) :
    PRGReal.perPort (H G) (budget := q) =
      𝓡₁.perPort G • PRGReal.perPort G (budget := 𝓡₁.insideBudget G q) := by
  -- Left:   prg-real^H        = source of H_* U
  -- Right:  𝓡₁ • prg-real^G   = 𝓡₁ • source of G_* U  =  source of (a, G b)_* (G_* U)
  rw [prgReal_eq_source (H G), prgReal_eq_source G, 𝓡₁_smul_source]
  -- Pushing forward twice is pushing forward along `(a, G b) ∘ G`, which is `H`.
  rw [ProbDist.map_map]
  rfl

/-- **The middle hop**: `𝓡₁` on `prg-rand` is `𝓡₂` on `prg-real^G`, a uniform `A` beside `G(s)`
for a uniform `s` either way. -/
lemma 𝓡₁_smul_prgRand (G : S → S × S) (q : Evaluation.Port → ℕ) :
    𝓡₁.perPort G (budget := q) •
        MemorylessSource.perPort (S × S) 𝒰[S × S] (budget := 𝓡₁.insideBudget G q) =
      𝓡₂.perPort S • PRGReal.perPort G (budget := 𝓡₂.insideBudget S q) := by
  -- Left:   𝓡₁ • prg-rand    = source of (a, G b)_* 𝒰[S × S]
  rw [𝓡₁_smul_source]
  -- Right:  𝓡₂ • prg-real^G  = 𝓡₂ • source of G_* 𝒰[S]  =  source of 𝒰[S] ⊗ G_* 𝒰[S]
  rw [prgReal_eq_source, 𝓡₂_smul_source]
  -- Equal laws: `(a, G b)` for a uniform pair is a uniform `a` beside `G` of a uniform seed.
  rw [map_uniform_eq_prod]

/-- **The last hop**: `𝓡₂` on `prg-rand` is `prg-rand` on `S × S × S`, a uniform `A` beside a
uniform `(C, D)`. -/
lemma 𝓡₂_smul_prgRand (q : Evaluation.Port → ℕ) :
    𝓡₂.perPort S (budget := q) •
        MemorylessSource.perPort (S × S) 𝒰[S × S] (budget := 𝓡₂.insideBudget S q) =
      MemorylessSource.perPort (S × S × S) 𝒰[S × S × S] (budget := q) := by
  -- Left:   𝓡₂ • prg-rand  = source of 𝒰[S] ⊗ 𝒰[S × S]
  rw [𝓡₂_smul_source]
  -- Equal laws: a product of uniform laws is the uniform law on the product.
  rw [show prodProbDist 𝒰[S] 𝒰[S × S] = 𝒰[S × S × S] from Subtype.ext prod_uniform]

/-! ### Security -/

/-- **PRG security with a fresh seed for every query** within `error`: against the admitted
distinguishers, `prg-real^G` substitutes for `prg-rand`, the beacon of uniform samples. -/
def PRGSamples
    [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    [Nonempty R] (G : S → R)
    -- `q` is the query budget; `error d` bounds the advantage of each admitted `d`.
    {q : Evaluation.Port → ℕ}
    (error : (TypedDistinguisher (Evaluation.perPort Unit R q)) → ENNReal) : Prop :=
  PRGReal.perPort G (budget := q) ≃[error] MemorylessSource.perPort R 𝒰[R] (budget := q)

/-- **PRG length extension**, as [1, Theorem 3.3] for `n = 2` with a fresh seed for every query:
if `G` is a secure PRG within `ε` and the calling programs `𝓡₁`, `𝓡₂` preserve the admitted
distinguishers, then `H` is a secure PRG within `D ↦ ε(D𝓡₁) + ε(D𝓡₂)`. -/
theorem prg_length_extension
    [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher] (G : S → S × S)
    -- `q` is the query budget of `H`'s interface.
    {q : Evaluation.Port → ℕ}
    -- `ε d` is the error of `G` against `d` on `G`'s interface (the inside budget of `𝓡₁`).
    (ε : (TypedDistinguisher (Evaluation.perPort Unit (S × S) (𝓡₁.insideBudget G q)))
      → ENNReal)
    -- `secure`: `prg-real^G ≃[ε] prg-rand`.
    (secure : PRGSamples G ε)
    -- `closed₁` and `closed₂` admit `D𝓡₁` and `D𝓡₂` whenever `D` is admitted.
    (closed₁ : AdmissibleDistinguishers.ClosedUnder
      (Phi := TypedSystem) (D := TypedDistinguisher) (𝓡₁.perPort G (budget := q)))
    (closed₂ : AdmissibleDistinguishers.ClosedUnder
      (Phi := TypedSystem) (D := TypedDistinguisher) (𝓡₂.perPort S (budget := q))) :
    PRGSamples (H G) (q := q) fun D =>
      ε (D.absorb (𝓡₁.perPort G)) +
        ε (D.absorb (𝓡₂.perPort S)) := by
  -- The hybrids, as systems (the distinguisher D on the left):
  --
  --   D ─ prg-real^H                                start
  --   D ─ 𝓡₁ ─ prg-real^G      =                    factor out            prgReal_H_eq
  --   D ─ 𝓡₁ ─ prg-rand        ≃[ε(D𝓡₁)]            swap: G is secure
  --   D ─ 𝓡₂ ─ prg-real^G      =                    middle hop            𝓡₁_smul_prgRand
  --   D ─ 𝓡₂ ─ prg-rand        ≃[ε(D𝓡₂)]            swap: G is secure
  --   D ─ prg-rand             =                    last hop              𝓡₂_smul_prgRand
  --
  -- Exact equalities preserve advantage; the two substitutions add their losses at `D`.
  cc_calc quantitative
    -- The first hop: factor out the first call of `G`.
    PRGReal.perPort (H G) = 𝓡₁.perPort G • PRGReal.perPort G := prgReal_H_eq G q
    -- The first swap: `prg-real^G` ≃ `prg-rand` (`secure`), attached through `𝓡₁`; its loss is
    -- `ε(D𝓡₁)`, and `closed₁` admits `D𝓡₁` (`substitutesWithin_attach`).
    _ ≃[fun D => ε (D.absorb (𝓡₁.perPort G))]
        𝓡₁.perPort G • MemorylessSource.perPort (S × S) 𝒰[S × S] :=
      AdmissibleDistinguishers.substitutesWithin_attach _ closed₁ secure
    -- The middle hop: both are the memoryless source of `𝒰[S] ⊗ G_* 𝒰[S]`.
    _ = 𝓡₂.perPort S • PRGReal.perPort G := 𝓡₁_smul_prgRand G q
    -- The second swap, through `𝓡₂`; its loss is `ε(D𝓡₂)`, and `closed₂` admits `D𝓡₂`.
    _ ≃[fun D => ε (D.absorb (𝓡₂.perPort S))]
        𝓡₂.perPort S • MemorylessSource.perPort (S × S) 𝒰[S × S] :=
      AdmissibleDistinguishers.substitutesWithin_attach _ closed₂ secure
    -- The last hop: both are the memoryless source of `𝒰[S × S × S]`.
    _ = MemorylessSource.perPort (S × S × S) 𝒰[S × S × S] := 𝓡₂_smul_prgRand q

end

end Examples.PRGLengthExtension
