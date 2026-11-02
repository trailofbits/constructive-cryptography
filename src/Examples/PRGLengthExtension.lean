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
`prgReal_H_eq`, `𝓡₁_smul_prgRand` and `𝓡₂_smul_prgRand` justify the exact equalities below.

```text
 system                law of one reply (U = 𝒰[S])     reason
 prg-real^H            H_* U
 = 𝓡₁ • prg-real^G     (a, G b)_* (G_* U)              (a, G b) ∘ G = H
 ≃ 𝓡₁ • prg-rand       (a, G b)_* U²                    security of G, loss ε(D𝓡₁)
 = 𝓡₂ • prg-real^G     U ⊗ G_* U                       (a, G b) = (id × G)(a, b)
 ≃ 𝓡₂ • prg-rand       U ⊗ U²                          security of G, loss ε(D𝓡₂)
 = prg-rand            U³                              U ⊗ U² = U³
```

`prg_length_extension` combines these equalities and two uses of `PRGSamples G ε`.
At a distinguisher `D`, the losses are `ε(D𝓡₁)` and `ε(D𝓡₂)`. The hypotheses `closed₁` and
`closed₂` assume that the selected class is closed under absorbing the respective converters.

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
   https://toc.cryptobook.us/book.pdf
2. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

@[expose] public section

namespace Examples.PRGLengthExtension

open ConstructiveCryptography
open Commons Probability Probability.Distribution SystemAlgebra SystemAlgebra.DSL
  SystemAlgebra.Interface RandomSystem
open scoped SystemAlgebra SystemAlgebra.DSL

/-- **The 2-wise sequential composition** of `G` [1, §3.4.2, p. 59]: `H(s) = (A, C, D)` for
`(A, B) := G(s)` and `(C, D) := G(B)`. -/
def H
    -- `G` expands a seed in `S` into two elements of `S`; `seed` is the initial seed.
    {S : Type} (G : S → S × S) (seed : S) : S × S × S :=
  let (A, B) := G seed
  let (C, D) := G B
  (A, C, D)

-- `S` carries the seeds and `R` the replies, both finite alphabets.
variable {S R : Type} [Fintype S] [Fintype R]

/-- On each admitted `eval(())`, return `G(s)` for a fresh uniform seed `s`.
The reply law is `G_* 𝒰[S]`, with at most `budget` calls. -/
noncomputable def PRGReal
    -- `G` maps a uniform seed to the reply; nonempty `S` makes its uniform law normalized.
    (G : S → R) [Nonempty S]
    -- `budget` bounds the total evaluation queries.
    {budget : ℕ} :
    TypedSystem (Evaluation Unit R budget) :=
  MemorylessSource R (ProbDist.map G 𝒰[S])

/-- The same reply law `G_* 𝒰[S]` on the per-port domain selected by `budget`. -/
noncomputable def PRGReal.perPort
    -- `G` maps uniform seeds to replies; `budget .eval` is the allowed number of evaluations.
    (G : S → R) [Nonempty S] {budget : Evaluation.Port → ℕ} :
    TypedSystem (Evaluation.perPort Unit R budget) :=
  MemorylessSource.perPort R (ProbDist.map G 𝒰[S])

-- `𝓡₁`: query `(a, b) ← prg.eval(())` and return `(a, G(b))`.
converter 𝓡₁(G : S → S × S) : Evaluation Unit (S × S × S)
  inside prg : Evaluation Unit (S × S)
  on eval(_input : Unit) → S × S × S
    (A, B) ← prg.eval(())
    return (A, G B)

-- `𝓡₂`: return `(a, c, d)` for independent `a ← 𝒰[S]` and `(c, d) ← prg.eval(())`.
--
--   eval(()) ──► 𝓡₂ ── randomness(()) ──► source(𝒰[S]), fresh a
--                   └─ prg.eval(()) ─────► inside source, reply (c, d)
--            ◄── (a, c, d)
converter 𝓡₂(S : Type) [Fintype S] [Nonempty S] : Evaluation Unit (S × S × S)
  inside prg : Evaluation Unit (S × S)
  on eval(_input : Unit) → S × S × S
    A ←$ 𝒰[S]
    CD ← prg.eval(())
    return (A, CD)

noncomputable section

-- `q .eval` selects the query allowance in the system equations below.
variable {q : Evaluation.Port → ℕ}

/-! ### The systems of the proof are memoryless sources -/

/-- `prg-real^G` is defined by the source of `G_* 𝒰[S]`. -/
lemma prgReal_eq_source
    -- `G` maps the fresh uniform seed to each reply.
    [Nonempty S] (G : S → R) :
    PRGReal.perPort G (budget := q) = MemorylessSource.perPort R (ProbDist.map G 𝒰[S]) := rfl

/-- **`𝓡₁` on the memoryless source** of `(A, B)` is the memoryless source of `(A, G(B))`. -/
lemma 𝓡₁_smul_source
    -- `ν` is the inside reply law; `G` expands its second coordinate.
    (G : S → S × S) (ν : ProbDist (S × S)) :
    𝓡₁.perPort G (budget := q) • MemorylessSource.perPort (S × S) ν =
      MemorylessSource.perPort (S × S × S) (ProbDist.map (fun AB => (AB.1, G AB.2)) ν) := by
  -- Express the target as the typed memoryless system of `(a, G b)_* ν`.
  conv_rhs => rw [MemorylessSource.eq_ofMemoryless]
  -- Fresh inside replies `(a, b) ∼ ν` reduce the attachment to one invocation per state.
  inline using (MemorylessSource.eq_ofMemoryless ν _)
  -- In either state, sampling `(a, b)` and returning `(a, G b)` defines this pushforward.
  all_goals rfl

/-- **`𝓡₂` on the memoryless source** of `(C, D)` is the memoryless source of `(A, C, D)` for a
uniform `A`. -/
lemma 𝓡₂_smul_source
    -- `ν` is the inside pair's law; the converter independently supplies a uniform `S` value.
    [Nonempty S] (ν : ProbDist (S × S)) :
    𝓡₂.perPort S (budget := q) • MemorylessSource.perPort (S × S) ν =
      MemorylessSource.perPort (S × S × S) (prodProbDist 𝒰[S] ν) := by
  -- Express the target as the typed memoryless system of `𝒰[S] ⊗ ν`.
  conv_rhs => rw [MemorylessSource.eq_ofMemoryless]
  -- Certify both fresh laws: inside `(c, d) ∼ ν` and independent own-source `a ∼ 𝒰[S]`.
  inline using (MemorylessSource.eq_ofMemoryless ν _), (TypedSystem.source_eq_ofMemoryless _ _)
  all_goals
    -- Read the two port laws; their independent sequential draws have the product law.
    simp only [parallelLaw, 𝓡₂.law1]
    exact (prod_eq_bindK _ _).symm

/-! ### The hops -/

variable [Nonempty S]

/-- `(A, G(B))` for a uniform `(A, B)` is a uniform `A` beside `G(s)` for a uniform `s`. -/
lemma map_uniform_eq_prod
    -- `G` transforms only the second coordinate of the independent uniform pair.
    (G : S → S × S) :
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
lemma prgReal_H_eq
    -- `G` is the seed expander; `q .eval` bounds queries to either side of the equality.
    (G : S → S × S) (q : Evaluation.Port → ℕ) :
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
lemma 𝓡₁_smul_prgRand
    -- `G` is the seed expander; `q .eval` bounds queries to either side of the equality.
    (G : S → S × S) (q : Evaluation.Port → ℕ) :
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
lemma 𝓡₂_smul_prgRand
    -- `q .eval` bounds the triple-valued replies on both sides.
    (q : Evaluation.Port → ℕ) :
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
    -- The instance selects the admitted distinguishers at each interface.
    [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    -- `G` maps seeds to replies; nonempty `R` admits the uniform ideal reply law.
    [Nonempty R] (G : S → R)
    -- `q` is the query budget; `error d` bounds the advantage of each admitted `d`.
    {q : Evaluation.Port → ℕ}
    (error : (TypedDistinguisher (Evaluation.perPort Unit R q)) → ENNReal) : Prop :=
  PRGReal.perPort G (budget := q) ≃[error] MemorylessSource.perPort R 𝒰[R] (budget := q)

/-- [1, Theorem 3.3, p. 59]: "If G is a secure PRG, then the n-wise sequential composition G′
of G is also a secure PRG." Here `n = 2`, each query uses a fresh seed, and the two reductions
bound `H`'s advantage by `D ↦ ε(D𝓡₁) + ε(D𝓡₂)`. -/
theorem prg_length_extension
    -- The instance selects admitted distinguishers; `G` expands one seed into two `S` values.
    [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher] (G : S → S × S)
    -- `q` is the query budget of `H`'s interface.
    {q : Evaluation.Port → ℕ}
    -- `ε d` bounds `G`'s advantage at `d`. Both converters make one inside call per evaluation,
    -- so their inside budgets coincide with `𝓡₁.insideBudget G q`.
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
