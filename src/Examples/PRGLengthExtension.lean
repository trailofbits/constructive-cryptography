import Commons.Definitions.Ideal
import ConstructiveCryptography.Tactics.Substitution

/-!
# PRG length extension

The 2-wise sequential composition of a length-doubling PRG `G : S → S × S` [1, §3.4.2, p. 59],

```
  H(s) = (A, C, D)     where (A, B) := G(s) and (C, D) := G(B),
```

is a secure PRG when `G` is, here with a fresh seed for every query: `prg-real^G` answers each
`eval(())` with `G(s)` for a fresh uniform seed `s`, and `prg-rand` is the beacon of uniform
samples [2, Example 3.2, p. 56], the memoryless source `MemorylessSource 𝒰[R]`.

Every system of the proof is a memoryless source [2, Definition 3.1, p. 55], and the calling
programs `𝓡₁` and `𝓡₂` of the two swaps map memoryless sources to memoryless sources, with the
law of one invocation (the composition laws `TypedConverter.*_smul_memoryless`). `inline`
applies them from explicit memorylessness certificates and the generated invocation equations;
the identity of laws that remains is proved in place. So each hop is an equality of the laws of
one reply:

```
 system                 law of one reply to eval(())       (U = 𝒰[S])
 prg-real^H             H_* U
 = 𝓡₁ • prg-real^G      (a, G b)_* (G_* U)                  H = (a, G b) ∘ G
 ≃ 𝓡₁ • prg-rand        (a, G b)_* U²
 = 𝓡₂ • prg-real^G      U ⊗ G_* U                           (a, b) ↦ (a, G b) is id × G
 ≃ 𝓡₂ • prg-rand        U ⊗ U²
 = prg-rand             U³                                  a product of uniform laws
```

Each swap `≃` is the security of `G` attached through the calling program, and costs `ε` at the
actual distinguisher with that program absorbed, `ε(D𝓡₁)` or `ε(D𝓡₂)`. The admitted
distinguishers are an arbitrary selected class; the theorem asks only that `𝓡₁` and `𝓡₂`
preserve it (`AdmissibleDistinguishers.ClosedUnder`), not that every converter does.

## Main definitions

* `H G`: the 2-wise sequential composition of `G`
* `PRGReal G`: `prg-real^G`, a fresh seed for every query
* `𝓡₁ G`, `𝓡₂ S`: the calling programs of the two swaps
* `PRGSamples G error`: PRG security with a fresh seed for every query

## Main results

* `prgReal_eq_source`: `prg-real^G` is the memoryless source of `G_* 𝒰[S]`
* `𝓡₁_smul_source`, `𝓡₂_smul_source`: `𝓡₁` and `𝓡₂` on memoryless sources
* `prgReal_H_eq`, `𝓡₁_smul_prgRand`, `𝓡₂_smul_prgRand`: the three hops
* `prg_length_extension`: `H` is a secure PRG within the losses of the two swaps

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
2. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

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

variable {S R : Type} [Fintype S] [Fintype R]

-- `prg-real^G`: on `eval(())`, a fresh uniform seed `s`, and `G(s)`.
system PRGReal(G : S → R) [Nonempty S] : Evaluation Unit R
  on eval(_input : Unit) → R
    seed ←$ 𝒰[S]
    return G seed

-- `𝓡₁`: `(A, B) ← prg.eval(())`, and `(A, G(B))`.
converter 𝓡₁(G : S → S × S) : Evaluation Unit (S × S × S)
  inside prg : Evaluation Unit (S × S)
  on eval(_input : Unit) → S × S × S
    (A, B) ← prg.eval(())
    return (A, G B)

-- `𝓡₂`: a fresh uniform `A`, `(C, D) ← prg.eval(())`, and `(A, C, D)`.
converter 𝓡₂(S : Type) [Fintype S] [Nonempty S] : Evaluation Unit (S × S × S)
  inside prg : Evaluation Unit (S × S)
  on eval(_input : Unit) → S × S × S
    A ←$ 𝒰[S]
    CD ← prg.eval(())
    return (A, CD)

noncomputable section

variable {q : Evaluation.Port → ℕ}

/-! ### The systems of the proof are memoryless sources -/

/-- **`prg-real^G` is the memoryless source of `G(s)` for a uniform seed `s`.** -/
lemma prgReal_eq_source [Nonempty S] (G : S → R) :
    PRGReal.perPort G (budget := q) = MemorylessSource.perPort R (ProbDist.map G 𝒰[S]) := by
  -- Equal systems: compare their random systems.
  apply Subtype.ext
  -- `prg-real^G` is its program attached to its source of seeds:
  --
  --   eval(()) ──► program ── randomness(()) ──► source, seeds s ← 𝒰[S]
  --            ◄── eval ⇒ G s
  --
  -- The source is memoryless, so by the composition law `prg-real^G` is memoryless with the law
  -- of one invocation of the program.
  have real : (PRGReal.perPort G (budget := q)).1 =
      memoryless _ (portLaw fun _ _ => ProbDist.map G 𝒰[S]) := by
    -- `inline` applies `TypedConverter.ofProgram_smul_memoryless` with the certificate that the
    -- source of seeds is memoryless (`TypedSystem.source_eq_memoryless`), then the generated
    -- `PRGReal.memorylessReplyLaw_eval_initial`/`_resumed`.
    inline using (TypedSystem.source_eq_memoryless _ _)
    -- In either state, `s ← 𝒰[S]; return G s` is by definition the pushforward `G_* 𝒰[S]`.
    all_goals rfl
  -- The memoryless source of `G_* 𝒰[S]` is the same memoryless system.
  rw [real, MemorylessSource.memoryless_eq]

/-- **`𝓡₁` on the memoryless source** of `(A, B)` is the memoryless source of `(A, G(B))`. -/
lemma 𝓡₁_smul_source (G : S → S × S) (ν : ProbDist (S × S)) :
    𝓡₁.perPort G (budget := q) • MemorylessSource.perPort (S × S) ν =
      MemorylessSource.perPort (S × S × S) (ProbDist.map (fun AB => (AB.1, G AB.2)) ν) := by
  -- Equal systems: compare their random systems.
  apply Subtype.ext
  -- One invocation of `𝓡₁` against the source of `ν`:
  --
  --   eval(()) ──► 𝓡₁ ── prg.eval(()) ──► source of ν, prg.eval ⇒ (a, b) ← ν
  --            ◄── eval ⇒ (a, G b)
  have attached : (𝓡₁.perPort G (budget := q) •
      MemorylessSource.perPort (S × S) ν (budget := 𝓡₁.insideBudget G q)).1 =
      memoryless _ (portLaw fun _ _ => ProbDist.map (fun AB => (AB.1, G AB.2)) ν) := by
    -- `𝓡₁.perPort` is the converter of a port-preserving program. `inline` applies its
    -- composition law `TypedConverter.ofPreservingProgram_smul_memoryless` with the certificate
    -- that the source of `ν` is memoryless (`MemorylessSource.memoryless_eq`), then the
    -- generated `𝓡₁.memorylessReplyLaw_eval_initial`/`_resumed`.
    inline using (MemorylessSource.memoryless_eq ν _)
    -- In either state, `(a, b) ← ν; return (a, G b)` is by definition `(a, G b)_* ν`.
    all_goals rfl
  -- The memoryless source of `(a, G b)_* ν` is the same memoryless system.
  rw [attached, MemorylessSource.memoryless_eq]

/-- **`𝓡₂` on the memoryless source** of `(C, D)` is the memoryless source of `(A, C, D)` for a
uniform `A`. -/
lemma 𝓡₂_smul_source [Nonempty S] (ν : ProbDist (S × S)) :
    𝓡₂.perPort S (budget := q) • MemorylessSource.perPort (S × S) ν =
      MemorylessSource.perPort (S × S × S) (prodProbDist 𝒰[S] ν) := by
  -- Equal systems: compare their random systems.
  apply Subtype.ext
  -- One invocation of `𝓡₂` against the source of `ν`, with its own source of `A`'s beside:
  --
  --   eval(()) ──► 𝓡₂ ── randomness(()) ──► own source, randomness ⇒ a ← 𝒰[S]
  --                   ── prg.eval(())   ──► source of ν, prg.eval ⇒ (c, d) ← ν
  --            ◄── eval ⇒ (a, c, d)
  have attached : (𝓡₂.perPort S (budget := q) •
      MemorylessSource.perPort (S × S) ν (budget := 𝓡₂.insideBudget S q)).1 =
      memoryless _ (portLaw fun _ _ => prodProbDist 𝒰[S] ν) := by
    -- `𝓡₂.perPort` is its program with its own source beside the inside interface. `inline`
    -- places that source beside the source of `ν` (`comp_smul`, `attach_rightContext`), as in
    -- `TypedConverter.ofPreservingProgram_comp_rightContext_smul_memoryless`. Two certificates,
    -- the source of `ν` (`MemorylessSource.memoryless_eq`) and the source of the `a`'s
    -- (`TypedSystem.source_eq_memoryless`), give the side-by-side law
    -- (`TypedSystem.parallel_eq_memoryless`) for `ofPreservingProgram_smul_memoryless`.
    -- The generated `𝓡₂.memorylessReplyLaw_eval_initial`/`_resumed` give the law of one
    -- invocation against their side-by-side laws: `a ← 𝒰[S]; (c, d) ← ν; return (a, c, d)`.
    inline using (MemorylessSource.memoryless_eq ν _), (TypedSystem.source_eq_memoryless _ _)
    all_goals
      -- Read the side-by-side laws at the two ports: `𝒰[S]` for `a` (`𝓡₂.law1`), `ν` for
      -- `(c, d)` ...
      simp only [parallelLaw, 𝓡₂.law1]
      -- ... and sampling `a`, then independently `(c, d)`, is the product `𝒰[S] ⊗ ν`.
      exact (prod_eq_bindK _ _).symm
  -- The memoryless source of `𝒰[S] ⊗ ν` is the same memoryless system.
  rw [attached, MemorylessSource.memoryless_eq]

/-! ### The hops -/

variable [Nonempty S]

/-- `(A, G(B))` for a uniform `(A, B)` is a uniform `A` beside `G(s)` for a uniform `s`. -/
lemma map_uniform_eq_prod (G : S → S × S) :
    ProbDist.map (fun AB => (AB.1, G AB.2)) 𝒰[S × S] =
      prodProbDist 𝒰[S] (ProbDist.map G 𝒰[S]) := by
  -- Equal laws: compare their distributions.
  apply Subtype.ext
  -- `(a, b) ↦ (a, G b)` is the product map `id × G` ...
  change fTransform (Prod.map id G) (Distribution.uniform (S × S)) = _
  -- ... 𝒰[S × S] is 𝒰[S] ⊗ 𝒰[S] ...
  rw [← prod_uniform]
  -- ... a product map acts factor by factor ...
  rw [fTransform_prod]
  -- ... and `id` leaves 𝒰[S] unchanged.
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
    -- `closed₁`, `closed₂`: absorbing `𝓡₁`, resp. `𝓡₂`, keeps admitted distinguishers admitted;
    -- these are the only converters whose closure is assumed.
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
  -- One chain: the equalities cost nothing, each swap costs `ε` at the distinguisher with the
  -- calling converter absorbed, and the losses add up. `cc_calc quantitative` reads the
  -- substitution model of the goal, the decision advantage of the admitted distinguishers.
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
