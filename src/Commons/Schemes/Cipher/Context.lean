module

public import Commons.Schemes.Cipher.DaviesMeyer

/-!
# Hidden-key replacement inside a cipher-dependent context

A context `evaluate : Auxiliary → (Block → State) → CipherFamily Block State → ∀ i, A.X i → A.Y i`
evaluates both a challenge table and the shared public ideal cipher `E`:

```text
context ── challenge calls ──► m ↦ mask K (E_m K)   ≈   F(m)
       └── cipher calls ─────► E, E⁻¹                   E, E⁻¹
```

Whenever `evaluate` respects a deterministic cipher-call trace (`RespectsCalls`) making at most
`budget` cipher calls across any admitted input history, replacing the hidden-key Davies–Meyer
table by an independent uniform table `F` costs at most `2 * budget / |State|` in transcript
ratio (`transcript_ratio`) and in `Δ` distance (`security`).

## Main definitions

* `real`, `ideal`, `planted`: the real, ideal, and programmed context systems on `A`
* `guesses`: candidate keys collected from the context's actual cipher calls
* `RespectsCalls`: trace-locality certificate that changing `E` off `calls` preserves replies

## Main results

* `real_eq_planted`: exact reparametrization via `DaviesMeyer.plant_uniform`
* `transcript_ratio`: pointwise `(1 - 2 * budget / |State|) * ideal h ≤ real h`
* `security`: `Δ (real P mask evaluate) (ideal P evaluate) ≤ 2 * budget / |State|`

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

set_option autoImplicit false

namespace Commons.CipherContext

open SystemAlgebra Probability Commons.DaviesMeyer
open scoped NNReal SystemAlgebra SystemAlgebra.DSL

noncomputable section

-- `Block`, `State` parameterize the ideal cipher; `Auxiliary` carries independent randomness;
-- `A` is the outside interface presented by the context.
variable {Block State Auxiliary : Type} [Fintype Block] [Fintype State] [Nonempty State]
  {A : Interface}

local notation "Ciphers" => CipherFamily Block State
local notation "Table" => Block → State
local notation "Input" => Sigma (Interface.X A)
local notation "Seed" => Auxiliary × (Ciphers × Table)
local notation "μ[" T "]" => Distribution.uniform T

variable (P : Distribution Auxiliary) [Distribution.IsProbability P]
  (mask : State → Equiv.Perm State)
  (evaluate : Auxiliary → (Block → State) → CipherFamily Block State → ∀ i, A.X i → A.Y i)

open Classical in
/-- Real context system: one uniform hidden key `k` feeds the Davies–Meyer table while the
context also queries the same shared cipher `E`. -/
def real : TypedSystem A :=
  sample a ← P; sample k ← μ[State]; sample E ← μ[Ciphers];
    TypedSystem.ofFunction (evaluate a (fun m => mask k (E m k)) E)

open Classical in
/-- Ideal context system: an independent uniform challenge table alongside the same cipher. -/
def ideal : TypedSystem A :=
  sample seed ← P.prod μ[Ciphers × Table];
    TypedSystem.ofFunction (evaluate seed.1 seed.2.2 seed.2.1)

local notation "Law" => P.prod μ[Ciphers × Table]

/-- Programmed real reply function obtained by planting `seed.2.2` into `seed.2.1` at key `k`. -/
def planted (seed : Seed) (k : State) : ∀ i, A.X i → A.Y i :=
  evaluate seed.1 seed.2.2 (DaviesMeyer.plant mask k seed.2.1 seed.2.2)

open Classical in
/-- Exact reparametrization of `real` using the uniform planted-cipher marginal. -/
lemma real_eq_planted : real P mask evaluate =
    (sample seed ← Law; sample k ← μ[State];
      TypedSystem.ofFunction (planted mask evaluate seed k)) := by
  unfold real
  rw [TypedSystem.sample_prod]
  apply congrArg (TypedSystem.sample P)
  funext a
  conv_rhs => rw [TypedSystem.sample_comm]
  apply congrArg (TypedSystem.sample μ[State])
  funext k
  let body (E : Ciphers) :=
    TypedSystem.ofFunction (evaluate a (fun m => mask k (E m k)) E)
  have he := TypedSystem.sample_fTransform
    (fun pair => DaviesMeyer.plant mask k pair.1 pair.2) μ[Ciphers × Table] body
  simp only [DaviesMeyer.plant_uniform] at he
  refine he.trans ?_
  apply congrArg (TypedSystem.sample μ[Ciphers × Table])
  funext seed
  have ht : (fun m => mask k (DaviesMeyer.plant mask k seed.1 seed.2 m k)) = seed.2 :=
    funext (DaviesMeyer.plant_hidden mask k seed.1 seed.2)
  exact congrArg TypedSystem.ofFunction (congrArg
    (fun F => evaluate a F (DaviesMeyer.plant mask k seed.1 seed.2)) ht)

variable (mask_injective : ∀ y, Function.Injective (fun k => mask k y))
  (calls : Auxiliary → (Block → State) → CipherFamily Block State →
    Sigma A.X → List (CipherQuery Block State))

/-- Candidate keys collected from every cipher call made along an input history `xs`. -/
def guesses (seed : Seed) (xs : List Input) : List State :=
  (xs.flatMap (calls seed.1 seed.2.2 seed.2.1)).flatMap
    (DaviesMeyer.queryGuesses mask mask_injective seed.2.1 seed.2.2)

omit [Fintype Block] [Nonempty State] in
/-- Each actual cipher call contributes exactly two candidate keys. -/
lemma guesses_length (seed : Seed) (xs : List Input) :
    (guesses mask mask_injective calls seed xs).length =
      2 * (xs.flatMap (calls seed.1 seed.2.2 seed.2.1)).length := by
  simp only [guesses, List.length_flatMap, DaviesMeyer.queryGuesses,
    List.length_cons, List.length_nil, List.map_const', List.sum_replicate, smul_eq_mul]
  omega

/-- Deterministic trace-locality: modifying the cipher outside `calls a F E x` leaves the
context's reply at `x` unchanged. -/
def RespectsCalls : Prop :=
  ∀ a F E E' x,
    (∀ q ∈ calls a F E x, cipherReply E' q = cipherReply E q) →
      evaluate a F E' x.1 x.2 = evaluate a F E x.1 x.2

omit [Fintype Block] [Nonempty State] in
/-- Off the candidate-key list, trace-locality identifies planted and ideal replies. -/
lemma planted_eq_ideal (respectsCalls : RespectsCalls evaluate calls) (seed : Seed) (k : State)
    (xs : List Input) (hk : k ∉ guesses mask mask_injective calls seed xs)
    (x : Input) (hx : x ∈ xs) :
    planted mask evaluate seed k x.1 x.2 = evaluate seed.1 seed.2.2 seed.2.1 x.1 x.2 := by
  apply respectsCalls
  intro q hq
  apply DaviesMeyer.cipherReply_plant_eq mask mask_injective
  intro hg
  exact hk (List.mem_flatMap.mpr ⟨q, List.mem_flatMap.mpr ⟨x, hx, hq⟩, hg⟩)

include mask_injective in
open Classical in
/-- Pointwise transcript ratio for a bounded cipher-dependent context, for use inside hybrids. -/
lemma transcript_ratio (budget : Nat) (respectsCalls : RespectsCalls evaluate calls)
    (hbudget : ∀ a F E xs, xs = [] ∨ A.domain xs →
      (xs.flatMap (calls a F E)).length ≤ budget)
    (h : List (Input × Sigma A.Y)) :
    (1 - (cipherKeyGuessing State budget : ℝ)) * (ideal P evaluate).1 h ≤
      (real P mask evaluate).1 h := by
  rw [real_eq_planted]
  apply TypedSystem.sample_ratio_of_bad_keys Law
    (planted mask evaluate) (fun seed => evaluate seed.1 seed.2.2 seed.2.1)
    (fun seed xs k => k ∈ guesses mask mask_injective calls seed xs)
    (cipherKeyGuessing State budget)
  · intro seed xs hd
    refine (Counting.uniform_mass_mem_list_le _).trans ?_
    change _ ≤ (2 * budget : Nat) / (Fintype.card State : ℝ)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact Nat.cast_le.mpr ((guesses_length mask mask_injective calls seed xs).le.trans
      (Nat.mul_le_mul_left 2 (hbudget seed.1 seed.2.2 seed.2.1 xs hd)))
  · exact planted_eq_ideal mask evaluate mask_injective calls respectsCalls

include mask_injective in
open Classical in
/-- **Single-root context replacement** [1, Theorem 8.5, p. 311]: replacing one hidden-key
Davies–Meyer table inside a cipher-dependent context making at most `budget` cipher calls
incurs `Δ` distance at most `2 * budget / |State|`. -/
theorem security (budget : Nat) (respectsCalls : RespectsCalls evaluate calls)
    (hbudget : ∀ a F E xs, xs = [] ∨ A.domain xs →
      (xs.flatMap (calls a F E)).length ≤ budget) :
    Δ (real P mask evaluate) (ideal P evaluate) ≤
      (cipherKeyGuessing State budget : ℝ≥0) := by
  rw [Interface.cc_distance_eq, real_eq_planted]
  exact TypedSystem.sample_distance_le_of_key_guesses Law
    (planted mask evaluate) (fun seed => evaluate seed.1 seed.2.2 seed.2.1)
    (guesses mask mask_injective calls) (2 * budget)
    (fun seed xs hd => (guesses_length mask mask_injective calls seed xs).le.trans
      (Nat.mul_le_mul_left 2 (hbudget seed.1 seed.2.2 seed.2.1 xs hd)))
    (planted_eq_ideal mask evaluate mask_injective calls respectsCalls)

end

end Commons.CipherContext
