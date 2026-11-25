module

public import Commons.Definitions.Ideal
public import ConstructiveCryptography.Notation
public import Probability.Counting.Guessing
public import RandomSystems.Typed.QueryRouting
public import RandomSystems.Typed.KeyGuessing
public import RandomSystems.Typed.Memoryless
public import RandomSystems.Typed.SampleLaws
public import RandomSystems.Typed.SamplingAlgebra

/-!
# Ideal-cipher Davies–Meyer PRF security

For a family of permutations `E : Block → Equiv.Perm State` and a bijective feed-forward family
`mask : State → Equiv.Perm State` that is also injective in its key argument (covering XOR and
group addition), the Davies–Meyer compression function `m ↦ mask K (E m K)` is a PRF in the
public ideal-cipher model [1, Theorem 8.5, p. 311]:

```text
real:   m ↦ mask K (E_m K)       public: E, E⁻¹
ideal:  m ↦ F(m)                 public: E, E⁻¹
```

Here `K`, `E`, and `F` are sampled independently and retained for the whole interaction.

To compare the two experiments, `plant mask K E F` swaps `E_m(K)` with `(mask K)⁻¹ (F m)` for
every block `m`. Retaining the replaced values gives an involution `exchange` on `(E, F)`, so
the planted cipher marginal stays uniform (`plant_uniform`). Any public forward or inverse query
can detect the swap for at most two hidden keys (`queryGuesses`), and the H-coefficient ratio
bound (`TypedSystem.distance_le_of_transcript_ratio`) handles adaptive queries, yielding
`2r / |State|` (`chainingCipherPRF_security`).

## Main definitions

* `CipherFamily`, `CipherQuery`, `cipherReply`, `CipherInterface`, `cipherSystem`, `idealCipher`
* `ChainingCipherPRFInterface`, `cipherKeyGuessing`
* `chainingCipherPRFReal`, `chainingCipherPRFIdeal`, `chainingCipherPRFSecurity`
* `plant`, `exchange`, `exchangeEquiv`, `queryGuesses`

## Main results

* `plant_hidden`, `exchange_involutive`, `plant_uniform`
* `cipherReply_plant_eq`, `real_eq_planted`
* `chainingCipherPRF_security`, `chainingCipherPRF_addGroup_security`
* `cipherReplyPresentation_real`, `cipherReplyPresentation_ideal`

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

set_option autoImplicit false

namespace Commons.DaviesMeyer

open SystemAlgebra Probability
open TypedSystem (ofFunction)
open scoped NNReal SystemAlgebra SystemAlgebra.DSL

noncomputable section

/-! ### Ideal-cipher types and interfaces -/

/-- A family of permutations indexed by cipher key blocks. -/
abbrev CipherFamily (Block State : Type) := Block → Equiv.Perm State

/-- A public ideal-cipher query: inverse flag (`false` for encryption, `true` for decryption),
cipher key block, and state value. -/
abbrev CipherQuery (Block State : Type) := Bool × Block × State

/-- Evaluate a forward or inverse cipher query against a fixed permutation family. -/
def cipherReply {Block State : Type} (E : CipherFamily Block State)
    (query : CipherQuery Block State) : State :=
  if query.1 then (E query.2.1).symm query.2.2 else E query.2.1 query.2.2

/-- Public ideal-cipher interface with one aggregate budget `queries` across both directions. -/
abbrev CipherInterface (Block State : Type) [Fintype Block] [Fintype State] (queries : Nat) :
    Interface :=
  Interface.queryBudget Unit (fun _ => CipherQuery Block State) (fun _ => State) queries

/-- Both directions of a fixed cipher, sharing one permutation family. -/
def cipherSystem {Block State : Type} [Fintype Block] [Fintype State]
    (E : CipherFamily Block State) (queries : Nat) :
    TypedSystem (CipherInterface Block State queries) :=
  system _ query => cipherReply E query

/-- Translate a tagged cipher query to the corresponding forward or inverse port.
Each outside query makes one inside query and returns its reply unchanged. -/
def cipherRouting (Block State : Type) [Fintype Block] [Fintype State] (queries : Nat) :
    TypedConverter (CipherInterface Block State queries) (TweakedBidirectional Block State queries) :=
  TypedConverter.routing
    (fun u => if u.2.1 then ⟨.inverse, u.2.2⟩ else ⟨.forward, u.2.2⟩)
    (fun _ r => match r with | ⟨.forward, y⟩ => y | ⟨.inverse, y⟩ => y)
    (fun _ hx => Interface.queryBudget_domain_map _ le_rfl hx)

open Classical in
/-- The standard tweakable ideal permutation, with its direction encoded in each query.
Both directions at a key use the same retained permutation. -/
def idealCipher (Block State : Type) [Fintype Block] [Fintype State] (queries : Nat) :
    TypedSystem (CipherInterface Block State queries) :=
  cipherRouting Block State queries • TweakableStrongURP Block State (q := queries)

open Classical in
/-- Sampling the shared cipher family once presents the routed standard ideal cipher. -/
lemma idealCipher_eq_sample (Block State : Type) [Fintype Block] [Fintype State]
    (queries : Nat) :
    idealCipher Block State queries =
      TypedSystem.sample (Distribution.uniform (CipherFamily Block State))
        (fun E => cipherSystem E queries) := by
  rw [idealCipher, TweakableStrongURP, TypedConverter.smul_sample]
  congr 1
  funext E
  rw [cipherRouting, TypedConverter.routing_smul_ofFunction]
  apply congrArg TypedSystem.ofFunction
  funext i query
  rcases query with ⟨inverse, key, x⟩
  cases inverse <;> rfl

/-- Hidden chaining-key challenge port alongside a public forward/inverse cipher port, with
separate query budgets. -/
abbrev ChainingCipherPRFInterface (Block State : Type) [Fintype Block] [Fintype State]
    (queries publicQueries : Nat) : Interface :=
  (Commons.Evaluation Block State queries).tensor (CipherInterface Block State publicQueries)

/-- Key-guessing error budget `2 * publicQueries / |State|` [1, Theorem 8.5, p. 311]. -/
abbrev cipherKeyGuessing (State : Type) [Fintype State] (publicQueries : Nat) : ℝ≥0 :=
  ((2 * publicQueries : Nat) : ℝ≥0) / Fintype.card State

/-! ### Davies–Meyer PRF model -/

variable {Block State : Type} [Fintype Block] [Fintype State] [Nonempty State]

local notation "Ciphers" => CipherFamily Block State
local notation "Seed" => Ciphers × (Block → State)
local notation "Eval[" T ", " q "]" => Commons.Evaluation Block T q
local notation "μ" => Distribution.uniform Seed
local notation "μK" => Distribution.uniform State
local notation "μE" => Distribution.uniform Ciphers

section Model
variable (mask : State → Equiv.Perm State) (queries publicQueries : Nat)

open Classical in
/-- Real Davies–Meyer PRF experiment: the PRF `m ↦ mask K (E_m K)` and public forward/inverse
cipher share one retained permutation family `E`. -/
def chainingCipherPRFReal : TypedSystem
    (ChainingCipherPRFInterface Block State queries publicQueries) :=
  sample pair ←$ 𝒰[State × Ciphers];
    (system [Eval[State, queries]] _ m => mask pair.1 (pair.2 m pair.1)) ∥
      cipherSystem pair.2 publicQueries

open Classical in
/-- Ideal PRF experiment: the PRF table `F : Block → State` is sampled independently of the
public ideal cipher `E`. -/
def chainingCipherPRFIdeal : TypedSystem
    (ChainingCipherPRFInterface Block State queries publicQueries) :=
  sample pair ←$ 𝒰[Seed];
    (system [Eval[State, queries]] _ m => pair.2 m) ∥
      cipherSystem pair.1 publicQueries

/-- Public-ideal-cipher PRF security target `Δ Real Ideal ≤ 2r / |State|`
[1, Theorem 8.5, p. 311]. -/
def chainingCipherPRFSecurity : Prop :=
  Δ (chainingCipherPRFReal (Block := Block) mask queries publicQueries)
    (chainingCipherPRFIdeal (Block := Block) (State := State) queries publicQueries) ≤
      (cipherKeyGuessing State publicQueries : ℝ≥0)

end Model

/-! ### Cipher programming involution -/

variable (mask : State → Equiv.Perm State)

open Classical in
/-- Plant one challenge value `F m` at hidden input `k` for each block `m`, preserving the
permutation property by swapping `E m k` with `(mask k)⁻¹ (F m)`. -/
def plant (k : State) (E : Ciphers) (F : Block → State) : Ciphers :=
  fun m => Equiv.swap (E m k) ((mask k).symm (F m)) * E m

omit [Fintype Block] [Fintype State] [Nonempty State] in
/-- Feed-forward at the hidden key `k` recovers the planted challenge value `F m`. -/
lemma plant_hidden (k : State) (E : Ciphers) (F : Block → State) (m : Block) :
    mask k (plant mask k E F m k) = F m := by
  classical
  simp only [plant, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]

/-- Paired seed transformation retaining the displaced hidden outputs so planting is invertible. -/
def exchange (k : State) (pair : Seed) : Seed :=
  (plant mask k pair.1 pair.2, fun m => mask k (pair.1 m k))

omit [Fintype Block] [Fintype State] [Nonempty State] in
/-- Applying `exchange` twice restores both the cipher family and the challenge table. -/
theorem exchange_involutive (k : State) :
    Function.Involutive (exchange (Block := Block) mask k) := by
  classical
  intro pair
  apply Prod.ext
  · funext m
    apply Equiv.ext
    intro x
    simp only [exchange, plant, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.symm_apply_apply]
    rw [Equiv.swap_comm ((mask k).symm (pair.2 m)) (pair.1 m k)]
    exact Equiv.swap_apply_self _ _ _
  · funext m
    exact plant_hidden mask k pair.1 pair.2 m

/-- Bijective reparametrization of `(E, F)` induced by `exchange`. -/
def exchangeEquiv (k : State) : Seed ≃ Seed where
  toFun := exchange mask k
  invFun := exchange mask k
  left_inv := exchange_involutive mask k
  right_inv := exchange_involutive mask k

open Classical in
/-- **Uniform cipher marginal**: planting a uniform table `F` into a uniform cipher family `E`
yields a uniform cipher family. -/
theorem plant_uniform (k : State) :
    Distribution.fTransform (fun pair => plant mask k pair.1 pair.2) μ = μE := by
  classical
  -- Push the uniform joint law through the bijection `exchangeEquiv` and project to the cipher.
  have he := Distribution.fTransform_equiv_uniform (exchangeEquiv (Block := Block) mask k)
  have hp := congrArg (Distribution.fTransform Prod.fst) he
  rw [Distribution.fTransform_fTransform, ← Distribution.prod_uniform,
    Distribution.fTransform_fst_prod, Distribution.weight_uniform, one_smul] at hp
  have hmap : Prod.fst ∘ (exchangeEquiv (Block := Block) mask k) =
      fun pair => plant mask k pair.1 pair.2 := rfl
  rw [hmap, Distribution.prod_uniform] at hp
  exact hp

/-! ### Candidate keys and identical replies -/

variable (mask_injective : ∀ y, Function.Injective (fun k => mask k y))

/-- For fixed cipher output `y`, a proposed PRF answer uniquely determines a candidate key. -/
def keyGuess (y answer : State) : State :=
  (Equiv.ofBijective (fun k => mask k y)
    (Finite.injective_iff_bijective.mp (mask_injective y))).symm answer

omit [Fintype Block] [Nonempty State] in
/-- `keyGuess` inverts `k ↦ mask k y`. -/
lemma keyGuess_mask (y k : State) : keyGuess mask mask_injective y (mask k y) = k :=
  Equiv.symm_apply_apply _ _

omit [Fintype Block] [Fintype State] [Nonempty State] in
/-- Away from the two inputs touched by the swap, `plant` leaves `E m x` unchanged. -/
lemma plant_apply_eq (k : State) (E : Ciphers) (F : Block → State)
    (m : Block) (x : State) (hk : k ≠ x) (hy : mask k (E m x) ≠ F m) :
    plant mask k E F m x = E m x := by
  classical
  apply Equiv.swap_apply_of_ne_of_ne
  · exact fun he => hk ((E m).injective he).symm
  · intro he
    apply hy
    rw [he, Equiv.apply_symm_apply]

/-- The two candidate hidden keys exposed by a public forward or inverse cipher query. -/
def queryGuesses (E : Ciphers) (F : Block → State) (q : CipherQuery Block State) : List State :=
  let plaintext := if q.1 then (E q.2.1).symm q.2.2 else q.2.2
  let ciphertext := if q.1 then q.2.2 else E q.2.1 q.2.2
  [plaintext, keyGuess mask mask_injective ciphertext (F q.2.1)]

omit [Fintype Block] [Nonempty State] in
/-- Every public forward or inverse answer is unchanged if `k` avoids its two candidates. -/
lemma cipherReply_plant_eq (k : State) (E : Ciphers) (F : Block → State)
    (q : CipherQuery Block State) (hk : k ∉ queryGuesses mask mask_injective E F q) :
    cipherReply (plant mask k E F) q = cipherReply E q := by
  rcases q with ⟨direction, m, x⟩
  cases direction
  · simp only [queryGuesses, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at hk
    apply plant_apply_eq mask k E F m x hk.1
    intro he
    apply hk.2
    rw [← he, keyGuess_mask]
  · simp only [queryGuesses, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    change (plant mask k E F m).symm x = (E m).symm x
    apply (plant mask k E F m).symm_apply_eq.mpr
    have he := plant_apply_eq mask k E F m ((E m).symm x) hk.1
    rw [Equiv.apply_symm_apply] at he
    apply (he ?_).symm
    intro hy
    apply hk.2
    rw [← hy, keyGuess_mask]

section Accounting

variable (queries publicQueries : Nat)
local notation "A" => ChainingCipherPRFInterface Block State queries publicQueries
local notation "Input" => Sigma (Interface.X A)
local notation "public[" xs "]" =>
  restrict (some ()) (List.map (Equiv.symm (sumAlphabet (Interface.X A))) xs)

/-- Candidate keys collected from the public cipher queries of an input history. -/
def guesses (E : Ciphers) (F : Block → State) (xs : List Input) : List State :=
  xs.flatMap fun
    | ⟨.inl _, _⟩ => []
    | ⟨.inr _, q⟩ => queryGuesses mask mask_injective E F q

omit [Nonempty State] in
/-- Each public forward or inverse query contributes exactly two candidate keys. -/
lemma guesses_length (E : Ciphers) (F : Block → State) (xs : List Input) :
    (guesses mask mask_injective queries publicQueries E F xs).length = 2 * public[xs].length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨(i | i), q⟩
    · simpa only [guesses, List.flatMap_cons, List.nil_append, List.map_cons,
        sumAlphabet, Equiv.coe_fn_symm_mk,
        restrict_cons_ne (by simp only [ne_eq, reduceCtorEq, not_false_eq_true] :
          (none : Option Unit) ≠ some ())] using ih
    · simp only [guesses, List.flatMap_cons, List.length_append, queryGuesses,
        List.length_cons, List.length_nil, List.map_cons, sumAlphabet,
        Equiv.coe_fn_symm_mk, restrict_cons_self, List.length_cons] at ih ⊢
      omega

omit [Nonempty State] in
/-- The public-port budget bounds the candidate list independently of honest queries. -/
lemma guesses_length_le (E : Ciphers) (F : Block → State)
    (xs : List Input) (hd : xs = [] ∨ (A).domain xs) :
    (guesses mask mask_injective queries publicQueries E F xs).length ≤ 2 * publicQueries := by
  rw [guesses_length]
  apply Nat.mul_le_mul_left
  rcases hd with rfl | hd
  · exact Nat.zero_le _
  · rcases hd.2.2 with he | he
    · rw [he]
      exact Nat.zero_le _
    · exact he.2

/-- Real replies reparametrized by an independent ideal seed `(E, F)` and hidden key `k`. -/
def plantedReplies (pair : Seed) (k : State) : ∀ i, (A).X i → (A).Y i :=
  Sum.rec (fun _ m => mask k (plant mask k pair.1 pair.2 m k))
    (fun _ q => cipherReply (plant mask k pair.1 pair.2) q)

/-- Ideal replies of the independent PRF table and public cipher. -/
def idealReplies (pair : Seed) : ∀ i, (A).X i → (A).Y i :=
  Sum.rec (fun _ m => pair.2 m) (fun _ q => cipherReply pair.1 q)

omit [Nonempty State] in
/-- Every reply of an input history agrees when the hidden key misses its candidate list. -/
lemma replies_eq (pair : Seed) (k : State) (xs : List Input)
    (hk : k ∉ guesses mask mask_injective queries publicQueries pair.1 pair.2 xs)
    (x : Input) (hx : x ∈ xs) :
    plantedReplies mask queries publicQueries pair k x.1 x.2 =
      idealReplies queries publicQueries pair x.1 x.2 := by
  rcases x with ⟨(i | i), q⟩
  · exact plant_hidden mask k pair.1 pair.2 q
  · apply cipherReply_plant_eq mask mask_injective k pair.1 pair.2 q
    intro hmem
    exact hk (List.mem_flatMap.mpr ⟨⟨.inr i, q⟩, hx, hmem⟩)

open Classical in
/-- Reparametrize the real experiment using the uniform planted cipher marginal. -/
lemma real_eq_planted :
    chainingCipherPRFReal (Block := Block) mask queries publicQueries =
      (sample pair ← μ; sample k ← μK;
        ofFunction (plantedReplies mask queries publicQueries pair k)) := by
  rw [TypedSystem.sample_comm]
  unfold chainingCipherPRFReal
  conv_lhs => simp only [DSL.uniform, ← Distribution.prod_uniform, TypedSystem.sample_prod]
  apply congrArg (TypedSystem.sample μK)
  funext k
  let fixedKey (E : Ciphers) : TypedSystem A :=
    (system [Eval[State, queries]] _ m => mask k (E m k)) ∥ cipherSystem E publicQueries
  change TypedSystem.sample μE fixedKey = _
  have he := TypedSystem.sample_fTransform (fun pair => plant mask k pair.1 pair.2) μ fixedKey
  simp only [plant_uniform] at he
  refine he.trans ?_
  apply congrArg (TypedSystem.sample μ)
  funext pair
  dsimp only [fixedKey]
  rw [Interface.cc_parallel_eq]
  exact TypedSystem.parallel_ofFunction _ _

end Accounting

/-! ### Security theorems -/

section Security

variable (queries publicQueries : Nat)

include mask_injective in
/-- **Davies–Meyer PRF security** [1, Theorem 8.5, p. 311]: “is a secure PRF in the ideal cipher
model”, with adaptive distance bound `2r / |State|` for any bijective feed-forward `mask` that
is injective in the key argument. -/
theorem chainingCipherPRF_security :
    chainingCipherPRFSecurity (Block := Block) mask queries publicQueries := by
  classical
  change Δ (chainingCipherPRFReal (Block := Block) mask queries publicQueries)
      (chainingCipherPRFIdeal (Block := Block) (State := State) queries publicQueries) ≤
    (cipherKeyGuessing State publicQueries : ℝ≥0)
  rw [real_eq_planted]
  have ideal_eq :
      chainingCipherPRFIdeal (Block := Block) (State := State) queries publicQueries =
        (sample pair ← μ; ofFunction (idealReplies queries publicQueries pair)) := by
    unfold chainingCipherPRFIdeal
    apply congrArg (TypedSystem.sample μ)
    funext pair
    rw [Interface.cc_parallel_eq]
    exact TypedSystem.parallel_ofFunction _ _
  rw [Interface.cc_distance_eq, ideal_eq]
  exact TypedSystem.sample_distance_le_of_key_guesses μ
    (plantedReplies mask queries publicQueries) (idealReplies queries publicQueries)
    (fun pair => guesses mask mask_injective queries publicQueries pair.1 pair.2)
    (2 * publicQueries)
    (fun pair => guesses_length_le mask mask_injective queries publicQueries pair.1 pair.2)
    (replies_eq mask mask_injective queries publicQueries)

end Security

/-- Group-addition feed-forward satisfies key injectivity by cancellation, giving PRF security
`2r / |State|` directly. -/
theorem chainingCipherPRF_addGroup_security [AddGroup State] (queries publicQueries : Nat) :
    chainingCipherPRFSecurity (Block := Block) (fun k : State => Equiv.addRight k)
      queries publicQueries :=
  chainingCipherPRF_security _ (fun _ _ _ he => add_left_cancel he) queries publicQueries

/-! ### Exact changes of state presentation -/

section Presentation

variable {Output : Type} [Fintype Output] [Nonempty Output]

local notation "μState" => Distribution.uniform (State × Ciphers)
local notation "μOutput" => Distribution.uniform (Output × Ciphers)
local notation "νOutput" => Distribution.uniform (Ciphers × (Block → Output))

/-- Rename the output alphabet of an evaluation interface via `e : Output ≃ State`. -/
abbrev replyPresentation (e : Output ≃ State) (q : Nat) :
    TypedConverter (Eval[Output, q]) (Eval[State, q]) :=
  TypedConverter.rename (Equiv.refl _) (Equiv.refl _)
    (Equiv.sigmaCongrRight fun _ => e)
    (fun _ => rfl) (fun _ => rfl)
    (fun xs => by simp only [Equiv.coe_refl, List.map_id])

/-- Change the challenge reply representation without altering the public cipher port. -/
abbrev cipherReplyPresentation (e : Output ≃ State) (q r : Nat) :
    TypedConverter
      (Interface.tensor (Eval[Output, q]) (CipherInterface Block State r))
      (ChainingCipherPRFInterface Block State q r) :=
  TypedConverter.parallel (replyPresentation (Block := Block) e q)
    (TypedConverter.id (CipherInterface Block State r))

omit [Nonempty State] [Nonempty Output] in
/-- Output renaming acts pointwise on a deterministic evaluation system. -/
lemma replyPresentation_attach (e : Output ≃ State) (q : Nat) (f : Block → State) :
    replyPresentation e q • (system [Eval[State, q]] _ m => f m) =
      (system [Eval[Output, q]] _ m => e.symm (f m)) := by
  apply TypedSystem.eq_ofFunction
  intro h hd hf
  rw [replyPresentation, TypedConverter.rename_mass]
  apply TypedSystem.ofFunction_mass_eq_one
  · rcases hd with rfl | hd
    · exact Or.inl rfl
    · right
      simpa only [List.map_map, Equiv.prodCongr_apply, Equiv.refl_apply,
        Prod.map_fst, Function.comp_def] using hd
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    simp only [Equiv.prodCongr_apply, Prod.map_snd]
    rw [hf w hw]
    exact congrArg (Sigma.mk w.1.1) (e.apply_symm_apply (f w.1.2))

open Classical in
/-- Changing the key/reply presentation transports the real Davies–Meyer experiment exactly. -/
lemma cipherReplyPresentation_real (e : Output ≃ State) (mask : State → Equiv.Perm State)
    (feed : Output → State → Output)
    (hfeed : ∀ k y, feed k y = e.symm (mask (e k) y)) (q r : Nat) :
    cipherReplyPresentation (Block := Block) e q r • chainingCipherPRFReal mask q r =
      (sample pair ← μOutput;
        (system [Eval[Output, q]] _ m => feed pair.1 (pair.2 m (e pair.1))) ∥
          cipherSystem pair.2 r) := by
  refine (TypedConverter.smul_sample _ _ _).trans ?_
  trans sample pair ← μState;
    (system [Eval[Output, q]] _ m => e.symm (mask pair.1 (pair.2 m pair.1))) ∥
      cipherSystem pair.2 r
  · apply congrArg (TypedSystem.sample μState)
    funext pair
    exact (TypedConverter.parallel_attach _ _ _ _).trans
      (congrArg₂ TypedSystem.parallel
        (replyPresentation_attach e q (fun m => mask pair.1 (pair.2 m pair.1)))
        (TypedConverter.identity_attach (cipherSystem pair.2 r)))
  refine (TypedSystem.sample_uniform_equiv (e.prodCongr (Equiv.refl _)) _).trans ?_
  apply congrArg (TypedSystem.sample μOutput)
  funext pair
  apply congrArg (fun R : TypedSystem (Eval[Output, q]) => R ∥ cipherSystem pair.2 r)
  apply congrArg (ofFunction (A := Eval[Output, q]))
  funext i m
  exact (hfeed pair.1 (pair.2 m (e pair.1))).symm

open Classical in
/-- Changing the reply presentation transports the ideal PRF table exactly while keeping the
public cipher untouched. -/
lemma cipherReplyPresentation_ideal (e : Output ≃ State) (q r : Nat) :
    cipherReplyPresentation (Block := Block) e q r •
      chainingCipherPRFIdeal (Block := Block) (State := State) q r =
      (sample pair ← νOutput;
        (system [Eval[Output, q]] _ m => pair.2 m) ∥
          cipherSystem pair.1 r) := by
  unfold chainingCipherPRFIdeal
  simp only [TypedConverter.smul_sample, cipherReplyPresentation, Interface.cc_parallel_eq,
    TypedConverter.parallel_attach, TypedConverter.identity_attach, replyPresentation_attach]
  simpa only [Distribution.ProbDist.uniform, Interface.cc_parallel_eq, Equiv.prodCongr_apply,
    Prod.map_fst, Prod.map_snd, Equiv.refl_apply, Equiv.piCongrRight_apply, Pi.map_apply] using
    (TypedSystem.sample_uniform_equiv
      (A := Interface.tensor (Eval[Output, q]) (CipherInterface Block State r))
      ((Equiv.refl Ciphers).prodCongr (Equiv.piCongrRight fun _ : Block => e.symm))
      (fun pair => (system [Eval[Output, q]] _ m => pair.2 m) ∥ cipherSystem pair.1 r)).symm

end Presentation

end

end Commons.DaviesMeyer
