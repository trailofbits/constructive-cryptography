module

public import Commons.Schemes.Cipher.Context

/-!
# Multi-root replacement inside one shared-cipher context

A context `evaluate` accesses `users` independent hidden-key Davies–Meyer tables alongside the
same shared public ideal cipher `E`:

```text
slot 0 ... slot u−1  ── m ↦ mask (K_i) (E_m (K_i)) ──► independent F_i
context / later real slots ───────────────────────────► the same public E, E⁻¹
```

Replacing one hidden root at a time via `CipherContext.security` and
`CipherContext.transcript_ratio` replaces all `users` slots with total loss `2 * users * budget /
|State|`, where `budget` bounds the sum of challenge and cipher calls across any admitted history.
Independent root keys may coincide; no distinct-key hypothesis is required.

## Main definitions

* `oracle`, `hybrid`, `real`, `ideal`, `Security`
* `selected`, `selectedReplies`, `RespectsCalls`, `selectedCalls`

## Main results

* `hybrid_zero`, `hybrid_all`: endpoints of the `users`-step hybrid ladder
* `hybrid_step`, `hybrid_step_ratio`: single-slot replacement via `CipherContext`
* `transcript_ratio`: telescoped pointwise ratio `(1 - 2 * users * budget / |State|)`
* `security`:
  `Δ (real users P mask evaluate) (ideal users P evaluate) ≤ users * (2 * budget / |State|)`

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

set_option autoImplicit false

namespace Commons.CipherMultiContext

open SystemAlgebra Probability Commons.DaviesMeyer
open scoped NNReal SystemAlgebra SystemAlgebra.DSL

noncomputable section

-- `Block`, `State` parameterize the ideal cipher; `Auxiliary` carries independent randomness;
-- `A` is the outside interface; `users` is the number of independent hidden-key slots.
variable {Block State Auxiliary : Type} [Fintype Block] [Fintype State] [Nonempty State]
  {A : Interface} (users : Nat)
  (P : Distribution Auxiliary) [Distribution.IsProbability P]
  (mask : State → Equiv.Perm State)
  (evaluate : Auxiliary → (Fin users × Block → State) → CipherFamily Block State →
    ∀ i, A.X i → A.Y i)

local notation "Ciphers" => CipherFamily Block State
local notation "Coins" => Fin users → State × (Block → State)
local notation "Input" => Sigma (Interface.X A)
local notation "μ[" T "]" => Distribution.uniform T

/-- Hybrid oracle at cut `level`: ideal table for slots `< level`, Davies–Meyer compression
under the slot's hidden key for slots `≥ level`. -/
def oracle (level : Nat) (coins : Coins) (E : Ciphers) (x : Fin users × Block) : State :=
  if x.1.val < level then (coins x.1).2 x.2 else mask (coins x.1).1 (E x.2 (coins x.1).1)

open Classical in
/-- The `level`-th hybrid system, sharing one ideal cipher `E` across all slots and context. -/
def hybrid (level : Nat) : TypedSystem A :=
  sample a ← P; sample coins ← μ[Coins]; sample E ← μ[Ciphers];
    TypedSystem.ofFunction (evaluate a (oracle users mask level coins E) E)

open Classical in
/-- Real multi-root system: `users` independent uniform hidden keys sharing one cipher `E`. -/
def real : TypedSystem A :=
  sample a ← P; sample keys ← μ[Fin users → State]; sample E ← μ[Ciphers];
    TypedSystem.ofFunction (evaluate a (fun x => mask (keys x.1) (E x.2 (keys x.1))) E)

open Classical in
/-- Ideal multi-root system: an independent uniform table on `Fin users × Block` alongside `E`. -/
def ideal : TypedSystem A :=
  sample a ← P; sample F ← μ[Fin users × Block → State]; sample E ← μ[Ciphers];
    TypedSystem.ofFunction (evaluate a F E)

/-- Multi-root replacement security target in `Δ`. -/
def Security (budget : Nat) : Prop :=
  Δ (real users P mask evaluate) (ideal users P evaluate) ≤
    ((users : ℝ≥0) * cipherKeyGuessing State budget : ℝ≥0)

open Classical in
/-- The `0`-th hybrid equals the real independent-hidden-root system. -/
lemma hybrid_zero : hybrid users P mask evaluate 0 = real users P mask evaluate := by
  let split := Equiv.arrowProdEquivProdArrow (Fin users) (fun _ => State)
    (fun _ => Block → State)
  unfold hybrid real
  apply congrArg (TypedSystem.sample P)
  funext a
  refine (TypedSystem.sample_uniform_equiv split.symm _).trans ?_
  simp only [Distribution.ProbDist.uniform, ← Distribution.prod_uniform, TypedSystem.sample_prod]
  have hr (keys : Fin users → State) (tables : Fin users → Block → State) (E : Ciphers) :
      oracle users mask 0 (split.symm (keys, tables)) E =
        fun x => mask (keys x.1) (E x.2 (keys x.1)) := by
    funext x
    simp only [oracle, Nat.not_lt_zero, ite_false]
    rfl
  simp only [hr, TypedSystem.sample_const]

open Classical in
/-- The `users`-th hybrid equals the ideal independent-table system. -/
lemma hybrid_all : hybrid users P mask evaluate users = ideal users P evaluate := by
  let split := Equiv.arrowProdEquivProdArrow (Fin users) (fun _ => State)
    (fun _ => Block → State)
  unfold hybrid ideal
  apply congrArg (TypedSystem.sample P)
  funext a
  refine (TypedSystem.sample_uniform_equiv split.symm _).trans ?_
  simp only [Distribution.ProbDist.uniform, ← Distribution.prod_uniform, TypedSystem.sample_prod]
  have hr (keys : Fin users → State) (tables : Fin users → Block → State) (E : Ciphers) :
      oracle users mask users (split.symm (keys, tables)) E = Function.uncurry tables := by
    funext x
    simp only [oracle, ite_eq_left x.1.isLt]
    rfl
  simp only [hr, TypedSystem.sample_const]
  exact (TypedSystem.sample_uniform_equiv (Equiv.curry (Fin users) Block State).symm
    (fun F => sample E ← μ[Ciphers]; TypedSystem.ofFunction (evaluate a F E))).symm

/-- Hybrid oracle isolating slot `i` to read an external table `F : Block → State`. -/
def selected (i : Fin users) (coins : Coins) (F : Block → State) (E : Ciphers)
    (x : Fin users × Block) : State :=
  if x.1 = i then F x.2 else oracle users mask i.val coins E x

/-- Single-slot context replies exposed when replacing slot `i`. -/
def selectedReplies (i : Fin users) (seed : Auxiliary × Coins) (F : Block → State) (E : Ciphers) :
    ∀ j, A.X j → A.Y j :=
  evaluate seed.1 (selected users mask i seed.2 F E) E

omit [Fintype Block] [Fintype State] [Nonempty State] in
/-- Updating slot `i` to `(k, F)` at cut `i` plugs the Davies–Meyer function of `k` into
slot `i`. -/
lemma oracle_update_real (i : Fin users) (coins : Coins) (k : State) (F : Block → State)
    (E : Ciphers) :
    oracle users mask i.val (Function.update coins i (k, F)) E =
      selected users mask i coins (fun m => mask k (E m k)) E := by
  funext x
  by_cases hx : x.1 = i
  · simp only [oracle, selected, hx, Function.update_self, lt_self_iff_false,
      ite_false, ite_true]
  · simp only [oracle, selected, ite_eq_right hx, Function.update_of_ne hx]

omit [Fintype Block] [Fintype State] [Nonempty State] in
/-- Updating slot `i` to `(k, F)` at cut `i + 1` plugs the ideal table `F` into slot `i`. -/
lemma oracle_update_ideal (i : Fin users) (coins : Coins) (k : State) (F : Block → State)
    (E : Ciphers) :
    oracle users mask (i.val + 1) (Function.update coins i (k, F)) E =
      selected users mask i coins F E := by
  funext x
  by_cases hx : x.1 = i
  · simp only [oracle, selected, hx, Function.update_self, Nat.lt_succ_self, ite_true]
  · have hl : x.1.val < i.val + 1 ↔ x.1.val < i.val := by
      have hn : x.1.val ≠ i.val := fun h => hx (Fin.ext h)
      omega
    simp only [oracle, selected, ite_eq_right hx, Function.update_of_ne hx, hl]

open Classical in
/-- Resampling coordinate `i` of the uniform coin vector preserves `hybrid level`. -/
lemma hybrid_resample (i : Fin users) (level : Nat) :
    hybrid users P mask evaluate level =
      (sample a ← P; sample coins ← μ[Coins]; sample fresh ← μ[State × (Block → State)];
        sample E ← μ[Ciphers]; TypedSystem.ofFunction
          (evaluate a (oracle users mask level (Function.update coins i fresh) E) E)) := by
  unfold hybrid
  apply congrArg (TypedSystem.sample P)
  funext a
  let body (coins : Coins) := sample E ← μ[Ciphers];
    TypedSystem.ofFunction (evaluate a (oracle users mask level coins E) E)
  have h := TypedSystem.sample_fTransform (fun pair => Function.update pair.1 i pair.2)
    μ[Coins × (State × (Block → State))] body
  simp only [Counting.fTransform_update_uniform] at h
  simpa only [body, ← Distribution.prod_uniform, TypedSystem.sample_prod] using h

open Classical in
/-- Hybrid `i` is the real single-root context experiment for `selectedReplies i`. -/
lemma hybrid_eq_context_real (i : Fin users) :
    hybrid users P mask evaluate i.val =
      CipherContext.real (P.prod μ[Coins]) mask (selectedReplies users mask evaluate i) := by
  rw [hybrid_resample users P mask evaluate i i.val]
  simp only [CipherContext.real, ← Distribution.prod_uniform, TypedSystem.sample_prod]
  apply congrArg (TypedSystem.sample P)
  funext a
  apply congrArg (TypedSystem.sample μ[Coins])
  funext coins
  apply congrArg (TypedSystem.sample μ[State])
  funext k
  simp only [oracle_update_real, TypedSystem.sample_const]
  rfl

open Classical in
/-- Hybrid `i + 1` is the ideal single-root context experiment for `selectedReplies i`. -/
lemma hybrid_eq_context_ideal (i : Fin users) :
    hybrid users P mask evaluate (i.val + 1) =
      CipherContext.ideal (P.prod μ[Coins]) (selectedReplies users mask evaluate i) := by
  rw [hybrid_resample users P mask evaluate i (i.val + 1)]
  simp only [CipherContext.ideal, ← Distribution.prod_uniform, TypedSystem.sample_prod]
  apply congrArg (TypedSystem.sample P)
  funext a
  apply congrArg (TypedSystem.sample μ[Coins])
  funext coins
  simp only [oracle_update_ideal, TypedSystem.sample_const]
  rw [TypedSystem.sample_comm]
  rfl

variable
  (challengeCalls : Auxiliary → (Fin users × Block → State) → CipherFamily Block State →
    Sigma A.X → List (Fin users × Block))
  (cipherCalls : Auxiliary → (Fin users × Block → State) → CipherFamily Block State →
    Sigma A.X → List (CipherQuery Block State))

/-- Deterministic dependency certificate across both the multi-root challenge table and cipher. -/
def RespectsCalls : Prop :=
  ∀ a G G' E E' x,
    (∀ q ∈ challengeCalls a G E x, G' q = G q) →
    (∀ q ∈ cipherCalls a G E x, cipherReply E' q = cipherReply E q) →
      evaluate a G' E' x.1 x.2 = evaluate a G E x.1 x.2

/-- Total cipher calls exposed when isolating slot `i`: direct cipher calls plus encryption calls
made by still-real slots `j > i`. -/
def selectedCalls (i : Fin users) (seed : Auxiliary × Coins) (F : Block → State) (E : Ciphers)
    (x : Input) : List (CipherQuery Block State) :=
  let G := selected users mask i seed.2 F E
  cipherCalls seed.1 G E x ++ (challengeCalls seed.1 G E x).filterMap
    (fun q => if i.val < q.1.val then some (false, q.2, (seed.2 q.1).1) else none)

omit [Fintype Block] [Fintype State] [Nonempty State] in
/-- Multi-oracle locality implies single-cipher locality for each isolated slot `i`. -/
lemma selected_respectsCalls
    (respectsCalls : RespectsCalls users evaluate challengeCalls cipherCalls)
    (i : Fin users) :
    CipherContext.RespectsCalls (selectedReplies users mask evaluate i)
      (selectedCalls users mask challengeCalls cipherCalls i) := by
  intro seed F E E' x he
  apply respectsCalls
  · intro q hq
    by_cases hi : q.1 = i
    · simp only [selected, ite_eq_left hi]
    · simp only [selected, ite_eq_right hi, oracle]
      by_cases hl : q.1.val < i.val
      · rw [ite_eq_left hl, ite_eq_left hl]
      · rw [ite_eq_right hl, ite_eq_right hl]
        have hil : i.val < q.1.val := by
          have hn : q.1.val ≠ i.val := fun h => hi (Fin.ext h)
          omega
        apply congrArg (mask (seed.2 q.1).1)
        exact he (false, q.2, (seed.2 q.1).1)
          (List.mem_append_right _ (List.mem_filterMap.mpr ⟨q, hq, ite_eq_left hil⟩))
  · intro q hq
    exact he q (List.mem_append_left _ hq)

omit [Fintype Block] [Fintype State] [Nonempty State] in
/-- Combined challenge and cipher call count bounds the isolated slot's cipher calls. -/
lemma selectedCalls_length_le (budget : Nat)
    (hbudget : ∀ a G E xs, xs = [] ∨ A.domain xs →
      (xs.flatMap (challengeCalls a G E)).length +
        (xs.flatMap (cipherCalls a G E)).length ≤ budget)
    (i : Fin users) (seed : Auxiliary × Coins) (F : Block → State) (E : Ciphers)
    (xs : List Input) (hd : xs = [] ∨ A.domain xs) :
    (xs.flatMap (selectedCalls users mask challengeCalls cipherCalls i seed F E)).length ≤
      budget := by
  let G := selected users mask i seed.2 F E
  refine le_trans ?_ (hbudget seed.1 G E xs hd)
  clear hd hbudget
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, selectedCalls]
    have hf := List.length_filterMap_le
      (f := fun q : Fin users × Block => if i.val < q.1.val then
        some (false, q.2, (seed.2 q.1).1) else none) (l := challengeCalls seed.1 G E x)
    dsimp only [G] at ih hf ⊢
    omega

variable (mask_injective : ∀ y, Function.Injective (fun k => mask k y))

include mask_injective in
open Classical in
/-- Single-slot `Δ` distance bound between consecutive hybrids `i` and `i + 1`. -/
lemma hybrid_step (budget : Nat)
    (respectsCalls : RespectsCalls users evaluate challengeCalls cipherCalls)
    (hbudget : ∀ a G E xs, xs = [] ∨ A.domain xs →
      (xs.flatMap (challengeCalls a G E)).length +
        (xs.flatMap (cipherCalls a G E)).length ≤ budget)
    (i : Fin users) :
    Δ (hybrid users P mask evaluate i.val) (hybrid users P mask evaluate (i.val + 1)) ≤
      (cipherKeyGuessing State budget : ℝ≥0) := by
  rw [hybrid_eq_context_real, hybrid_eq_context_ideal]
  exact CipherContext.security (P.prod μ[Coins]) mask (selectedReplies users mask evaluate i)
    mask_injective (selectedCalls users mask challengeCalls cipherCalls i) budget
    (selected_respectsCalls users mask evaluate challengeCalls cipherCalls respectsCalls i)
    (selectedCalls_length_le users mask challengeCalls cipherCalls budget hbudget i)

include mask_injective in
open Classical in
/-- Single-slot pointwise transcript ratio between consecutive hybrids `i` and `i + 1`. -/
lemma hybrid_step_ratio (budget : Nat)
    (respectsCalls : RespectsCalls users evaluate challengeCalls cipherCalls)
    (hbudget : ∀ a G E xs, xs = [] ∨ A.domain xs →
      (xs.flatMap (challengeCalls a G E)).length +
        (xs.flatMap (cipherCalls a G E)).length ≤ budget)
    (i : Fin users) (h : List (Input × Sigma A.Y)) :
    (1 - (cipherKeyGuessing State budget : ℝ)) *
      (hybrid users P mask evaluate (i.val + 1)).1 h ≤
        (hybrid users P mask evaluate i.val).1 h := by
  rw [hybrid_eq_context_real, hybrid_eq_context_ideal]
  exact CipherContext.transcript_ratio (P.prod μ[Coins]) mask
    (selectedReplies users mask evaluate i) mask_injective
    (selectedCalls users mask challengeCalls cipherCalls i) budget
    (selected_respectsCalls users mask evaluate challengeCalls cipherCalls respectsCalls i)
    (selectedCalls_length_le users mask challengeCalls cipherCalls budget hbudget i) h

include mask_injective in
/-- Pointwise transcript ratio telescoping across all `users` hidden-key slots. -/
lemma transcript_ratio (budget : Nat)
    (respectsCalls : RespectsCalls users evaluate challengeCalls cipherCalls)
    (hbudget : ∀ a G E xs, xs = [] ∨ A.domain xs →
      (xs.flatMap (challengeCalls a G E)).length +
        (xs.flatMap (cipherCalls a G E)).length ≤ budget)
    (h : List (Input × Sigma A.Y)) :
    (1 - (users : ℝ) * cipherKeyGuessing State budget) *
      (ideal users P evaluate).1 h ≤ (real users P mask evaluate).1 h := by
  rw [← hybrid_zero users P mask evaluate, ← hybrid_all users P mask evaluate]
  exact TypedSystem.transcript_ratio_chain (hybrid users P mask evaluate) users
    (cipherKeyGuessing State budget) (fun d hd =>
      hybrid_step_ratio users P mask evaluate challengeCalls cipherCalls mask_injective
        budget respectsCalls hbudget ⟨d, hd⟩) h

include mask_injective in
/-- **Multi-root shared-cipher replacement** [1, Theorem 8.5, p. 311]: replacing all `users`
hidden-key Davies–Meyer slots inside a context with combined call budget `budget` incurs `Δ`
distance at most `users * (2 * budget / |State|)`. -/
theorem security (budget : Nat)
    (respectsCalls : RespectsCalls users evaluate challengeCalls cipherCalls)
    (hbudget : ∀ a G E xs, xs = [] ∨ A.domain xs →
      (xs.flatMap (challengeCalls a G E)).length +
        (xs.flatMap (cipherCalls a G E)).length ≤ budget) :
    Security users P mask evaluate budget := by
  change Δ (real users P mask evaluate) (ideal users P evaluate) ≤ _
  rw [Interface.cc_distance_eq]
  exact TypedSystem.distance_le_of_transcript_ratio
    (real users P mask evaluate) (ideal users P evaluate)
    ((users : ℝ≥0) * cipherKeyGuessing State budget)
    (fun h => by
      simpa only [NNReal.coe_mul, NNReal.coe_natCast] using
        transcript_ratio users P mask evaluate challengeCalls cipherCalls mask_injective
          budget respectsCalls hbudget h)

end

end Commons.CipherMultiContext
