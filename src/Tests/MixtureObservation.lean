module

public import Tests.TypedNaryParallel
public import ConstructiveCryptography.Instances.Algebra

/-!
# Observation and distance of initially sampled systems

Generic checks:

* the observation identity `D.probability (mix P R) = E_{k ∼ P}[D.probability (R k)]` in its
  `expect` form;
* the bound `Δ(sample P R, sample P S) ≤ error` for an arbitrary normalized law, and with
  `error = 0` for equal components;
* an elaboration guard: the bound does not elaborate for two different laws `P`, `Q`. It is
  not a statement about the resulting distance.

Concrete checks on the fixtures `bitInterface` and `fixedBit c : ()(()) ⇒ c` of
`Tests.TypedNaryParallel`:

* `sample_single_distance_eq_one`: on the same family `fixedBit`, the point masses `δ_true`
  and `δ_false` give `Δ = 1`. The one-query observer `bitQuery` is compatible with the domain,
  the singleton transcript `()(()) ⇒ true` has probabilities `1` and `0`, and
  `transcriptDistance_le_one` gives the upper bound;
* `biasedNat = (1/3)δ₀ + (2/3)δ₁`, normalized and nonuniform on the infinite `ℕ`: sampling
  `natBit` replies `true` with probability `2/3`, and every compatible observer `D` satisfies
  `Pr[D(sample biasedNat R) = 1] = (1/3) · Pr[D(R 0) = 1] + (2/3) · Pr[D(R 1) = 1]`.
-/

@[expose] public section

open Probability SystemAlgebra
open scoped NNReal SystemAlgebra

/-- `D.probability (mix P R) = P.expect (k ↦ D.probability (R k))` for a compatible `D`:
`probability_mix` in the `expect` spelling, `expect P f = ∑ k ∈ supp P, P(k) · f k`. -/
example {A : Interface} {K : Type} (P : Distribution.ProbDist K)
    (R : K → TypedSystem A) (D : A.inputDomain.Distinguisher) :
    D.probability (RandomSystem.mix P (fun k => (R k).1)) =
      P.1.expect (fun k => D.probability (R k).1) :=
  Domain.Distinguisher.probability_mix P _ D

/-- `(∀ k, Δ(R k, S k) ≤ error) → Δ(sample P R, sample P S) ≤ error` for any normalized law
`P` on `K`, nonuniform or on an infinite `K`: finite support comes from `Distribution`, not
from a `Fintype K` assumption. -/
example {A : Interface} {K : Type} (P : Distribution K) [Distribution.IsProbability P]
    (R S : K → TypedSystem A) (error : ℝ≥0)
    (bound : ∀ k, Δ (R k) (S k) ≤ error) :
    Δ (TypedSystem.sample P R) (TypedSystem.sample P S) ≤ error :=
  Interface.distance_sample_le P R S error bound

/-- With `R b = S b` for each `b : Bool`, `Δ(R b, S b) = 0`, so
`Δ(sample U R, sample U S) ≤ 0` for the uniform law `U(b) = 1/2`. -/
example {A : Interface} (R S : Bool → TypedSystem A)
    (same : ∀ b, R b = S b) :
    Δ (TypedSystem.sample (Distribution.uniform Bool) R)
      (TypedSystem.sample (Distribution.uniform Bool) S) ≤ (0 : ℝ≥0) := by
  apply Interface.distance_sample_le
  intro b
  -- At each index the compared resources coincide.
  simp only [same b, ConstructiveCryptography.CryptographicAlgebra.distance_self,
    ENNReal.coe_zero, le_refl]

/-- Applying the bound with `P` fixes the law on both sides of the comparison. -/
example {A : Interface} {K : Type} (P Q : Distribution K)
    [Distribution.IsProbability P] [Distribution.IsProbability Q]
    (R S : K → TypedSystem A) (error : ℝ≥0)
    (_bound : ∀ k, Δ (R k) (S k) ≤ error) : True := by
  fail_if_success
    have : Δ (TypedSystem.sample P R) (TypedSystem.sample Q S) ≤ error :=
      Interface.distance_sample_le P R S error _bound
  trivial

/-- The point law `δ₇` needs a component bound only at `7`, with no reply-port assumptions. -/
example {domain : Domain (Σ _ : Bool, Unit) (Σ _ : Bool, Unit)}
    (R S : ℕ → RandomSystem _ _ domain) (ε : NNReal)
    (bound : (R 7).transcriptDistance (S 7) ≤ (ε : ENNReal)) :
    (RandomSystem.mix (Distribution.ProbDist.single 7) R).transcriptDistance
      (RandomSystem.mix (Distribution.ProbDist.single 7) S) ≤ (ε : ENNReal) := by
  simpa only [Distribution.expect_const, Distribution.ProbDist.single,
    Distribution.weight_single, mul_one, Real.toNNReal_coe] using
    RandomSystem.transcriptDistance_mix_le_expect (Distribution.ProbDist.single 7)
      R S (fun _ => ε) (by
        intro k supported
        have hk : k = 7 := (Finsupp.mem_support_single k 7 (1 : ℝ)).mp supported |>.1
        simpa only [hk] using bound)

#print axioms RandomSystem.transcriptDistance_mix_le_expect
#print axioms Domain.Distinguisher.probability_mix
#print axioms TypedSystem.transcriptDistance_sample_le

namespace SystemAlgebra.Tests.MixtureObservation

open SystemAlgebra.Tests

noncomputable section

/-- One query on `bitInterface`, then stop: `E [] = ()`, undefined after any reply. -/
def bitQuery : DDE (Σ i, bitInterface.X i) (Σ i, bitInterface.Y i) :=
  DDE.ofQueries [⟨(), ()⟩]

/-- `bitQuery` makes at most one query: `E ys` is defined only for `ys = []`. -/
lemma bitQuery_bounded : QueryBounded 1 bitQuery := by
  -- `E ys` is the entry `ys.length` of the one-element query list, so `ys.length < 1`.
  intro ys hd
  simpa only [Order.lt_one_iff, List.length_eq_zero_iff, bitQuery, DDE.ofQueries, fixedQueries,
    Part.ofOption_dom, isSome_getElem?, List.length_cons, List.length_nil, zero_add] using hd

/-- `bitQuery` asks only admitted inputs: its single query `()` follows the empty history, and
`[()]` is within the budget 1 of `bitInterface`. -/
lemma bitQuery_compatible : bitInterface.inputDomain.Compatible bitQuery := by
  intro _ _ h x _ _ hx
  -- A query `x ∈ E (replies of h)` exists only before any reply, so `h = []`.
  have hh : h.length = 0 := by
    have hb := bitQuery_bounded (h.map Prod.snd) (Part.dom_iff_mem.mpr ⟨x, hx⟩)
    simp only [List.length_map] at hb
    omega
  have he : h = [] := List.length_eq_zero_iff.mp hh
  subst h
  -- The history `[x]` is nonempty and has length `1 ≤ 1`.
  simp only [bitInterface, Interface.queryBudget, ne_eq, Interface.inputDomain, Domain.ofInputs,
    List.append_eq_nil_iff, List.map_eq_nil_iff, List.cons_ne_self, and_false, not_false_eq_true,
    List.length_append, List.length_map, List.length_cons, List.length_nil, zero_add,
    add_le_iff_nonpos_left, nonpos_iff_eq_zero, List.length_eq_zero_iff, true_and]

/-- Sampling the same family `fixedBit` with `δ_true` and `δ_false` gives distance `1`:
`Δ(sample δ_true fixedBit, sample δ_false fixedBit) = 1`. The compatible one-query environment
`bitQuery` sees `()(()) ⇒ true` with probabilities `1` and `0`. -/
lemma sample_single_distance_eq_one :
    (TypedSystem.sample (Finsupp.single true 1) fixedBit).1.transcriptDistance
    (TypedSystem.sample (Finsupp.single false 1) fixedBit).1 = 1 := by
  let R := TypedSystem.sample (Finsupp.single true 1) fixedBit
  let S := TypedSystem.sample (Finsupp.single false 1) fixedBit
  change R.1.transcriptDistance S.1 = 1
  -- `Δ ≤ 1` for any two normalized systems; it remains to show `1 ≤ Δ(R, S)`.
  apply le_antisymm (RandomSystem.transcriptDistance_le_one R.2 S.2)
  -- The transcript `t = [()(()) ⇒ true]`.
  let t : List ((Σ i, bitInterface.X i) × (Σ i, bitInterface.Y i)) :=
    [(⟨(), ()⟩, ⟨(), true⟩)]
  -- `t` follows `bitQuery` and is complete within one round.
  have ht : Good bitQuery.1 1 t := by
    constructor
    -- `t = [] ++ [()(()) ⇒ true]`: the empty prefix follows trivially, and the query
    -- `()` is `bitQuery`'s answer at the empty reply history, `E [] = ()`.
    · apply (FollowsStrategy.snoc_iff (h := [])).mpr
      refine ⟨FollowsStrategy.nil, ?_⟩
      simp only [bitQuery, DDE.ofQueries, List.map_nil, fixedQueries, List.length_nil,
        List.getElem?_cons_zero, Part.coe_some, Part.mem_some_iff]
    -- Completeness: `t` has reached the round bound `1`.
    · exact Or.inl rfl
  -- The singleton event `{t}` gives `R.sLaw(t) − S.sLaw(t) ≤ δ(R.sLaw, S.sLaw)`.
  have hg := mass_sub_mass_le_statDist (R.1.sLaw bitQuery.1 1) (S.1.sLaw bitQuery.1 1)
    (fun h => h = t)
  -- As `t` is good, each transcript-law value is the system's mass: `R(t) − S(t) ≤ δ`.
  rw [Distribution.mass_singleton, Distribution.mass_singleton,
    RandomSystem.sLaw_apply, RandomSystem.sLaw_apply, ite_eq_left ht, ite_eq_left ht] at hg
  -- `R(t) = 1` (component `fixedBit true`) and `S(t) = 0` (component `fixedBit false`).
  norm_num [R, S, TypedSystem.sample_mass, fixedBit, TypedSystem.ofFunction_mass,
    bitInterface, t] at hg
  -- `1 ≤ δ ≤ Δ(R, S)`: `bitQuery` is one-query bounded and compatible with the domain.
  have hb := ENNReal.ofReal_le_ofReal hg
  simpa only [ENNReal.ofReal_one] using hb.trans
    (RandomSystem.statDist_le_transcriptDistance bitQuery_bounded bitQuery_compatible R.1 S.1)

/-- A normalized nonuniform law on the infinite carrier `ℕ`:
`P(0) = 1/3`, `P(1) = 2/3`, and `P(k) = 0` otherwise. -/
def biasedNat : Distribution ℕ :=
  (1 / 3 : ℝ) • Finsupp.single 0 1 + (2 / 3 : ℝ) • Finsupp.single 1 1

/-- `biasedNat` is a probability law: `P(k) ≥ 0` and `1/3 + 2/3 = 1`. -/
instance : Distribution.IsProbability biasedNat where
  nonNeg k := by
    -- `P(k) = (1/3) · δ₀(k) + (2/3) · δ₁(k)`, a sum of nonnegative terms.
    simp only [biasedNat, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    exact add_nonneg
      (mul_nonneg (by norm_num) ((Distribution.isProbDist_single 0).1 k))
      (mul_nonneg (by norm_num) ((Distribution.isProbDist_single 1).1 k))
  weight_eq_one := by
    -- Weight is linear and each point mass has weight 1: `|P| = 1/3 · 1 + 2/3 · 1`.
    rw [biasedNat, Distribution.weight_add, Distribution.weight_smul, Distribution.weight_smul,
      (Distribution.isProbDist_single 0).weight_eq, (Distribution.isProbDist_single 1).weight_eq]
    norm_num

/-- `natBit k` returns `false` at `k = 0` and `true` otherwise, on the one-query bit interface. -/
def natBit : ℕ → TypedSystem bitInterface
  | 0 => fixedBit false
  | _ + 1 => fixedBit true

/-- Sampling `natBit` with `biasedNat` returns `true` with probability `2/3`:
`Pr[()(()) ⇒ true] = 1/3 · 0 + 2/3 · 1`. -/
example : (TypedSystem.sample biasedNat natBit).1 [(⟨(), ()⟩, ⟨(), true⟩)] = 2 / 3 := by
  -- The mass is `∑ k ∈ supp P, P(k) · (natBit k)(h)` over the support `{0, 1}`.
  rw [TypedSystem.sample_mass]
  -- The two support points contribute `1/3 · 0` and `2/3 · 1`, respectively.
  norm_num [biasedNat, Finsupp.support_add_eq, natBit, fixedBit,
    TypedSystem.ofFunction_mass, bitInterface]

/-- For any compatible observer `D` and any family `R` on `ℕ`, sampling with
`P = (1/3)δ₀ + (2/3)δ₁` gives
`Pr[D(sample P R) = 1] = (1/3) · Pr[D(R 0) = 1] + (2/3) · Pr[D(R 1) = 1]`,
although the carrier `ℕ` is infinite. -/
example {A : Interface} (R : ℕ → TypedSystem A) (D : A.inputDomain.Distinguisher) :
    D.probability (TypedSystem.sample biasedNat R).1 =
      (1 / 3 : ℝ) * D.probability (R 0).1 + (2 / 3 : ℝ) * D.probability (R 1).1 := by
  -- `probability_mix`: the left side is `E_{k ∼ P}[Pr[D(R k) = 1]]`.
  simp only [TypedSystem.sample, Domain.Distinguisher.probability_mix]
  change biasedNat.expect (fun k => D.probability (R k).1) = _
  -- Expectation is linear in the law, and `E_{δ_k}[f] = f k`.
  rw [biasedNat, Distribution.expect_add_left, Distribution.expect_smul_left,
    Distribution.expect_smul_left]
  simp only [Distribution.expect, Finsupp.sum_single_index, zero_mul, one_mul]

/-- Only the positive indices can differ from the constant-false resource. Under `biasedNat`
they have total mass `2/3`, so the weighted error improves on the uniform bound of one. -/
example :
    Δ (TypedSystem.sample biasedNat natBit) (TypedSystem.sample biasedNat (fun _ => fixedBit false))
      ≤ (2 / 3 : NNReal) := by
  let ε : ℕ → NNReal := fun k => if k = 0 then 0 else 1
  have component (k : ℕ) : Δ (natBit k) (fixedBit false) ≤ (ε k : ENNReal) := by
    cases k with
    | zero =>
      -- Both resources always return false at index zero.
      simp only [natBit, ε, ite_true, ConstructiveCryptography.CryptographicAlgebra.distance_self,
        ENNReal.coe_zero, le_refl]
    | succ k =>
      -- At every other index the normalized transcript distance is at most one.
      exact RandomSystem.transcriptDistance_le_one (natBit (k + 1)).2 (fixedBit false).2
  have weighted := Interface.distance_sample_le_expect biasedNat natBit
    (fun _ => fixedBit false) ε component
  -- The two atoms carry errors zero and one, respectively.
  have average : biasedNat.expect (fun k => (ε k : ℝ)) = 2 / 3 := by
    rw [biasedNat, Distribution.expect_add_left, Distribution.expect_smul_left,
      Distribution.expect_smul_left]
    norm_num [Distribution.expect, ε, Finsupp.sum_single_index]
  have cast : Real.toNNReal (2 / 3) = (2 / 3 : NNReal) := by
    apply NNReal.eq
    norm_num
  simpa only [average, cast] using weighted

#print axioms Interface.distance_sample_le_expect

#print axioms sample_single_distance_eq_one

end

end SystemAlgebra.Tests.MixtureObservation
