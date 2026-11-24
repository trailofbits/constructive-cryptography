module

public import Commons.Definitions.MAC.Algorithms
public import RandomSystems.Typed.QueryRouting

/-!
# Stateless MAC algorithms as a memoryless system

Tests `MAC.algorithms.eq_ofMemoryless` on the bit MAC that tags every message with a fresh fair
bit and accepts a tag equal to the key. Two tags of the same message are independent fair draws,
and verification returns the point law of `t == k`. Attaching a stateless router fixes a key and
yields a closed memoryless form directly.
-/

@[expose] public section

namespace Tests.MACAlgorithms

open CategoryTheory Commons SystemAlgebra Probability Probability.Distribution

/-- Bit MAC that tags every message with a fresh fair bit and verifies `t == k`. -/
noncomputable def bitMAC : MAC Bool Bool Bool where
  gen := 𝒰[Bool]
  tag _ _ := 𝒰[Bool]
  verify k _ t := t == k

/-- On `bitMAC`, `tag(k, m)` replies with a fresh fair bit for any `k` and `m`. -/
example (k m : Bool) :
    MAC.algorithms.replyLaw bitMAC .tag (k, m) = 𝒰[Bool] := rfl

/-- On `bitMAC`, `verify(k, m, t)` replies with the point law of `t == k`. -/
example (k m t : Bool) :
    MAC.algorithms.replyLaw bitMAC .verify (k, m, t) = ProbDist.single (t == k) := rfl

/-- Two tags of the same `(k, m)` are independent fair draws, each pair having probability `1/4`
(including distinct tags `t₀ ≠ t₁`). -/
example (k m t₀ t₁ : Bool) :
    (MAC.algorithms (budget := 2) bitMAC).1
      [(⟨.tag, (k, m)⟩, ⟨.tag, t₀⟩), (⟨.tag, (k, m)⟩, ⟨.tag, t₁⟩)] = 1 / 4 := by
  rw [MAC.algorithms.eq_ofMemoryless, TypedSystem.ofMemoryless_val]
  have hunif : ∀ b : Bool, 𝒰[Bool].1 b = (1 / 2 : ℝ) := fun b => by
    change Distribution.uniform Bool b = (1 / 2 : ℝ)
    simp only [Distribution.uniform_apply, Fintype.card_bool, Nat.cast_ofNat]
  have hd1 : (MACAlgorithms Bool Bool Bool 2).inputDomain [] ⟨.tag, (k, m)⟩ :=
    ⟨List.cons_ne_nil _ _, by norm_num⟩
  have hd2 : (MACAlgorithms Bool Bool Bool 2).inputDomain
      [(⟨.tag, (k, m)⟩, ⟨.tag, t₀⟩)] ⟨.tag, (k, m)⟩ :=
    ⟨List.cons_ne_nil _ _, by norm_num⟩
  change RandomSystem.memoryless (MACAlgorithms Bool Bool Bool 2).inputDomain
    (RandomSystem.portLaw (MAC.algorithms.replyLaw bitMAC))
    ([(⟨.tag, (k, m)⟩, ⟨.tag, t₀⟩)] ++ [(⟨.tag, (k, m)⟩, ⟨.tag, t₁⟩)]) = 1 / 4
  rw [RandomSystem.memoryless_snoc, ite_eq_left hd2, RandomSystem.portLaw_apply_mk]
  change RandomSystem.memoryless (MACAlgorithms Bool Bool Bool 2).inputDomain
    (RandomSystem.portLaw (MAC.algorithms.replyLaw bitMAC))
    ([] ++ [(⟨.tag, (k, m)⟩, ⟨.tag, t₀⟩)]) * (MAC.algorithms.replyLaw bitMAC .tag (k, m)).1 t₁ =
    1 / 4
  rw [RandomSystem.memoryless_snoc, ite_eq_left hd1, RandomSystem.mass_nil, one_mul,
    RandomSystem.portLaw_apply_mk]
  change 𝒰[Bool].1 t₀ * 𝒰[Bool].1 t₁ = 1 / 4
  rw [hunif t₀, hunif t₁]
  norm_num

/-- Verification answers `verify(k, m, t)` by the point law of `t == k`. -/
example (k m t v : Bool) :
    (MAC.algorithms (budget := 1) bitMAC).1
      [(⟨.verify, (k, m, t)⟩, ⟨.verify, v⟩)] = if v = (t == k) then 1 else 0 := by
  rw [MAC.algorithms.eq_ofMemoryless, TypedSystem.ofMemoryless_val]
  have hd : (MACAlgorithms Bool Bool Bool 1).inputDomain [] ⟨.verify, (k, m, t)⟩ :=
    ⟨List.cons_ne_nil _ _, le_rfl⟩
  change RandomSystem.memoryless (MACAlgorithms Bool Bool Bool 1).inputDomain
    (RandomSystem.portLaw (MAC.algorithms.replyLaw bitMAC))
    ([] ++ [(⟨.verify, (k, m, t)⟩, ⟨.verify, v⟩)]) = _
  rw [RandomSystem.memoryless_snoc, ite_eq_left hd, RandomSystem.mass_nil, one_mul,
    RandomSystem.portLaw_apply_mk]
  change (ProbDist.single (t == k)).1 v = _
  simp only [ProbDist.single, Finsupp.single_apply, eq_comm]

/-- Attaching a stateless router that supplies a fixed key `k` reduces `MAC.algorithms bitMAC`
to a memoryless `Tagging` system directly. -/
example (k : Bool) (q : ℕ) :
    let req : (Σ i, (Tagging Bool Bool q).X i) → (Σ i, (MACAlgorithms Bool Bool Bool q).X i) :=
      fun
        | ⟨.tag, m⟩ => ⟨.tag, (k, m)⟩
        | ⟨.verify, (m, t)⟩ => ⟨.verify, (k, m, t)⟩
    let ans : (u : Σ i, (Tagging Bool Bool q).X i) →
        (Σ i, (MACAlgorithms Bool Bool Bool q).Y i) → (Tagging Bool Bool q).Y u.1 :=
      fun
        | ⟨.tag, _⟩, ⟨.tag, t⟩ => t
        | ⟨.tag, _⟩, ⟨.verify, b⟩ => b
        | ⟨.verify, _⟩, ⟨.tag, t⟩ => t
        | ⟨.verify, _⟩, ⟨.verify, b⟩ => b
    let hmap : ∀ us, (Tagging Bool Bool q).domain us →
        (MACAlgorithms Bool Bool Bool q).domain (us.map req) := fun us hus =>
      ⟨fun h => hus.1 (List.map_eq_nil_iff.mp h),
       by simpa only [List.length_map] using hus.2⟩
    TypedConverter.routing req ans hmap • MAC.algorithms (budget := q) bitMAC =
      TypedSystem.ofMemoryless (Tagging Bool Bool q) (fun o u =>
        ProbDist.map (fun y => ans ⟨o, u⟩ ⟨(req ⟨o, u⟩).1, y⟩)
          (MAC.algorithms.replyLaw bitMAC (req ⟨o, u⟩).1 (req ⟨o, u⟩).2)) := by
  intro req ans hmap
  rw [MAC.algorithms.eq_ofMemoryless, TypedConverter.routing_smul_ofMemoryless]

/-- `MAC.algorithms.eq_ofMemoryless` composes cleanly with `cc_normalize` on converter chains. -/
example {A B : Interface} {K M T : Type} [Fintype K] [Fintype M] [Fintype T]
    [DecidableEq K] [DecidableEq M] (mac : MAC K M T) (q : ℕ)
    (α : A ⟶ B) (β : B ⟶ MACAlgorithms K M T q) :
    (α ≫ β) • MAC.algorithms (budget := q) mac =
      α • (β • TypedSystem.ofMemoryless (MACAlgorithms K M T q)
        (MAC.algorithms.replyLaw mac)) := by
  rw [MAC.algorithms.eq_ofMemoryless]
  cc_normalize

#print axioms Commons.MAC.algorithms
#print axioms Commons.MAC.algorithms.replyLaw
#print axioms Commons.MAC.algorithms.eq_ofMemoryless

end Tests.MACAlgorithms
