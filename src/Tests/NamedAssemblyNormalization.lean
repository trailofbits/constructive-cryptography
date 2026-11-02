module

public import Commons.Constructions.EncryptThenMAC
public import ConstructiveCryptography.Substitution.FiniteFamily
public import Tests.TypedNaryParallel

/-!
# Normalizing declared named assemblies

`encryptThenMAC.system_eq` exposes the named construction's common converter and independent
components, so a supplied component equality can be used directly. `parallelAllContext_smul`
reduces a named finite-family context to its exact component update. The guarded residual goals
show that normalization leaves the component equalities to the caller. A draw attached at a
selected component stays there. Bound distances with `cc_nonexpand` before normalizing, or use
`distance_parallelAll_update_le` on the resulting update families.

A retained draw around a family stays shared: `guard_hyp` pins its position, and the transcript
masses of `sharedBit` and `independentBit` from `Tests.TypedNaryParallel` distinguish it from
per-component draws. An explicit interface swap remains until its own law is supplied.
-/

@[expose] public section

namespace SystemAlgebra.Tests.NamedAssemblyNormalization
open Commons Probability SystemAlgebra.Substitution
open scoped SystemAlgebra NNReal

-- The trace exposes the EtM assembly; the residual goal retains the component equation.
/--
trace: [Meta.Tactic.simp.rewrite] encryptThenMAC.system_eq:1000:
      encryptThenMAC.system scheme mac q
    ==>
      encryptThenMAC M C T • (AE.system scheme ∥ mac.system)
[Meta.Tactic.simp.rewrite] Interface.cc_parallel_eq:100:
      AE.system scheme ∥ mac.system
    ==>
      (AE.system scheme).parallel mac.system
[Meta.Tactic.simp.rewrite] Interface.smul_eq_typed_smul:100:
      encryptThenMAC M C T • (AE.system scheme).parallel mac.system
    ==>
      (have this := encryptThenMAC M C T;
        this) •
        (AE.system scheme).parallel mac.system
[Meta.Tactic.simp.rewrite] Interface.cc_parallel_eq:100:
      R ∥ mac.system
    ==>
      R.parallel mac.system
[Meta.Tactic.simp.rewrite] Interface.smul_eq_typed_smul:100:
      encryptThenMAC M C T • R.parallel mac.system
    ==>
      (have this := encryptThenMAC M C T;
        this) •
        R.parallel mac.system
-/
#guard_msgs (whitespace := lax) in
example
    -- `K`, `L` carry keys; `M`, `C`, `T` carry messages, ciphertexts and tags.
    {K L M C T : Type} [Fintype K] [Fintype L] [Fintype M] [Fintype C] [Fintype T]
    [DecidableEq K] [DecidableEq L] [DecidableEq M] [DecidableEq C]
    -- `scheme` and `mac` are the fixed components; `q` is the outside query budget.
    (scheme : SymmetricEncryption K M C) (mac : MAC L C T) (q : ℕ)
    -- `R` is the replacement encryption system, with its local equation `h`.
    (R : TypedSystem (AE M C (2 * q))) (h : AE.system scheme = R) :
    encryptThenMAC.system scheme mac q = encryptThenMAC M C T • (R ∥ MAC.system mac) := by
  cc_normalize?
  guard_target = encryptThenMAC M C T • TypedSystem.parallel (AE.system scheme) (MAC.system mac) =
    encryptThenMAC M C T • TypedSystem.parallel R (MAC.system mac)
  rw [h]

/-- Family normalization exposes the selected component, retaining its local equality obligation. -/
example
    -- `K` tags the interfaces `A k`; `R j` supplies fixed components outside selected index `k`.
    {K : Type} [Fintype K] [DecidableEq K] {A : K → Interface}
    -- `S`, `T` are the local pair and `h` is their independently supplied equation.
    (R : ∀ k, TypedSystem (A k)) (k : K) (S T : TypedSystem (A k)) (h : S = T) :
    TypedConverter.parallelAllContext R k • S = (∥ j, Function.update R k T j) := by
  cc_normalize
  guard_target = (∥ j, Function.update R k S j) = (∥ j, Function.update R k T j)
  rw [h]

/-- The normalized family distance is bounded directly by the changed component's distance. -/
example
    -- `K` tags interfaces `A j`; `R j` fixes components outside `k`, with local pair `S`, `T`.
    {K : Type} [Fintype K] [DecidableEq K] {A : K → Interface}
    (R : ∀ k, TypedSystem (A k)) (k : K) (S T : TypedSystem (A k)) :
    Δ (TypedConverter.parallelAllContext R k • S)
      (TypedConverter.parallelAllContext R k • T) ≤ Δ S T := by
  cc_normalize
  guard_target = Δ (∥ j, Function.update R k S j) (∥ j, Function.update R k T j) ≤ Δ S T
  fail_if_success cc_nonexpand
  exact distance_parallelAll_update_le R k S T

/-- Bound the common attachment first, then normalize its exact component-update presentation. -/
example
    -- `K` tags interfaces `A j`; `R j` fixes components outside the selected tag `k`.
    {K : Type} [Fintype K] [DecidableEq K] {A : K → Interface}
    (R : ∀ k, TypedSystem (A k)) (k : K) (S T : TypedSystem (A k))
    -- `ε` bounds the selected pair by the supplied component contract `hlocal`.
    (ε : ℝ≥0) (hlocal : Δ S T ≤ ε) :
    Δ (∥ j, Function.update R k S j) (∥ j, Function.update R k T j) ≤ ε := by
  have hcontext : Δ (TypedConverter.parallelAllContext R k • S)
      (TypedConverter.parallelAllContext R k • T) ≤ Δ S T := by cc_nonexpand
  cc_normalize at hcontext
  guard_hyp hcontext : Δ (∥ j, Function.update R k S j) (∥ j, Function.update R k T j) ≤ Δ S T
  exact hcontext.trans hlocal

/-- EtM assembly normalization exposes the two existing non-expansion steps. -/
example
    -- `K`, `L` carry keys; `M`, `C`, `T` carry messages, ciphertexts and tags.
    {K L M C T : Type} [Fintype K] [Fintype L] [Fintype M] [Fintype C] [Fintype T]
    [DecidableEq K] [DecidableEq L] [DecidableEq M] [DecidableEq C]
    -- `scheme`, `mac`, `q` fix the assembly; `R` replaces only its encryption component.
    (scheme : SymmetricEncryption K M C) (mac : MAC L C T) (q : ℕ)
    (R : TypedSystem (AE M C (2 * q))) :
    Δ (encryptThenMAC.system scheme mac q)
      (encryptThenMAC M C T • (R ∥ MAC.system mac)) ≤ Δ (AE.system scheme) R := by
  cc_normalize
  calc
    _ ≤ Δ (TypedSystem.parallel (AE.system scheme) (MAC.system mac))
        (TypedSystem.parallel R (MAC.system mac)) := by cc_nonexpand
    _ ≤ Δ (AE.system scheme) R := by cc_nonexpand

/-- A retained draw inside the selected component stays in that component after isolation. -/
example
    -- `K` tags the interfaces `A j`; `R j` supplies fixed systems outside the selected tag `k`.
    {K : Type} [Fintype K] [DecidableEq K] {A : K → Interface}
    -- `Ω` carries retained values; `P` is their normalized law.
    {Ω : Type} (R : ∀ k, TypedSystem (A k)) (k : K) (P : Distribution.ProbDist Ω)
    -- `S s` is the inside system selected by the single retained value `s : Ω`.
    (S : Ω → TypedSystem (A k)) :
    TypedConverter.parallelAllContext R k • TypedSystem.sample P S =
      (∥ j, Function.update R k (TypedSystem.sample P S) j) := by
  cc_normalize

/-- The sampled component's supplied contract remains usable after normalization. -/
example
    -- `K` tags interfaces `A j`; `Ω` carries values drawn from `P` to select the system `S`.
    {K : Type} [Fintype K] [DecidableEq K] {A : K → Interface} {Ω : Type}
    (R : ∀ k, TypedSystem (A k)) (k : K) (P : Distribution.ProbDist Ω)
    -- `T` is the component described by the supplied retained-sample equation `h`.
    (S : Ω → TypedSystem (A k)) (T : TypedSystem (A k)) (h : TypedSystem.sample P S = T) :
    TypedConverter.parallelAllContext R k • TypedSystem.sample P S =
      ∥ j, Function.update R k T j := by
  cc_normalize
  rw [h]

/-- Serial composition isolates the selected component before considering its retained draw. -/
example
    -- `K` tags interfaces `A j`; `C` is the outside interface and `Ω` carries retained values.
    {K : Type} [Fintype K] [DecidableEq K] {A : K → Interface} {C : Interface} {Ω : Type}
    -- `R j` fixes components outside `k`; `context` attaches to the family and exposes `C`.
    (R : ∀ j, TypedSystem (A j)) (k : K) (context : TypedConverter C (⨂ j, A j))
    -- `P` is the retained law; `h` identifies its selected system `S` with component `T`.
    (P : Distribution.ProbDist Ω) (S : Ω → TypedSystem (A k)) (T : TypedSystem (A k))
    (h : TypedSystem.sample P S = T) :
    TypedConverter.comp context (TypedConverter.parallelAllContext R k) •
        TypedSystem.sample P S = context • (∥ j, Function.update R k T j) := by
  cc_normalize
  rw [h]

/-- Bound both common attachments before distributing the outer family converters. -/
example
    -- `K` tags inside interfaces `A j` and outside interfaces `B j`.
    {K : Type} [Fintype K] [DecidableEq K] {A B : K → Interface}
    -- `R j` fixes components outside `k`; `α j` is each component's common converter.
    (R : ∀ j, TypedSystem (A j)) (k : K) (α : ∀ j, TypedConverter (B j) (A j))
    -- `S`, `T` are the only differing inside component.
    (S T : TypedSystem (A k)) :
    Δ (∥ j, α j • Function.update R k S j) (∥ j, α j • Function.update R k T j) ≤ Δ S T := by
  have hcontext : Δ (TypedConverter.parallelAllContext R k • S)
      (TypedConverter.parallelAllContext R k • T) ≤ Δ S T := by cc_nonexpand
  have houter : Δ ((⨂ₘ j, α j) • (TypedConverter.parallelAllContext R k • S))
      ((⨂ₘ j, α j) • (TypedConverter.parallelAllContext R k • T)) ≤ Δ S T :=
    (Interface.distance_smul_le (⨂ₘ j, α j) _ _).trans hcontext
  cc_normalize at houter
  guard_hyp houter : Δ (∥ j, α j • Function.update R k S j)
    (∥ j, α j • Function.update R k T j) ≤ Δ S T
  exact houter

/-- The normalized shared-bit family still differs from independent per-component draws. -/
example :
    (sample b ←$ 𝒰[Bool];
      TypedConverter.parallelAllContext (fun _k : Bool => fixedBit b) false • fixedBit b) ≠
      independentBit := by
  intro he
  cc_normalize at he
  guard_hyp he :
    (sample b ←$ 𝒰[Bool]; ∥ j, Function.update (fun _k : Bool => fixedBit b) false (fixedBit b) j) =
      independentBit
  -- Restoring the selected bit makes every coordinate use the same sampled bit.
  simp only [Function.update_eq_self] at he
  -- The resulting family is the shared-bit fixture with its known transcript mass.
  change sharedBit = independentBit at he
  -- Mixed replies have mass zero with one shared bit and one quarter with independent bits.
  have hm := congrArg (fun R : TypedSystem (⨂ _k : Bool, bitInterface) => R.1 mixedReplies) he
  rw [sharedBit_mixedReplies_eq_zero, independentBit_mixedReplies_eq_quarter] at hm
  norm_num at hm

/-- The explicit swap remains visible until the caller supplies its ordered wiring equation. -/
example
    -- `context` attaches to the ordered `A`, `B` pair and exposes `C`; `R`, `S` occupy the pair.
    {A B C : Interface} (context : TypedConverter C (A.tensor B))
    (R : TypedSystem A) (S : TypedSystem B) :
    context • ((Interface.swap A B).hom • TypedSystem.parallel S R) =
      context • TypedSystem.parallel R S := by
  cc_normalize
  guard_target = context • ((Interface.swap A B).hom • TypedSystem.parallel S R) =
    context • TypedSystem.parallel R S
  rw [Interface.parallel_swap]

/-- Normalization leaves an unsupported exchange of arbitrary components unresolved. -/
example
    -- `R`, `S` have the same interface `A`; the exchange requires its own supplied fact `h`.
    {A : Interface} (R S : TypedSystem A)
    (h : TypedSystem.parallel R S = TypedSystem.parallel S R) :
    TypedSystem.parallel R S = TypedSystem.parallel S R := by
  fail_if_success solve | cc_normalize
  exact h

-- Diagnostic: the named context reduces by its exact attachment equation.
/--
trace: [Meta.Tactic.simp.rewrite] TypedConverter.parallelAllContext_smul:1000:
      TypedConverter.parallelAllContext R k • S
    ==>
      ∥ (j : K), Function.update R k S j
[Meta.Tactic.simp.rewrite] eq_self:1000:
      (∥ (j : K), Function.update R k S j) = ∥ (j : K), Function.update R k S j
    ==>
      True
-/
#guard_msgs (whitespace := lax) in
example
    -- `K` tags component interfaces `A k`; `R j` fixes the components other than `k`.
    {K : Type} [Fintype K] [DecidableEq K] {A : K → Interface}
    -- `S` replaces the selected component `k` through the named context.
    (R : ∀ k, TypedSystem (A k)) (k : K) (S : TypedSystem (A k)) :
    TypedConverter.parallelAllContext R k • S = ∥ j, Function.update R k S j := by
  cc_normalize?

#print axioms Commons.encryptThenMAC.system_eq
#print axioms SystemAlgebra.TypedConverter.parallelAllContext_smul

end SystemAlgebra.Tests.NamedAssemblyNormalization
