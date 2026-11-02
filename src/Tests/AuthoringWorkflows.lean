module

public import Commons.Definitions.PublicKeyEncryption.Keyed
public import Commons.Constructions.EncryptThenMAC
public import RandomSystems.Typed.FiniteFamilyCollect

/-!
# Three public authoring workflows

`retainedOracle_snoc` computes the cumulative mass of one more encryption exchange on the stock
PKE oracle. `PKE.system.perPort_eq_keyed` and `TypedSystem.keyed_snoc` give

  `mass (h ++ [(enc m, enc c)]) = ∑ k ∈ supp gen, gen k * L k h * ν k c`,

where `L k h` is the fixed-key mass of the previous history and `henc` supplies its next reply law.

`retainedDrawClient` retains one draw `s ∼ P` around a family independent given `s`, then
collects one reply per component on each trigger. `TypedConverter.smul_sample`, the contracts
`hR`, and `TypedConverter.collect_smul_parallelAll_source` give `collectedSharedSources_eq`:

  `retainedDrawClient order q P R = sample P (s ↦ source (piDep (μ s)) q)`.

Tuples are fresh conditional on `s`, which remains fixed for the whole interaction.

`encryptThenMACClient` attaches an outside context to the standard construction.
`encryptThenMAC_component_bound` is one conditional cipher hybrid. `encryptThenMAC.system_eq`
exposes the assembly; attachment and fixed-right parallel non-expansion give

  `Δ (ctx • EtM • (AE ∥ MAC)) (ctx • EtM • (AE' ∥ MAC)) ≤ Δ AE AE' ≤ ε`.

The guarded remaining goal is the supplied local distance bound `hlocal`.
-/

@[expose] public section

open Probability Probability.Distribution Commons
open scoped SystemAlgebra NNReal BigOperators
namespace SystemAlgebra.Tests.AuthoringWorkflows

/-- The cumulative mass of an admitted encryption extension is the key-weighted sum of the
previous-history mass times `ν keys c`. The same retained pair indexes both factors. -/
lemma retainedOracle_snoc
    -- `PK`, `SK` carry keys; `M`, `C` carry messages and ciphertexts.
    {PK SK M C : Type} [Fintype PK] [Fintype SK] [Fintype M] [Fintype C]
    [DecidableEq PK] [DecidableEq M]
    -- `scheme` is the stock PKE scheme; `q i` bounds queries separately at port `i`.
    (scheme : PublicKeyEncryption PK SK M C) (q : PKE.Port → ℕ)
    -- `h` is the previous typed transcript, possibly with publication or decryption queries.
    (h : List ((Σ i, (PKE.perPort PK M C q).X i) × (Σ i, (PKE.perPort PK M C q).Y i)))
    -- `m` is the next plaintext, `c` its candidate reply, and `ν keys` its stated reply law.
    (m : M) (c : C) (ν : PK × SK → ProbDist C)
    -- `henc` supplies that local law at every generated pair; `hd` admits the next query.
    (henc : ∀ keys ∈ scheme.gen.1.support, scheme.enc keys.1 m = ν keys)
    (hd : (PKE.perPort PK M C q).inputDomain h ⟨.enc, m⟩) :
    (PKE.system.perPort (budget := q) scheme).1 (h ++ [(⟨.enc, m⟩, ⟨.enc, c⟩)]) =
      ∑ keys ∈ scheme.gen.1.support, scheme.gen keys *
        (TypedSystem.ofMemoryless (PKE.perPort PK M C q) (PKE.system.replyLaw scheme keys)).1 h *
          ν keys c := by
  -- The correspondence retains the pair; the keyed chain rule gives the next cumulative mass.
  rw [PKE.system.perPort_eq_keyed, TypedSystem.keyed_snoc _ _ _ _ _ _ hd]
  -- Each supported summand uses exactly the supplied encryption-law contract.
  apply Finset.sum_congr rfl
  intro keys hk
  rw [PKE.system.replyLaw, henc keys hk]

/-- Retain `s ∼ P` once on a tuple-source interface with budget `q`, with components independent
given `s`. Each outside trigger collects one reply per component in `order`. -/
noncomputable def retainedDrawClient
    -- `K` tags components, and `Z k` carries component `k`'s replies.
    {K : Type} [Fintype K] [DecidableEq K] {Z : K → Type} [∀ k, Fintype (Z k)]
    -- `Ω` carries the value retained by `P`; `order` visits all `n` tags and `q` bounds triggers.
    {Ω : Type} {n : ℕ} (order : Fin n ≃ K) (q : ℕ) (P : ProbDist Ω)
    -- `R s k` is the component system conditional on the one retained shared value `s`.
    (R : Ω → ∀ k, TypedSystem (Interface.source (Z k) q)) :
    TypedSystem (Interface.source (∀ k, Z k) q) :=
  TypedConverter.collect (A := Interface.source (∀ k, Z k) q)
    (B := fun k => Interface.source (Z k) q) order
    (fun _ _ => ⟨(), ()⟩) (fun _ ys => ys)
    -- Each tuple trigger calls each component once, so its projected history fits budget `q`.
    (fun _ _ hu => Interface.queryBudget_domain_map _ le_rfl hu) •
      TypedSystem.sample P (fun s => ∥ k, R s k)

/-- Conditional source contracts give fresh independent tuples conditional on the same retained
value. The conclusion preserves `P` outside the tuple source for the whole interaction. -/
lemma collectedSharedSources_eq
    -- `K`, `Z k` name component tags and replies; `Ω` carries the shared retained value.
    {K : Type} [Fintype K] [DecidableEq K] {Z : K → Type} [∀ k, Fintype (Z k)]
    -- `order` visits all `n` tags; `q` is the trigger budget and `P` the retained law.
    {Ω : Type} {n : ℕ} (order : Fin n ≃ K) (q : ℕ) (P : ProbDist Ω)
    -- `R s k` supplies the concrete conditional component at every `s : Ω`.
    (R : Ω → ∀ k, TypedSystem (Interface.source (Z k) q))
    -- `μ s k` is the fresh reply law promised for `R s k` by `hR`, for every retained value.
    (μ : Ω → ∀ k, ProbDist (Z k))
    (hR : ∀ s k, R s k = TypedSystem.source (μ s k) q) :
    retainedDrawClient order q P R =
      TypedSystem.sample P (fun s => TypedSystem.source (ProbDist.piDep (μ s)) q) := by
  -- Attachment enters the shared sample once, retaining its value across all components.
  rw [retainedDrawClient, TypedConverter.smul_sample]
  congr 1
  funext s
  -- At fixed `s`, the component contracts expose the independent stock sources.
  simp_rw [hR]
  -- Collecting those independent sources gives the fresh dependent-tuple source.
  exact TypedConverter.collect_smul_parallelAll_source order q (μ s)

/-- Expose interface `O` by attaching `context` to the standard EtM construction on budget `q`.
The encryption and MAC components sit on separate sides of `∥`, retaining independent keys. -/
noncomputable def encryptThenMACClient
    -- `K`, `L` carry keys; `M`, `C`, `T` carry messages, ciphertexts and tags.
    {K L M C T : Type} [Fintype K] [Fintype L] [Fintype M] [Fintype C] [Fintype T]
    [DecidableEq K] [DecidableEq L] [DecidableEq M] [DecidableEq C]
    -- `scheme`, `mac` provide the construction with `q` calls; `context` exposes outside `O`.
    {O : Interface} (scheme : SymmetricEncryption K M C) (mac : MAC L C T) (q : ℕ)
    (context : TypedConverter O (AE M (C × T) q)) : TypedSystem O :=
  context • encryptThenMAC.system scheme mac q

/-- One conditional cipher hybrid transports `hlocal` through the common MAC and both attachments.
The component bound is an explicit premise, to be supplied by a separate local argument. -/
lemma encryptThenMAC_component_bound
    -- `K`, `L` carry keys; `M`, `C`, `T` carry messages, ciphertexts and tags.
    {K L M C T : Type} [Fintype K] [Fintype L] [Fintype M] [Fintype C] [Fintype T]
    [DecidableEq K] [DecidableEq L] [DecidableEq M] [DecidableEq C]
    -- `scheme`, `mac` give both assemblies with `q` calls; `context` exposes outside `O`.
    {O : Interface} (scheme : SymmetricEncryption K M C) (mac : MAC L C T) (q : ℕ)
    (context : TypedConverter O (AE M (C × T) q))
    -- `cipher'` is the replacement on the declared `2 * q` allowance; `ε` is its scalar error.
    -- The converter uses at most two inside calls per invocation, giving this uniform allowance.
    (cipher' : TypedSystem (AE M C (2 * q))) (ε : ℝ≥0)
    -- `hlocal` is the supplied component distance bound, with its declared query allowance.
    (hlocal : Δ (AE.system scheme) cipher' ≤ ε) :
    Δ (encryptThenMACClient scheme mac q context)
      (context • (encryptThenMAC M C T • (cipher' ∥ MAC.system mac))) ≤ ε := by
  -- Expose only the declared assemblies, keeping the cipher and MAC as named components.
  rw [encryptThenMACClient]
  cc_normalize
  refine le_trans (b := Δ (AE.system scheme) cipher') ?_ ?_
  · -- Absorb the outside context, then the EtM converter, then the common MAC component.
    calc
      _ ≤ Δ (encryptThenMAC M C T • TypedSystem.parallel (AE.system scheme) (MAC.system mac))
          (encryptThenMAC M C T • TypedSystem.parallel cipher' (MAC.system mac)) := by cc_nonexpand
      _ ≤ Δ (TypedSystem.parallel (AE.system scheme) (MAC.system mac))
          (TypedSystem.parallel cipher' (MAC.system mac)) := by cc_nonexpand
      _ ≤ Δ (AE.system scheme) cipher' := by cc_nonexpand
  · guard_target = Δ (AE.system scheme) cipher' ≤ (ε : ENNReal)
    exact hlocal

#print axioms SystemAlgebra.Tests.AuthoringWorkflows.retainedOracle_snoc
#print axioms SystemAlgebra.Tests.AuthoringWorkflows.collectedSharedSources_eq
#print axioms SystemAlgebra.Tests.AuthoringWorkflows.encryptThenMAC_component_bound

end SystemAlgebra.Tests.AuthoringWorkflows
