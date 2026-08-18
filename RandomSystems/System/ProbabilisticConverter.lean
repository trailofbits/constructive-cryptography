/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import RandomSystems.System.MetricFullyDefined

/-!
# Probabilistic converters (CR18 Definition 3.17)

CR18 **Definition 3.17** (printed p. 64): "A *probabilistic discrete converter*
(a **PDC** for short) (for given alphabets) is a random variable over a set of
DDC (for the same alphabets)."  And immediately after: "The composition of a
probabilistic converter with a probabilistic system is a probabilistic system
and is defined naturally via the function `(α, s) ↦ αs`, where the arguments
and hence also the function value are random variables."

Both halves are already on this carrier and neither is re-defined here.

* The **object** is a `PDS` at the engine alphabet — a distribution over the
  deterministic converter programs `System.DDS (Uni ⊕ Option Uni) (Uni ⊕ Uni)`
  that `System.attachEngineFully` runs.  `PDC` names it; the type is the one
  the landed generator already takes.
* The **composition** `(α, s) ↦ αs` lifted to laws is
  `RandomSystems.connectPhi` (`ConnectPhi.lean`): the independent product of
  the two laws pushed along the deterministic interpreter.  `attachLawAt` is
  that same lift at MauRen16 §3.3's interface index `i`, over the repaired
  primitive `System.attachEngineFully` instead of the refuted `System.connect`
  composite.

What is new here is the **metric** half, which CR18 does not state: the
interface-indexed probabilistic attachment is non-expanding whenever every
program in the converter's support is (Ruling R4's `Adv⊥`).  The argument is
not new either — it is `parRight_mem_nonexpandingConverters`'s
(`Absorb.lean`), which reduces a fixed *law* partner to its deterministic
support through `Distribution.prod_eq_sum_right` and averages the
per-atom bounds with `mem_nonexpandingConverters_of_sum`.  The only forced
delta is the slot: the fixed factor sits on the *left* of the product here, so
the decomposition is reached through `Distribution.fTransform_swap_prod`.

`converterMonoidAtProb` is a **new** submonoid with its own non-expansion
instance.  `converterMonoidAt` is untouched — it carries the metric-facing
`IsNonexpandingSMul` instance and every leg-(c)/(d) receipt, and its generator
set is pinned by `scripts/ledgerAudit.sh` check 5 — and the relation between
the two is the containment `converterMonoidAt_le_converterMonoidAtProb`: a
deterministic converter is the point-mass case (`PDS.ofDDS`).

Converter equivalence (CR18 §3.6, "equivalence of converters is defined"; used
at eq. (6.1)) is equality of the induced endomorphism of `Φ`, at every
interface.  Nothing is quotiented: the relation is stated and its basic
calculus proved, in the shape `PDS.equivalent` (`ClassDistance.lean`) already
uses for systems.
-/

namespace RandomSystems

open Probability (Distribution)
open scoped ENNReal

universe u

noncomputable section

/-! ## The object -/

/-- **CR18 Definition 3.17** (printed p. 64): a *probabilistic discrete
converter* is a random variable over deterministic converters — here a law over
the engine programs `System.attachEngineFully` runs, at the alphabet the
repaired primitive fixes (`Uni ⊕ Option Uni` in, `Uni ⊕ Uni` out: a converter
reads outer queries and resource answers, refusals included by Ruling R2, and
either answers or requests).

An abbreviation, not a structure: a PDC *is* a PDS at that alphabet, which is
what makes the whole `Distribution` calculus — support, weight, `NonNeg`,
mixtures — available to it with nothing to transport. -/
abbrev PDC : Type (u + 1) :=
  PDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})

/-! ## Definition 3.17's composition, at an interface -/

/-- **CR18 Definition 3.17's `(α, s) ↦ αs`, at MauRen16 §3.3's interface `i`**:
the converter and the resource are sampled independently and the deterministic
attachment is run on the pair.

This is `RandomSystems.connectPhi`'s shape — the composition CR18 defines is
already in the tree and is not re-defined — over the repaired primitive
`System.attachEngineFully i`, whose whole-face case (`attachAt_univ`) is the
one CR18 writes.  The deterministic generator `attachAt i E` is the point-mass
case (`attachLawAt_ofDDS`). -/
def attachLawAt (i : Set Uni.{u}) (EL : PDC.{u}) : Function.End Phi.{u} :=
  fun R =>
    Distribution.fTransform
      (fun p : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u}) ×
          System.DDS Uni.{u} Uni.{u} =>
        System.attachEngineFully i p.1 p.2)
      (Distribution.prod EL R)

/-- **Definition 3.17's composition decomposed over the converter's support**:
sampling the converter first and hardwiring it turns the probabilistic
attachment into a finite mixture of the deterministic ones, weighted by the
converter's own masses.

`Distribution.prod_eq_sum_right` decomposes a product over its *right* factor;
the converter is the left one, so the two are exchanged first
(`Distribution.fTransform_swap_prod`).  That is the whole delta from
`parRight_mem_nonexpandingConverters`'s decomposition step, which this lemma
otherwise repeats verbatim. -/
theorem attachLawAt_apply_eq_sum (i : Set Uni.{u}) (EL : PDC.{u}) (L : Phi.{u}) :
    attachLawAt i EL L = ∑ E ∈ EL.support, EL E • ofPhi (attachAt i E L) := by
  show Distribution.fTransform
      (fun p : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u}) ×
          System.DDS Uni.{u} Uni.{u} =>
        System.attachEngineFully i p.1 p.2)
      (Distribution.prod EL L) = _
  rw [← Distribution.fTransform_swap_prod L EL,
    Distribution.fTransform_fTransform,
    Distribution.prod_eq_sum_right L EL, Distribution.fTransform_sum]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [Distribution.fTransform_smul, Distribution.fTransform_fTransform]
  rfl

/-- The point-mass converter is the deterministic generator: CR18's Definition
3.17 has Definition 3.13's `αⁱs` as its degenerate case. -/
@[simp] theorem attachLawAt_ofDDS (i : Set Uni.{u})
    (E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) :
    attachLawAt i (PDS.ofDDS E) = attachAt i E := by
  funext L
  rw [attachLawAt_apply_eq_sum]
  show ∑ F ∈ (Finsupp.single E (1 : ℝ)).support,
    (Finsupp.single E (1 : ℝ)) F • ofPhi (attachAt i F L) = _
  rw [Finsupp.support_single_ne_zero _ (one_ne_zero (α := ℝ)),
    Finset.sum_singleton, Finsupp.single_eq_same, one_smul]
  rfl

/-! ## The metric half: mixtures of absorbed programs are absorbed -/

/-- **The interface-indexed probabilistic attachment never helps a
distinguisher**, whenever every program in the converter's support is one of
CR18 Definition 3.8's.

The proof is `parRight_mem_nonexpandingConverters`'s, adapted: a fixed *law* in
one slot of a product is its own finite mixture of atoms
(`Distribution.prod_eq_sum_right`, reached here through
`Distribution.fTransform_swap_prod`), each atom is
`attachAt_mem_nonexpandingConverters`, and convexity of `δ` at a sub-probability
budget averages the bounds back to the same constant
(`mem_nonexpandingConverters_of_sum`).  Non-negativity and `‖EL‖ ≤ 1` are that
lemma's honest hypotheses on the signed carrier, not decoration.

The scope note at the end of `Absorb.lean` says the mixture argument was
waiting for a deterministic family; legs (c)/(d) supplied it, and this is the
statement it was waiting for. -/
theorem attachLawAt_mem_nonexpandingConverters {i : Set Uni.{u}} {EL : PDC.{u}}
    (h0 : ∀ E, 0 ≤ EL E) (h1 : EL.weight ≤ 1)
    (hE : ∀ E ∈ EL.support,
      System.InnerTotal E ∧ System.AnswersWithinUniformBudget E) :
    attachLawAt i EL ∈ nonexpandingConverters.{u} := by
  refine mem_nonexpandingConverters_of_sum EL.support (fun E => EL E)
    (fun E => attachAt i E) (attachLawAt i EL) (fun E _ => h0 E) ?_ ?_
    (attachLawAt_apply_eq_sum i EL)
  · rw [← Distribution.weight_eq_sum_of_support_subset EL (Finset.Subset.refl _)]
    exact h1
  · intro E hEmem
    obtain ⟨hIT, β, K, hβ, hK⟩ := hE E hEmem
    exact attachAt_mem_nonexpandingConverters hIT hβ hK

/-! ## The probabilistic Σ -/

/-- **The interface-indexed converter monoid, with Definition 3.17's converters**
— `converterMonoidAt` with its attachment family widened from deterministic
programs to *laws over* programs, and the three non-attachment families
(blocks, the two parallel frames at a sub-probability partner) spelled exactly
as there.

This is a **new** submonoid, not a widening: `converterMonoidAt` carries the
metric-facing `IsNonexpandingSMul` instance and every leg-(c)/(d) receipt, so
changing its generator set would silently change what those receipts mean.  The
relation between the two is `converterMonoidAt_le_converterMonoidAtProb`.

The generator conditions are the mixture argument's: the converter is a
sub-probability law and every program in its support is inner-total and
budgeted uniformly (CR18 Definition 3.8).  Programs outside the support are
unconstrained — they carry no mass, so they carry no advantage.

(The name is a coinage, flagged, in the pattern of `converterMonoidAt`; the
object it names is CR18 Definition 3.17's converter set.) -/
def converterMonoidAtProb : Submonoid (Function.End Phi.{u}) :=
  Submonoid.closure
    ({π | ∃ (i : Set Uni.{u}) (EL : PDC.{u}), (∀ E, 0 ≤ EL E) ∧ EL.weight ≤ 1 ∧
        (∀ E ∈ EL.support,
          System.InnerTotal E ∧ System.AnswersWithinUniformBudget E) ∧
          π = attachLawAt i EL} ∪
      {π | ∃ Q : Set Uni.{u}, π = block Q} ∪
      {π | ∃ (c : Set Uni.{u}) (TL : Phi.{u}), (∀ t, 0 ≤ ofPhi TL t) ∧
        (ofPhi TL).weight ≤ 1 ∧ π = fun RL => par c RL TL} ∪
      {π | ∃ (c : Set Uni.{u}) (TL : Phi.{u}), (∀ t, 0 ≤ ofPhi TL t) ∧
        (ofPhi TL).weight ≤ 1 ∧ π = fun RL => par c TL RL})

theorem attachLawAt_mem_converterMonoidAtProb (i : Set Uni.{u}) {EL : PDC.{u}}
    (h0 : ∀ E, 0 ≤ EL E) (h1 : EL.weight ≤ 1)
    (hE : ∀ E ∈ EL.support,
      System.InnerTotal E ∧ System.AnswersWithinUniformBudget E) :
    attachLawAt i EL ∈ converterMonoidAtProb.{u} :=
  Submonoid.subset_closure (Or.inl (Or.inl (Or.inl ⟨i, EL, h0, h1, hE, rfl⟩)))

theorem block_mem_converterMonoidAtProb (Q : Set Uni.{u}) :
    block Q ∈ converterMonoidAtProb.{u} :=
  Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨Q, rfl⟩)))

theorem parRight_mem_converterMonoidAtProb (c : Set Uni.{u})
    {TL : Phi.{u}} (h0 : ∀ t, 0 ≤ ofPhi TL t) (h1 : (ofPhi TL).weight ≤ 1) :
    (fun RL => par c RL TL) ∈ converterMonoidAtProb.{u} :=
  Submonoid.subset_closure (Or.inl (Or.inr ⟨c, TL, h0, h1, rfl⟩))

theorem parLeft_mem_converterMonoidAtProb (c : Set Uni.{u})
    {TL : Phi.{u}} (h0 : ∀ t, 0 ≤ ofPhi TL t) (h1 : (ofPhi TL).weight ≤ 1) :
    (fun RL => par c TL RL) ∈ converterMonoidAtProb.{u} :=
  Submonoid.subset_closure (Or.inr ⟨c, TL, h0, h1, rfl⟩)

/-- **The deterministic Σ sits inside the probabilistic one**: a deterministic
converter is Definition 3.17's degenerate random variable, the point mass
(`attachLawAt_ofDDS`), and the other three generator families are literally the
same sets.  So every statement already proved over `converterMonoidAt` is a
statement about a sub-family of this Σ, and nothing is re-derived to keep it.

This is the B2 mitigation in one line: the pinned generator set of
`converterMonoidAt` is untouched, and the containment is what relates the two. -/
theorem converterMonoidAt_le_converterMonoidAtProb :
    converterMonoidAt.{u} ≤ converterMonoidAtProb.{u} := by
  classical
  refine Submonoid.closure_le.mpr ?_
  rintro π ((((⟨i, E, hIT, hβ, rfl⟩) | ⟨Q, rfl⟩) |
    ⟨c, TL, h0, h1, rfl⟩) | ⟨c, TL, h0, h1, rfl⟩)
  · refine (attachLawAt_ofDDS i E) ▸
      attachLawAt_mem_converterMonoidAtProb i (EL := PDS.ofDDS E) ?_ ?_ ?_
    · intro F
      rw [PDS.ofDDS, Finsupp.single_apply]
      split_ifs <;> norm_num
    · rw [PDS.ofDDS, Distribution.weight_eq_finsupp_sum]
      simp
    · intro F hF
      have hFE : F = E :=
        Finset.mem_singleton.mp (Finsupp.support_single_subset hF)
      exact hFE ▸ ⟨hIT, hβ⟩
  · exact block_mem_converterMonoidAtProb Q
  · exact parRight_mem_converterMonoidAtProb c h0 h1
  · exact parLeft_mem_converterMonoidAtProb c h0 h1

/-- **The probabilistic Σ is non-expanding** — the closure step at Definition
3.17's converters.  Every generator absorbs into the environment: probabilistic
attachments by `attachLawAt_mem_nonexpandingConverters`, blocks by
`exists_absorb_blockSet`, parallel frames by `exists_absorb_par` — and
`nonexpandingConverters` is a submonoid, so the whole closure does.

The re-based counterpart of `converterMonoidAt_le_nonexpandingConverters`, and
the receipt that makes the abstract `ε`-relaxation calculus available over the
probabilistic Σ. -/
theorem converterMonoidAtProb_le_nonexpandingConverters :
    converterMonoidAtProb.{u} ≤ nonexpandingConverters.{u} := by
  refine Submonoid.closure_le.mpr ?_
  rintro π ((((⟨i, EL, h0, h1, hE, rfl⟩) | ⟨Q, rfl⟩) |
    ⟨c, TL, h0, h1, rfl⟩) | ⟨c, TL, h0, h1, rfl⟩)
  · exact attachLawAt_mem_nonexpandingConverters h0 h1 hE
  · exact block_mem_nonexpandingConverters Q
  · exact parRight_mem_nonexpandingConverters h0 h1
  · exact parLeft_mem_nonexpandingConverters h0 h1

/-- Definition 3.17's converters act non-expandingly — the typeclass the
abstract `ε`-relaxation calculus consumes (`Relaxation.epsilonRelaxation_compatible`,
`Constructs.epsilonRelaxation_trans`), at the probabilistic Σ.  Derived, no
choices: the submonoid inclusion into `nonexpandingConverters` composed with
`nonexpandingConverters_le_nonexpandingEnd`.

This instance is the reason `converterMonoidAtProb` is a separate object: the
one on `converterMonoidAt` keeps its meaning untouched. -/
instance : AbstractCryptography.IsNonexpandingSMul
    (converterMonoidAtProb.{u}) Phi.{u} :=
  ⟨fun σ => nonexpandingConverters_le_nonexpandingEnd
    (converterMonoidAtProb_le_nonexpandingConverters σ.2)⟩

/-- **MauRen16 Definition 2 over the probabilistic Σ**: applying any Definition
3.17 converter to both sides never increases the distance. -/
theorem edist_apply_le_of_mem_converterMonoidAtProb
    {σ : Function.End Phi.{u}} (hσ : σ ∈ converterMonoidAtProb.{u})
    (L M : Phi.{u}) : edist (σ L) (σ M) ≤ edist L M :=
  edist_apply_le_of_mem_nonexpandingConverters
    (converterMonoidAtProb_le_nonexpandingConverters hσ) L M

/-! ## Equivalence of converters (CR18 §3.6) -/

namespace PDC

/-- **Equivalence of converters** — CR18 §3.6's "equivalence of converters is
defined" (the relation eq. (6.1) uses), read the way this carrier reads
equivalence of systems: two converters are equivalent when they induce the same
endomorphism of `Φ`, at every interface.

Not a new notion of equivalence (Ruling R11 bars that): the induced
endomorphism is Definition 3.17's own composition `(α, s) ↦ αs`, so this is
equality of what the definition already produces.  Quantifying over the
interface is R7″'s reading of §3.3's `αⁱ`; the whole-face instance is
`i = Set.univ`. -/
def equivalent (EL FL : PDC.{u}) : Prop :=
  ∀ i : Set Uni.{u}, attachLawAt i EL = attachLawAt i FL

theorem equivalent_refl (EL : PDC.{u}) : equivalent EL EL := fun _ => rfl

theorem equivalent_symm {EL FL : PDC.{u}} (h : equivalent EL FL) :
    equivalent FL EL := fun i => (h i).symm

theorem equivalent_trans {EL FL GL : PDC.{u}} (h : equivalent EL FL)
    (h' : equivalent FL GL) : equivalent EL GL := fun i => (h i).trans (h' i)

theorem equivalent_equivalence : Equivalence (equivalent : PDC.{u} → PDC.{u} → Prop) :=
  ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

/-- Equal converters are equivalent — the direction that makes the relation
usable as a rewriting discipline. -/
theorem equivalent_of_eq {EL FL : PDC.{u}} (h : EL = FL) : equivalent EL FL :=
  h ▸ equivalent_refl EL

/-- What equivalence buys: equivalent converters produce the same law from
every resource, at every interface. -/
theorem apply_eq_of_equivalent {EL FL : PDC.{u}} (h : equivalent EL FL)
    (i : Set Uni.{u}) (L : Phi.{u}) : attachLawAt i EL L = attachLawAt i FL L :=
  congrFun (h i) L

/-- Equivalence is a congruence for the distance: equivalent converters are
interchangeable inside every `Adv⊥` statement. -/
theorem edist_attachLawAt_congr {EL FL : PDC.{u}} (h : equivalent EL FL)
    (i : Set Uni.{u}) (L M : Phi.{u}) :
    edist (attachLawAt i EL L) (attachLawAt i EL M)
      = edist (attachLawAt i FL L) (attachLawAt i FL M) := by
  rw [apply_eq_of_equivalent h i L, apply_eq_of_equivalent h i M]

/-- A deterministic converter's equivalence class is decided by its
endomorphism, through the point-mass case. -/
theorem equivalent_ofDDS_iff
    {E F : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})} :
    equivalent (PDS.ofDDS E) (PDS.ofDDS F) ↔ ∀ i : Set Uni.{u}, attachAt i E = attachAt i F := by
  constructor
  · intro h i
    have := h i
    rwa [attachLawAt_ofDDS, attachLawAt_ofDDS] at this
  · intro h i
    rw [attachLawAt_ofDDS, attachLawAt_ofDDS]
    exact h i

end PDC

end

end RandomSystems
