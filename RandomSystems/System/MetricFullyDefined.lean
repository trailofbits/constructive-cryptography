/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.AttachEngineFully
import AbstractCryptography.Metric.Epsilon

/-!
# Φ as a pseudo-emetric space, and the MauRen16 receipts

Ruling R4 fixes the statement-facing distance of the fully defined carrier as
`Adv⊥` (`PDS.advFullyDefined`).  Ruling B2 records that `Adv⊥` is symmetric
exactly at equal weight — a property of Lanzenberger Definition 2.4 on the
signed carrier, not a gap — so the metric installed here is its symmetrization

  `edist L M := Adv⊥(L, M) ⊔ Adv⊥(M, L)`,

which agrees with `Adv⊥` on every equal-weight pair, in particular on any two
probability laws (`edist_eq_advFullyDefined_of_weight_eq`).  Reflexivity,
symmetry and the triangle inequality are then the B1/B2 laws read under `⊔`.

With the instance in place the abstract layer applies verbatim:

* **MauRen16 Definition 2** — `nonexpandingConverters` is a
  submonoid of `AbstractCryptography.nonexpandingEnd Phi`, so every
  converter proved absorbing in `Absorb.lean` acts as a `1`-Lipschitz map
  (`edist_apply_le_of_mem_nonexpandingConverters`).  This is the *hypothesis*
  MauRen16 Lemma 2 consumes, not Lemma 2 itself: Lemma 2 is the ε-ball
  transfer `ℛ —π→ 𝒮 ⟹ ℛᵋ —π→ 𝒮ᵋ`.
* **JM20 Corollary 1.1.1 (MauRen16 Lemma 1 composed with Lemma 2)** — errors add along a
  chain of constructions, `AbstractCryptography.Constructs.epsilonRelaxation_trans`,
  which consumes exactly `IsNonexpandingSMul`; the instance for the
  `nonexpandingConverters` action is registered here and
  `constructs_epsilonRelaxation_trans_phi` is that theorem on Φ.

**Scope.**  The nonexpanding family is blocking, the parallel frames (B4/B5,
B6) and — since B4-RESUME — the *migrated* attachment `attachFully`, whose
converter observes the completion instead of dying on its refusals.  The
receipts are therefore stated twice: once at `nonexpandingConverters`, which is
the specification, and once at `converterMonoidFullyBudgeted`, which is the
generated Σ the statement layer names.

**Scope, re-based (DRIFT-REPAIR leg c).**  The attachment the receipts range
over is now the *interface-indexed* `attachAt i E` — MauRen16 §3.3's `αⁱ`, the
Φ-level pushforward of `System.attachEngineFully` — and the Σ they are stated
at is `converterMonoidAt`, which it generates together with the same blocks and
parallel frames.  The whole-face family is not removed: `attachFully` and both
`Fully` monoids keep their statements and their receipts, and
`converterMonoidFullyBudgeted_le_converterMonoidAt` places the old Σ inside the
new one through `attachAt_univ`.  The re-based receipts are the three at the
end of this file, plus the §4.2 remark; the whole-face ones directly above them
are superseded, not deleted.

Attachment through the old `connect` is *not* in the family and never will be:
the B4 witness lives inside `converterMonoid`, and `attach`/`connectPhi` carry
no nonexpansion claim.  Nor is A6's `converterMonoidFully`, whose attachment
family is budgeted only history by history (LEDGER, B4-RESUME delta), nor its
re-based counterpart `converterMonoidAtWeakBudget`.

**Parallel composition — no longer deferred, and where it lives.**  `Par` is a
single binary operation while `RandomSystems.par` is indexed by a splitting
`c : Set Uni`; the addressing ruling that closed that gap elects the splitting
from the left argument's own face, and `ParFace.lean` registers `instParPhi`
together with the canonicity theorem that makes the election carry no
information on separated faces.  `instParConverterMonoidAt` does the same for
MauRen11 §6.2's `α∣β` at `Σ` (multiplication, with the fn.-23 ruling recorded at
the instance), and `ParFrame.lean` proves the framing law the two `Par`s have to
satisfy together.

What stays unobtainable is the *unconditional* form of the two abstract classes
`SMulParClass` and `IsNonexpandingPar`, and with them
`Constructs.epsilonRelaxation_par` as an instance-driven theorem: this carrier is
signed, of arbitrary weight, and `parF` is parallel composition only on
separated faces.  Both are replaced by conditional theorems with the hypotheses
named — `RandomSystems.smul_parF` and `RandomSystems.edist_parF_parF_le` — and
the parallel half of JM20 Corollary 1 is assembled from them as
`RandomSystems.constructs_epsilonRelaxation_parF`.  Its metric input is the pair
proved here: `parRight_mem_nonexpandingConverters` /
`parLeft_mem_nonexpandingConverters`.
-/

namespace RandomSystems

open scoped ENNReal

universe u

noncomputable section

/-! ## The pseudo-emetric -/

/-- **Ruling R4's distance, symmetrized.**  `Adv⊥` is one-sided on the signed
carrier and symmetric exactly at equal weight (B2), so the pseudo-emetric is
its `⊔`-symmetrization: no information is added — on the intended objects the
two suprema coincide (`edist_eq_advFullyDefined_of_weight_eq`) — and none is
lost, since each summand is bounded by the symmetrized distance.

Reflexivity is `advFullyDefined_self`, symmetry is commutativity of `⊔`, and
the triangle inequality is `advFullyDefined_triangle` applied once in each
orientation. -/
instance : PseudoEMetricSpace Phi.{u} where
  edist L M := PDS.advFullyDefined L M ⊔ PDS.advFullyDefined M L
  edist_self L := by simp
  edist_comm L M := sup_comm _ _
  edist_triangle L M N := by
    refine sup_le ((PDS.advFullyDefined_triangle L M N).trans
      (add_le_add le_sup_left le_sup_left)) ?_
    refine (PDS.advFullyDefined_triangle N M L).trans ?_
    rw [add_comm]
    exact add_le_add le_sup_right le_sup_right

@[simp]
theorem edist_def (L M : Phi.{u}) :
    edist L M = PDS.advFullyDefined L M ⊔ PDS.advFullyDefined M L :=
  rfl

/-- On equal-weight laws — in particular on any two probability laws — the
symmetrization is invisible: the installed metric *is* Ruling R4's `Adv⊥`.
The hypothesis is spelled through `ofPhi` because `Phi` is a `def`, so the
`Finsupp` structure that carries `weight` is not found by instance search. -/
theorem edist_eq_advFullyDefined_of_weight_eq {L M : Phi.{u}}
    (h : (ofPhi L).weight = (ofPhi M).weight) :
    edist L M = PDS.advFullyDefined L M := by
  rw [edist_def, PDS.advFullyDefined_comm_of_weight_eq M L h.symm, sup_idem]

/-! ## MauRen16 Definition 2 -/

/-- **MauRen16 Definition 2 on Φ**: every converter that an environment can
absorb is a `1`-Lipschitz map for the installed metric.  The absorption
statements are one-sided in each argument order, and the `⊔` needs exactly
those two. -/
theorem nonexpandingConverters_le_nonexpandingEnd :
    nonexpandingConverters.{u} ≤ AbstractCryptography.nonexpandingEnd Phi.{u} := by
  intro σ hσ
  refine LipschitzWith.of_edist_le fun L M => ?_
  rw [edist_def, edist_def]
  exact sup_le_sup (hσ L M) (hσ M L)

/-- **MauRen16 Definition 2, concrete receipt**: applying an absorbed converter
to both sides never increases the distance.  (Definition 2 is this inequality;
Lemma 2 is the ε-ball transfer that consumes it.) -/
theorem edist_apply_le_of_mem_nonexpandingConverters
    {σ : Function.End Phi.{u}} (hσ : σ ∈ nonexpandingConverters.{u})
    (L M : Phi.{u}) : edist (σ L) (σ M) ≤ edist L M := by
  rw [edist_def, edist_def]
  exact sup_le_sup (hσ L M) (hσ M L)

/-- The absorbed converters act non-expandingly — the typeclass the abstract
`ε`-relaxation calculus consumes (`Relaxation.epsilonRelaxation_compatible`,
`Constructs.epsilonRelaxation_trans`).  It is derived, not chosen: the
`Function.End Phi` action restricted to the submonoid, at
`nonexpandingConverters_le_nonexpandingEnd`. -/
instance : AbstractCryptography.IsNonexpandingSMul
    (nonexpandingConverters.{u}) Phi.{u} :=
  ⟨fun σ => nonexpandingConverters_le_nonexpandingEnd σ.2⟩

/-! ## JM20 Corollary 1.1.1 — errors add along a chain -/

/-- **The composition receipt** (JM20 Corollary 1.1, item 1; MauRen16 Lemma 1
composed with Lemma 2), on Φ at absorbed converters: if `σ` brings `L` within `ε₁` of `M` and
`τ` brings `M` within `ε₂` of `N`, then the composite converter brings `L`
within `ε₁ + ε₂` of `N`.

This is `AbstractCryptography.Constructs.epsilonRelaxation_trans` instantiated at
`Sigma := nonexpandingConverters`, `Φ := Phi` — the abstract statement
consumes `Monoid`, `MulAction`, `PseudoEMetricSpace` and `IsNonexpandingSMul`,
all four of which are now instances — and read back through
`constructs_singleton_epsilonRelaxation_iff`, which is the dictionary between the
specification form `{L} —[π]→ ({M})^ε` and the metric form `edist (π • L) M ≤ ε`.
(The name is a coinage; the abstract statement it instantiates is not.) -/
theorem constructs_epsilonRelaxation_trans_phi
    {σ τ : nonexpandingConverters.{u}} {L M N : Phi.{u}} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : edist (σ • L) M ≤ ε₁) (h₂ : edist (τ • M) N ≤ ε₂) :
    edist ((τ * σ) • L) N ≤ ε₁ + ε₂ :=
  AbstractCryptography.constructs_singleton_epsilonRelaxation_iff.mp
    (AbstractCryptography.Constructs.epsilonRelaxation_trans
      (AbstractCryptography.constructs_singleton_epsilonRelaxation_iff.mpr h₁)
      (AbstractCryptography.constructs_singleton_epsilonRelaxation_iff.mpr h₂))

/-! ## S4 finish line — the receipts over the migrated converter monoid

B4-RESUME closes the pipeline: the generated Σ of the fully defined carrier —
migrated attachments at CR18 Definition 3.8's uniform request bound, blocks and
parallel frames — is inside `nonexpandingConverters`, so MauRen16's Definition 2
and the JM20 Corollary 1.1 composition receipt hold over it verbatim.  Everything
below is derived: no instance is chosen, and no statement is re-proved.

The submonoid is `converterMonoidFullyBudgeted` rather than A6's
`converterMonoidFully`; the delta is CR18's uniform bound and is recorded at
both definitions and in `LEDGER.md`. -/

/-- The migrated converters act non-expandingly — the typeclass the abstract
`ε`-relaxation calculus consumes, now at the generated Σ.  Derived, no choices:
the submonoid inclusion into `nonexpandingConverters` composed with the B7
instance's content. -/
instance : AbstractCryptography.IsNonexpandingSMul
    (converterMonoidFullyBudgeted.{u}) Phi.{u} :=
  ⟨fun σ => nonexpandingConverters_le_nonexpandingEnd
    (converterMonoidFullyBudgeted_le_nonexpandingConverters σ.2)⟩

/-- **MauRen16 Definition 2 over the migrated converter monoid**: applying any
converter of Σ to both sides never increases the distance.  Blocks, parallel
frames *and* migrated attachments — which is the statement B4 could not make
for `attach` and B5 could not make for `converterMonoid`. -/
theorem edist_apply_le_of_mem_converterMonoidFullyBudgeted
    {σ : Function.End Phi.{u}} (hσ : σ ∈ converterMonoidFullyBudgeted.{u})
    (L M : Phi.{u}) : edist (σ L) (σ M) ≤ edist L M :=
  edist_apply_le_of_mem_nonexpandingConverters
    (converterMonoidFullyBudgeted_le_nonexpandingConverters hσ) L M

/-- **MauRen16 §4.2's remark over the migrated converter monoid**: "`πRβ ≈ᵋ
Sσβ` due to the non-expanding property of the pseudo-metric".  Equation (3)'s
closeness survives a further converter attached to both sides, so a
simulator-based statement is not destroyed by what the environment does next.

This is `AbstractCryptography.edist_mul_smul_le_of_edist_le` at
`Sigma := converterMonoidFullyBudgeted`, `Φ := Phi`; the abstract statement
consumes `IsNonexpandingSMul`, which is the instance registered above.  Right
attachment is multiplication in the one monoid — on this carrier an interface
is a tag inside the acted-on element, not a side of the juxtaposition. -/
theorem edist_mul_smul_le_of_edist_le_fully
    {π σ β : converterMonoidFullyBudgeted.{u}} {L M : Phi.{u}} {ε : ℝ≥0∞}
    (h : edist (π • L) (σ • M) ≤ ε) :
    edist ((β * π) • L) ((β * σ) • M) ≤ ε :=
  AbstractCryptography.edist_mul_smul_le_of_edist_le h β

/-- **The composition receipt over the migrated converter monoid** (JM20
Corollary 1.1 item 1; MauRen16 Lemma 1 composed with Lemma 2): errors add along a chain of
constructions, with the converters taken from the generated Σ of the fully
defined carrier. -/
theorem constructs_epsilonRelaxation_trans_fully
    {σ τ : converterMonoidFullyBudgeted.{u}} {L M N : Phi.{u}} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : edist (σ • L) M ≤ ε₁) (h₂ : edist (τ • M) N ≤ ε₂) :
    edist ((τ * σ) • L) N ≤ ε₁ + ε₂ :=
  AbstractCryptography.constructs_singleton_epsilonRelaxation_iff.mp
    (AbstractCryptography.Constructs.epsilonRelaxation_trans
      (AbstractCryptography.constructs_singleton_epsilonRelaxation_iff.mpr h₁)
      (AbstractCryptography.constructs_singleton_epsilonRelaxation_iff.mpr h₂))

/-! ## S4 finish line, re-based — the receipts over the interface-indexed Σ

DRIFT-REPAIR leg (c).  The three receipts above range over the whole-face
attachment, which is not MauRen16 §3.3's `αⁱ` but its `i = Set.univ` case; the
repaired primitive `System.attachEngineFully` carries the interface, and
`converterMonoidAt` is the Σ its Φ-level pushforward generates.  The receipts
re-state over it with nothing new proved: `converterMonoidAt` is inside
`nonexpandingConverters` (`converterMonoidAt_le_nonexpandingConverters`, whose
attachment generator is `System.exists_absorb_attachEngineFully`), and
everything below is that inclusion composed with the specification-level
statements — no instance is chosen, no statement is re-proved.

The whole-face receipts are **superseded, not deleted**.  They stay valid, and
`converterMonoidFullyBudgeted_le_converterMonoidAt` says what they are: the
same statements at a sub-family of this Σ.

The submonoid is `converterMonoidAt` rather than `converterMonoidAtWeakBudget`
for the same reason as before the repair — CR18 Definition 3.8's request bound
has to be uniform over converter histories, and absorption is what needs it. -/

/-- The interface-indexed converters act non-expandingly — the typeclass the
abstract `ε`-relaxation calculus consumes, at the re-based Σ.  Derived, no
choices: the submonoid inclusion into `nonexpandingConverters` composed with the
B7 instance's content. -/
instance : AbstractCryptography.IsNonexpandingSMul
    (converterMonoidAt.{u}) Phi.{u} :=
  ⟨fun σ => nonexpandingConverters_le_nonexpandingEnd
    (converterMonoidAt_le_nonexpandingConverters σ.2)⟩

/-- **MauRen16 Definition 2 over the interface-indexed converter monoid**:
applying any converter of Σ to both sides never increases the distance.  Blocks,
parallel frames *and* attachments at an interface — which is the statement the
whole-face receipt could only make at `i = Set.univ`. -/
theorem edist_apply_le_of_mem_converterMonoidAt
    {σ : Function.End Phi.{u}} (hσ : σ ∈ converterMonoidAt.{u})
    (L M : Phi.{u}) : edist (σ L) (σ M) ≤ edist L M :=
  edist_apply_le_of_mem_nonexpandingConverters
    (converterMonoidAt_le_nonexpandingConverters hσ) L M

/-- **MauRen16 §4.2's remark over the interface-indexed converter monoid**:
"`πRβ ≈ᵋ Sσβ` due to the non-expanding property of the pseudo-metric".
Equation (3)'s closeness survives a further converter attached to both sides, so
a simulator-based statement is not destroyed by what the environment does next.

This is `AbstractCryptography.edist_mul_smul_le_of_edist_le` at
`Sigma := converterMonoidAt`, `Φ := Phi`; the abstract statement consumes
`IsNonexpandingSMul`, which is the instance registered above.  Right attachment
is multiplication in the one monoid — on this carrier an interface is a tag
inside the acted-on element, not a side of the juxtaposition, and `attachAt`'s
index is exactly that tag. -/
theorem edist_mul_smul_le_of_edist_le_at
    {π σ β : converterMonoidAt.{u}} {L M : Phi.{u}} {ε : ℝ≥0∞}
    (h : edist (π • L) (σ • M) ≤ ε) :
    edist ((β * π) • L) ((β * σ) • M) ≤ ε :=
  AbstractCryptography.edist_mul_smul_le_of_edist_le h β

/-- **The composition receipt over the interface-indexed converter monoid**
(JM20 Corollary 1.1 item 1; MauRen16 Lemma 1 composed with Lemma 2): errors add
along a chain of constructions, with the converters taken from the re-based Σ of
the fully defined carrier. -/
theorem constructs_epsilonRelaxation_trans_at
    {σ τ : converterMonoidAt.{u}} {L M N : Phi.{u}} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : edist (σ • L) M ≤ ε₁) (h₂ : edist (τ • M) N ≤ ε₂) :
    edist ((τ * σ) • L) N ≤ ε₁ + ε₂ :=
  AbstractCryptography.constructs_singleton_epsilonRelaxation_iff.mp
    (AbstractCryptography.Constructs.epsilonRelaxation_trans
      (AbstractCryptography.constructs_singleton_epsilonRelaxation_iff.mpr h₁)
      (AbstractCryptography.constructs_singleton_epsilonRelaxation_iff.mpr h₂))

end

end RandomSystems
