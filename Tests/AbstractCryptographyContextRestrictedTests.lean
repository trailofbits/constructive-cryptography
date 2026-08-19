/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import ConstructiveCryptography.Generalizations.ContextRestricted

/-!
# Permanent regression gate for context-restricted constructions

**MR11-DEFERRED (provenance fence, 2026-08-17): MauRen11 constructs
quarantined pending the MR11 reconciliation task.  No MR16-track file may
import this module — enforced by `scripts/ledgerAudit.sh`.  See `LEDGER.md`
PROVENANCE FENCE.**

Every statement here is a *usability* receipt, not a mathematical one: each
`example` asserts that a §4.2 phrase **elaborates and closes** with the
arguments a reader of Jost's Chapter 4 would naturally write, and with none of
the plumbing the module exists to hide.  A regression shows up as a build
failure here rather than as silent drift in `ConstructiveCryptography.Generalizations.ContextRestricted`.

Four things are pinned.

* **The collapse (Proposition 4.2.7).** `𝒞̄_id = Σ × Θ`, the ordinary notion is
  the `𝒞_id` case of the restricted one, and a restricted construction is a
  family of ordinary ones with the context folded in.
* **The closure (Definition 4.2.4, Proposition 4.2.5).** Its displayed
  one-step shape is admissible, `𝒞 ⊆ 𝒞̄` is a constructor, and the notion is
  invariant under it.
* **Composition (Theorem 4.2.6).** Both rules fire on the smallest non-trivial
  context sets, with the side condition discharged by `subset_closure` alone.
* **Corollary 2.2.16 as a special case.** §4.2.3's closing remark: "Using
  `𝒞̄_id = Σ × Θ`, it is also easy to see that the composition theorem
  Corollary 2.2.16 for regular (asymptotic) simulation-based constructions is
  just a special case of Theorem 4.2.6."

The pins are stated over an abstract carrier on purpose: §4.2 is
carrier-agnostic, and a concrete model would test the model rather than the
chapter.
-/

namespace AbstractCryptographyContextRestrictedTests

open AbstractCryptography
open scoped AbstractCryptography
open scoped ENNReal
open Pointwise

variable {Sigma Φ : Type*} [Monoid Sigma] [MulAction Sigma Φ] [Par Φ] [Par Sigma]
  [SMulParClass Sigma Φ] [IsAssociativePar Φ]
  {D : DistinguisherClass Sigma Φ} [D.IsClosedUnderPar]
  {H : Submonoid Sigma} {E : BudgetClass D}

/-! ### Definition 4.2.2 elaborates in paper shape -/

/-- The real and ideal systems of Figure 4.3 are named, not spelled out. -/
example (c : Context Sigma Φ) (π σ : Sigma) (R S : Set Φ) : Prop :=
  c.real π R ⊆ c.ideal σ S

/-- Definition 4.2.2 takes simulator and budget *families* indexed by contexts,
exactly as `⟨σ_C⟩_{C∈𝒞}` and `⟨ε_C⟩_{C∈𝒞}` are written. -/
example (π : Sigma) (C : ContextSet Sigma Φ) (σ : Context Sigma Φ → Sigma)
    (ε : Context Sigma Φ → D.tests → ℝ≥0∞) (R S : Set Φ) : Prop :=
  ConstructsRestricted D π C σ ε R S

/-- Definition 4.2.2 refines Definition 4.2.3 with no unfolding. -/
example (π : Sigma) (C : ContextSet Sigma Φ) (σ : Context Sigma Φ → Sigma)
    (ε : Context Sigma Φ → D.tests → ℝ≥0∞) (R S : Set Φ)
    (hσ : ∀ c ∈ C, σ c ∈ H) (hε : ∀ c ∈ C, ε c ∈ E.carrier)
    (h : ConstructsRestricted D π C σ ε R S) :
    ConstructsRestrictedAsym D H E π C R S :=
  constructsRestrictedAsym_of_constructsRestricted hσ hε h

/-! ### Definition 4.2.4 and Proposition 4.2.5 -/

/-- Definition 4.2.4's displayed clause — an outer filter `h`, an extra
parallel resource `U` — is admissible in one step. -/
example (C : ContextSet Sigma Φ) (d : Context Sigma Φ) (hd : d ∈ C) (h : Sigma) (U : Φ) :
    (⟨h * (d.filter ∥ (1 : Sigma)), d.aux ∥ U⟩ : Context Sigma Φ) ∈ ContextSet.closure C :=
  ContextSet.mem_closure_paperForm hd h U

/-- "The implication `⟸` is trivial, since `𝒞 ⊆ 𝒞̄`." -/
example (C : ContextSet Sigma Φ) : C ⊆ ContextSet.closure C :=
  ContextSet.subset_closure C

/-- Proposition 4.2.5, used left to right without naming the transported
budgets. -/
example (hH : ∀ σ ∈ H, σ ∥ (1 : Sigma) ∈ H) (π : Sigma) (C : ContextSet Sigma Φ)
    (R S : Set Φ) (h : ConstructsRestrictedAsym D H E π C R S) :
    ConstructsRestrictedAsym D H E π (ContextSet.closure C) R S :=
  (constructsRestrictedAsym_closure_iff hH).mp h

/-- …and right to left. -/
example (hH : ∀ σ ∈ H, σ ∥ (1 : Sigma) ∈ H) (π : Sigma) (C : ContextSet Sigma Φ)
    (R S : Set Φ)
    (h : ConstructsRestrictedAsym D H E π (ContextSet.closure C) R S) :
    ConstructsRestrictedAsym D H E π C R S :=
  (constructsRestrictedAsym_closure_iff hH).mpr h

/-! ### Theorem 4.2.6 fires on the smallest non-trivial context sets

The side condition is discharged by `subset_closure` alone: `𝒞₁` is chosen to
be exactly the context the rule needs, which is the sharpest instance of
"the context sets have to be defined in a form that containment can be easily
verified" (§4.2.2). -/

/-- **Sequential composition**, at singleton context sets. -/
example (hcentral : ∀ (m : Sigma), ∀ σ ∈ H, Commute m σ)
    (hH : ∀ σ ∈ H, σ ∥ (1 : Sigma) ∈ H) (π₁ π₂ : Sigma) (c : Context Sigma Φ)
    (R S T : Set Φ)
    (h₁ : ConstructsRestrictedAsym D H E π₁
      ({⟨c.filter * (π₂ ∥ (1 : Sigma)), c.aux⟩} : ContextSet Sigma Φ) R S)
    (h₂ : ConstructsRestrictedAsym D H E π₂ ({c} : ContextSet Sigma Φ) S T) :
    ConstructsRestrictedAsym D H E (π₂ * π₁) ({c} : ContextSet Sigma Φ) R T := by
  refine constructsRestrictedAsym_seq hcentral hH (fun c' hc' => ?_) h₁ h₂
  have hc'' : c' = c := hc'
  subst hc''
  exact ContextSet.subset_closure _ rfl

/-- **Parallel composition**, at singleton context sets. -/
example (hH : ∀ σ ∈ H, σ ∥ (1 : Sigma) ∈ H) (π₁ : Sigma) (U : Φ) (c : Context Sigma Φ)
    (R S : Set Φ)
    (h : ConstructsRestrictedAsym D H E π₁
      ({⟨c.filter, U ∥ c.aux⟩} : ContextSet Sigma Φ) R S) :
    ConstructsRestrictedAsym D H E (π₁ ∥ (1 : Sigma)) ({c} : ContextSet Sigma Φ)
      (R ∥ ({U} : Set Φ)) (S ∥ ({U} : Set Φ)) := by
  refine constructsRestrictedAsym_par U (fun c' hc' => ?_) hH h
  have hc'' : c' = c := hc'
  subst hc''
  exact ContextSet.subset_closure _ rfl

/-- Both rules are available as genuine `iff`s on the derivation rule, under
the closure-completeness premise the source leaves implicit. -/
example (hcentral : ∀ (m : Sigma), ∀ σ ∈ H, Commute m σ)
    (hH : ∀ σ ∈ H, σ ∥ (1 : Sigma) ∈ H) (π₁ π₂ : Sigma) (C₁ C₂ : ContextSet Sigma Φ)
    (hcomplete : ContextSet.ClosureComplete C₁ D H E π₁) :
    (∀ R S T : Set Φ,
        ConstructsRestrictedAsym D H E π₁ C₁ R S →
        ConstructsRestrictedAsym D H E π₂ C₂ S T →
        ConstructsRestrictedAsym D H E (π₂ * π₁) C₂ R T) ↔
      ∀ c ∈ C₂,
        (⟨c.filter * (π₂ ∥ (1 : Sigma)), c.aux⟩ : Context Sigma Φ) ∈
          ContextSet.closure C₁ :=
  constructsRestrictedAsym_seq_iff hcentral hH hcomplete

/-- Under closure-completeness, Definition 4.2.4's syntactic closure *is* the
set of semantically dominated contexts. -/
example (hH : ∀ σ ∈ H, σ ∥ (1 : Sigma) ∈ H) (π : Sigma) (C : ContextSet Sigma Φ)
    (hcomplete : ContextSet.ClosureComplete C D H E π) (c : Context Sigma Φ) :
    c ∈ ContextSet.closure C ↔ ContextSet.Dominates C D H E π c :=
  ContextSet.mem_closure_iff_dominates hH hcomplete

/-! ### Proposition 4.2.7 — the collapse to the ordinary notion -/

/-- "`𝒞̄_id = Σ × Θ`, i.e., the closure equals the set of all resources and
converters." -/
example (u : Φ) (hone : ((1 : Sigma) ∥ (1 : Sigma)) = 1) (hleft : ∀ R : Φ, u ∥ R = R) :
    ContextSet.closure (contextId (Sigma := Sigma) u) = Set.univ :=
  closure_contextId_eq_univ hone hleft

/-- Proposition 4.2.7, first equivalence: the regular simulation-based notion
is the `𝒞_id` case. -/
example (u : Φ) (hright : ∀ R : Φ, R ∥ u = R) (π : Sigma) (R S : Set Φ) :
    ConstructsAsym D H E π R S ↔
      ConstructsRestrictedAsym D H E π (contextId (Sigma := Sigma) u) R S :=
  constructsAsym_iff_constructsRestrictedAsym_contextId hright

/-- Proposition 4.2.7, second equivalence: a context-restricted construction is
a family of ordinary construction statements with the context folded into the
assumed resource and the protocol. -/
example (hcentral : ∀ (m : Sigma), ∀ σ ∈ H, Commute m σ) (π : Sigma)
    (C : ContextSet Sigma Φ) (R S : Set Φ) :
    ConstructsRestrictedAsym D H E π C R S ↔
      ∀ c ∈ C, ConstructsAsym D H E (c.filter * (π ∥ (1 : Sigma)))
        (R ∥ ({c.aux} : Set Φ)) (c.filter • (S ∥ ({c.aux} : Set Φ))) :=
  constructsRestrictedAsym_iff_forall_constructsAsym hcentral

/-! ### §4.2.3's closing remark: Corollary 2.2.16 is a special case

With `𝒞₁ = 𝒞_id` the sequential side condition of Theorem 4.2.6 is vacuous,
because `𝒞̄_id` is everything.  Composing an ordinary construction with a
`𝒞₂`-restricted one therefore never needs a containment check — which is
exactly what makes ordinary constructions generally composable. -/
example (u : Φ) (hone : ((1 : Sigma) ∥ (1 : Sigma)) = 1) (hleft : ∀ R : Φ, u ∥ R = R)
    (hcentral : ∀ (m : Sigma), ∀ σ ∈ H, Commute m σ)
    (hH : ∀ σ ∈ H, σ ∥ (1 : Sigma) ∈ H) (hright : ∀ R : Φ, R ∥ u = R)
    (π₁ π₂ : Sigma) (C₂ : ContextSet Sigma Φ) (R S T : Set Φ)
    (h₁ : ConstructsAsym D H E π₁ R S)
    (h₂ : ConstructsRestrictedAsym D H E π₂ C₂ S T) :
    ConstructsRestrictedAsym D H E (π₂ * π₁) C₂ R T := by
  refine constructsRestrictedAsym_seq hcentral hH (fun c _ => ?_)
    ((constructsAsym_iff_constructsRestrictedAsym_contextId hright).mp h₁) h₂
  rw [closure_contextId_eq_univ hone hleft]
  trivial

end AbstractCryptographyContextRestrictedTests
