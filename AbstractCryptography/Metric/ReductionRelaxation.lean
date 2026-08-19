/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import AbstractCryptography.Metric.Distinguisher
import AbstractCryptography.Metric.Epsilon

/-!
# The distinguisher-indexed reduction relaxation

**MR11-DEFERRED (provenance fence, 2026-08-17): MauRen11 constructs
quarantined pending the MR11 reconciliation task.  No MR16-track file may
import this module — enforced by `scripts/ledgerAudit.sh`.  See `LEDGER.md`
PROVENANCE FENCE.**

Split out of `AbstractCryptography.Metric.Epsilon` on 2026-08-17.  Every
declaration here is indexed by a `DistinguisherClass` — MauRen11 Definition
15/16 provenance — and therefore sits behind the fence; the scalar `ε`-ball
calculus it is stated against stays on the MR16 track in `Metric.Epsilon`,
which this module imports (fenced → unfenced is the permitted direction).

Two error notions on a resource carrier, and their comparison:

* **Indexed** (Jost Definition 2.2.9 / JM20 Definition 3) —
  `DistinguisherClass.reductionRelaxation`, where the budget `ε` is a function
  of the distinguisher, with transport theorems `attachBudget`,
  `parRightBudget`, `parLeftBudget`.
* **Scalar** (CR18 §5.2.1) — `Relaxation.epsilonRelaxation`, the closed `ε`-ball
  of a `PseudoEMetricSpace`, in `AbstractCryptography.Metric.Epsilon`.
* **The bridge** — `reductionRelaxation_const_eq_epsilonRelaxation`: on a carrier whose
  metric is the distinguisher-class metric the two coincide, while
  `reductionRelaxation_singleton_ne_epsilonRelaxation` shows that collapsing an indexed
  budget to a scalar radius loses information.

The generic calculus these specialize lives in
`AbstractCryptography.Specification.Relaxation`; the `∗`-relaxation, which needs a
converter submonoid rather than a metric, lives in
`AbstractCryptography.Algebra.Star`.
-/

namespace AbstractCryptography

open Pointwise
open scoped ENNReal

variable {Sigma Φ : Type*}

/-! ### The distinguisher-indexed reduction relaxation (JM20 Definition 3) -/

namespace DistinguisherClass

variable [SMul Sigma Φ]

/-- JM20 Definition 3's reduction relaxation.  A resource `q'` is admitted
around `q` when every test in the chosen distinguisher class has advantage at
most its own budget `ε`.

The paper's budgets take values in `[0,1]`; the codomain here is `ℝ≥0∞`, in
which Theorem 2's addition does not truncate.  An empty test class therefore
relaxes every nonempty specification to `Set.univ`. -/
noncomputable def reductionRelaxation (D : DistinguisherClass Sigma Φ)
    (ε : D.tests → ℝ≥0∞) : Relaxation Φ :=
  Relaxation.ofPointwise
    (fun q => {q' | ∀ t : D.tests, adv t.1 q q' ≤ ε t})
    (fun q t => by simp [adv])

/-- Membership in JM20 Definition 3's reduction relaxation: some resource of
the specification meets the individual budget of every admitted test. -/
theorem mem_reductionRelaxation_iff
    {D : DistinguisherClass Sigma Φ} {ε : D.tests → ℝ≥0∞}
    {R : Specification Φ} {q' : Φ} :
    q' ∈ D.reductionRelaxation ε R ↔
      ∃ q ∈ R, ∀ t : D.tests, adv t.1 q q' ≤ ε t := by
  simp [reductionRelaxation]

/-- JM20 Theorem 2: applying budgets `ε₁` and `ε₂` successively is contained
in applying their pointwise sum.

JM20 Appendix A.1's final `ε₁(D) + ε₁(D)` is a typo: its preceding bounds, and
the theorem statement, give `ε₁(D) + ε₂(D)`. -/
theorem reductionRelaxation_reductionRelaxation_subset
    (D : DistinguisherClass Sigma Φ) {ε₁ ε₂ : D.tests → ℝ≥0∞} (R : Specification Φ) :
    D.reductionRelaxation ε₂ (D.reductionRelaxation ε₁ R) ⊆
      D.reductionRelaxation (ε₁ + ε₂) R := by
  intro q'' hq''
  obtain ⟨q', hq', h₂⟩ := mem_reductionRelaxation_iff.mp hq''
  obtain ⟨q, hq, h₁⟩ := mem_reductionRelaxation_iff.mp hq'
  exact mem_reductionRelaxation_iff.mpr
    ⟨q, hq, fun t =>
      (adv_triangle t.1 q q' q'').trans (add_le_add (h₁ t) (h₂ t))⟩

/-- JM20 Theorem 3's protocol-budget transform `ε_c(D) = ε(D c(·))`: first
attach `c` to the resource, then run the test, and charge the original budget
for that absorbed test. -/
def attachBudget (D : DistinguisherClass Sigma Φ) (c : Sigma)
    (ε : D.tests → ℝ≥0∞) : D.tests → ℝ≥0∞ :=
  fun t => ε ⟨fun q => t.1 (c • q), D.test_attach c t.2⟩

/-- JM20 Theorem 3's protocol transport:
`c • (R^ε) ⊆ (c • R)^(ε_c)`, where `ε_c(D) = ε(D c(·))`. -/
theorem smul_reductionRelaxation_subset
    (D : DistinguisherClass Sigma Φ) (c : Sigma)
    (ε : D.tests → ℝ≥0∞) (R : Specification Φ) :
    c • D.reductionRelaxation ε R ⊆
      D.reductionRelaxation (D.attachBudget c ε) (c • R) := by
  rintro _ ⟨q', hq', rfl⟩
  obtain ⟨q, hq, hbound⟩ := mem_reductionRelaxation_iff.mp hq'
  refine mem_reductionRelaxation_iff.mpr
    ⟨c • q, Set.smul_mem_smul_set hq, ?_⟩
  intro t
  simpa [attachBudget, adv] using
    hbound ⟨fun x => t.1 (c • x), D.test_attach c t.2⟩

/-- JM20 Theorem 3's displayed parallel-budget transform
`ε_S(D) = sup_{s ∈ S} ε(D[·,s])`: hardwire each resource `s` in the right
parallel slot, then take the worst original budget over the context
specification.  For an empty `S` the supremum is `0`. -/
noncomputable def parRightBudget (D : DistinguisherClass Sigma Φ)
    [Par Φ] [D.IsClosedUnderPar] (S : Specification Φ)
    (ε : D.tests → ℝ≥0∞) : D.tests → ℝ≥0∞ :=
  fun t => ⨆ s : S,
    ε ⟨fun q => t.1 (q ∥ s.1), IsClosedUnderPar.test_par_right s.1 t.2⟩

/-- JM20 Theorem 3's displayed parallel transport:
`[R^ε, S] ⊆ [R, S]^(ε_S)`, with the worst-context budget
`ε_S(D) = sup_{s ∈ S} ε(D[·,s])`.

The paper's displayed orientation only: the relaxed resource on the left, the
context on the right. -/
theorem reductionRelaxation_par_subset
    (D : DistinguisherClass Sigma Φ) [Par Φ] [D.IsClosedUnderPar]
    (ε : D.tests → ℝ≥0∞) (R S : Specification Φ) :
    D.reductionRelaxation ε R ∥ S ⊆
      D.reductionRelaxation (D.parRightBudget S ε) (R ∥ S) := by
  rintro _ ⟨q', hq', s, hs, rfl⟩
  obtain ⟨q, hq, hbound⟩ := mem_reductionRelaxation_iff.mp hq'
  refine mem_reductionRelaxation_iff.mpr ⟨q ∥ s, par_mem_par hq hs, ?_⟩
  intro t
  have h := hbound
    ⟨fun x => t.1 (x ∥ s), IsClosedUnderPar.test_par_right s t.2⟩
  exact h.trans <| by
    apply le_iSup_of_le (⟨s, hs⟩ : S)
    rfl

/-- The left-context counterpart of `parRightBudget`, hardwiring each `s ∈ 𝒮`
in the *left* parallel slot: `ε_{𝒮,left}(D) = sup_{s ∈ 𝒮} ε(D[s, ·])`.

Jost's thesis displays only the right-context orientation (Thm 2.2.11's
`[ℛ^ε, 𝒮] ⊆ [ℛ, 𝒮]^{ε_𝒮}`), and CR18 Definition 5.7 the binary slots.
Parallel composition is not assumed commutative here, so the left orientation
is an independent statement, supported by MauRen11 Definition 16's second
closure clause (`IsClosedUnderPar.test_par_left`). -/
noncomputable def parLeftBudget (D : DistinguisherClass Sigma Φ)
    [Par Φ] [D.IsClosedUnderPar] (S : Specification Φ)
    (ε : D.tests → ℝ≥0∞) : D.tests → ℝ≥0∞ :=
  fun t => ⨆ s : S,
    ε ⟨fun q => t.1 (s.1 ∥ q), IsClosedUnderPar.test_par_left s.1 t.2⟩

/-- Left-context parallel transport at an indexed budget:
`[𝒮, ℛ^ε] ⊆ [𝒮, ℛ]^(ε_{𝒮,left})`. -/
theorem reductionRelaxation_par_left_subset
    (D : DistinguisherClass Sigma Φ) [Par Φ] [D.IsClosedUnderPar]
    (ε : D.tests → ℝ≥0∞) (R S : Specification Φ) :
    S ∥ D.reductionRelaxation ε R ⊆
      D.reductionRelaxation (D.parLeftBudget S ε) (S ∥ R) := by
  rintro _ ⟨s, hs, q', hq', rfl⟩
  obtain ⟨q, hq, hbound⟩ := mem_reductionRelaxation_iff.mp hq'
  refine mem_reductionRelaxation_iff.mpr ⟨s ∥ q, par_mem_par hs hq, ?_⟩
  intro t
  have h := hbound
    ⟨fun x => t.1 (s ∥ x), IsClosedUnderPar.test_par_left s t.2⟩
  exact h.trans <| by
    apply le_iSup_of_le (⟨s, hs⟩ : S)
    rfl

/-- Monotonicity of Jost Definition 2.2.9 in the budget: a pointwise larger
per-distinguisher budget admits at least as many resources.  Jost
Cor. 2.2.13 uses this to replace `ε_{π'}` by any pointwise upper bound. -/
theorem reductionRelaxation_mono_budget (D : DistinguisherClass Sigma Φ)
    {ε ε' : D.tests → ℝ≥0∞} (h : ε ≤ ε') (R : Specification Φ) :
    D.reductionRelaxation ε R ⊆ D.reductionRelaxation ε' R := by
  intro q' hq'
  obtain ⟨q, hq, hb⟩ := mem_reductionRelaxation_iff.mp hq'
  exact mem_reductionRelaxation_iff.mpr ⟨q, hq, fun t => (hb t).trans (h t)⟩

end DistinguisherClass

/-! ### Jost Corollary 2.2.13 at indexed budgets

The structural inputs are MauRen11 Def 16's converter-emulation closure
(`test_attach`) and, for the parallel leg, `IsClosedUnderPar`; no metric is
involved. -/

section IndexedConstructs

variable [Monoid Sigma] [MulAction Sigma Φ]

/-- Jost, *Thesis*, **Corollary 2.2.13.1** at an indexed budget:
`ℛ —π→ 𝒮^ε ∧ 𝒮 —π'→ 𝒯^{ε'} ⟹ ℛ —π'∘π→ 𝒯^{ε_{π'} + ε'}`, where
`ε_{π'}(D) = ε(Dπ'(·))` is `attachBudget`. -/
theorem Constructs.reductionRelaxation_trans
    (D : DistinguisherClass Sigma Φ) {π π' : Sigma} {R S T : Specification Φ}
    {ε ε' : D.tests → ℝ≥0∞}
    (h : R —[π]→ D.reductionRelaxation ε S)
    (h' : S —[π']→ D.reductionRelaxation ε' T) :
    R —[π' * π]→ D.reductionRelaxation (D.attachBudget π' ε + ε') T := by
  rw [constructs_iff, mul_smul]
  calc π' • π • R ⊆ π' • D.reductionRelaxation ε S := Set.smul_set_mono h
    _ ⊆ D.reductionRelaxation (D.attachBudget π' ε) (π' • S) :=
        D.smul_reductionRelaxation_subset π' ε S
    _ ⊆ D.reductionRelaxation (D.attachBudget π' ε)
          (D.reductionRelaxation ε' T) :=
        (D.reductionRelaxation (D.attachBudget π' ε)).mono h'
    _ ⊆ D.reductionRelaxation (ε' + D.attachBudget π' ε) T :=
        D.reductionRelaxation_reductionRelaxation_subset T
    _ ⊆ D.reductionRelaxation (D.attachBudget π' ε + ε') T := by
        rw [add_comm]

/-- Jost, *Thesis*, **Corollary 2.2.13.2** at an indexed budget:
`ℛ —π→ 𝒮^ε ⟹ [ℛ, 𝒯] —π→ [𝒮, 𝒯]^{ε_𝒯}`, with
`ε_𝒯(D) = sup_{T ∈ 𝒯} ε(D[·, T])`. -/
theorem Constructs.reductionRelaxation_par [Par Φ] [Par Sigma] [SMulParClass Sigma Φ]
    (D : DistinguisherClass Sigma Φ) [DistinguisherClass.IsClosedUnderPar D]
    {π : Sigma} {R S : Specification Φ} {ε : D.tests → ℝ≥0∞}
    (h : R —[π]→ D.reductionRelaxation ε S) (T : Specification Φ) :
    R ∥ T —[π ∥ (1 : Sigma)]→
      D.reductionRelaxation (D.parRightBudget T ε) (S ∥ T) :=
  fun _ hx => D.reductionRelaxation_par_subset ε S T (Constructs.par_left T h hx)

/-- Left-context form of `Constructs.reductionRelaxation_par`, using
`parLeftBudget`. -/
theorem Constructs.reductionRelaxation_par_right [Par Φ] [Par Sigma] [SMulParClass Sigma Φ]
    (D : DistinguisherClass Sigma Φ) [DistinguisherClass.IsClosedUnderPar D]
    {π : Sigma} {R S : Specification Φ} {ε : D.tests → ℝ≥0∞}
    (h : R —[π]→ D.reductionRelaxation ε S) (T : Specification Φ) :
    T ∥ R —[(1 : Sigma) ∥ π]→
      D.reductionRelaxation (D.parLeftBudget T ε) (T ∥ S) :=
  fun _ hx => D.reductionRelaxation_par_left_subset ε S T (red_one_par T h hx)

end IndexedConstructs

/-! ### The scalar ball *is* the indexed relaxation at a constant budget

Jost's Definition 2.2.9 takes `ε` to be a function of the distinguisher; CR18's
`ε`-relaxation takes a single radius against a pseudo-emetric.  On a carrier
whose metric is the distinguisher-class metric `Δ^𝒟`, `Relaxation.epsilonRelaxation ε` is
equal to `reductionRelaxation` at the constant budget `fun _ => ε`. -/

namespace DistinguisherClass

variable [SMul Sigma Φ]

/-- The distinguishing advantage is symmetric in the two resources. -/
theorem adv_comm (t : Φ → ℝ≥0∞) (q q' : Φ) : adv t q q' = adv t q' q :=
  sup_comm _ _

/-- MauRen11 §6.1's class distance is below a bound exactly when *every*
admitted test is: `Δ^𝒟(R,S) ≤ ε ↔ ∀ D ∈ 𝒟, Δ^D(R,S) ≤ ε`. -/
theorem edistD_le_iff (D : DistinguisherClass Sigma Φ) {q q' : Φ} {ε : ℝ≥0∞} :
    D.edistD q q' ≤ ε ↔ ∀ t ∈ D.tests, adv t q q' ≤ ε :=
  iSup₂_le_iff

section Bridge

variable [PseudoEMetricSpace Φ]

/-- When the installed pseudo-emetric agrees with the distinguisher-class
metric, CR18's scalar `ε`-relaxation is exactly Jost Definition 2.2.9 at the
constant budget.  The agreement is supplied as `hd`; for the instance-level
form see `reductionRelaxation_const_eq_epsilonRelaxation_self`. -/
theorem reductionRelaxation_const_eq_epsilonRelaxation (D : DistinguisherClass Sigma Φ)
    (hd : ∀ x y : Φ, edist x y = D.edistD x y) (ε : ℝ≥0∞) (R : Specification Φ) :
    D.reductionRelaxation (fun _ => ε) R = Relaxation.epsilonRelaxation ε R := by
  ext x
  rw [mem_reductionRelaxation_iff, Relaxation.mem_epsilonRelaxation_iff]
  constructor
  · rintro ⟨q, hq, h⟩
    refine ⟨q, hq, ?_⟩
    rw [hd]
    exact D.edistD_le_iff.mpr fun t ht => by
      rw [adv_comm]; exact h ⟨t, ht⟩
  · rintro ⟨q, hq, h⟩
    rw [hd] at h
    refine ⟨q, hq, fun t => ?_⟩
    rw [adv_comm]
    exact D.edistD_le_iff.mp h t.1 t.2

/-- `reductionRelaxation_const_eq_epsilonRelaxation` as an equality of `Relaxation`
values. -/
theorem reductionRelaxation_const_eq_epsilonRelaxation' (D : DistinguisherClass Sigma Φ)
    (hd : ∀ x y : Φ, edist x y = D.edistD x y) (ε : ℝ≥0∞) :
    D.reductionRelaxation (fun _ => ε) = Relaxation.epsilonRelaxation (Φ := Φ) ε :=
  Relaxation.toFun_injective
    (funext fun R => D.reductionRelaxation_const_eq_epsilonRelaxation hd ε R)

end Bridge

/-- `reductionRelaxation_const_eq_epsilonRelaxation'` on the class's own metric, where the
agreement is `rfl`. -/
theorem reductionRelaxation_const_eq_epsilonRelaxation_self (D : DistinguisherClass Sigma Φ)
    (ε : ℝ≥0∞) :
    letI := D.toPseudoEMetricSpace
    D.reductionRelaxation (fun _ => ε) = Relaxation.epsilonRelaxation (Φ := Φ) ε :=
  letI := D.toPseudoEMetricSpace
  D.reductionRelaxation_const_eq_epsilonRelaxation' (fun _ _ => rfl) ε

section Overapproximation

variable [PseudoEMetricSpace Φ]

/-- When the installed metric only *dominates* the class metric (`Δ^𝒟 ≤ d`)
rather than equalling it, the scalar ball is still contained in the constant
indexed budget: a scalar guarantee implies the per-distinguisher one. -/
theorem epsilonRelaxation_subset_reductionRelaxation_const (D : DistinguisherClass Sigma Φ)
    (hd : ∀ x y : Φ, D.edistD x y ≤ edist x y) (ε : ℝ≥0∞) (R : Specification Φ) :
    Relaxation.epsilonRelaxation ε R ⊆ D.reductionRelaxation (fun _ => ε) R := by
  intro x hx
  obtain ⟨q, hq, hle⟩ := Relaxation.mem_epsilonRelaxation_iff.mp hx
  refine mem_reductionRelaxation_iff.mpr ⟨q, hq, fun t => ?_⟩
  rw [adv_comm]
  exact D.edistD_le_iff.mp ((hd x q).trans hle) t.1 t.2

/-- The scalar over-approximation of an indexed budget by its supremum:
`ℛ^ε ⊆ ℛ^(sup_D ε(D))`.  The converse fails, by
`reductionRelaxation_singleton_ne_epsilonRelaxation`. -/
theorem reductionRelaxation_subset_epsilonRelaxation_iSup (D : DistinguisherClass Sigma Φ)
    (hd : ∀ x y : Φ, edist x y = D.edistD x y) (ε : D.tests → ℝ≥0∞)
    (R : Specification Φ) :
    D.reductionRelaxation ε R ⊆ Relaxation.epsilonRelaxation (⨆ t, ε t) R := by
  refine (D.reductionRelaxation_mono_budget (fun t => le_iSup ε t) R).trans ?_
  exact (D.reductionRelaxation_const_eq_epsilonRelaxation hd _ R).subset

/-- A separation criterion: for a singleton centre `r`, if some `x` is admitted
by the indexed budget `ε`, some `y` is not, and `y` is no further from `r` than
`x` is in the class metric, then `ℛ^ε` differs from the scalar ball of *every*
radius `c`. -/
theorem reductionRelaxation_singleton_ne_epsilonRelaxation (D : DistinguisherClass Sigma Φ)
    (hd : ∀ x y : Φ, edist x y = D.edistD x y) {ε : D.tests → ℝ≥0∞}
    {r x y : Φ}
    (hx : x ∈ D.reductionRelaxation ε ({r} : Specification Φ))
    (hy : y ∉ D.reductionRelaxation ε ({r} : Specification Φ))
    (hle : D.edistD y r ≤ D.edistD x r) (c : ℝ≥0∞) :
    D.reductionRelaxation ε ({r} : Specification Φ) ≠ Relaxation.epsilonRelaxation c ({r} : Specification Φ) := by
  intro heq
  by_cases hxc : D.edistD x r ≤ c
  · exact hy (heq ▸ Relaxation.mem_epsilonRelaxation_iff.mpr
      ⟨r, rfl, by rw [hd]; exact hle.trans hxc⟩)
  · exact hxc (by
      have := Relaxation.mem_epsilonRelaxation_iff.mp (heq ▸ hx)
      obtain ⟨s, hs, hsle⟩ := this
      rw [Set.mem_singleton_iff] at hs
      subst hs
      rwa [hd] at hsle)

end Overapproximation

end DistinguisherClass

end AbstractCryptography
