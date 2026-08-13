/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import AbstractCryptography.Metric.Distinguisher
import AbstractCryptography.Metric.Nonexpansion
import AbstractCryptography.Specification.Relaxation

/-!
# The `ε`-relaxation and the distinguisher-indexed budgets

Two error notions on a resource carrier:

* **Indexed** (Jost Definition 2.2.9 / JM20 Definition 3) —
  `DistinguisherClass.reductionRelaxation`, where the budget `ε` is a function
  of the distinguisher, with transport theorems `attachBudget`,
  `parRightBudget`, `parLeftBudget`.
* **Scalar** (CR18 §5.2.1) — `Relaxation.epsilonRelaxation`, the closed `ε`-ball of a
  `PseudoEMetricSpace`, together with JM20 Theorem 2/3 and Corollary 1.
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

variable {M Φ : Type*}

/-! ### The distinguisher-indexed reduction relaxation (JM20 Definition 3) -/

namespace DistinguisherClass

variable [SMul M Φ]

/-- JM20 Definition 3's reduction relaxation.  A resource `q'` is admitted
around `q` when every test in the chosen distinguisher class has advantage at
most its own budget `ε`.

The paper's budgets take values in `[0,1]`; the codomain here is `ℝ≥0∞`, in
which Theorem 2's addition does not truncate.  An empty test class therefore
relaxes every nonempty specification to `Set.univ`. -/
noncomputable def reductionRelaxation (D : DistinguisherClass M Φ)
    (ε : D.tests → ℝ≥0∞) : Relaxation Φ :=
  Relaxation.ofPointwise
    (fun q => {q' | ∀ t : D.tests, adv t.1 q q' ≤ ε t})
    (fun q t => by simp [adv])

/-- Membership in JM20 Definition 3's reduction relaxation: some resource of
the specification meets the individual budget of every admitted test. -/
theorem mem_reductionRelaxation_iff
    {D : DistinguisherClass M Φ} {ε : D.tests → ℝ≥0∞}
    {R : Set Φ} {q' : Φ} :
    q' ∈ D.reductionRelaxation ε R ↔
      ∃ q ∈ R, ∀ t : D.tests, adv t.1 q q' ≤ ε t := by
  simp [reductionRelaxation]

/-- JM20 Theorem 2: applying budgets `ε₁` and `ε₂` successively is contained
in applying their pointwise sum.

JM20 Appendix A.1's final `ε₁(D) + ε₁(D)` is a typo: its preceding bounds, and
the theorem statement, give `ε₁(D) + ε₂(D)`. -/
theorem reductionRelaxation_reductionRelaxation_subset
    (D : DistinguisherClass M Φ) {ε₁ ε₂ : D.tests → ℝ≥0∞} (R : Set Φ) :
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
def attachBudget (D : DistinguisherClass M Φ) (c : M)
    (ε : D.tests → ℝ≥0∞) : D.tests → ℝ≥0∞ :=
  fun t => ε ⟨fun q => t.1 (c • q), D.test_attach c t.2⟩

/-- JM20 Theorem 3's protocol transport:
`c • (R^ε) ⊆ (c • R)^(ε_c)`, where `ε_c(D) = ε(D c(·))`. -/
theorem smul_reductionRelaxation_subset
    (D : DistinguisherClass M Φ) (c : M)
    (ε : D.tests → ℝ≥0∞) (R : Set Φ) :
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
noncomputable def parRightBudget (D : DistinguisherClass M Φ)
    [Par Φ] [D.IsClosedUnderPar] (S : Set Φ)
    (ε : D.tests → ℝ≥0∞) : D.tests → ℝ≥0∞ :=
  fun t => ⨆ s : S,
    ε ⟨fun q => t.1 (q ∥ s.1), IsClosedUnderPar.test_par_right s.1 t.2⟩

/-- JM20 Theorem 3's displayed parallel transport:
`[R^ε, S] ⊆ [R, S]^(ε_S)`, with the worst-context budget
`ε_S(D) = sup_{s ∈ S} ε(D[·,s])`.

The paper's displayed orientation only: the relaxed resource on the left, the
context on the right. -/
theorem reductionRelaxation_par_subset
    (D : DistinguisherClass M Φ) [Par Φ] [D.IsClosedUnderPar]
    (ε : D.tests → ℝ≥0∞) (R S : Set Φ) :
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
noncomputable def parLeftBudget (D : DistinguisherClass M Φ)
    [Par Φ] [D.IsClosedUnderPar] (S : Set Φ)
    (ε : D.tests → ℝ≥0∞) : D.tests → ℝ≥0∞ :=
  fun t => ⨆ s : S,
    ε ⟨fun q => t.1 (s.1 ∥ q), IsClosedUnderPar.test_par_left s.1 t.2⟩

/-- Left-context parallel transport at an indexed budget:
`[𝒮, ℛ^ε] ⊆ [𝒮, ℛ]^(ε_{𝒮,left})`. -/
theorem reductionRelaxation_par_left_subset
    (D : DistinguisherClass M Φ) [Par Φ] [D.IsClosedUnderPar]
    (ε : D.tests → ℝ≥0∞) (R S : Set Φ) :
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
theorem reductionRelaxation_mono_budget (D : DistinguisherClass M Φ)
    {ε ε' : D.tests → ℝ≥0∞} (h : ε ≤ ε') (R : Set Φ) :
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

variable [Monoid M] [MulAction M Φ]

/-- Jost, *Thesis*, **Corollary 2.2.13.1** at an indexed budget:
`ℛ —π→ 𝒮^ε ∧ 𝒮 —π'→ 𝒯^{ε'} ⟹ ℛ —π'∘π→ 𝒯^{ε_{π'} + ε'}`, where
`ε_{π'}(D) = ε(Dπ'(·))` is `attachBudget`. -/
theorem Constructs.reductionRelaxation_trans
    (D : DistinguisherClass M Φ) {π π' : M} {R S T : Set Φ}
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
theorem Constructs.reductionRelaxation_par [Par Φ] [Par M] [SMulParClass M Φ]
    (D : DistinguisherClass M Φ) [DistinguisherClass.IsClosedUnderPar D]
    {π : M} {R S : Set Φ} {ε : D.tests → ℝ≥0∞}
    (h : R —[π]→ D.reductionRelaxation ε S) (T : Set Φ) :
    R ∥ T —[π ∥ (1 : M)]→
      D.reductionRelaxation (D.parRightBudget T ε) (S ∥ T) :=
  fun _ hx => D.reductionRelaxation_par_subset ε S T (Constructs.par_left T h hx)

/-- Left-context form of `Constructs.reductionRelaxation_par`, using
`parLeftBudget`. -/
theorem Constructs.reductionRelaxation_par_right [Par Φ] [Par M] [SMulParClass M Φ]
    (D : DistinguisherClass M Φ) [DistinguisherClass.IsClosedUnderPar D]
    {π : M} {R S : Set Φ} {ε : D.tests → ℝ≥0∞}
    (h : R —[π]→ D.reductionRelaxation ε S) (T : Set Φ) :
    T ∥ R —[(1 : M) ∥ π]→
      D.reductionRelaxation (D.parLeftBudget T ε) (T ∥ S) :=
  fun _ hx => D.reductionRelaxation_par_left_subset ε S T (red_one_par T h hx)

end IndexedConstructs

/-! ### The ε-relaxation (CR18 §5.2.3, JM20 Def 3) -/

namespace Relaxation

section EBall

variable [PseudoEMetricSpace Φ]

/-- CR18 §5.2.1: "If a (pseudo-)metric `d` is defined on `Φ`, a natural
type of relaxation is the so-called `ǫ`-relaxation: For `ǫ > 0` we have

  `Rᵋ = {R′ | d(R, R′) ≤ ǫ}`

and hence

  `ℛᵋ = {R′ | ∃R ∈ ℛ : d(R, R′) ≤ ǫ}`."

Built as the `ofPointwise` (JM20 Definition 2) lift of the closed `ε`-ball. -/
@[crypto_rule "ac.relaxation.epsilonRelaxation" ac_specification abstract_crypto]
noncomputable def epsilonRelaxation (ε : ℝ≥0∞) : Relaxation Φ :=
  ofPointwise (fun R => Metric.closedEBall R ε) fun _ => Metric.mem_closedEBall_self

/-- Paper-order form of the scalar `ε`-relaxation. -/
@[reducible] def epsilonRelaxed (R : Set Φ) (ε : ℝ≥0∞) : Set Φ :=
  Relaxation.epsilonRelaxation ε R

/-- `R ^ε[ε]` expands to `Relaxation.epsilonRelaxed R ε`.  This denotes
a relaxed specification, not metric equality. -/
scoped[AbstractCryptography] notation:max R:max " ^ε[" ε "]" =>
  Relaxation.epsilonRelaxed R ε

theorem mem_epsilonRelaxation_iff {ε : ℝ≥0∞} {R : Set Φ} {x : Φ} :
    x ∈ epsilonRelaxation ε R ↔ ∃ r ∈ R, edist x r ≤ ε := by
  simp [epsilonRelaxation, Metric.mem_closedEBall]

/-- JM20 §2.3: "First, the errors just add up, as expressed by the
following theorem."

**Theorem 2**: "Let `ℛ` be an arbitrary specification, and let `ε₁` and
`ε₂` be arbitrary `ε`-relaxations.  Then we have `(ℛ^{ε₁})^{ε₂} ⊆
ℛ^{ε₁+ε₂}`."

"*Proof.* This follows directly from the triangle inequality of the
distinguishing advantage." -/
theorem epsilonRelaxation_epsilonRelaxation_subset {ε₁ ε₂ : ℝ≥0∞} (R : Set Φ) :
    epsilonRelaxation ε₂ (epsilonRelaxation ε₁ R) ⊆ epsilonRelaxation (ε₁ + ε₂) R := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_epsilonRelaxation_iff.mp hx
  obtain ⟨r, hr, hyr⟩ := mem_epsilonRelaxation_iff.mp hy
  exact mem_epsilonRelaxation_iff.mpr
    ⟨r, hr, (edist_triangle x y r).trans <| (add_le_add hxy hyr).trans_eq (add_comm _ _)⟩

/-- JM20 §2.3, **Theorem 3**, first half: "The `ε`-relaxation is
compatible with protocol application in the following sense that
`π(ℛ^ε) ⊆ (πℛ)^{ε_π}`, for `ε_π(D) := ε(Dπ(·))`, where `Dπ(·)` denotes
the distinguisher that first attaches `π` to the given resource and then
executes `D`."

Here at a fixed scalar radius, under CR18 §5.2.3's sufficient criterion: "A
function `γ ∈ Γ` is called non-expanding for the pseudo-metric `d` if
`d(γ(R), γ(S)) ≤ d(R, S)`" for resource points `R, S`. "If all `γ ∈ Γ` are
non-expanding for `d`, then the `ǫ`-relaxation is compatible with `Γ`." -/
theorem epsilonRelaxation_compatible [SMul M Φ] [IsNonexpandingSMul M Φ] (ε : ℝ≥0∞) :
    (epsilonRelaxation (Φ := Φ) ε).Compatible M := by
  rintro π R _ ⟨y, hy, rfl⟩
  obtain ⟨r, hr, hyr⟩ := mem_epsilonRelaxation_iff.mp hy
  exact mem_epsilonRelaxation_iff.mpr
    ⟨π • r, Set.smul_mem_smul_set hr, (edist_smul_le π y r).trans hyr⟩

/-- JM20 §2.3, **Theorem 3**, second half: "Moreover, it is compatible
with parallel composition, i.e., `[ℛ^ε, 𝒮] ⊆ [ℛ, 𝒮]^{ε_𝒮}`, for
`ε_𝒮(D) := sup_{S∈𝒮} ε(D[ · , S])`, where `D[ · , S]` denotes the
distinguisher that emulates `S` in parallel to the given resource and
then lets `D` interact with them."

Here at a fixed scalar radius, valid in both ordered binary slots under
`IsNonexpandingPar`.  The second slot is CR18 Definition 5.7's, supported by
MauRen11 footnote 9's independent right-context inequality. -/
theorem epsilonRelaxation_parCompatible [Par Φ] [IsNonexpandingPar Φ] (ε : ℝ≥0∞) :
    (epsilonRelaxation (Φ := Φ) ε).ParCompatible := by
  intro R T
  constructor
  · rintro x ⟨y, hy, t, ht, rfl⟩
    obtain ⟨r, hr, hyr⟩ := mem_epsilonRelaxation_iff.mp hy
    exact mem_epsilonRelaxation_iff.mpr
      ⟨r ∥ t, par_mem_par hr ht, (edist_par_left_le y r t).trans hyr⟩
  · rintro x ⟨t, ht, y, hy, rfl⟩
    obtain ⟨r, hr, hyr⟩ := mem_epsilonRelaxation_iff.mp hy
    exact mem_epsilonRelaxation_iff.mpr
      ⟨t ∥ r, par_mem_par ht hr, (edist_par_right_le t y r).trans hyr⟩

end EBall

end Relaxation

/-! ### The scalar ball *is* the indexed relaxation at a constant budget

Jost's Definition 2.2.9 takes `ε` to be a function of the distinguisher; CR18's
`ε`-relaxation takes a single radius against a pseudo-emetric.  On a carrier
whose metric is the distinguisher-class metric `Δ^𝒟`, `Relaxation.epsilonRelaxation ε` is
equal to `reductionRelaxation` at the constant budget `fun _ => ε`. -/

namespace DistinguisherClass

variable [SMul M Φ]

/-- The distinguishing advantage is symmetric in the two resources. -/
theorem adv_comm (t : Φ → ℝ≥0∞) (q q' : Φ) : adv t q q' = adv t q' q :=
  sup_comm _ _

/-- MauRen11 §6.1's class distance is below a bound exactly when *every*
admitted test is: `Δ^𝒟(R,S) ≤ ε ↔ ∀ D ∈ 𝒟, Δ^D(R,S) ≤ ε`. -/
theorem edistD_le_iff (D : DistinguisherClass M Φ) {q q' : Φ} {ε : ℝ≥0∞} :
    D.edistD q q' ≤ ε ↔ ∀ t ∈ D.tests, adv t q q' ≤ ε :=
  iSup₂_le_iff

section Bridge

variable [PseudoEMetricSpace Φ]

/-- When the installed pseudo-emetric agrees with the distinguisher-class
metric, CR18's scalar `ε`-relaxation is exactly Jost Definition 2.2.9 at the
constant budget.  The agreement is supplied as `hd`; for the instance-level
form see `reductionRelaxation_const_eq_epsilonRelaxation_self`. -/
theorem reductionRelaxation_const_eq_epsilonRelaxation (D : DistinguisherClass M Φ)
    (hd : ∀ x y : Φ, edist x y = D.edistD x y) (ε : ℝ≥0∞) (R : Set Φ) :
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
theorem reductionRelaxation_const_eq_epsilonRelaxation' (D : DistinguisherClass M Φ)
    (hd : ∀ x y : Φ, edist x y = D.edistD x y) (ε : ℝ≥0∞) :
    D.reductionRelaxation (fun _ => ε) = Relaxation.epsilonRelaxation (Φ := Φ) ε :=
  Relaxation.toFun_injective
    (funext fun R => D.reductionRelaxation_const_eq_epsilonRelaxation hd ε R)

end Bridge

/-- `reductionRelaxation_const_eq_epsilonRelaxation'` on the class's own metric, where the
agreement is `rfl`. -/
theorem reductionRelaxation_const_eq_epsilonRelaxation_self (D : DistinguisherClass M Φ)
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
theorem epsilonRelaxation_subset_reductionRelaxation_const (D : DistinguisherClass M Φ)
    (hd : ∀ x y : Φ, D.edistD x y ≤ edist x y) (ε : ℝ≥0∞) (R : Set Φ) :
    Relaxation.epsilonRelaxation ε R ⊆ D.reductionRelaxation (fun _ => ε) R := by
  intro x hx
  obtain ⟨q, hq, hle⟩ := Relaxation.mem_epsilonRelaxation_iff.mp hx
  refine mem_reductionRelaxation_iff.mpr ⟨q, hq, fun t => ?_⟩
  rw [adv_comm]
  exact D.edistD_le_iff.mp ((hd x q).trans hle) t.1 t.2

/-- The scalar over-approximation of an indexed budget by its supremum:
`ℛ^ε ⊆ ℛ^(sup_D ε(D))`.  The converse fails, by
`reductionRelaxation_singleton_ne_epsilonRelaxation`. -/
theorem reductionRelaxation_subset_epsilonRelaxation_iSup (D : DistinguisherClass M Φ)
    (hd : ∀ x y : Φ, edist x y = D.edistD x y) (ε : D.tests → ℝ≥0∞)
    (R : Set Φ) :
    D.reductionRelaxation ε R ⊆ Relaxation.epsilonRelaxation (⨆ t, ε t) R := by
  refine (D.reductionRelaxation_mono_budget (fun t => le_iSup ε t) R).trans ?_
  exact (D.reductionRelaxation_const_eq_epsilonRelaxation hd _ R).subset

/-- A separation criterion: for a singleton centre `r`, if some `x` is admitted
by the indexed budget `ε`, some `y` is not, and `y` is no further from `r` than
`x` is in the class metric, then `ℛ^ε` differs from the scalar ball of *every*
radius `c`. -/
theorem reductionRelaxation_singleton_ne_epsilonRelaxation (D : DistinguisherClass M Φ)
    (hd : ∀ x y : Φ, edist x y = D.edistD x y) {ε : D.tests → ℝ≥0∞}
    {r x y : Φ}
    (hx : x ∈ D.reductionRelaxation ε ({r} : Set Φ))
    (hy : y ∉ D.reductionRelaxation ε ({r} : Set Φ))
    (hle : D.edistD y r ≤ D.edistD x r) (c : ℝ≥0∞) :
    D.reductionRelaxation ε ({r} : Set Φ) ≠ Relaxation.epsilonRelaxation c ({r} : Set Φ) := by
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

section EBallConstruction

variable [Monoid M] [MulAction M Φ] [PseudoEMetricSpace Φ]

/-- JM20 Definitions 1 and 3 (printed pp. 8 and 10) / CR18 Definitions 5.4
and 5.5 (printed pp. 115--116), scalar
specialization: constructing the `ε`-relaxation of `S` is exactly the
pointwise obligation that every constructed source resource lies within `ε`
of some center in `S`. -/
theorem constructs_epsilonRelaxation_iff {π : M} {R S : Set Φ} {ε : ℝ≥0∞} :
    R —[π]→ Relaxation.epsilonRelaxation ε S ↔
      ∀ r ∈ R, ∃ s ∈ S, edist (π • r) s ≤ ε := by
  constructor
  · intro h r hr
    exact Relaxation.mem_epsilonRelaxation_iff.mp (h (Set.smul_mem_smul_set hr))
  · rintro h _ ⟨r, hr, rfl⟩
    exact Relaxation.mem_epsilonRelaxation_iff.mpr (h r hr)

/-- Singleton specialization of `constructs_epsilonRelaxation_iff`, matching JM20's
singleton-specification convention after Definition 1 (printed p. 8). -/
theorem constructs_singleton_epsilonRelaxation_iff {π : M} {R S : Φ} {ε : ℝ≥0∞} :
    ({R} : Set Φ) —[π]→ Relaxation.epsilonRelaxation ε ({S} : Set Φ) ↔
      edist (π • R) S ≤ ε := by
  rw [constructs_epsilonRelaxation_iff]
  simp

omit [Monoid M] [MulAction M Φ] in
/-- Scalar approximate construction: a reducible wrapper around the ordinary
construction relation into `Relaxation.epsilonRelaxation`, introducing no independent
relation.  It needs only `HasReduction`, not a `Monoid`/`MulAction` on `M`,
so it accepts the same converters as the exact form. -/
@[reducible] def ApproximatelyConstructs [HasReduction (Set Φ) M]
    (π : M) (ε : ℝ≥0∞)
    (R S : Set Φ) : Prop :=
  HasReduction.Red R π (Relaxation.epsilonRelaxation ε S)

/-- `R —[π; ε]→ S` is `ApproximatelyConstructs π ε R S`. -/
scoped notation:50 R " —[" π "; " ε "]→ " S:51 =>
  ApproximatelyConstructs π ε R S

/-- Transport a scalar approximate construction across a supplied equality of
protocols.  The error and endpoint specifications are unchanged; only the
constructor label is rewritten. -/
theorem approximately_constructs_congr_protocol {π π' : M} {ε : ℝ≥0∞}
    {R S : Set Φ} (same : π = π') :
    (R —[π; ε]→ S) ↔ R —[π'; ε]→ S := by
  subst π'
  rfl

end EBallConstruction

section Cor1

variable [Monoid M] [MulAction M Φ] [PseudoEMetricSpace Φ]

/-- JM20 §2.3: "The composition theorem with `ε`-relaxations then follows
directly from these compatibility results.  The following corollary
phrases the corresponding result — which in older version of Constructive
Cryptography used to be called the composition theorem, thereby
hard-coding computational security."

**Corollary 1.1**: "For any specifications `ℛ`, `𝒮`, and `𝒯`, any
protocols `π` and `π′`, and any `ε`-relaxation `ε` and `ε′`, we have

  1. `ℛ —π→ 𝒮^ε ∧ 𝒮 —π′→ 𝒯^{ε′}  ⟹  ℛ —π′∘π→ 𝒯^{ε_{π′} + ε′}`"

— here at a fixed scalar radius, under `IsNonexpandingSMul`. -/
@[crypto_rule "ac.constructs.epsilonRelaxation_serial" ac_spec_construction abstract_crypto]
theorem Constructs.epsilonRelaxation_trans [IsNonexpandingSMul M Φ] {π π' : M} {R S T : Set Φ}
    {ε ε' : ℝ≥0∞} (h : R —[π]→ Relaxation.epsilonRelaxation ε S) (h' : S —[π']→ Relaxation.epsilonRelaxation ε' T) :
    R —[π' * π]→ Relaxation.epsilonRelaxation (ε + ε') T := by
  rw [add_comm ε ε']
  exact fun x hx =>
    Relaxation.epsilonRelaxation_epsilonRelaxation_subset T
      (Constructs.relax_trans h h' (Relaxation.epsilonRelaxation_compatible ε) hx)

/-- JM20 §2.3, **Corollary 1**, item 2:
`ℛ —π→ 𝒮^ε ⟹ [ℛ, 𝒯] —π→ [𝒮, 𝒯]^{ε_𝒯}`, where Theorem 3 defines
`ε_𝒯(D) := sup_{T∈𝒯} ε(D[·, T])`.

The paper overloads `π` for its extension to the untouched parallel interface;
the homogeneous model here writes that converter `π ∥ 1`.  At a fixed scalar
radius, under `IsNonexpandingPar`. -/
theorem Constructs.epsilonRelaxation_par [Par Φ] [Par M] [SMulParClass M Φ] [IsNonexpandingPar Φ]
    {π : M} {R S : Set Φ} {ε : ℝ≥0∞} (h : R —[π]→ Relaxation.epsilonRelaxation ε S) (T : Set Φ) :
    R ∥ T —[π ∥ 1]→ Relaxation.epsilonRelaxation ε (S ∥ T) :=
  h.relax_par T (Relaxation.epsilonRelaxation_parCompatible ε)

/-- Resource-level presentation of `Constructs.epsilonRelaxation_par`, on singleton
specifications. -/
theorem Constructs.epsilonRelaxation_par_resource
    [Par Φ] [Par M] [SMulParClass M Φ] [IsNonexpandingPar Φ]
    {π : M} {R S : Φ} {ε : ℝ≥0∞}
    (h : ApproximatelyConstructs π ε ({R} : Set Φ) ({S} : Set Φ))
    (T : Φ) :
    ApproximatelyConstructs (π ∥ 1) ε
      ({R ∥ T} : Set Φ) ({S ∥ T} : Set Φ) := by
  simpa only [singleton_par_singleton] using
    h.epsilonRelaxation_par ({T} : Set Φ)

end Cor1

end AbstractCryptography
