/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import AbstractCryptography.Algebra.Attachment
import AbstractCryptography.Specification.Basic

/-!
# Distinguisher classes and the derived pseudo-metric (MauRen11 §4.4, §6.1)

**MR11-DEFERRED (provenance fence, 2026-08-17): MauRen11 constructs
quarantined pending the MR11 reconciliation task.  No MR16-track file may
import this module — enforced by `scripts/ledgerAudit.sh`.  See `LEDGER.md`
PROVENANCE FENCE.**

MauRen11 **Definition 15**: a test `D : R ↦ DR` read as the probability
its output bit is `1` — here any `[0, 1]`-valued observable on the
resource carrier `Φ`.  **Definition 16**: "a distinguisher class `𝒟`" is
closed under converter emulation, `𝒟Σⁱ ⊆ 𝒟`, where
`𝒟Σⁱ = {Dαⁱ : D ∈ 𝒟, α ∈ Σ}` and `(Dαⁱ) : R ↦ D(αⁱR)` (fn. 24).

From the class, §6.1's `Δ^𝒟(R, S) = sup_{D ∈ 𝒟} Δ^D(R, S)` is a
pseudo-emetric (MauRen11 §2.2's axioms become theorems), and MauRen11
§4.4 Def 2 eq. (4) — `d(αⁱR, αⁱS) ≤ d(R, S)` — is a **theorem**
(`edistD_attach_le`), precisely because `𝒟Σⁱ ⊆ 𝒟`: the emulation
`D ↦ Dαⁱ` stays in the class.  Per §6.3, "computational security" and
"information-theoretic security" then differ only in the choice of `𝒟`.

MauRen11 indexes tests by an interface signature.  This development is
homogeneous (MauRen11 Def 14): the carrier is a single `Φ` and converters
a monoid `Sigma` acting on it, so the signature indexing vanishes and Def 16's
closure is under the whole converter monoid (`test_attach` over `c : Sigma`).
Def 17's restricted feasible classes are represented by the choice of `Sigma`,
`Φ`, and `𝒟` themselves.
-/

open scoped ENNReal

namespace AbstractCryptography

variable {Sigma Φ : Type*}

/-- MauRen11 **Definition 16**: "a distinguisher class `𝒟`", homogeneous
form.  A set of `[0, 1]`-valued tests on the carrier `Φ`, closed under
emulation of a converter — Def 16's `𝒟Σⁱ ⊆ 𝒟`, here `𝒟Σ ⊆ 𝒟` over the
whole converter monoid `Sigma`. -/
structure DistinguisherClass (Sigma Φ : Type*) [SMul Sigma Φ] where
  /-- MauRen11 Def 15's `D : R ↦ DR`, read as the probability of the
  output bit.  Def 16's "if `R ≈ S` then `DR = DS`" is built in: a test is
  a function on `Φ`. -/
  tests : Set (Φ → ℝ≥0∞)
  /-- "the set of binary distributions" (Def 15). -/
  test_le_one : ∀ {t}, t ∈ tests → ∀ q, t q ≤ 1
  /-- MauRen11 Def 16: "`𝒟Σⁱ ⊆ 𝒟` for `i ∈ I`, i.e. `𝒟` is closed under
  emulation of a converter in `Σ`" — where `(Dαⁱ) : R ↦ D(αⁱR)`.  Over the
  homogeneous monoid: closed under `t ↦ t(c • ·)` for every `c : Sigma`. -/
  test_attach : ∀ (c : Sigma) {t}, t ∈ tests → (fun q => t (c • q)) ∈ tests

/-- The two ordered parallel-resource emulation closures used by MauRen11
Lemma 1 to derive full parallel non-expansion of the distinguisher metric:
Definition 16's `𝒟[· ∥ Φ] ⊆ 𝒟` and Lemma 1's `𝒟[Φ ∥ ·] ⊆ 𝒟`.

Parallel composition is not assumed commutative or associative, so neither
ordered field follows from the other. -/
class DistinguisherClass.IsClosedUnderPar [SMul Sigma Φ] [Par Φ]
    (D : DistinguisherClass Sigma Φ) : Prop where
  /-- Closure under emulating a fixed resource in the right parallel slot. -/
  test_par_right : ∀ (r : Φ) {t}, t ∈ D.tests →
    (fun q => t (q ∥ r)) ∈ D.tests
  /-- Closure under emulating a fixed resource in the left parallel slot. -/
  test_par_left : ∀ (r : Φ) {t}, t ∈ D.tests →
    (fun q => t (r ∥ q)) ∈ D.tests

namespace DistinguisherClass

variable [SMul Sigma Φ] (D : DistinguisherClass Sigma Φ)

/-- MauRen11 §6.1: "`Δ^D(R, S)` is the advantage of `D` in distinguishing
`R` and `S`, i.e., the statistical distance of the binary random variables
`DR` and `DS`". -/
noncomputable def adv (t : Φ → ℝ≥0∞) (q q' : Φ) : ℝ≥0∞ :=
  (t q - t q') ⊔ (t q' - t q)

/-- MauRen11 §6.1: "the distance between two resource systems is the best
advantage a distinguisher in a certain class `𝒟` can achieve" —
`Δ^𝒟(R, S) = sup_{D ∈ 𝒟} Δ^D(R, S)`. -/
noncomputable def edistD (q q' : Φ) : ℝ≥0∞ :=
  ⨆ t ∈ D.tests, adv t q q'

/-- MauRen11's class advantage (printed p. 13): the advantage of any admitted
test is bounded by the supremum over the class. -/
theorem adv_le_edistD {t : Φ → ℝ≥0∞} (ht : t ∈ D.tests) (q q' : Φ) :
    adv t q q' ≤ D.edistD q q' :=
  le_iSup₂ (f := fun t _ => adv t q q') t ht

/-- The left-to-right test-value consequence of a class-distance bound. -/
theorem test_left_tsub_right_le_of_edistD_le {t : Φ → ℝ≥0∞}
    (ht : t ∈ D.tests) {q q' : Φ} {ε : ℝ≥0∞}
    (hd : D.edistD q q' ≤ ε) :
    t q - t q' ≤ ε :=
  (le_sup_left.trans (D.adv_le_edistD ht q q')).trans hd

/-- The right-to-left test-value consequence of a class-distance bound. -/
theorem test_right_tsub_left_le_of_edistD_le {t : Φ → ℝ≥0∞}
    (ht : t ∈ D.tests) {q q' : Φ} {ε : ℝ≥0∞}
    (hd : D.edistD q q' ≤ ε) :
    t q' - t q ≤ ε :=
  (le_sup_right.trans (D.adv_le_edistD ht q q')).trans hd

/-- Definition 15's binary-output bound, lifted to the whole distinguisher
class: the best distinguishing advantage is at most `1`. -/
theorem edistD_le_one (q q' : Φ) : D.edistD q q' ≤ 1 := by
  refine iSup₂_le fun t ht => sup_le ?_ ?_
  · exact tsub_le_self.trans (D.test_le_one ht q)
  · exact tsub_le_self.trans (D.test_le_one ht q')

theorem edistD_self (q : Φ) : D.edistD q q = 0 := by simp [edistD, adv]

/-- When the admitted tests separate points, zero distinguisher distance is
exactly equality.  `Set.SeparatesPoints` is an explicit premise: it does not
follow from emulator closure, and in MauRen11 §6.3's feasible/computational
case zero distance instead represents negligible advantage. -/
theorem edistD_eq_zero_iff_of_separatesPoints
    (hsep : D.tests.SeparatesPoints) (q q' : Φ) :
    D.edistD q q' = 0 ↔ q = q' := by
  constructor
  · intro h0
    by_contra hne
    obtain ⟨t, ht, hneq⟩ := hsep hne
    have hadv : adv t q q' = 0 :=
      le_antisymm
        ((le_iSup₂ (f := fun t _ => adv t q q') t ht).trans h0.le)
        (zero_le _)
    have hqq' : t q - t q' = 0 :=
      le_antisymm (le_sup_left.trans hadv.le) (zero_le _)
    have hq'q : t q' - t q = 0 :=
      le_antisymm (le_sup_right.trans hadv.le) (zero_le _)
    exact hneq (le_antisymm (tsub_eq_zero_iff_le.mp hqq')
      (tsub_eq_zero_iff_le.mp hq'q))
  · rintro rfl
    exact D.edistD_self q

theorem edistD_comm (q q' : Φ) : D.edistD q q' = D.edistD q' q := by
  simp only [edistD, adv, sup_comm]

theorem adv_triangle (t : Φ → ℝ≥0∞) (q q' q'' : Φ) :
    adv t q q'' ≤ adv t q q' + adv t q' q'' := by
  refine sup_le ?_ ?_
  · calc t q - t q'' ≤ (t q - t q') + (t q' - t q'') := tsub_le_tsub_add_tsub ..
      _ ≤ adv t q q' + adv t q' q'' := add_le_add le_sup_left le_sup_left
  · calc t q'' - t q ≤ (t q'' - t q') + (t q' - t q) := tsub_le_tsub_add_tsub ..
      _ ≤ adv t q' q'' + adv t q q' := add_le_add le_sup_right le_sup_right
      _ = adv t q q' + adv t q' q'' := add_comm ..

theorem edistD_triangle (q q' q'' : Φ) :
    D.edistD q q'' ≤ D.edistD q q' + D.edistD q' q'' := by
  refine iSup₂_le fun t ht => ?_
  calc adv t q q'' ≤ adv t q q' + adv t q' q'' := adv_triangle t q q' q''
    _ ≤ D.edistD q q' + D.edistD q' q'' :=
        add_le_add (le_iSup₂ (f := fun t _ => adv t q q') t ht)
          (le_iSup₂ (f := fun t _ => adv t q' q'') t ht)

/-- MauRen11 §4.4 Def 2, eq. (4) — `d(αⁱR, αⁱS) ≤ d(R, S)` — for `Δ^𝒟`,
by Def 16's closure `𝒟Σ ⊆ 𝒟`. -/
theorem edistD_attach_le (c : Sigma) (q q' : Φ) :
    D.edistD (c • q) (c • q') ≤ D.edistD q q' := by
  refine iSup₂_le fun t ht => ?_
  exact le_iSup₂ (f := fun t _ => adv t q q')
    (fun q => t (c • q)) (D.test_attach c ht)

/-- MauRen11 Lemma 1's fixed-right-context inequality, from Definition 16's
`𝒟[· ∥ Φ] ⊆ 𝒟` closure. -/
theorem edistD_par_left_le [Par Φ] [D.IsClosedUnderPar] (q q' r : Φ) :
    D.edistD (q ∥ r) (q' ∥ r) ≤ D.edistD q q' := by
  refine iSup₂_le fun t ht => ?_
  exact le_iSup₂ (f := fun t _ => adv t q q')
    (fun q => t (q ∥ r)) (IsClosedUnderPar.test_par_right r ht)

/-- MauRen11 Lemma 1's independent fixed-left-context inequality, from its
additional `𝒟[Φ ∥ ·] ⊆ 𝒟` premise. -/
theorem edistD_par_right_le [Par Φ] [D.IsClosedUnderPar] (r q q' : Φ) :
    D.edistD (r ∥ q) (r ∥ q') ≤ D.edistD q q' := by
  refine iSup₂_le fun t ht => ?_
  exact le_iSup₂ (f := fun t _ => adv t q q')
    (fun q => t (r ∥ q)) (IsClosedUnderPar.test_par_left r ht)

/-- MauRen11 Definition 2 equation (3), as in Lemma 1, from the two ordered
fixed-context inequalities and the triangle inequality. -/
theorem edistD_par_par_le [Par Φ] [D.IsClosedUnderPar] (a a' b b' : Φ) :
    D.edistD (a ∥ b) (a' ∥ b') ≤ D.edistD a a' + D.edistD b b' := by
  calc
    D.edistD (a ∥ b) (a' ∥ b')
        ≤ D.edistD (a ∥ b) (a' ∥ b) + D.edistD (a' ∥ b) (a' ∥ b') :=
      D.edistD_triangle _ _ _
    _ ≤ D.edistD a a' + D.edistD b b' :=
      add_le_add (D.edistD_par_left_le a a' b)
        (D.edistD_par_right_le a' b b')

/-- The pseudo-emetric `Δ^𝒟` induced by a distinguisher class, satisfying
MauRen11 §2.2's axioms. -/
@[reducible] noncomputable def toPseudoEMetricSpace : PseudoEMetricSpace Φ where
  edist := D.edistD
  edist_self := D.edistD_self
  edist_comm := D.edistD_comm
  edist_triangle q q' q'' := D.edistD_triangle q q' q''

/-- MauRen11 §4.4 Def 2 eq. (4) as an `IsNonexpandingSMul` instance for the
class's own metric. -/
theorem isNonexpandingSMul :
    letI := D.toPseudoEMetricSpace; IsNonexpandingSMul Sigma Φ :=
  letI := D.toPseudoEMetricSpace
  ⟨fun c x y => by
    simp only [ENNReal.coe_one, one_mul]
    exact D.edistD_attach_le c x y⟩

/-- MauRen11 Definition 2 equation (3) and Lemma 1 as an `IsNonexpandingPar`
instance for this class's own metric. -/
theorem isNonexpandingPar [Par Φ] [D.IsClosedUnderPar] :
    letI := D.toPseudoEMetricSpace; IsNonexpandingPar Φ :=
  letI := D.toPseudoEMetricSpace
  ⟨D.edistD_par_par_le⟩

end DistinguisherClass

/-! ### Property-defined specifications -/

/-- The specification cut out by property tests `Ts`: resources on which
every defining test passes with certainty.  "Traditional security properties
like consistency and validity can naturally be understood as specifications"
(LiuMau20, abstract). -/
def propSpec (Ts : Set (Φ → ℝ≥0∞)) : Specification Φ := {q | ∀ t ∈ Ts, t q = 1}

/-- More defining tests is a stronger property specification. -/
theorem propSpec_antitone {Ts Ts' : Set (Φ → ℝ≥0∞)} (h : Ts ⊆ Ts') :
    propSpec (Φ := Φ) Ts' ⊆ propSpec Ts :=
  fun _ hq t ht => hq t (h ht)

/-- Property-spec membership is behavioral: within zero class-distance of a
resource satisfying the properties, they hold too. -/
theorem mem_propSpec_of_edistD_eq_zero [SMul Sigma Φ] (D : DistinguisherClass Sigma Φ)
    {Ts : Set (Φ → ℝ≥0∞)} (hTs : Ts ⊆ D.tests) {q q' : Φ}
    (hq' : q' ∈ propSpec Ts) (h0 : D.edistD q q' = 0) :
    q ∈ propSpec Ts := by
  intro t ht
  have h1 : t q' - t q = 0 :=
    le_antisymm (D.test_right_tsub_left_le_of_edistD_le (hTs ht) h0.le) (zero_le _)
  have h2 : t q - t q' = 0 :=
    le_antisymm (D.test_left_tsub_right_le_of_edistD_le (hTs ht) h0.le) (zero_le _)
  have hpass := hq' t ht
  refine le_antisymm ?_ ?_
  · rw [← hpass]; exact tsub_eq_zero_iff_le.mp h2
  · rw [← hpass]; exact tsub_eq_zero_iff_le.mp h1

/-- A resource within class-distance `ε` of a property specification
satisfies each defining test up to `ε`. -/
theorem one_tsub_le_test_of_close [SMul Sigma Φ] (D : DistinguisherClass Sigma Φ)
    {Ts : Set (Φ → ℝ≥0∞)} (hTs : Ts ⊆ D.tests) {q q' : Φ}
    (hq' : q' ∈ propSpec Ts) {ε : ℝ≥0∞} (hd : D.edistD q q' ≤ ε)
    {t : Φ → ℝ≥0∞} (ht : t ∈ Ts) :
    1 - ε ≤ t q := by
  have hpass := hq' t ht
  have hle : t q' - t q ≤ ε :=
    D.test_right_tsub_left_le_of_edistD_le (hTs ht) hd
  rw [hpass] at hle
  exact tsub_le_iff_right.mpr (tsub_le_iff_left.mp hle)

end AbstractCryptography
