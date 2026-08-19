/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import AbstractCryptography.Metric.Distinguisher

/-!
# The carrier taken up to equivalence (MauRen11 Definition 14)

**MR11-DEFERRED (provenance fence, 2026-08-17): MauRen11 constructs
quarantined pending the MR11 reconciliation task.  No MR16-track file may
import this module — enforced by `scripts/ledgerAudit.sh`.  See `LEDGER.md`
PROVENANCE FENCE.**

MauRen11 Definition 14 states its axioms with `≈`, not `=`: "`1ⁱR ≈ R` for
all `i ∈ I` and `R ∈ Φ`", "`αⁱβʲR ≈ βʲαⁱR` for all `i ≠ j`".  The equality-level
rendering in `AbstractCryptography.Algebra.Attachment` therefore applies only
after the carrier has been taken up to `≈`.

This file performs that step, once and generically.  `≈` is the zero set of the
class distance `Δ^𝒟` of `AbstractCryptography.Metric.Distinguisher`, so a model
supplies a distinguisher class and the algebra on presentations, where every law
is an equality, and receives the whole selected surface on `Behaviour`:

| supplied on `Φ`                        | obtained on `D.Behaviour`      |
|----------------------------------------|--------------------------------|
| `DistinguisherClass Sigma Φ`               | `EMetricSpace`                 |
| `test_attach` (Def 16's `𝒟Σ ⊆ 𝒟`)      | `IsNonexpandingSMul Sigma`         |
| `IsClosedUnderPar` (Lemma 1)           | `IsNonexpandingPar`            |
| `MulAction Sigma Φ`                        | `MulAction Sigma`                  |
| `Par Φ`                                | `Par`                          |
| `SMulParClass Sigma Φ`                     | `SMulParClass Sigma`               |

The distance is an `EMetricSpace`, not merely a pseudo one: `Δ^𝒟(R, S) = 0` is
by construction the relation quotiented out, so Definition 14's clauses (iii)
and (iv) "hold by construction, the carrier being taken up to `≈`" in the exact
sense that `edist = 0 ↔ =` on `Behaviour`.
-/

open scoped ENNReal

namespace AbstractCryptography

namespace DistinguisherClass

variable {Sigma Φ : Type*}

/-! ## Equivalence -/

section Equivalent

variable [SMul Sigma Φ] (D : DistinguisherClass Sigma Φ)

/-- MauRen11 Definition 14's `≈`: no admitted test separates the two
resources.  Equivalently, §6.1's class distance `Δ^𝒟` between them is zero. -/
def Equivalent (q q' : Φ) : Prop := D.edistD q q' = 0

theorem equivalent_refl (q : Φ) : D.Equivalent q q := D.edistD_self q

theorem equivalent_symm {q q' : Φ} (h : D.Equivalent q q') : D.Equivalent q' q := by
  rwa [Equivalent, D.edistD_comm]

theorem equivalent_trans {q q' q'' : Φ} (h : D.Equivalent q q')
    (h' : D.Equivalent q' q'') : D.Equivalent q q'' := by
  show D.edistD q q'' = 0
  have step := D.edistD_triangle q q' q''
  rw [show D.edistD q q' = 0 from h, show D.edistD q' q'' = 0 from h',
    add_zero] at step
  exact le_antisymm step (zero_le _)

/-- Every admitted test agrees on equivalent resources, in both directions.
This is the operational reading of `≈`. -/
theorem test_eq_of_equivalent {t : Φ → ℝ≥0∞} (ht : t ∈ D.tests) {q q' : Φ}
    (h : D.Equivalent q q') : t q - t q' = 0 ∧ t q' - t q = 0 :=
  ⟨le_antisymm (D.test_left_tsub_right_le_of_edistD_le ht h.le) (zero_le _),
   le_antisymm (D.test_right_tsub_left_le_of_edistD_le ht h.le) (zero_le _)⟩

/-- The class distance is an invariant of the equivalence classes of its own
zero set, which is what lets it descend to the quotient. -/
theorem edistD_congr {q₁ q₁' q₂ q₂' : Φ} (h₁ : D.Equivalent q₁ q₁')
    (h₂ : D.Equivalent q₂ q₂') : D.edistD q₁ q₂ = D.edistD q₁' q₂' := by
  have mono : ∀ {a a' b b' : Φ}, D.Equivalent a a' → D.Equivalent b b' →
      D.edistD a b ≤ D.edistD a' b' := by
    intro a a' b b' ha hb
    have ha' : D.edistD a a' = 0 := ha
    have hb' : D.edistD b' b = 0 := D.equivalent_symm hb
    calc D.edistD a b ≤ D.edistD a a' + D.edistD a' b := D.edistD_triangle a a' b
      _ ≤ D.edistD a a' + (D.edistD a' b' + D.edistD b' b) :=
          add_le_add le_rfl (D.edistD_triangle a' b' b)
      _ = D.edistD a' b' := by rw [ha', hb', add_zero, zero_add]
  exact le_antisymm (mono h₁ h₂) (mono (D.equivalent_symm h₁) (D.equivalent_symm h₂))

/-- The setoid cut out by `≈`. -/
def setoid : Setoid Φ where
  r := D.Equivalent
  iseqv := ⟨D.equivalent_refl, D.equivalent_symm, D.equivalent_trans⟩

/-- MauRen11 Definition 14's carrier: `Φ` taken up to `≈`.  Definition 14's
axioms are equalities here. -/
def Behaviour : Type _ := Quotient D.setoid

/-- The equivalence class of a resource presentation. -/
def toBehaviour (q : Φ) : D.Behaviour := Quotient.mk D.setoid q

theorem toBehaviour_surjective : Function.Surjective D.toBehaviour :=
  Quotient.exists_rep

@[simp] theorem toBehaviour_eq_iff {q q' : Φ} :
    D.toBehaviour q = D.toBehaviour q' ↔ D.Equivalent q q' := by
  show Quotient.mk D.setoid q = Quotient.mk D.setoid q' ↔ _
  exact ⟨Quotient.exact, Quotient.sound (s := D.setoid)⟩

@[elab_as_elim] theorem Behaviour.ind {motive : D.Behaviour → Prop}
    (h : ∀ q, motive (D.toBehaviour q)) : ∀ R, motive R := Quotient.ind h

@[elab_as_elim] theorem Behaviour.ind₂ {motive : D.Behaviour → D.Behaviour → Prop}
    (h : ∀ q q', motive (D.toBehaviour q) (D.toBehaviour q')) : ∀ R S, motive R S :=
  Quotient.ind₂ h

end Equivalent

/-! ## The metric

MauRen11 §6.1's `Δ^𝒟` descends, and on the quotient it separates points. -/

section Metric

variable [SMul Sigma Φ] (D : DistinguisherClass Sigma Φ)

noncomputable instance instEDist : EDist D.Behaviour where
  edist := Quotient.lift₂ D.edistD fun _ _ _ _ h₁ h₂ => D.edistD_congr h₁ h₂

@[simp] theorem edist_toBehaviour (q q' : Φ) :
    edist (D.toBehaviour q) (D.toBehaviour q') = D.edistD q q' := rfl

noncomputable instance instEMetricSpace : EMetricSpace D.Behaviour where
  edist_self := Behaviour.ind D fun q => D.edistD_self q
  edist_comm := Behaviour.ind₂ D fun q q' => D.edistD_comm q q'
  edist_triangle R S T := by
    induction R using Behaviour.ind with | _ q =>
    induction S using Behaviour.ind with | _ q' =>
    induction T using Behaviour.ind with | _ q'' =>
    exact D.edistD_triangle q q' q''
  eq_of_edist_eq_zero {R S} h := by
    induction R using Behaviour.ind with | _ q =>
    induction S using Behaviour.ind with | _ q' =>
    exact Quotient.sound h

/-- Definition 15's binary-output bound survives the quotient. -/
theorem edist_le_one (R S : D.Behaviour) : edist R S ≤ 1 := by
  induction R using Behaviour.ind with | _ q =>
  induction S using Behaviour.ind with | _ q' =>
  exact D.edistD_le_one q q'

end Metric

/-! ## Converter attachment

Definition 16's closure `𝒟Σ ⊆ 𝒟` is exactly what makes the action descend, and
the same closure makes it non-expanding — Definition 2 eq. (4). -/

section Action

variable [Monoid Sigma] [MulAction Sigma Φ] (D : DistinguisherClass Sigma Φ)

theorem equivalent_smul (c : Sigma) {q q' : Φ} (h : D.Equivalent q q') :
    D.Equivalent (c • q) (c • q') :=
  le_antisymm (h ▸ D.edistD_attach_le c q q') (zero_le _)

instance instSMul : SMul Sigma D.Behaviour where
  smul c := Quotient.map (c • ·) fun _ _ h => D.equivalent_smul c h

@[simp] theorem smul_toBehaviour (c : Sigma) (q : Φ) :
    c • D.toBehaviour q = D.toBehaviour (c • q) := rfl

instance instMulAction : MulAction Sigma D.Behaviour where
  one_smul := Behaviour.ind D fun q => by simp
  mul_smul c c' := Behaviour.ind D fun q => by simp [mul_smul]

/-- MauRen11 Definition 2 eq. (4), `d(αⁱR, αⁱS) ≤ d(R, S)`, on the quotient. -/
instance instIsNonexpandingSMul : IsNonexpandingSMul Sigma D.Behaviour where
  lipschitz_smul c := LipschitzWith.of_edist_le fun R S => by
    induction R using Behaviour.ind with | _ q =>
    induction S using Behaviour.ind with | _ q' =>
    simpa using D.edistD_attach_le c q q'

end Action

/-! ## Parallel composition

Lemma 1's two ordered closures make `‖` descend and make it non-expanding —
Definition 2 eq. (3). -/

section Parallel

variable [SMul Sigma Φ] [Par Φ] (D : DistinguisherClass Sigma Φ) [D.IsClosedUnderPar]

theorem equivalent_par {a a' b b' : Φ} (ha : D.Equivalent a a')
    (hb : D.Equivalent b b') : D.Equivalent (a ∥ b) (a' ∥ b') := by
  show D.edistD (a ∥ b) (a' ∥ b') = 0
  have step := D.edistD_par_par_le a a' b b'
  rw [show D.edistD a a' = 0 from ha, show D.edistD b b' = 0 from hb,
    add_zero] at step
  exact le_antisymm step (zero_le _)

instance instPar : Par D.Behaviour where
  par := Quotient.map₂ (· ∥ ·) fun _ _ ha _ _ hb => D.equivalent_par ha hb

@[simp] theorem par_toBehaviour (q q' : Φ) :
    D.toBehaviour q ∥ D.toBehaviour q' = D.toBehaviour (q ∥ q') := rfl

/-- MauRen11 Definition 2 eq. (3), via Lemma 1, on the quotient. -/
instance instIsNonexpandingPar : IsNonexpandingPar D.Behaviour where
  edist_par_par_le a a' b b' := by
    induction a using Behaviour.ind with | _ qa =>
    induction a' using Behaviour.ind with | _ qa' =>
    induction b using Behaviour.ind with | _ qb =>
    induction b' using Behaviour.ind with | _ qb' =>
    exact D.edistD_par_par_le qa qa' qb qb'

end Parallel

/-! ## Parallel converters

MauRen11 §6.2's `(α|β)ⁱ(R‖S) := αⁱR ‖ βⁱS` is an equation between
presentations, so it descends by congruence with no metric input. -/

section ParallelAction

variable [Monoid Sigma] [MulAction Sigma Φ] [Par Sigma] [Par Φ] [SMulParClass Sigma Φ]
  (D : DistinguisherClass Sigma Φ) [D.IsClosedUnderPar]

instance instSMulParClass : SMulParClass Sigma D.Behaviour where
  smul_par α β R S := by
    induction R using Behaviour.ind with | _ q =>
    induction S using Behaviour.ind with | _ q' =>
    exact congrArg D.toBehaviour (smul_par α β q q')

end ParallelAction

end DistinguisherClass

end AbstractCryptography
