import RandomSystems.DDC.Absorb
import RandomSystems.System.DDE
import Probability.StatisticalDistance

/-!
# Environments and distinguishers

An environment (DDE) generates the next query from the replies so far and stops when its
next query is undefined; it outputs no decision. A distinguisher (DDD) is a system with a
trigger and a bit output, with a finite interaction discipline. An environment with a test
of its completed transcript is a distinguisher, and the queries of a distinguisher form an
environment. Source: Lanzenberger, Definitions 2.11–2.12 and 2.26 (printed pp. 14, 18).

## Main definitions

* `eRun`, `tr E n s`: the run of an environment against a total system
* `envProbe E A`: an environment with a transcript test, as a distinguisher
* `ddeOf hD`: the queries of a distinguisher, as an environment
* `DPort.map`, `trigMap`, `decMap`: relabeling a distinguisher

## Main results

* `envProbe_isDDD`, `envOf_envProbe`: the probe is a distinguisher and asks the
  environment's queries
* `ddeOf_bounded`: a distinguisher's environment is query-bounded
* `IsDDD.relabel`: relabeling keeps a distinguisher
* `abs_mass_sub_le_statDist`, `abs_average_sub_le`: distinguishing probabilities are
  bounded by statistical distance
-/

set_option linter.unusedSimpArgs false

namespace SystemAlgebra

open Classical
open Probability (Distribution statDist)

variable {X Y K : Type}

/-! ## The run of an environment against a total system -/

section Run

/-- Total resources on labels `K`: the samples of a probabilistic resource. -/
abbrev TotRes (X Y K : Type) := {R : SingleAlphabetSystem X Y K // TotalResource R}

/-- The reply of a total resource to a nonempty history. -/
noncomputable def reply (s : TotRes X Y K) (h : List (Σ _ : K, X)) (hne : h ≠ []) : Σ _ : K, Y :=
  (s.1 h).get ((s.2.1 h).mpr hne)

variable (e : List (Σ _ : K, Y) →. Σ _ : K, X) (s : TotRes X Y K)

/-- The first `n` rounds of the environment `e` against `s`: queries and replies. -/
noncomputable def eRun : ℕ → List (Σ _ : K, X) × List (Σ _ : K, Y)
  | 0 => ([], [])
  | n + 1 =>
    let p := eRun n
    if hd : (e p.2).Dom then
      (p.1 ++ [(e p.2).get hd],
        p.2 ++ [reply s (p.1 ++ [(e p.2).get hd]) (by simp)])
    else p

theorem eRun_succ_of_dom (n : ℕ) (hd : (e (eRun e s n).2).Dom) :
    eRun e s (n + 1) = ((eRun e s n).1 ++ [(e (eRun e s n).2).get hd],
      (eRun e s n).2 ++ [reply s ((eRun e s n).1 ++ [(e (eRun e s n).2).get hd]) (by simp)]) := by
  simp only [eRun, dif_pos hd]

theorem eRun_succ_of_not_dom (n : ℕ) (hd : ¬ (e (eRun e s n).2).Dom) :
    eRun e s (n + 1) = eRun e s n := by
  simp only [eRun, dif_neg hd]

theorem reply_mem (h : List (Σ _ : K, X)) (x : Σ _ : K, X) :
    reply s (h ++ [x]) (by simp) ∈ s.1 (h ++ [x]) :=
  Part.get_mem _

end Run

/-- The transcript of `s` with `E` after at most `n` rounds. -/
noncomputable def tr (E : DDE (Σ _ : K, X) (Σ _ : K, Y)) (n : ℕ) (s : TotRes X Y K) :
    List (Σ _ : K, X) × List (Σ _ : K, Y) :=
  eRun E.1 s n

/-! ## The queries of a transcript are a function of its replies -/

section Queries

/-- The queries of `e` along the replies `ys`. -/
noncomputable def qsOf {A B : Type} (e : List B →. A) (ys : List B) : List A :=
  (List.range ys.length).filterMap fun k => (e (ys.take k)).toOption

theorem qsOf_snoc {A B : Type} {e : List B →. A} {ys : List B} {x y}
    (hx : x ∈ e ys) : qsOf e (ys ++ [y]) = qsOf e ys ++ [x] := by
  unfold qsOf
  rw [List.length_append, List.length_singleton, List.range_succ, List.filterMap_append]
  congr 1
  · refine List.filterMap_congr fun k hk => ?_
    rw [List.take_append_of_le_length (List.mem_range.mp hk).le]
  · simp [List.take_left', Part.toOption_eq_some_iff.mpr hx]

theorem eRun_fst (e : List (Σ _ : K, Y) →. Σ _ : K, X) (s : TotRes X Y K) :
    ∀ m, (eRun e s m).1 = qsOf e (eRun e s m).2 := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    by_cases hd : (e (eRun e s m).2).Dom
    · rw [eRun_succ_of_dom e s m hd]
      simp only
      rw [qsOf_snoc (Part.get_mem hd), ih]
    · rw [eRun_succ_of_not_dom e s m hd, ih]

theorem tr_fst (E : DDE (Σ _ : K, X) (Σ _ : K, Y)) (n : ℕ) (s : TotRes X Y K) :
    (tr E n s).1 = qsOf E.1 (tr E n s).2 :=
  eRun_fst _ _ _

/-- Runs of two environments that agree along the run coincide. -/
theorem eRun_congr {e e' : List (Σ _ : K, Y) →. Σ _ : K, X} (s : TotRes X Y K)
    (H : ∀ m, e' (eRun e s m).2 = e (eRun e s m).2) : ∀ m, eRun e' s m = eRun e s m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    by_cases hd : (e (eRun e s m).2).Dom
    · have hd' : (e' (eRun e' s m).2).Dom := by rw [ih, H m]; exact hd
      rw [eRun_succ_of_dom e' s m hd', eRun_succ_of_dom e s m hd]
      have hx : ∀ h, (e' (eRun e s m).2).get h = (e (eRun e s m).2).get hd := fun h =>
        Part.get_eq_of_mem (by rw [H m]; exact Part.get_mem hd) h
      simp only [ih, hx]
    · have hd' : ¬ (e' (eRun e' s m).2).Dom := by rw [ih, H m]; exact hd
      rw [eRun_succ_of_not_dom e' s m hd', eRun_succ_of_not_dom e s m hd, ih]

end Queries

/-! ## An environment with a test is a decision-producing distinguisher -/

section EnvProbe

variable {Xi Yi : K → Type}

/-- Replies `ys` along which `e` queried at the labels answered. -/
def EFits (e : List (Σ i, Yi i) →. Σ i, Xi i) (ys : List (Σ i, Yi i)) : Prop :=
  ∀ k (hk : k < ys.length), ∃ x ∈ e (ys.take k), (ys[k]'hk).1 = x.1

variable {e : List (Σ i, Yi i) →. Σ i, Xi i}

theorem EFits.nil : EFits e [] := fun k hk => absurd hk (by simp)

theorem EFits.of_snoc {ys : List (Σ i, Yi i)} {y} (hv : EFits e (ys ++ [y])) :
    EFits e ys ∧ ∃ x ∈ e ys, y.1 = x.1 := by
  refine ⟨fun k hk => ?_, ?_⟩
  · obtain ⟨x, hx, hl⟩ := hv k (by simp; omega)
    rw [List.take_append_of_le_length hk.le] at hx
    exact ⟨x, hx, by simpa [List.getElem_append_left hk] using hl⟩
  · obtain ⟨x, hx, hl⟩ := hv ys.length (by simp)
    rw [List.take_left' rfl] at hx
    exact ⟨x, hx, by simpa using hl⟩

theorem EFits.snoc {ys : List (Σ i, Yi i)} (hv : EFits e ys) {x y} (hx : x ∈ e ys)
    (hy : y.1 = x.1) : EFits e (ys ++ [y]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  by_cases hlt : k < ys.length
  · obtain ⟨x', hx', hl⟩ := hv k hlt
    rw [List.take_append_of_le_length hlt.le]
    exact ⟨x', hx', by simpa [List.getElem_append_left hlt] using hl⟩
  · have e' : k = ys.length := by omega
    subst e'
    rw [List.take_left' rfl]
    exact ⟨x, hx, by simpa using hy⟩

variable (E : DDE (Σ i, Xi i) (Σ i, Yi i))
  (A : List (Σ i, Xi i) × List (Σ i, Yi i) → Prop)

/-- The next output: the environment's query, or the test of the completed transcript. -/
noncomputable def envReply (ys : List (Σ i, Yi i)) : Part (Σ p, dOut Xi p) :=
  if h : (E.1 ys).Dom then Part.some ⟨.res ((E.1 ys).get h).1, ((E.1 ys).get h).2⟩
  else Part.some ⟨.dec, decide (A (qsOf E.1 ys, ys))⟩

/-- **The environment `E` with the test `A`** as a decision-producing distinguisher. It is
silent on replies at the wrong label. -/
noncomputable def envProbe : DDD K Xi Yi
  | ⟨.start, _⟩ :: ws =>
    if hv : ∃ ys, ws = ys.map envIn ∧ EFits E.1 ys then envReply E A (Classical.choose hv)
    else Part.none
  | _ => Part.none

variable {E A}

theorem envProbe_dHist {ys : List (Σ i, Yi i)} (hv : EFits E.1 ys) :
    envProbe E A (dHist ys) = envReply E A ys := by
  have hex : ∃ ys', ys.map envIn = ys'.map envIn ∧ EFits E.1 ys' := ⟨ys, rfl, hv⟩
  simp only [envProbe, dHist, dif_pos hex]
  have e : Classical.choose hex = ys :=
    (List.map_injective_iff.mpr envIn_injective (Classical.choose_spec hex).1).symm
  rw [e]

theorem envProbe_dom {w} (hd : (envProbe E A w).Dom) : ∃ ys, w = dHist ys ∧ EFits E.1 ys := by
  match w, hd with
  | ⟨.start, ()⟩ :: ws, hd =>
    simp only [envProbe] at hd
    split_ifs at hd with hv
    · exact ⟨Classical.choose hv, by rw [dHist, ← (Classical.choose_spec hv).1],
        (Classical.choose_spec hv).2⟩
    · exact hd.elim
  | [], hd => exact hd.elim
  | ⟨.dec, e⟩ :: _, _ => exact e.elim
  | ⟨.res _, _⟩ :: _, hd => exact hd.elim

theorem envReply_of_mem {ys : List (Σ i, Yi i)} {x} (hx : x ∈ E.1 ys) :
    envReply E A ys = Part.some ⟨.res x.1, x.2⟩ := by
  have hd : (E.1 ys).Dom := Part.dom_iff_mem.mpr ⟨x, hx⟩
  unfold envReply
  rw [dif_pos hd]
  obtain rfl := Part.get_eq_of_mem hx hd
  rfl

variable {n : ℕ}

theorem envProbe_finite (hE : QueryBounded n E) : Finite (n + 1) (envProbe E A) := by
  intro w hd
  obtain ⟨ys, rfl, hv⟩ := envProbe_dom hd
  simp only [dHist, List.length_cons, List.length_map]
  rcases List.eq_nil_or_concat ys with rfl | ⟨ys₀, y, rfl⟩
  · simp
  · rw [List.concat_eq_append] at hv ⊢
    obtain ⟨-, x, hx, -⟩ := hv.of_snoc
    have := hE _ (Part.dom_iff_mem.mpr ⟨x, hx⟩)
    simp; omega

/-- **`envProbe E A` is a DDD**, with bound `n + 1` for an environment with query bound `n`. -/
theorem envProbe_isDDD (hE : QueryBounded n E) : IsDDD (envProbe E A) := by
  refine ⟨?_, ⟨n + 1, envProbe_finite hE⟩, ?_, ?_, ?_⟩
  · simp [SilentAtEmpty, envProbe]
  · intro w z hr
    obtain ⟨ys', e, -⟩ := envProbe_dom (reach_snoc_iff.mp hr).2
    rcases dHist_snoc_inv e with ⟨rfl, rfl⟩ | ⟨ys, y, rfl, rfl, rfl⟩
    · simp
    · simp [dHist_ne_nil, envIn]
  · intro w z i hr hl
    obtain ⟨ys', e, hv'⟩ := envProbe_dom (reach_snoc_iff.mp hr).2
    rcases dHist_snoc_inv e with ⟨rfl, rfl⟩ | ⟨ys, y, rfl, rfl, rfl⟩
    · simp [replyLabel, envProbe] at hl
    · obtain ⟨hv, x, hx, hyx⟩ := hv'.of_snoc
      rw [replyLabel, envProbe_dHist hv, envReply_of_mem hx] at hl
      simp only [Part.some_dom, dite_true, Part.get_some, Option.some.injEq, DPort.res.injEq] at hl
      simp [envIn, hyx, hl]
  · intro w z hr hl
    obtain ⟨ys', e, hv'⟩ := envProbe_dom (reach_snoc_iff.mp hr).2
    rcases dHist_snoc_inv e with ⟨rfl, rfl⟩ | ⟨ys, y, rfl, rfl, rfl⟩
    · simp [replyLabel, envProbe] at hl
    · obtain ⟨hv, x, hx, -⟩ := hv'.of_snoc
      rw [replyLabel, envProbe_dHist hv, envReply_of_mem hx] at hl
      simp at hl

theorem envOf_envProbe {ys : List (Σ i, Yi i)} (hv : EFits E.1 ys) :
    envOf (envProbe E A) ys = E.1 ys := by
  unfold envOf
  rw [envProbe_dHist hv]
  by_cases hd : (E.1 ys).Dom
  · rw [envReply_of_mem (Part.get_mem hd)]
    simp only [Part.bind_some, query]
    exact (Part.get_eq_iff_eq_some.mp rfl).symm
  · simp only [envReply, dif_neg hd, Part.bind_some, query]
    exact (Part.eq_none_iff'.mpr hd).symm

end EnvProbe

section TotalEnvProbe

variable {E : DDE (Σ _ : K, X) (Σ _ : K, Y)}
  {A : List (Σ _ : K, X) × List (Σ _ : K, Y) → Prop} {n : ℕ}

theorem eRun_fits (s : TotRes X Y K) : ∀ m, EFits E.1 (eRun E.1 s m).2 := by
  intro m
  induction m with
  | zero => exact EFits.nil
  | succ m ih =>
    by_cases hd : (E.1 (eRun E.1 s m).2).Dom
    · rw [eRun_succ_of_dom _ s m hd]
      exact ih.snoc (Part.get_mem hd) (s.2.2 _ _ _ (reply_mem s _ _))
    · rw [eRun_succ_of_not_dom _ s m hd]; exact ih

theorem eRun_envProbe (s : TotRes X Y K) (m : ℕ) :
    eRun (envOf (envProbe E A)) s m = eRun E.1 s m :=
  eRun_congr s (fun m => envOf_envProbe (eRun_fits s m)) m

end TotalEnvProbe

/-! ## A distinguisher's bit is determined by its transcript -/

section OfDDD

variable {Xi Yi : K → Type} {D : DDD K Xi Yi}

/-- The environment of the queries of a distinguisher, on its reachable part. -/
noncomputable def ddeOf (hD : IsDDD D) : DDE (Σ i, Xi i) (Σ i, Yi i) :=
  ⟨envOf (trim D), fun ys y hd => by
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hd
    rw [mem_envOf] at hx
    have hr : Reach D (dHist (ys ++ [y])) := by
      by_contra h; simp [trim, h] at hx
    rw [show dHist (ys ++ [y]) = dHist ys ++ [envIn y] by simp [dHist]] at hr
    have hr₀ := (reach_snoc_iff.mp hr).1
    have hd₀ : (D (dHist ys)).Dom := hr₀ _ [] (by simp) (dHist_ne_nil ys)
    have hne := hD.2.2.2.2 _ _ hr
    obtain ⟨o, ho⟩ := Part.dom_iff_mem.mp hd₀
    rcases o with ⟨_ | _ | i, v⟩
    · exact v.elim
    · exact absurd (replyLabel_of_mem D ho) hne
    · refine Part.dom_iff_mem.mpr ⟨⟨i, v⟩, mem_envOf.mpr ?_⟩
      simp only [trim, if_pos hr₀]
      exact ho⟩

/-- The environment of a distinguisher's queries is bounded by the distinguisher's bound. -/
theorem ddeOf_bounded (hD : IsDDD D) : QueryBounded hD.2.1.choose (ddeOf hD) := by
  intro ys hd
  obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hd
  have hx : x ∈ envOf (trim D) ys := hx
  rw [mem_envOf] at hx
  have hd' : (D (dHist ys)).Dom := by
    by_cases h : Reach D (dHist ys)
    · simp only [trim, if_pos h] at hx; exact Part.dom_iff_mem.mpr ⟨_, hx⟩
    · simp [trim, h] at hx
  have := hD.2.1.choose_spec _ hd'
  simp [dHist] at this
  omega

theorem finite_trim {n : ℕ} {s : System X Y} (hs : Finite n s) : Finite n (trim s) := by
  intro h hd
  apply hs
  by_contra hn
  by_cases hr : Reach s h
  · simp [trim, hr] at hd; exact hn hd
  · simp [trim, hr] at hd

end OfDDD

theorem abs_mass_sub_le_statDist {S : Type} (P Q : Distribution.ProbDist S) (A : S → Prop) :
    |P.1.mass A - Q.1.mass A| ≤ statDist P.1 Q.1 := by
  rw [abs_le]
  refine ⟨?_, Probability.mass_sub_mass_le_statDist _ _ _⟩
  have h := Probability.mass_sub_mass_le_statDist Q.1 P.1 A
  rw [Probability.statDist_symm_of_eq_weight _ _ (by rw [P.2.2, Q.2.2])] at h
  linarith

/-! ## Distinguisher utilities -/

section Utilities

/-- Closing with the reachable part of an environment decides as closing with the
environment. -/
theorem close_trim_start {I : Type} {Xf Yf : I → Type} (D : DDD I Xf Yf) (R : InterfaceSystem I Xf Yf) :
    close (trim D) R [startIn] = close D R [startIn] := by
  rw [close_eq, close_eq]
  have hb := EqOnReachable.interconnect (EqOnReachable.pair_left (trim_behEq D) R) closeRoute closeInj
  by_cases hr : Reach (interconnect (pair (trim D) R) closeRoute closeInj) [startIn]
  · exact hb.2 _ hr (by simp)
  · have hr' := (not_congr (hb.1 _)).mp hr
    rw [show ([startIn] : List (Σ l : Free (closeSet I), twoFam (dIn Yf) Xf l.1)) = [] ++ [startIn]
      from rfl, reach_snoc_iff] at hr hr'
    simp only [reach_nil, true_and] at hr hr'
    exact (Part.eq_none_iff'.mpr hr).trans (Part.eq_none_iff'.mpr hr').symm

/-- **Averaging.** Under a probability distribution, a pointwise bound on a difference
bounds the difference of the averages. -/
theorem abs_average_sub_le {S : Type} (A : Distribution.ProbDist S) (f g : S → ℝ) {ε : ℝ}
    (h : ∀ a, |f a - g a| ≤ ε) :
    |A.1.sum (fun a w => w * f a) - A.1.sum (fun a w => w * g a)| ≤ ε := by
  have hw : A.1.sum (fun _ w => w) = 1 := A.2.2
  unfold Finsupp.sum at hw ⊢
  rw [← Finset.sum_sub_distrib]
  calc |∑ a ∈ A.1.support, (A.1 a * f a - A.1 a * g a)|
      ≤ ∑ a ∈ A.1.support, |A.1 a * f a - A.1 a * g a| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a ∈ A.1.support, A.1 a * |f a - g a| := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg (A.2.1 a)]
    _ ≤ ∑ a ∈ A.1.support, A.1 a * ε :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (A.2.1 a)
    _ = ε := by rw [← Finset.sum_mul, hw, one_mul]

end Utilities

/-! ## Renaming the labels of a distinguisher -/

section RelabelDDD

/-- Rename the labels of an environment port. -/
def DPort.map {L L' : Type} (σ : L → L') : DPort L → DPort L'
  | .start => .start
  | .dec => .dec
  | .res i => .res (σ i)

variable {L L' : Type} {F G : DPort L → Type} {F' G' : DPort L' → Type}

theorem reach_relabel_iff (D : InterfaceSystem (DPort L) F G) (f : (Σ p, F' p) → Σ p, F p)
    (g : (Σ p, G p) → Σ p, G' p) (h : List (Σ p, F' p)) :
    Reach (relabel D f g) h ↔ Reach D (h.map f) := by
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h z ih =>
    rw [reach_snoc_iff, ih, List.map_append, List.map_singleton, reach_snoc_iff]
    simp [relabel]

theorem replyLabel_relabel (D : InterfaceSystem (DPort L) F G) (f : (Σ p, F' p) → Σ p, F p)
    (g : (Σ p, G p) → Σ p, G' p) (σ : L' ≃ L) (hg : ∀ y, (g y).1 = DPort.map σ.symm y.1)
    (h : List (Σ p, F' p)) :
    replyLabel (relabel D f g) h = (replyLabel D (h.map f)).map (DPort.map σ.symm) := by
  unfold replyLabel
  by_cases hd : (D (h.map f)).Dom
  · have hd' : (relabel D f g h).Dom := by simpa [relabel] using hd
    rw [dif_pos hd, dif_pos hd']
    exact congrArg some (hg _)
  · have hd' : ¬ (relabel D f g h).Dom := by simpa [relabel] using hd
    rw [dif_neg hd, dif_neg hd']
    rfl

/-- **Renaming the labels of a distinguisher along a bijection gives a distinguisher.** -/
theorem IsDDD.relabel {D : InterfaceSystem (DPort L) F G} (hD : IsDDD D) (f : (Σ p, F' p) → Σ p, F p)
    (g : (Σ p, G p) → Σ p, G' p) (σ : L' ≃ L) (hf : ∀ z, (f z).1 = DPort.map σ z.1)
    (hg : ∀ y, (g y).1 = DPort.map σ.symm y.1) : IsDDD (SystemAlgebra.relabel D f g) := by
  obtain ⟨hre, ⟨n, hn⟩, htr, hres, hdec⟩ := hD
  have hstart : ∀ p : DPort L', DPort.map σ p = .start ↔ p = .start := by
    intro p; cases p <;> simp [DPort.map]
  refine ⟨?_, ⟨n, fun h hd => ?_⟩, fun h z hr => ?_, fun h z i hr hl => ?_, fun h z hr hl => ?_⟩
  · simpa [SilentAtEmpty, SystemAlgebra.relabel] using hre
  · have := hn _ (by simpa [SystemAlgebra.relabel] using hd)
    simpa using this
  · rw [reach_relabel_iff, List.map_append, List.map_singleton] at hr
    have := htr _ _ hr
    rw [List.map_eq_nil_iff, hf, hstart] at this
    exact this
  · rw [reach_relabel_iff, List.map_append, List.map_singleton] at hr
    rw [replyLabel_relabel D f g σ hg] at hl
    obtain ⟨q, hq, e⟩ := Option.map_eq_some_iff.mp hl
    rcases q with _ | _ | i'
    · simp [DPort.map] at e
    · simp [DPort.map] at e
    · simp only [DPort.map, DPort.res.injEq] at e
      have := hres _ _ _ hr hq
      rw [hf] at this
      rcases hz : z.1 with _ | _ | i''
      · rw [hz] at this; simp [DPort.map] at this
      · rw [hz] at this; simp [DPort.map] at this
      · rw [hz] at this
        simp only [DPort.map, DPort.res.injEq] at this
        rw [← e, ← this]
        simp
  · rw [reach_relabel_iff, List.map_append, List.map_singleton] at hr
    rw [replyLabel_relabel D f g σ hg] at hl
    obtain ⟨q, hq, e⟩ := Option.map_eq_some_iff.mp hl
    rcases q with _ | _ | i'
    · simp [DPort.map] at e
    · exact hdec _ _ hr hq
    · simp [DPort.map] at e

end RelabelDDD

/-! ## Closing two systems side by side -/

section Neighbour

/-- The labels of `[R, S]`, read on `K ⊕ K'`. -/
def twoSum (K K' : Type) : Two K K' ≃ K ⊕ K' where
  toFun
    | ⟨none, k⟩ => .inl k
    | ⟨some (), k⟩ => .inr k
  invFun
    | .inl k => ⟨none, k⟩
    | .inr k => ⟨some (), k⟩
  left_inv := by rintro ⟨_ | ⟨⟨⟩⟩, k⟩ <;> rfl
  right_inv := by rintro (k | k) <;> rfl

/-- The trigger, between two closed systems. -/
def trigMap {I I' : Type} {Xf Yf : I → Type} {Xf' Yf' : I' → Type} :
    (Σ l : Free (closeSet I), twoFam (dIn Yf) Xf l.1) → Σ l : Free (closeSet I'), twoFam (dIn Yf') Xf' l.1
  | ⟨⟨⟨none, .start⟩, _⟩, u⟩ => ⟨⟨⟨none, .start⟩, id⟩, u⟩
  | ⟨⟨⟨none, .dec⟩, _⟩, e⟩ => e.elim
  | ⟨⟨⟨none, .res i⟩, h⟩, _⟩ => absurd (res_mem_closeSet i) h
  | ⟨⟨⟨some (), i⟩, h⟩, _⟩ => absurd (sys_mem_closeSet i) h

/-- The decision, between two closed systems. -/
def decMap {I I' : Type} {Xf Yf : I → Type} {Xf' Yf' : I' → Type} :
    (Σ l : Free (closeSet I), twoFam (dOut Xf) Yf l.1) → Σ l : Free (closeSet I'), twoFam (dOut Xf') Yf' l.1
  | ⟨⟨⟨none, .start⟩, _⟩, e⟩ => e.elim
  | ⟨⟨⟨none, .dec⟩, _⟩, b⟩ => ⟨⟨⟨none, .dec⟩, id⟩, b⟩
  | ⟨⟨⟨none, .res i⟩, h⟩, _⟩ => absurd (res_mem_closeSet i) h
  | ⟨⟨⟨some (), i⟩, h⟩, _⟩ => absurd (sys_mem_closeSet i) h

theorem trigMap_eq {I I' : Type} {Xf Yf : I → Type} {Xf' Yf' : I' → Type} (z) :
    trigMap (Xf := Xf) (Yf := Yf) (Xf' := Xf') (Yf' := Yf') z = startIn := by
  rcases z with ⟨⟨⟨_ | ⟨⟨⟩⟩, l⟩, hl⟩, v⟩
  · rcases l with _ | _ | i
    · rfl
    · exact v.elim
    · exact absurd (res_mem_closeSet i) hl
  · exact absurd (sys_mem_closeSet l) hl

/-- Maps sending decisions to decisions do not change whether `1` is decided. -/
theorem decOut_mem_map_iff {I I' : Type} {Xf Yf : I → Type} {Xf' Yf' : I' → Type}
    (g : (Σ l : Free (closeSet I), twoFam (dOut Xf) Yf l.1) → Σ l : Free (closeSet I'), twoFam (dOut Xf') Yf' l.1)
    (hg : ∀ b, g (decOut b) = decOut b) (P : Part (Σ l : Free (closeSet I), twoFam (dOut Xf) Yf l.1))
    (c : Bool) : decOut c ∈ P.map g ↔ decOut c ∈ P := by
  constructor
  · intro h
    obtain ⟨z, hz, e⟩ := Part.mem_map_iff _ |>.mp h
    obtain ⟨c', rfl⟩ := eq_decOut z
    rw [hg] at e
    obtain rfl := decOut_injective e
    exact hz
  · intro h
    exact Part.mem_map_iff _ |>.mpr ⟨_, h, hg c⟩

end Neighbour

end SystemAlgebra
