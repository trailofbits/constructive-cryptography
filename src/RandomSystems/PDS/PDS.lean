import RandomSystems.System.Replies
import Probability.Distribution

/-!
# Probabilistic discrete systems

A domain gives the admitted next queries after each transcript, with a bound on the
transcript length. A probabilistic discrete system (PDS) is a finite distribution over
deterministic systems with one common domain; its cumulative behavior is the mass of
the samples replying `ys` to `xs`. Source: Lanzenberger–Maurer, Definition 8 (printed p. 13).

## Main definitions

* `Domain A B`: the admitted next queries after each transcript, with a length bound
* `HasDomain D s`: `s` has domain `D`: it answers exactly the queries `D` admits along
  its transcripts
* `PDS A B D`: finite distributions over deterministic systems with domain `D`
* `behaviorMass P xs ys`: the cumulative behavior of a finite mixture
* `Equivalent P Q`: equality of cumulative behavior

## Main results

* `nextReply_apply`, `nextReply_weight_of_admitted`: the next-reply masses of a mixture
* `hasDomain_ofInputs_iff`: on an input domain `E`, having domain `E` is `dom(s) = E`
* `HasDomain.length_le`: transcripts stay within the domain's bound
-/

namespace SystemAlgebra

open Classical Probability

variable {A B : Type}

/-- Cumulative reply mass; the sample property does not impose totality or interface types. -/
noncomputable def behaviorMass {p : System A B → Prop}
    (P : Distribution {s : System A B // p s}) (xs : List A) (ys : List B) : ℝ :=
  P.mass fun s => Replies s.1 xs ys

theorem behaviorMass_ne_zero {p : System A B → Prop}
    {P : Distribution {s : System A B // p s}} {xs : List A} {ys : List B}
    (hm : behaviorMass P xs ys ≠ 0) : ∃ s ∈ P.support, Replies s.1 xs ys := by
  change (∑ s ∈ P.support, if Replies s.1 xs ys then P s else 0) ≠ 0 at hm
  obtain ⟨s, hs, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  refine ⟨s, hs, ?_⟩
  by_contra hr
  simp [hr] at ht

/-- Equality of cumulative behavior. For partial-system equivalence, both presentations
are compared in the same specified domain, as in Lanzenberger–Maurer Lemma 5. -/
def Equivalent {p : System A B → Prop}
    (P Q : Distribution {s : System A B // p s}) : Prop :=
  ∀ xs ys, behaviorMass P xs ys = behaviorMass Q xs ys

theorem Equivalent.refl {p : System A B → Prop}
    (P : Distribution {s : System A B // p s}) : Equivalent P P := fun _ _ => rfl
theorem Equivalent.symm {p : System A B → Prop}
    {P Q : Distribution {s : System A B // p s}} (h : Equivalent P Q) : Equivalent Q P :=
  fun xs ys => (h xs ys).symm
theorem Equivalent.trans {p : System A B → Prop}
    {P Q R : Distribution {s : System A B // p s}} (h : Equivalent P Q)
    (h' : Equivalent Q R) : Equivalent P R := fun xs ys => (h xs ys).trans (h' xs ys)

/-- The admitted next queries after each transcript, with a bound on the length of
admitted transcripts. The next query may depend on the preceding replies. -/
structure Domain (A B : Type) where
  /-- Query `x` is admitted after the transcript `h`. -/
  admits : List (A × B) → A → Prop
  /-- Every admitted transcript is shorter than `bound`. -/
  bound : ℕ
  length_lt : ∀ h x, admits h x → h.length < bound

instance : CoeFun (Domain A B) (fun _ => List (A × B) → A → Prop) := ⟨Domain.admits⟩

/-- The domain determined by a set of input histories. -/
def Domain.ofInputs (E : List A → Prop) (bound : ℕ) (hE : ∀ h, E h → h.length ≤ bound) :
    Domain A B where
  admits h x := E (h.map Prod.fst ++ [x])
  bound := bound
  length_lt h x hx := by
    have := hE _ hx
    simp only [List.length_append, List.length_map, List.length_singleton] at this
    omega

@[simp] theorem Domain.ofInputs_apply (E : List A → Prop) (bound : ℕ)
    (hE : ∀ h, E h → h.length ≤ bound) (h : List (A × B)) (x : A) :
    (Domain.ofInputs E bound hE : Domain A B) h x = E (h.map Prod.fst ++ [x]) := rfl

/-- `s` has domain `D`: it answers exactly the queries `D` admits along its own
transcripts. For a domain of input histories this is `dom(s) = D` (Lanzenberger–Maurer,
Definitions 5 and 8, printed pp. 11, 13). -/
def HasDomain (D : Domain A B) (s : System A B) : Prop :=
  ∀ h x, Replies s (h.map Prod.fst) (h.map Prod.snd) →
    ((s (h.map Prod.fst ++ [x])).Dom ↔ D h x)

/-- A system whose domain is a set of input histories has that input domain. -/
theorem HasDomain.ofInputs {E : List A → Prop} {bound : ℕ} {hE : ∀ h, E h → h.length ≤ bound}
    {s : System A B} (hs : ∀ h, (s h).Dom ↔ E h) :
    HasDomain (Domain.ofInputs E bound hE) s :=
  fun _ _ _ => hs _

/-- **On an input domain, `HasDomain` is `dom(s) = E`** (Lanzenberger–Maurer, Definitions 5
and 8, printed pp. 11, 13), for a DDS and a prefix-closed `E` without the empty history. -/
theorem hasDomain_ofInputs_iff {E : List A → Prop} {bound : ℕ}
    {hE : ∀ h, E h → h.length ≤ bound} (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    {s : System A B} (hs : IsDDS s) :
    HasDomain (Domain.ofInputs E bound hE) s ↔ ∀ h, (s h).Dom ↔ E h := by
  refine ⟨fun hd h => ?_, HasDomain.ofInputs⟩
  rw [← hs.trim_eq]
  refine trim_dom_of_admission hs.1 hE' (fun xs x ys hr => ?_) h
  have hx : (xs.zip ys).map Prod.fst = xs := List.map_fst_zip (by rw [hr.length])
  have hy : (xs.zip ys).map Prod.snd = ys := List.map_snd_zip (by rw [hr.length])
  have := hd (xs.zip ys) x (by rw [hx, hy]; exact hr)
  change _ ↔ E ((xs.zip ys).map Prod.fst ++ [x]) at this
  rwa [hx] at this

/-- Transcripts of a system with domain `D` stay within the bound of `D`. -/
theorem HasDomain.length_le {D : Domain A B} {s : System A B} (hs : HasDomain D s)
    {h : List (A × B)} (hr : Replies s (h.map Prod.fst) (h.map Prod.snd)) : h.length ≤ D.bound := by
  induction h using List.reverseRecOn with
  | nil => exact Nat.zero_le _
  | append_singleton h z ih =>
    simp only [List.map_append, List.map_singleton] at hr
    obtain ⟨hr, hz⟩ := replies_snoc.mp hr
    have hd : D h z.1 := (hs h z.1 hr).mp (by rw [hz]; trivial)
    have := D.length_lt h z.1 hd
    simp only [List.length_append, List.length_singleton]
    omega

/-- A probabilistic discrete system: a finite distribution over deterministic systems
with one common domain. Lanzenberger–Maurer, Definition 8 (printed p. 13):
"a distribution over (X, Y)-DDS such that all DDS in the support of S have the same
domain", with "We always assume that S is finite". -/
abbrev PDS (A B : Type) [Fintype A] [Fintype B] (D : Domain A B) :=
  Distribution {s : System A B // IsDDS s ∧ HasDomain D s}

namespace PDS

variable {p : System A B → Prop} (P : Distribution {s : System A B // p s})

/-- The mass of the next defined reply, jointly with the preceding replies. -/
noncomputable def nextReply (xs : List A) (ys : List B) (x : A) : Distribution B :=
  ∑ s ∈ P.support,
    if Replies s.1 xs ys then
      if hd : (s.1 (xs ++ [x])).Dom then Finsupp.single ((s.1 _).get hd) (P s)
      else 0
    else 0

/-- Next-reply masses are precisely the extended cumulative masses. -/
theorem nextReply_apply (xs : List A) (ys : List B) (x : A) (y : B) :
    nextReply P xs ys x y = behaviorMass P (xs ++ [x]) (ys ++ [y]) := by
  simp only [nextReply, Finsupp.finsetSum_apply, behaviorMass, Distribution.mass, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hr : Replies s.1 xs ys
  · simp only [if_pos hr, replies_snoc]
    by_cases hd : (s.1 (xs ++ [x])).Dom
    · simp only [dif_pos hd, Finsupp.single_apply]
      rw [Part.get_eq_iff_eq_some]
      simp only [hr, true_and]
    · simp [Part.eq_none_iff'.mpr hd]
  · simp [hr, replies_snoc]

theorem nextReply_nonneg (hP : P.NonNeg) (xs : List A) (ys : List B) (x : A) :
    (nextReply P xs ys x).NonNeg := by
  intro y
  rw [nextReply_apply]
  exact hP.mass_nonneg _

/-- The next-reply weight counts precisely the samples answering the extended query. -/
theorem nextReply_weight (xs : List A) (ys : List B) (x : A) :
    (nextReply P xs ys x).weight =
      P.mass (fun s => Replies s.1 xs ys ∧ (s.1 (xs ++ [x])).Dom) := by
  rw [nextReply, Distribution.weight_finset_sum]
  unfold Distribution.mass Finsupp.sum
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hr : Replies s.1 xs ys
  · by_cases hd : (s.1 (xs ++ [x])).Dom
    · simp [hr, hd, Distribution.weight, Finsupp.sum_single_index]
    · simp [hr, hd, Distribution.weight]
  · simp [hr, Distribution.weight]

/-- Partiality removes reply mass, without introducing an artificial reply. -/
theorem nextReply_weight_le (hP : P.NonNeg) (xs : List A) (ys : List B) (x : A) :
    (nextReply P xs ys x).weight ≤ behaviorMass P xs ys := by
  rw [nextReply_weight]
  exact Distribution.mass_mono hP (fun _ h => h.1)

/-- On a specified preceding transcript, every sample that produced it admits the
same next inputs. This also applies to converters, whose next port depends on the
preceding output rather than only on the input sequence. -/
theorem nextReply_weight_of_admitted {D : Prop} {xs : List A} {ys : List B} {x : A}
    (hD : ∀ s ∈ P.support, Replies s.1 xs ys → ((s.1 (xs ++ [x])).Dom ↔ D)) :
    (nextReply P xs ys x).weight = if D then behaviorMass P xs ys else 0 := by
  rw [nextReply_weight]
  have h := Distribution.mass_congr_of_support P (P := fun s =>
    Replies s.1 xs ys ∧ (s.1 (xs ++ [x])).Dom)
    (Q := fun s => Replies s.1 xs ys ∧ D)
    (fun s hs => and_congr_right (fun hr => hD s hs hr))
  rw [h]
  by_cases hd : D
  · simp only [hd, and_true, if_true, behaviorMass]
  · simp only [hd, and_false, if_false]
    exact Distribution.mass_eq_zero_of_forall_not _ (fun _ h => h)

/-- The empty cumulative mass is the distribution's weight. -/
theorem behaviorMass_nil : behaviorMass P [] [] = P.weight := by
  rw [behaviorMass, Distribution.mass_congr _ (fun _ => iff_true_intro (replies_nil _))]
  exact Distribution.mass_true _

end PDS
end SystemAlgebra
