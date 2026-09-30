import ConstructiveCryptography.Interface
import RandomSystems.PDS.Function

/-!
# Functional resources

Resources given by reply functions, by conditional reply laws, and by sampling once and
retaining the sample. Each is a random system on the declared alphabets and domain: reply
laws use `RandomSystem.ofConditional`, sampling uses `RandomSystem.mix`.

## Main definitions

* `Interface.Resource.ofConditional`: conditional reply distributions on the domain
* `Interface.Resource.ofFunction`: a reply function at each interface
* `Interface.Resource.sample`: sample once, then keep the sample

## Main results

* `Interface.Resource.ofFunction_mass`: the behavior of a function is the indicator of its
  admitted transcripts
* `Interface.Resource.eq_ofFunction`: probability one on the functional transcripts
  determines the resource
* `Interface.Resource.sample_ofFunction_mass`: sampled functions are the finite PDS of the
  function systems
-/

namespace SystemAlgebra

open Classical Probability CategoryTheory
open scoped BigOperators


namespace Interface.Resource

variable {A : Interface}

/-- Conditional reply distributions at the queried interface, on the declared domain. -/
noncomputable def ofConditional
    (q : ∀ (h : List ((Σ i, A.X i) × (Σ i, A.Y i))) (i : A.I) (x : A.X i),
      A.domain (h.map Prod.fst ++ [⟨i, x⟩]) → Distribution.ProbDist (A.Y i)) :
    Resource A := by
  let reply : ∀ h (x : Σ i, A.X i), A.inputDomain h x → Distribution.ProbDist (Σ i, A.Y i) :=
    fun h x hd => Distribution.PMF (q h x.1 x.2 hd) (fun y => (⟨x.1, y⟩ : Σ i, A.Y i))
  refine ⟨RandomSystem.ofConditional reply, ?_⟩
  intro h x y hne
  rw [RandomSystem.ofConditional_snoc]
  split_ifs with hd
  · have hz : reply h x hd y = 0 := by
      apply Distribution.fTransform_apply_of_forall_ne
      intro v he
      exact hne (congrArg Sigma.fst he).symm
    rw [hz, mul_zero]
  · rfl

/-- A deterministic function at each interface, on the declared input domain. -/
noncomputable def ofFunction (f : ∀ i, A.X i → A.Y i) : Resource A :=
  ofConditional fun _ i x _ => ⟨Finsupp.single (f i x) 1, Distribution.isProbDist_single _⟩

theorem ofFunction_snoc (f : ∀ i, A.X i → A.Y i)
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i))) (x : Σ i, A.X i) (y : Σ i, A.Y i) :
    (ofFunction f).1 (h ++ [(x, y)]) =
      if A.domain (h.map Prod.fst ++ [x]) then
        (ofFunction f).1 h * (if y = ⟨x.1, f x.1 x.2⟩ then 1 else 0) else 0 := by
  unfold ofFunction ofConditional
  rw [RandomSystem.ofConditional_snoc]
  by_cases hd : A.domain (h.map Prod.fst ++ [x])
  · rw [dif_pos (show A.inputDomain h x from hd), if_pos hd]
    congr 1
    simp [Distribution.PMF, Distribution.fTransform, Finsupp.single_apply, eq_comm]
  · rw [dif_neg (show ¬ A.inputDomain h x from hd), if_neg hd]

/-- A functional resource gives probability one to its prescribed answers on
each admitted history. -/
theorem ofFunction_mass_eq_one (f : ∀ i, A.X i → A.Y i)
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i)))
    (hd : h = [] ∨ A.domain (h.map Prod.fst))
    (he : ∀ z ∈ h, z.2 = ⟨z.1.1, f z.1.1 z.1.2⟩) :
    (ofFunction f).1 h = 1 := by
  induction h using List.reverseRecOn with
  | nil => exact RandomSystem.mass_nil _
  | append_singleton h z ih =>
    have hp : A.domain (h.map Prod.fst ++ [z.1]) := by
      rcases hd with hd | hd
      · simp at hd
      · simpa only [List.map_append, List.map_singleton] using hd
    have hh : h = [] ∨ A.domain (h.map Prod.fst) := by
      by_cases hn : h = []
      · exact Or.inl hn
      · exact Or.inr (A.nonempty_prefix.2 (List.prefix_append _ _) (by simpa using hn) hp)
    rw [ofFunction_snoc, if_pos hp, if_pos (he z (by simp)),
      ih hh (fun w hw => he w (List.mem_append_left _ hw)), mul_one]

theorem ofFunction_answers (f : ∀ i, A.X i → A.Y i)
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i))) (hm : (ofFunction f).1 h ≠ 0) :
    ∀ z ∈ h, z.2 = ⟨z.1.1, f z.1.1 z.1.2⟩ := by
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h z ih =>
    rw [ofFunction_snoc] at hm
    split_ifs at hm with hd hy
    · intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact ih (by simpa only [mul_one] using hm) w hw
      · exact (List.mem_singleton.mp hw) ▸ hy
    · simp at hm
    · exact (hm rfl).elim

/-- The cumulative law of a function is the indicator of its admitted
query/reply histories. -/
theorem ofFunction_mass (f : ∀ i, A.X i → A.Y i)
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i))) :
    (ofFunction f).1 h =
      if (h = [] ∨ A.domain (h.map Prod.fst)) ∧
        (∀ z ∈ h, z.2 = ⟨z.1.1, f z.1.1 z.1.2⟩) then 1 else 0 := by
  by_cases hd : h = [] ∨ A.domain (h.map Prod.fst)
  · by_cases he : ∀ z ∈ h, z.2 = ⟨z.1.1, f z.1.1 z.1.2⟩
    · rw [if_pos ⟨hd, he⟩]; exact ofFunction_mass_eq_one f h hd he
    · rw [if_neg (fun hc => he hc.2)]
      by_contra hn
      exact he (ofFunction_answers f h hn)
  · rw [if_neg (fun hc => hd hc.1)]
    obtain ⟨h, z, rfl⟩ := List.eq_nil_or_concat h |>.resolve_left (fun hn => hd (Or.inl hn))
    simp only [List.concat_eq_append, List.map_append, List.map_singleton] at hd ⊢
    rw [ofFunction_snoc, if_neg (fun hc => hd (Or.inr hc))]

/-- Probability one on the functional transcripts determines the entire
behavior, including probability zero for every different answer. -/
theorem eq_ofFunction (R : Resource A) (f : ∀ i, A.X i → A.Y i)
    (certain : ∀ h, (h = [] ∨ A.domain (h.map Prod.fst)) →
      (∀ z ∈ h, z.2 = ⟨z.1.1, f z.1.1 z.1.2⟩) → R.1 h = 1) :
    R = ofFunction f := by
  have mass (h : List ((Σ i, A.X i) × (Σ i, A.Y i))) :
      R.1 h = (ofFunction f).1 h := by
    induction h using List.reverseRecOn with
    | nil => rw [RandomSystem.mass_nil, RandomSystem.mass_nil]
    | append_singleton h z ih =>
      by_cases hd : A.domain (h.map Prod.fst ++ [z.1])
      · by_cases he : ∀ w ∈ h, w.2 = ⟨w.1.1, f w.1.1 w.1.2⟩
        · have hh : h = [] ∨ A.domain (h.map Prod.fst) := by
            by_cases hn : h = []
            · exact Or.inl hn
            · exact Or.inr (A.nonempty_prefix.2 (List.prefix_append _ _)
                (by simpa using hn) hd)
          have hp := certain h hh he
          let v : Σ i, A.Y i := ⟨z.1.1, f z.1.1 z.1.2⟩
          have hv : R.1 (h ++ [(z.1, v)]) = 1 := by
            apply certain _ (Or.inr (by simpa only [List.map_append, List.map_singleton] using hd))
            intro w hw
            rcases List.mem_append.mp hw with hw | hw
            · exact he w hw
            · obtain rfl := List.mem_singleton.mp hw
              rfl
          rw [ofFunction_snoc, if_pos hd, ← ih, hp, one_mul]
          by_cases hy : z.2 = v
          · rw [if_pos hy]
            have hz : z = (z.1, v) := Prod.ext rfl hy
            rw [hz]
            exact hv
          · rw [if_neg hy]
            have hc := Distribution.mass_add_compl (R.1.extensionLaw h z.1) (fun y => y = v)
            rw [Distribution.mass_singleton, RandomSystem.extensionLaw_apply, hv,
              RandomSystem.extensionLaw_weight, if_pos (show A.inputDomain h z.1 from hd), hp] at hc
            have hz := Distribution.apply_le_mass (R.1.extensionLaw_nonneg h z.1)
              (P := fun y => y ≠ v) (a := z.2) hy
            rw [RandomSystem.extensionLaw_apply] at hz
            exact le_antisymm (by linarith) (R.1.mass_nonneg _)
        · have zero : (ofFunction f).1 h = 0 := by
            by_contra hn
            exact he (ofFunction_answers f h hn)
          have hz := R.1.mass_eq_zero_of_prefix (List.prefix_append h [z]) (ih.trans zero)
          rw [hz, ofFunction_snoc, if_pos hd, zero, zero_mul]
      · rw [R.1.mass_eq_zero_of_not_admitted hd, ofFunction_snoc, if_neg hd]
  exact Subtype.ext (RandomSystem.ext mass)

/-- Sample once and retain that choice throughout the interaction. -/
noncomputable def sample {K : Type} (P : Distribution K) [Distribution.IsProbability P]
    (R : K → Resource A) : Resource A :=
  ⟨RandomSystem.mix ⟨P, Distribution.IsProbability.isProbDist P⟩ (fun k => (R k).1), by
    intro h x y hne
    rw [RandomSystem.mix_mass]
    exact Finset.sum_eq_zero fun k _ => by rw [(R k).2 h x y hne, mul_zero]⟩

theorem sample_mass {K : Type} (P : Distribution K) [Distribution.IsProbability P]
    (R : K → Resource A) h :
    (sample P R).1 h = ∑ k ∈ P.support, P k * (R k).1 h := rfl

/-- Initial sampling of functions is their existing finite DDS presentation. -/
theorem sample_ofFunction_mass {K : Type} (P : Distribution K)
    [Distribution.IsProbability P] (f : K → ∀ i, A.X i → A.Y i)
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i))) :
    (sample P (fun k => ofFunction (f k))).1 h =
      behaviorMass (Distribution.fTransform
        (fun k => DDS.ofFunction A.domain A.nonempty_prefix
          (fun x => ⟨x.1, f k x.1 x.2⟩)) P) (h.map Prod.fst) (h.map Prod.snd) := by
  rw [sample_mass, behaviorMass, Distribution.mass_fTransform]
  unfold Distribution.mass Finsupp.sum
  apply Finset.sum_congr rfl
  intro k _
  dsimp only
  simp only [ofFunction_mass, DDS.replies_ofFunction_iff]
  have answers : h.map Prod.snd = (h.map Prod.fst).map (fun x => ⟨x.1, f k x.1 x.2⟩) ↔
      ∀ z ∈ h, z.2 = ⟨z.1.1, f k z.1.1 z.1.2⟩ := by
    rw [List.map_map, List.map_eq_map_iff]
    rfl
  simp only [answers, List.map_eq_nil_iff]
  split_ifs <;> simp

end Interface.Resource

open Lean.Parser.Term in
/-- A function at each named interface. -/
scoped macro "system " i:funBinder x:funBinder " => " f:term : term =>
  `(Interface.Resource.ofFunction (fun $i $x => $f))

open Lean.Parser.Term in
/-- Annotate a functional system with its interface. -/
scoped macro "system " "[" A:term "] " i:funBinder x:funBinder " => " f:term : term =>
  `(Interface.Resource.ofFunction (A := $A) (fun $i $x => $f))

/-- Initial sampling scopes over the complete system expression that follows. -/
scoped macro "sample " k:ident " ← " law:term "; " body:term : term =>
  `(Interface.Resource.sample $law (fun $k => $body))

/-- Initial sampling, with the same sampling symbol as component declarations. -/
scoped macro "sample " k:ident " ←$ " law:term "; " body:term : term =>
  `(Interface.Resource.sample (show Probability.Distribution.ProbDist _ from $law).1
    (fun $k => $body))

end SystemAlgebra
