import RandomSystems.Converter.ConverterTensor
import RandomSystems.System.Automaton
import RandomSystems.PDS.Filter

/-!
# Parallel composition of PDSs

The parallel composition of two deterministic resources with domains `E` and `F` is a
deterministic resource with the parallel domain of `E` and `F`. Two PDSs of deterministic
resources compose in parallel as their independent product, mapped through this parallel
composition.

## Main definitions

* `parallelPDS`: the parallel composition of two PDSs
* `parallelStep f g`: two automata side by side

## Main results

* `parallel_system_dom`: the domain of the parallel composition of two DDSs
* `parallel_system_valid`: the parallel composition of two deterministic resources is a
  deterministic resource
* `parallel_automatonSystem`: two automata on domains, in parallel, are the automaton running
  both side by side
* `parallelStep_bisim`, `parallelStep_congr`: bisimulations side by side are a bisimulation, and
  automata with the same systems side by side have the same system
-/

namespace SystemAlgebra

open Classical Probability

variable {I J : Type} {X₁ Y₁ : I → Type} {X₂ Y₂ : J → Type}
  {E : List (Σ i, X₁ i) → Prop} {F : List (Σ j, X₂ j) → Prop}

/-- The exact domain of the parallel composition of two DDSs. -/
theorem parallel_system_dom {S : InterfaceSystem I X₁ Y₁} {T : InterfaceSystem J X₂ Y₂}
    (hS : IsDDS S) (hT : IsDDS T) (hdS : ∀ h, (S h).Dom ↔ E h) (hdT : ∀ h, (T h).Dom ↔ F h)
    (h : List (Σ l, Sum.rec X₁ X₂ l)) :
    (relabel (trim (pair S T)) (sumAlphabet (Sum.rec X₁ X₂)).symm
      (sumAlphabet (Sum.rec Y₁ Y₂)) h).Dom ↔ parallelInputs (F := Sum.rec X₁ X₂) E F h := by
  simp only [relabel, Part.map_Dom]
  have hc : ∀ k, IsDDS (optS S (fun _ : Unit => T) k) := by
    rintro (_ | ⟨⟩)
    · exact hS
    · exact hT
  rw [show pair S T = parAll (optS S (fun _ : Unit => T)) from rfl, trim_parAll_dom hc]
  have hn : h.map (sumAlphabet (Sum.rec X₁ X₂)).symm ≠ [] ↔ h ≠ [] :=
    not_congr List.map_eq_nil_iff
  simp only [hn, parallelInputs]
  constructor
  · rintro ⟨hne, hd⟩
    exact ⟨hne, (hd none).imp id ((hdS _).mp), (hd (some ())).imp id ((hdT _).mp)⟩
  · rintro ⟨hne, hs, ht⟩
    refine ⟨hne, ?_⟩
    rintro (_ | ⟨⟩)
    · exact hs.imp id ((hdS _).mpr)
    · exact ht.imp id ((hdT _).mpr)

/-- The parallel composition of two deterministic resources is a deterministic resource
with the parallel domain. -/
theorem parallel_system_valid {s : InterfaceSystem I X₁ Y₁} {t : InterfaceSystem J X₂ Y₂}
    (hs : IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ E h)
    (ht : IsDDS t ∧ RepliesAtQueriedInterface t ∧ ∀ h, (t h).Dom ↔ F h) :
    let r := relabel (trim (pair s t)) (sumAlphabet (Sum.rec X₁ X₂)).symm
      (sumAlphabet (Sum.rec Y₁ Y₂))
    IsDDS r ∧ RepliesAtQueriedInterface r ∧
      ∀ h, (r h).Dom ↔ parallelInputs (F := Sum.rec X₁ X₂) E F h := by
  refine ⟨?_, ?_, parallel_system_dom hs.1 ht.1 hs.2.2 ht.2.2⟩
  · dsimp only
    rw [← trim_relabel]
    exact SilentAtEmpty.isDDS_trim (by simp [SilentAtEmpty, relabel, pair, parAll])
  · dsimp only
    rw [← trim_relabel]
    exact (RepliesAtQueriedInterface.parallel hs.2.1 ht.2.1).trim

/-- Independent PDSs of deterministic resources, mapped through the same parallel
composition. -/
noncomputable def parallelPDS
    (P : Distribution.ProbDist {s : InterfaceSystem I X₁ Y₁ //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ E h})
    (Q : Distribution.ProbDist {t : InterfaceSystem J X₂ Y₂ //
      IsDDS t ∧ RepliesAtQueriedInterface t ∧ ∀ h, (t h).Dom ↔ F h}) :
    Distribution.ProbDist {r : InterfaceSystem (I ⊕ J) (Sum.rec X₁ X₂) (Sum.rec Y₁ Y₂) //
      IsDDS r ∧ RepliesAtQueriedInterface r ∧
        ∀ h, (r h).Dom ↔ parallelInputs (F := Sum.rec X₁ X₂) E F h} :=
  ⟨Distribution.fTransform (fun st => ⟨relabel (trim (pair st.1.1 st.2.1))
      (sumAlphabet (Sum.rec X₁ X₂)).symm (sumAlphabet (Sum.rec Y₁ Y₂)),
      parallel_system_valid st.1.2 st.2.2⟩) (Distribution.prod P.1 Q.1),
    Distribution.fTransform_isProbDist _ (Distribution.prod_isProbDist _ _ P.2 Q.2)⟩

section Automaton

variable {S T : Type} (f : S → (i : I) → X₁ i → S × Y₁ i) (g : T → (j : J) → X₂ j → T × Y₂ j)

/-- Two automata side by side, each answering its own labels. -/
def parallelStep : S × T → (l : I ⊕ J) → Sum.rec X₁ X₂ l → (S × T) × Sum.rec Y₁ Y₂ l
  | (a, b), .inl i, x => (((f a i x).1, b), (f a i x).2)
  | (a, b), .inr j, x => ((a, (g b j x).1), (g b j x).2)

/-- Side by side, each automaton reaches the state of its own inputs. -/
theorem stateAfter_parallelStep (a : S) (b : T) (h : List (Σ l, Sum.rec X₁ X₂ l)) :
    stateAfter (parallelStep f g) (a, b) h =
      (stateAfter f a (restrict none (h.map (sumAlphabet (Sum.rec X₁ X₂)).symm)),
        stateAfter g b (restrict (some ()) (h.map (sumAlphabet (Sum.rec X₁ X₂)).symm))) := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h z ih =>
    rw [stateAfter_snoc, ih, List.map_append, List.map_singleton, restrict_append,
      restrict_append]
    rcases z with ⟨(i | j), x⟩
    · simp [parallelStep, sumAlphabet, stateAfter_snoc, restrict_cons_ne]
    · simp [parallelStep, sumAlphabet, stateAfter_snoc, restrict_cons_ne]

/-- Bisimulations side by side are a bisimulation. -/
theorem parallelStep_bisim {S' T' : Type} {f' : S' → (i : I) → X₁ i → S' × Y₁ i}
    {g' : T' → (j : J) → X₂ j → T' × Y₂ j} {R : S → S' → Prop} {R' : T → T' → Prop}
    (hf : IsBisim f f' R) (hg : IsBisim g g' R') :
    IsBisim (parallelStep f g) (parallelStep f' g') (fun a a' => R a.1 a'.1 ∧ R' a.2 a'.2) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ (i | j) x ⟨ha, hb⟩
  · obtain ⟨h₁, h₂⟩ := hf a a' i x ha
    exact ⟨h₁, h₂, hb⟩
  · obtain ⟨h₁, h₂⟩ := hg b b' j x hb
    exact ⟨h₁, ha, h₂⟩

/-- An automaton's reply to an input after a history is determined by its system. -/
theorem step_reply_eq_of_system_eq {K S' S'' : Type} {Z W : K → Type}
    {f₁ : S' → (k : K) → Z k → S' × W k} {f₂ : S'' → (k : K) → Z k → S'' × W k} {a₁ : S'} {a₂ : S''}
    (h : automatonSystem f₁ a₁ = automatonSystem f₂ a₂) (hs : List (Σ k, Z k)) (x : Σ k, Z k) :
    (f₁ (stateAfter f₁ a₁ hs) x.1 x.2).2 = (f₂ (stateAfter f₂ a₂ hs) x.1 x.2).2 := by
  have e := congrFun h (hs ++ [x])
  rw [automatonSystem_snoc, automatonSystem_snoc, Part.some_inj] at e
  exact eq_of_heq (Sigma.mk.inj e).2

/-- Side by side, automata with the same systems have the same system. -/
theorem parallelStep_congr {S' T' : Type} {f' : S' → (i : I) → X₁ i → S' × Y₁ i}
    {g' : T' → (j : J) → X₂ j → T' × Y₂ j} {a : S} {b : T} {a' : S'} {b' : T'}
    (hf : automatonSystem f a = automatonSystem f' a')
    (hg : automatonSystem g b = automatonSystem g' b') :
    automatonSystem (parallelStep f g) (a, b) = automatonSystem (parallelStep f' g') (a', b') := by
  funext h
  rcases List.eq_nil_or_concat h with rfl | ⟨h, z, rfl⟩
  · rfl
  rw [List.concat_eq_append, automatonSystem_snoc, automatonSystem_snoc, stateAfter_parallelStep,
    stateAfter_parallelStep]
  rcases z with ⟨(i | j), x⟩
  · simp only [parallelStep]
    rw [step_reply_eq_of_system_eq hf _ ⟨i, x⟩]
  · simp only [parallelStep]
    rw [step_reply_eq_of_system_eq hg _ ⟨j, x⟩]

/-- **Two automata on domains, in parallel**, are the automaton running both side by side, on
the parallel domain. -/
theorem parallel_automatonSystem (hE : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p) (a : S) (b : T) :
    relabel (trim (pair (filterDom E (automatonSystem f a)) (filterDom F (automatonSystem g b))))
        (sumAlphabet (Sum.rec X₁ X₂)).symm (sumAlphabet (Sum.rec Y₁ Y₂)) =
      filterDom (parallelInputs (F := Sum.rec X₁ X₂) E F)
        (automatonSystem (parallelStep f g) (a, b)) := by
  have domS : ∀ h, (filterDom E (automatonSystem f a) h).Dom ↔ E h := by
    intro h
    rw [filterDom_dom, automatonSystem_dom]
    exact ⟨fun hd => hd.1, fun hd => ⟨hd, fun he => hE.1 (he ▸ hd)⟩⟩
  have domT : ∀ h, (filterDom F (automatonSystem g b) h).Dom ↔ F h := by
    intro h
    rw [filterDom_dom, automatonSystem_dom]
    exact ⟨fun hd => hd.1, fun hd => ⟨hd, fun he => hF.1 (he ▸ hd)⟩⟩
  have hL := parallel_system_dom (((automatonSystem_isDDS f a).filterDom E hE.2))
    ((automatonSystem_isDDS g b).filterDom F hF.2) domS domT
  have forward : ∀ h y, y ∈ relabel (trim (pair (filterDom E (automatonSystem f a))
      (filterDom F (automatonSystem g b)))) (sumAlphabet (Sum.rec X₁ X₂)).symm
      (sumAlphabet (Sum.rec Y₁ Y₂)) h →
      y ∈ filterDom (parallelInputs (F := Sum.rec X₁ X₂) E F)
        (automatonSystem (parallelStep f g) (a, b)) h := by
    intro h y hy
    have hp := (hL h).mp (Part.dom_iff_mem.mpr ⟨y, hy⟩)
    rcases List.eq_nil_or_concat h with rfl | ⟨h, z, rfl⟩
    · exact absurd rfl hp.1
    rw [List.concat_eq_append] at hy hp ⊢
    rw [filterDom, if_pos hp, automatonSystem_snoc, stateAfter_parallelStep]
    simp only [relabel, List.map_append, List.map_singleton, Part.mem_map_iff] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    rw [trim] at hy'
    split_ifs at hy' with hr
    · rcases z with ⟨(i | j), x⟩
      · rw [show (sumAlphabet (Sum.rec X₁ X₂)).symm ⟨Sum.inl i, x⟩ =
            (⟨none, ⟨i, x⟩⟩ : Two (Σ i, X₁ i) (Σ j, X₂ j)) from rfl, pair_left] at hy'
        obtain ⟨v, hv, rfl⟩ := Part.mem_map_iff _ |>.mp hy'
        rw [filterDom_mem_iff, automatonSystem_snoc] at hv
        obtain rfl := Part.mem_some_iff.mp hv.2
        exact Part.mem_some_iff.mpr rfl
      · rw [show (sumAlphabet (Sum.rec X₁ X₂)).symm ⟨Sum.inr j, x⟩ =
            (⟨some (), ⟨j, x⟩⟩ : Two (Σ i, X₁ i) (Σ j, X₂ j)) from rfl, pair_right] at hy'
        obtain ⟨v, hv, rfl⟩ := Part.mem_map_iff _ |>.mp hy'
        rw [filterDom_mem_iff, automatonSystem_snoc] at hv
        obtain rfl := Part.mem_some_iff.mp hv.2
        exact Part.mem_some_iff.mpr rfl
    · exact absurd hy' (Part.notMem_none _)
  funext h
  apply Part.ext
  intro y
  refine ⟨forward h y, fun hy => ?_⟩
  obtain ⟨y', hy'⟩ := Part.dom_iff_mem.mp ((hL h).mpr ((filterDom_mem_iff _ _ h y).mp hy).1)
  rwa [Part.mem_unique hy (forward h y' hy')]

end Automaton

end SystemAlgebra
