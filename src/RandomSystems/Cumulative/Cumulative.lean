import RandomSystems.PDS.PDS

/-!
# Random systems

A random system over finite alphabets on a bounded domain is given by its
cumulative probabilities: the probability `R h` of each transcript `h`. At an
admitted query the reply probabilities sum to the probability of the preceding
transcript; at any other query they vanish. A normalized PDS induces a random
system, and two PDSs induce the same one exactly when they are equivalent.
Source: Lanzenberger–Maurer, after Lemma 5 (printed p. 14): an equivalence class
is “characterized by the transcript distributions for all non-adaptive
deterministic environments”.

## Main definitions

* `RandomSystem A B D`: cumulative probabilities satisfying `IsRandomSystem`
* `PDS.behavior P`: the random system of a PDS
* `RandomSystem.ofPDSClass D`: the random system of a class of equivalent PDSs
* `RandomSystem.conditional`, `RandomSystem.ofConditional`: conditional reply laws,
  and the random system they define
* `RandomSystem.relabel`: renaming the alphabets

## Main results

* `PDS.behavior_eq_iff`, `ofPDSClass_injective`: behavior identifies exactly the
  equivalent PDSs
* `mass_eq_zero_of_not_admitted`, `mass_eq_zero_of_bound_lt`: no mass outside the domain
* `isRandomSystem_behaviorMass`: a mixture of systems with domain `D` is normalized on `D`
-/

namespace SystemAlgebra

open Classical Probability

variable {A B : Type}

/-- Normalized cumulative behavior, with finite reply laws at admitted queries. -/
def IsRandomSystem (D : List (A × B) → A → Prop) (p : List (A × B) → ℝ) : Prop :=
  p [] = 1 ∧ (∀ h, 0 ≤ p h) ∧
    ∀ h x, ∃ μ : Distribution B,
      (∀ y, μ y = p (h ++ [(x, y)])) ∧ μ.weight = if D h x then p h else 0

/-- The domain after renaming the input and output alphabets. -/
def Domain.relabel {A' B' : Type} (D : Domain A B) (inputs : A ≃ A') (outputs : B ≃ B') :
    Domain A' B' where
  admits h x := D (h.map (inputs.symm.prodCongr outputs.symm)) (inputs.symm x)
  bound := D.bound
  length_lt h x hx := by simpa using D.length_lt _ _ hx

/-- A random system over finite alphabets on a bounded domain: its cumulative
input/output probabilities. -/
abbrev RandomSystem (A B : Type) [Fintype A] [Fintype B] (D : Domain A B) :=
  {p : List (A × B) → ℝ // IsRandomSystem D p}

namespace RandomSystem

variable [Fintype A] [Fintype B] {D : Domain A B}

instance : CoeFun (RandomSystem A B D) (fun _ => List (A × B) → ℝ) := ⟨Subtype.val⟩

@[ext] theorem ext {R S : RandomSystem A B D} (h : ∀ t, R t = S t) : R = S :=
  Subtype.ext (funext h)

theorem mass_nil (R : RandomSystem A B D) : R [] = 1 := R.2.1
theorem mass_nonneg (R : RandomSystem A B D) (h : List (A × B)) : 0 ≤ R h := R.2.2.1 h

/-- Responding interface systems return their reply at the queried interface.
The alphabets may differ at every interface and the domain may be partial. -/
def RepliesAtQueriedInterface {I : Type} {X Y : I → Type}
    [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)] {D : Domain (Σ i, X i) (Σ i, Y i)}
    (R : RandomSystem (Σ i, X i) (Σ i, Y i) D) : Prop :=
  ∀ h x y, y.1 ≠ x.1 → R (h ++ [(x, y)]) = 0

/-- The finite reply law is determined by the cumulative masses, not extra data. -/
noncomputable def extensionLaw (R : RandomSystem A B D) (h : List (A × B)) (x : A) :
    Distribution B := Classical.choose (R.2.2.2 h x)

theorem extensionLaw_apply (R : RandomSystem A B D) (h : List (A × B)) (x : A) (y : B) :
    R.extensionLaw h x y = R (h ++ [(x, y)]) := (Classical.choose_spec (R.2.2.2 h x)).1 y

theorem extensionLaw_weight (R : RandomSystem A B D) (h : List (A × B)) (x : A) :
    (R.extensionLaw h x).weight = if D h x then R h else 0 :=
  (Classical.choose_spec (R.2.2.2 h x)).2

theorem extensionLaw_nonneg (R : RandomSystem A B D) (h : List (A × B)) (x : A) :
    (R.extensionLaw h x).NonNeg := by
  intro y
  rw [extensionLaw_apply]
  exact R.mass_nonneg _

theorem mass_snoc_le (R : RandomSystem A B D) (h : List (A × B)) (x : A) (y : B) :
    R (h ++ [(x, y)]) ≤ R h := by
  rw [← extensionLaw_apply]
  calc R.extensionLaw h x y ≤ (R.extensionLaw h x).mass (· = y) :=
      Distribution.apply_le_mass (R.extensionLaw_nonneg h x) rfl
    _ ≤ (R.extensionLaw h x).weight := Distribution.mass_le_weight (R.extensionLaw_nonneg h x) _
    _ ≤ R h := by rw [extensionLaw_weight]; split_ifs <;> simp [R.mass_nonneg]

theorem mass_append_le (R : RandomSystem A B D) (h e : List (A × B)) :
    R (h ++ e) ≤ R h := by
  induction e using List.reverseRecOn with
  | nil => simp
  | append_singleton e z ih =>
    rw [← List.append_assoc]
    exact (R.mass_snoc_le _ z.1 z.2).trans ih

theorem mass_eq_zero_of_prefix (R : RandomSystem A B D) {h h' : List (A × B)}
    (hp : h <+: h') (h0 : R h = 0) : R h' = 0 := by
  obtain ⟨e, rfl⟩ := hp
  exact le_antisymm (h0 ▸ R.mass_append_le h e) (R.mass_nonneg _)

/-- Every positive admitted history has at least one possible reply. -/
theorem exists_reply (R : RandomSystem A B D) {h : List (A × B)} {x : A}
    (hd : D h x) (hp : R h ≠ 0) : ∃ y, R (h ++ [(x, y)]) ≠ 0 := by
  by_contra hn
  have hz : R.extensionLaw h x = 0 := by
    ext y
    rw [extensionLaw_apply]
    exact not_not.mp (fun hy => hn ⟨y, hy⟩)
  have hw := R.extensionLaw_weight h x
  rw [hz, if_pos hd] at hw
  exact hp hw.symm

/-- Renaming input and output alphabets transports the admitted domain and the
same cumulative behavior. Interface relabeling uses equivalences of sigma types. -/
noncomputable def relabel {A' B' : Type} [Fintype A'] [Fintype B'] (R : RandomSystem A B D)
    (inputs : A ≃ A') (outputs : B ≃ B') :
    RandomSystem A' B' (D.relabel inputs outputs) :=
  ⟨fun h => R (h.map (inputs.symm.prodCongr outputs.symm)), by
    refine ⟨R.mass_nil, fun h => R.mass_nonneg _, fun h x => ?_⟩
    refine ⟨Distribution.fTransform outputs
      (R.extensionLaw (h.map (inputs.symm.prodCongr outputs.symm)) (inputs.symm x)), ?_, ?_⟩
    · intro y
      have hy := Distribution.fTransform_injective_apply
        (R.extensionLaw (h.map (inputs.symm.prodCongr outputs.symm)) (inputs.symm x))
        outputs outputs.injective (outputs.symm y)
      simpa [extensionLaw_apply] using hy
    · rw [Distribution.weight_fTransform, extensionLaw_weight]
      rfl⟩

theorem relabel_mass {A' B' : Type} [Fintype A'] [Fintype B'] (R : RandomSystem A B D)
    (inputs : A ≃ A') (outputs : B ≃ B') (h : List (A' × B')) :
    R.relabel inputs outputs h = R (h.map (inputs.symm.prodCongr outputs.symm)) := rfl

/-- Relabeling does not identify distinct probabilistic behaviors. -/
theorem relabel_injective {A' B' : Type} [Fintype A'] [Fintype B'] (inputs : A ≃ A')
    (outputs : B ≃ B') :
    Function.Injective (fun R : RandomSystem A B D => R.relabel inputs outputs) := by
  intro R S he
  apply ext
  intro h
  have hh := congrArg (fun T => T (h.map (inputs.prodCongr outputs))) he
  have hid : (inputs.symm.prodCongr outputs.symm) ∘ (inputs.prodCongr outputs) = id := by
    funext z
    rcases z with ⟨a, b⟩
    simp
  simpa only [relabel_mass, List.map_map, hid, List.map_id] using hh

/-- An inadmissible query has no reply mass at any output. -/
theorem mass_eq_zero_of_not_admitted (R : RandomSystem A B D) {h : List (A × B)} {x : A}
    (hd : ¬ D h x) (y : B) : R (h ++ [(x, y)]) = 0 := by
  apply le_antisymm _ (R.mass_nonneg _)
  rw [← extensionLaw_apply]
  calc R.extensionLaw h x y ≤ (R.extensionLaw h x).mass (· = y) :=
      Distribution.apply_le_mass (R.extensionLaw_nonneg h x) rfl
    _ ≤ (R.extensionLaw h x).weight := Distribution.mass_le_weight (R.extensionLaw_nonneg h x) _
    _ = 0 := by rw [extensionLaw_weight, if_neg hd]

/-- A random system has no mass on transcripts longer than its domain's bound. -/
theorem mass_eq_zero_of_bound_lt (R : RandomSystem A B D) {h : List (A × B)}
    (hl : D.bound < h.length) : R h = 0 := by
  have hi : D.bound < h.length := hl
  have ht : h.take (D.bound + 1) = h.take D.bound ++ [((h[D.bound]).1, (h[D.bound]).2)] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
  have hn : ¬ D (h.take D.bound) (h[D.bound]).1 := fun hd => by
    have := D.length_lt _ _ hd
    rw [List.length_take, min_eq_left hl.le] at this
    exact lt_irrefl _ this
  exact R.mass_eq_zero_of_prefix (List.take_prefix (D.bound + 1) h)
    (ht ▸ R.mass_eq_zero_of_not_admitted hn _)

/-- Every query in a possible transcript is admitted at a possible prefix. -/
theorem possible_prefix (R : RandomSystem A B D) {h : List (A × B)} (hh : R h ≠ 0)
    (i : ℕ) (hi : i < h.length) : D (h.take i) (h[i]).1 ∧ R (h.take i) ≠ 0 := by
  refine ⟨?_, fun hz => hh (R.mass_eq_zero_of_prefix (List.take_prefix i h) hz)⟩
  by_contra hn
  have hz := R.mass_eq_zero_of_not_admitted hn (h[i]).2
  have ht : h.take (i + 1) = h.take i ++ [((h[i]).1, (h[i]).2)] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
  exact hh (R.mass_eq_zero_of_prefix (List.take_prefix (i + 1) h) (ht ▸ hz))

omit [Fintype A] [Fintype B] in
/-- A finite mixture of systems with domain `D` has a cumulative behavior normalized on `D`. -/
theorem _root_.SystemAlgebra.isRandomSystem_behaviorMass {D : List (A × B) → A → Prop}
    {p : System A B → Prop} (P : Distribution {s : System A B // p s}) (hP : P.isProbDist)
    (hD : ∀ s ∈ P.support, ∀ h x, Replies s.1 (h.map Prod.fst) (h.map Prod.snd) →
      ((s.1 (h.map Prod.fst ++ [x])).Dom ↔ D h x)) :
    IsRandomSystem D (fun h => behaviorMass P (h.map Prod.fst) (h.map Prod.snd)) := by
  refine ⟨?_, fun h => hP.1.mass_nonneg _, fun h x => ?_⟩
  · simpa using (PDS.behaviorMass_nil P).trans hP.2
  · refine ⟨PDS.nextReply P (h.map Prod.fst) (h.map Prod.snd) x, ?_, ?_⟩
    · intro y
      simpa using PDS.nextReply_apply P (h.map Prod.fst) (h.map Prod.snd) x y
    · exact PDS.nextReply_weight_of_admitted P (fun s hs hr => hD s hs h x hr)

/-- A finite mixture induces cumulative behavior when the samples producing a
transcript agree on its admitted next inputs. -/
noncomputable def ofPDS {p : System A B → Prop}
    (P : Distribution {s : System A B // p s}) (hP : P.isProbDist)
    (hD : ∀ s ∈ P.support, ∀ h x, Replies s.1 (h.map Prod.fst) (h.map Prod.snd) →
      ((s.1 (h.map Prod.fst ++ [x])).Dom ↔ D h x)) : RandomSystem A B D :=
  ⟨fun h => behaviorMass P (h.map Prod.fst) (h.map Prod.snd), isRandomSystem_behaviorMass P hP hD⟩

/-- A normalized PDS induces its cumulative random system. -/
noncomputable def _root_.SystemAlgebra.PDS.behavior (P : PDS A B D) (hP : P.isProbDist) :
    RandomSystem A B D :=
  ofPDS P hP (fun s _ h x hr => s.2.2 h x hr)

theorem _root_.SystemAlgebra.PDS.behavior_mass (P : PDS A B D) (hP : P.isProbDist)
    (h : List (A × B)) :
    PDS.behavior P hP h = behaviorMass P (h.map Prod.fst) (h.map Prod.snd) := rfl

/-- The behavior map identifies exactly equal cumulative behaviors of PDSs. -/
theorem _root_.SystemAlgebra.PDS.behavior_eq_iff {P Q : PDS A B D} (hP : P.isProbDist)
    (hQ : Q.isProbDist) : PDS.behavior P hP = PDS.behavior Q hQ ↔ Equivalent P Q := by
  constructor
  · intro he xs ys
    by_cases hl : ys.length = xs.length
    · have h := congrArg (fun R : RandomSystem A B D => R (xs.zip ys)) he
      change behaviorMass P ((xs.zip ys).map Prod.fst) ((xs.zip ys).map Prod.snd) =
        behaviorMass Q ((xs.zip ys).map Prod.fst) ((xs.zip ys).map Prod.snd) at h
      rwa [List.map_fst_zip (by omega), List.map_snd_zip (by omega)] at h
    · have hz (R : PDS A B D) : behaviorMass R xs ys = 0 :=
        Distribution.mass_eq_zero_of_forall_not _ (fun _ hr => hl hr.length)
      rw [hz P, hz Q]
  · intro h
    exact ext fun t => h _ _

variable (D) in
/-- Behavioral equivalence of normalized PDSs on one domain. -/
def pdsSetoid : Setoid (Distribution.ProbDist {s : System A B // IsDDS s ∧ HasDomain D s}) where
  r P Q := Equivalent P.1 Q.1
  iseqv := ⟨fun P => Equivalent.refl P.1, fun h => h.symm, fun h h' => h.trans h'⟩

variable (D) in
/-- A PDS class determines its cumulative behavior. -/
noncomputable def ofPDSClass : Quotient (pdsSetoid D) → RandomSystem A B D :=
  Quotient.lift (fun P => PDS.behavior P.1 P.2)
    (fun P Q h => (PDS.behavior_eq_iff P.2 Q.2).mpr h)

@[simp] theorem ofPDSClass_mk (P : Distribution.ProbDist {s : System A B // IsDDS s ∧ HasDomain D s}) :
    ofPDSClass D (Quotient.mk (pdsSetoid D) P) = PDS.behavior P.1 P.2 := rfl

theorem ofPDSClass_injective : Function.Injective (ofPDSClass D) := by
  intro P Q
  induction P using Quotient.inductionOn with
  | _ P =>
    induction Q using Quotient.inductionOn with
    | _ Q =>
      intro h
      exact Quotient.sound ((PDS.behavior_eq_iff P.2 Q.2).mp h)

/-- Next-reply conditional probabilities are defined at admitted, positive-mass histories.
Their normalization follows from cumulative consistency. -/
noncomputable def conditional (R : RandomSystem A B D) (h : List (A × B)) (x : A) :
    Part (Distribution.ProbDist B) :=
  ⟨D h x ∧ R h ≠ 0, fun hd =>
    ⟨(R.extensionLaw h x).mapRange (fun w => w / R h) (zero_div _), by
      constructor
      · intro y
        exact div_nonneg (R.extensionLaw_nonneg h x y) (R.mass_nonneg h)
      · rw [Distribution.weight_mapRange_div, extensionLaw_weight, if_pos hd.1, div_self hd.2]⟩⟩

@[simp] theorem conditional_dom (R : RandomSystem A B D) (h : List (A × B)) (x : A) :
    (R.conditional h x).Dom ↔ D h x ∧ R h ≠ 0 := Iff.rfl

theorem conditional_apply (R : RandomSystem A B D) (h : List (A × B)) (x : A)
    (hd : (R.conditional h x).Dom) (y : B) :
    (R.conditional h x).get hd y = R (h ++ [(x, y)]) / R h := by
  change R.extensionLaw h x y / R h = _
  rw [extensionLaw_apply]

section ConditionalConstructor

variable (q : ∀ h x, D h x → Distribution.ProbDist B)

/-- The chain rule constructs cumulative masses from conditional reply distributions. -/
noncomputable def conditionalMass (t : List (A × B)) : ℝ :=
  List.reverseRecOn t 1 fun h z p => if hd : D h z.1 then p * q h z.1 hd z.2 else 0

omit [Fintype A] [Fintype B] in
@[simp] theorem conditionalMass_nil : conditionalMass q [] = 1 := by
  simp [conditionalMass]

omit [Fintype A] [Fintype B] in
theorem conditionalMass_snoc (h : List (A × B)) (x : A) (y : B) :
    conditionalMass q (h ++ [(x, y)]) =
      if hd : D h x then conditionalMass q h * q h x hd y else 0 := by
  unfold conditionalMass
  rw [List.reverseRecOn_concat]

omit [Fintype A] [Fintype B] in
theorem conditionalMass_nonneg (h : List (A × B)) : 0 ≤ conditionalMass q h := by
  induction h using List.reverseRecOn with
  | nil => rw [conditionalMass_nil]; exact zero_le_one
  | append_singleton h z ih =>
    rw [conditionalMass_snoc]
    split_ifs with hd
    · exact mul_nonneg ih ((q h z.1 hd).2.1 _)
    · exact le_rfl

/-- The random system defined by conditional reply distributions on its domain. -/
noncomputable def ofConditional : RandomSystem A B D :=
  ⟨conditionalMass q, conditionalMass_nil q, conditionalMass_nonneg q, by
    intro h x
    by_cases hd : D h x
    · refine ⟨conditionalMass q h • (q h x hd).1, ?_, ?_⟩
      · intro y
        simp [conditionalMass_snoc, hd, Finsupp.smul_apply]
      · rw [if_pos hd]
        have weighted : (conditionalMass q h • (q h x hd).1).weight =
            conditionalMass q h * (q h x hd).1.weight := by
          unfold Distribution.weight
          rw [Finsupp.sum_smul_index fun _ => rfl]
          unfold Finsupp.sum
          rw [Finset.mul_sum]
        rw [weighted, (q h x hd).2.2, mul_one]
    · exact ⟨0, fun y => by simp [conditionalMass_snoc, hd], by simp [hd, Distribution.weight]⟩⟩

theorem ofConditional_snoc (h : List (A × B)) (x : A) (y : B) :
    ofConditional q (h ++ [(x, y)]) =
      if hd : D h x then ofConditional q h * q h x hd y else 0 :=
  conditionalMass_snoc q h x y

end ConditionalConstructor

end RandomSystem
end SystemAlgebra
