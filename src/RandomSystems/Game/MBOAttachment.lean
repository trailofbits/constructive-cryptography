import RandomSystems.Game.MBO
import RandomSystems.Converter.ConverterRelabel

/-!
# Converters attached to games

A converter attaches to a game through its MBO-forwarding lift: the lift runs the converter on
the inside replies without their MBO and tags each outside reply with the MBO of the latest
inside reply. The lift of a DDC from `E` to `F` is a DDC from `E` to `F`, the lift of a PDC is
the PDC of the lifts of a presentation, and the lift is functorial. Attaching a lift commutes
with the visible system, and attaching it to a game gives a game. A probabilistic
distinguisher with a PDC absorbed wins a game as the distinguisher wins the lift of the PDC
attached to it; so the solver behaviors, the decision probabilities on random systems and the
winning probabilities for games of one distinguisher, are closed under absorbing a PDC.

Sources: CR18, Definition 4.13 (`R g`) and the proof of Lemma 4.9 (`g(W R) = (R g)(W)`).

## Main definitions

* `latestMBO`, `liftMBO`, `PDCBehavior.liftMBO`: the MBO-forwarding lift of a DDC and of a PDC
* `TaggedMBO`: converter transcripts whose outside replies carry the latest inside MBO
* `Domain.SolverBehavior`, `Domain.SolverBehavior.absorb`: solver behaviors

## Main results

* `IsDDCFrom.liftMBO`: the lift of a DDC from `E` to `F` is a DDC from `E` to `F`
* `replies_liftMBO_iff`, `PDCBehavior.liftMBO_apply`: the transcripts of a lift
* `PDCBehavior.liftMBO_id`, `PDCBehavior.liftMBO_comp`: the lift is functorial
* `RandomSystem.visible_attach_liftMBO`: attaching a lift attaches to the visible system
* `RandomSystem.MonotoneMBO.attach_liftMBO`: attaching a lift to a game gives a game
* `Domain.Distinguisher.exists_absorbAll_winProbability`: absorbing a PDC into a winner
-/

namespace SystemAlgebra

open Classical Probability

/-! ## The lift of a DDC -/

section LiftDDC

variable {O J : Type} {U V : O → Type} {X Y : J → Type}

/-- The MBO of an input of a converter: that of an inside reply. -/
def inputMBO : (Σ l, twoFam U (withMBO Y) l) → Option Bool
  | ⟨⟨none, _⟩, _⟩ => none
  | ⟨⟨some (), _⟩, y⟩ => some y.2

/-- The MBO of the latest inside reply of an input history, unset before any. -/
def latestMBO (h : List (Σ l, twoFam U (withMBO Y) l)) : Bool :=
  (h.reverse.findSome? inputMBO).getD false

theorem latestMBO_snoc (h : List (Σ l, twoFam U (withMBO Y) l)) (z : Σ l, twoFam U (withMBO Y) l) :
    latestMBO (h ++ [z]) = (inputMBO z).getD (latestMBO h) := by
  simp only [latestMBO, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.findSome?_cons]
  cases inputMBO z <;> rfl

@[simp] theorem latestMBO_nil : latestMBO ([] : List (Σ l, twoFam U (withMBO Y) l)) = false := rfl

/-- **The MBO-forwarding lift** of a converter: it runs the converter on the inside replies
without their MBO, and tags each outside reply with the MBO of the latest inside reply. -/
def liftMBO (a : InsideOutsideSystem O J U V X Y) :
    InsideOutsideSystem O J U (withMBO V) X (withMBO Y) :=
  fun h => (a (h.map (insideMap forgetMBO))).map (outsideMap (tagMBO (latestMBO h)))

theorem insideMap_forgetMBO_fst (z : Σ l, twoFam U (withMBO Y) l) :
    (insideMap forgetMBO z).1 = z.1 := by
  rcases z with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, y⟩ <;> rfl

theorem outsideMap_tagMBO_fst (b : Bool) (y : Σ l, twoFam V X l) :
    (outsideMap (tagMBO b) y).1 = y.1 := by
  rcases y with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, y⟩ <;> rfl

theorem outsideMap_forgetMBO_fst (y : Σ l, twoFam (withMBO V) X l) :
    (outsideMap forgetMBO y).1 = y.1 := by
  rcases y with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, y⟩ <;> rfl

@[simp] theorem outsideMap_forgetMBO_tagMBO (b : Bool) (y : Σ l, twoFam V X l) :
    outsideMap forgetMBO (outsideMap (tagMBO b) y) = y := by
  rcases y with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, y⟩ <;> rfl

theorem mem_liftMBO {a : InsideOutsideSystem O J U V X Y} {h} {y} :
    y ∈ liftMBO a h ↔ outsideMap forgetMBO y ∈ a (h.map (insideMap forgetMBO)) ∧
      y = outsideMap (tagMBO (latestMBO h)) (outsideMap forgetMBO y) := by
  constructor
  · intro hy
    obtain ⟨y₀, hy₀, rfl⟩ := (Part.mem_map_iff _).mp hy
    simpa using hy₀
  · rintro ⟨hy, he⟩
    exact (Part.mem_map_iff _).mpr ⟨_, hy, he.symm⟩

theorem liftMBO_dom (a : InsideOutsideSystem O J U V X Y) (h) :
    (liftMBO a h).Dom ↔ (a (h.map (insideMap forgetMBO))).Dom := Iff.rfl

/-- **The lift without its outside MBOs** is the converter run on the inside replies without
their MBO. -/
theorem relabel_liftMBO (a : InsideOutsideSystem O J U V X Y) :
    relabel (liftMBO a) id (outsideMap forgetMBO) = relabel a (insideMap forgetMBO) id := by
  funext h
  simp only [relabel, liftMBO, List.map_id, Part.map_map]
  congr 1
  funext y
  simp

theorem replyLabel_liftMBO (a : InsideOutsideSystem O J U V X Y) (h) :
    replyLabel (liftMBO a) h = replyLabel a (h.map (insideMap forgetMBO)) := by
  unfold replyLabel
  by_cases hd : (a (h.map (insideMap forgetMBO))).Dom
  · rw [dif_pos hd, dif_pos ((liftMBO_dom a h).mpr hd)]
    exact congrArg some (outsideMap_tagMBO_fst _ _)
  · rw [dif_neg hd, dif_neg (fun h' => hd ((liftMBO_dom a h).mp h'))]

theorem lastOuter_insideMap_forgetMBO (h : List (Σ l, twoFam U (withMBO Y) l)) :
    lastOuter (h.map (insideMap forgetMBO)) = lastOuter h := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h z ih =>
    rw [List.map_append, List.map_singleton, lastOuter_snoc, lastOuter_snoc, ih]
    rcases z with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, y⟩ <;> rfl

theorem insideRun_liftMBO (a : InsideOutsideSystem O J U V X Y) (h) :
    insideRun (liftMBO a) h = insideRun a (h.map (insideMap forgetMBO)) := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h z ih =>
    rw [insideRun, run_snoc, List.map_append, List.map_singleton, insideRun, run_snoc, ← insideRun,
      ← insideRun, ih]
    congr 1
    apply propext
    constructor
    · rintro ⟨y, hy, hi⟩
      exact ⟨_, by simpa only [List.map_append, List.map_singleton] using (mem_liftMBO.mp hy).1, by
        rw [IsInside, outsideMap_forgetMBO_fst]; exact hi⟩
    · rintro ⟨y, hy, hi⟩
      refine ⟨outsideMap (tagMBO (latestMBO (h ++ [z]))) y,
        (Part.mem_map_iff _).mpr ⟨y, by simpa using hy, rfl⟩, ?_⟩
      rw [IsInside, outsideMap_tagMBO_fst]
      exact hi

/-- The lift of a DDC is a DDC with the same bound. -/
theorem IsDDC.liftMBO {b : ℕ} {a : InsideOutsideSystem O J U V X Y} (ha : IsDDC b a) :
    IsDDC b (SystemAlgebra.liftMBO a) where
  dds := ⟨fun hd => ha.dds.1 hd, fun l₁ l₂ hp hne hd =>
    ha.dds.2 (hp.map _) (by simpa using hne) hd⟩
  admits h z hd := by
    have := ha.admits (h.map (insideMap forgetMBO)) (insideMap forgetMBO z)
      (by simpa only [liftMBO_dom, List.map_append, List.map_singleton] using hd)
    rw [Admits, ← replyLabel_liftMBO, insideMap_forgetMBO_fst] at this
    exact this
  bound h hd := by
    rw [insideRun_liftMBO]
    exact ha.bound _ hd
  replies h y o hy hl := by
    have := ha.replies _ _ o (mem_liftMBO.mp hy).1 (by rw [outsideMap_forgetMBO_fst]; exact hl)
    rwa [lastOuter_insideMap_forgetMBO] at this

/-- A converter transcript with the MBOs of its inside replies and outside replies forgotten. -/
def forgetConverterMBO
    (h : List ((Σ l, twoFam U (withMBO Y) l) × (Σ l, twoFam (withMBO V) X l))) :
    List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l)) :=
  h.map (Prod.map (insideMap forgetMBO) (outsideMap forgetMBO))

/-- **The outside replies of a converter transcript carry the latest inside MBO.** -/
def TaggedMBO
    (h : List ((Σ l, twoFam U (withMBO Y) l) × (Σ l, twoFam (withMBO V) X l))) : Prop :=
  ∀ p z t, h = p ++ z :: t →
    z.2 = outsideMap (tagMBO (latestMBO (p.map Prod.fst ++ [z.1]))) (outsideMap forgetMBO z.2)

theorem taggedMBO_snoc
    {h : List ((Σ l, twoFam U (withMBO Y) l) × (Σ l, twoFam (withMBO V) X l))} {z} :
    TaggedMBO (h ++ [z]) ↔ TaggedMBO h ∧
      z.2 = outsideMap (tagMBO (latestMBO (h.map Prod.fst ++ [z.1])))
        (outsideMap forgetMBO z.2) := by
  constructor
  · intro ht
    exact ⟨fun p w t he => ht p w (t ++ [z]) (by rw [he]; simp), ht h z [] rfl⟩
  · rintro ⟨ht, hz⟩ p w t he
    rcases List.eq_nil_or_concat t with rfl | ⟨t, v, rfl⟩
    · have he' : h ++ [z] = p ++ [w] := he
      obtain ⟨rfl, hw⟩ := List.append_inj' he' rfl
      obtain rfl : z = w := by simpa using hw
      exact hz
    · rw [List.concat_eq_append] at he
      have he' : h ++ [z] = (p ++ w :: t) ++ [v] := by rw [he]; simp
      obtain ⟨rfl, -⟩ := List.append_inj' he' rfl
      exact ht p w t rfl

/-- **The transcripts of a lift** are the transcripts of the converter with the MBOs forgotten
whose outside replies carry the latest inside MBO. -/
theorem replies_liftMBO_iff (a : InsideOutsideSystem O J U V X Y)
    (h : List ((Σ l, twoFam U (withMBO Y) l) × (Σ l, twoFam (withMBO V) X l))) :
    Replies (liftMBO a) (h.map Prod.fst) (h.map Prod.snd) ↔
      Replies a ((forgetConverterMBO h).map Prod.fst) ((forgetConverterMBO h).map Prod.snd) ∧
        TaggedMBO h := by
  induction h using List.reverseRecOn with
  | nil => simp [forgetConverterMBO, TaggedMBO]
  | append_singleton h z ih =>
    simp only [forgetConverterMBO, List.map_append, List.map_singleton, replies_snoc,
      taggedMBO_snoc] at ih ⊢
    rw [ih]
    have hz : liftMBO a (h.map Prod.fst ++ [z.1]) = Part.some z.2 ↔
        a ((h.map (Prod.map (insideMap forgetMBO) (outsideMap forgetMBO))).map Prod.fst ++
          [(Prod.map (insideMap forgetMBO) (outsideMap forgetMBO) z).1]) =
            Part.some (Prod.map (insideMap forgetMBO) (outsideMap forgetMBO) z).2 ∧
          z.2 = outsideMap (tagMBO (latestMBO (h.map Prod.fst ++ [z.1])))
            (outsideMap forgetMBO z.2) := by
      rw [Part.eq_some_iff, Part.eq_some_iff, mem_liftMBO]
      simp only [List.map_append, List.map_map, List.map_singleton, Prod.map_fst, Prod.map_snd]
      rfl
    rw [hz]
    tauto

/-- Forgetting the MBOs keeps the labels of a converter transcript. -/
theorem admitted_forgetConverterMBO
    (h : List ((Σ l, twoFam U (withMBO Y) l) × (Σ l, twoFam (withMBO V) X l))) :
    Admitted converterAdmits (forgetConverterMBO h) ↔ Admitted converterAdmits h :=
  admitted_map_iff (insideMap forgetMBO) (outsideMap forgetMBO) id id Function.injective_id
    (fun z => by rw [insideMap_forgetMBO_fst]; rcases z with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, y⟩ <;> rfl)
    (fun z => by rw [outsideMap_forgetMBO_fst]; rcases z with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, y⟩ <;> rfl) h

theorem outsideInputs_insideMap_forgetMBO (xs : List (Σ l, twoFam U (withMBO Y) l)) :
    outsideInputs (xs.map (insideMap forgetMBO)) = outsideInputs xs := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    rw [List.map_append, outsideInputs_append, outsideInputs_append, ih]
    congr 1
    rcases x with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, u⟩ <;>
      simp [outsideInputs, insideMap, splitIn, restrict_cons_self, restrict_cons_ne]

variable {E : List (Σ j, X j) → Prop} {F : List (Σ o, U o) → Prop}

/-- Forgetting the MBOs keeps the converter domain. -/
theorem converterDomain_forgetConverterMBO
    (h : List ((Σ l, twoFam U (withMBO Y) l) × (Σ l, twoFam (withMBO V) X l)))
    (x : Σ l, twoFam U (withMBO Y) l) :
    converterDomain E F (forgetConverterMBO h) (insideMap forgetMBO x) ↔
      converterDomain E F h x := by
  have hadm : converterAdmits (forgetConverterMBO h) (insideMap forgetMBO x) ↔
      converterAdmits h x :=
    converterAdmits_map_iff (insideMap forgetMBO) (outsideMap forgetMBO) id id Function.injective_id
      (fun z => by rw [insideMap_forgetMBO_fst]; rcases z with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, y⟩ <;> rfl)
      (fun z => by rw [outsideMap_forgetMBO_fst]; rcases z with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, y⟩ <;> rfl) h x
  have hout : outsideInputs ((forgetConverterMBO h).map Prod.fst ++ [insideMap forgetMBO x]) =
      outsideInputs (h.map Prod.fst ++ [x]) := by
    rw [← outsideInputs_insideMap_forgetMBO (h.map Prod.fst ++ [x])]
    simp [forgetConverterMBO, List.map_map, Function.comp_def]
  have hin : insideQueries ((forgetConverterMBO h).map Prod.snd) =
      insideQueries (h.map Prod.snd) := by
    rw [← insideQueries_outsideMap forgetMBO (h.map Prod.snd)]
    simp [forgetConverterMBO, List.map_map, Function.comp_def]
  simp only [converterDomain, admitted_forgetConverterMBO, hadm, hout, hin]

/-- **The lift of a DDC from `E` to `F`** is a DDC from `E` to `F`. -/
theorem IsDDCFrom.liftMBO {b : ℕ} {a : InsideOutsideSystem O J U V X Y}
    (ha : IsDDCFrom E F b a) : IsDDCFrom E F b (SystemAlgebra.liftMBO a) where
  isDDC := ha.isDDC.liftMBO
  answers h x hr := by
    have hr' := ((replies_liftMBO_iff a h).mp hr).1
    rw [liftMBO_dom, ← converterDomain_forgetConverterMBO, ← ha.answers _ _ hr']
    simp [forgetConverterMBO, List.map_map, Function.comp_def]
  queries h hr := by
    have := ha.queries _ ((replies_liftMBO_iff a h).mp hr).1
    have hin : insideQueries ((forgetConverterMBO h).map Prod.snd) =
        insideQueries (h.map Prod.snd) := by
      rw [← insideQueries_outsideMap forgetMBO (h.map Prod.snd)]
      simp [forgetConverterMBO, List.map_map, Function.comp_def]
    rwa [hin] at this

/-- Lifting commutes with restricting to the outside inputs in a domain. -/
theorem liftMBO_filterDom (P : List (Σ o, U o) → Prop) (a : InsideOutsideSystem O J U V X Y) :
    liftMBO (filterDom (fun h => P (outsideInputs h)) a) =
      filterDom (fun h => P (outsideInputs h)) (liftMBO a) := by
  funext h
  simp only [liftMBO, filterDom, outsideInputs_insideMap_forgetMBO]
  split_ifs <;> simp

theorem admissible_liftMBO_iff (a : InsideOutsideSystem O J U V X Y) (h) :
    Admissible (liftMBO a) h ↔ Admissible a (h.map (insideMap forgetMBO)) := by
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h z ih =>
    rw [admissible_snoc, List.map_append, List.map_singleton, admissible_snoc, ih, Admits, Admits,
      replyLabel_liftMBO, insideMap_forgetMBO_fst, liftMBO_dom]
    simp

/-- Lifting commutes with restricting a converter to its admissible histories. -/
theorem liftMBO_canon (a : InsideOutsideSystem O J U V X Y) :
    liftMBO (canon a) = canon (liftMBO a) := by
  funext h
  simp only [liftMBO, canon, admissible_liftMBO_iff]
  split_ifs <;> simp

/-- **The lift of the forwarding converter** is the forwarding converter: an outside reply
forwards the latest inside reply with its MBO. -/
theorem liftMBO_forwardAll : liftMBO (forwardAll J X Y) = forwardAll J X (withMBO Y) := by
  funext h
  rcases List.eq_nil_or_concat h with rfl | ⟨h, z, rfl⟩
  · simp [liftMBO, forwardAll]
  · rw [List.concat_eq_append]
    rcases z with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, y⟩
    · simp only [liftMBO, List.map_append, List.map_singleton]
      change Part.map _ (forwardAll J X Y (_ ++ [⟨⟨none, j⟩, y⟩])) = _
      rw [forwardAll_snoc_outer, forwardAll_snoc_outer]
      rfl
    · simp only [liftMBO, List.map_append, List.map_singleton]
      change Part.map _ (forwardAll J X Y (_ ++ [⟨⟨some (), j⟩, y.1⟩])) = _
      rw [forwardAll_snoc_inner, forwardAll_snoc_inner, latestMBO_snoc]
      rfl

/-- **The lift of a filter** is the filter on replies with the MBO. -/
theorem liftMBO_filter (D : List (Σ j, X j) → Prop) (hD : ∀ {p h}, p <+: h → D h → D p) :
    liftMBO (DDC.filter (Y := Y) D hD).1 = (DDC.filter (Y := withMBO Y) D hD).1 := by
  change liftMBO (filterDom _ (canon (forwardAll J X Y))) = filterDom _ (canon _)
  rw [liftMBO_filterDom, liftMBO_canon, liftMBO_forwardAll]

end LiftDDC

/-! ## The lift of a PDC -/

section LiftPDC

variable {O J : Type} [Fintype O] [Fintype J] {U V : O → Type} {X Y : J → Type}
  [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] [∀ j, Fintype (X j)] [∀ j, Fintype (Y j)]
  {E : List (Σ j, X j) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
  {F : List (Σ o, U o) → Prop} {n : ℕ} {hF : ∀ h, F h → h.length ≤ n}

/-- The lifts of the DDCs of a presentation. -/
noncomputable def liftPresentation {b : ℕ}
    (P : Distribution.ProbDist {a : InsideOutsideSystem O J U V X Y // IsDDCFrom E F b a}) :
    Distribution.ProbDist
      {c : InsideOutsideSystem O J U (withMBO V) X (withMBO Y) // IsDDCFrom E F b c} :=
  ⟨Distribution.fTransform (fun a => ⟨liftMBO a.1, a.2.liftMBO⟩) P.1,
    Distribution.fTransform_isProbDist _ P.2⟩

omit [Fintype O] [Fintype J] [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] [∀ j, Fintype (X j)]
  [∀ j, Fintype (Y j)] in
/-- On a converter transcript, the lifted presentation gives the mass of the transcript with the
MBOs forgotten when its outside replies carry the latest inside MBO, and zero otherwise. -/
theorem behaviorMass_liftPresentation {b : ℕ}
    (P : Distribution.ProbDist {a : InsideOutsideSystem O J U V X Y // IsDDCFrom E F b a})
    (h : List ((Σ l, twoFam U (withMBO Y) l) × (Σ l, twoFam (withMBO V) X l))) :
    behaviorMass (liftPresentation P).1 (h.map Prod.fst) (h.map Prod.snd) =
      if TaggedMBO h then
        behaviorMass P.1 ((forgetConverterMBO h).map Prod.fst) ((forgetConverterMBO h).map Prod.snd)
      else 0 := by
  simp only [behaviorMass, liftPresentation, Distribution.mass_fTransform, replies_liftMBO_iff]
  split_ifs with ht
  · exact Distribution.mass_congr _ fun a => and_iff_left ht
  · exact Distribution.mass_eq_zero_of_forall_not _ fun a ha => ht ha.2

/-- **The MBO-forwarding lift** of a PDC: the PDC of the lifts of a presentation. -/
noncomputable def PDCBehavior.liftMBO (α : PDCBehavior O J U V X Y E m hE F n hF) :
    PDCBehavior O J U (withMBO V) X (withMBO Y) E m hE F n hF :=
  PDCBehavior.ofPDC (liftPresentation α.2.choose_spec.choose)

/-- **The transcripts of a lifted PDC**: the mass of a transcript with the MBOs forgotten, when
its outside replies carry the latest inside MBO. -/
theorem PDCBehavior.liftMBO_apply (α : PDCBehavior O J U V X Y E m hE F n hF)
    (h : List ((Σ l, twoFam U (withMBO Y) l) × (Σ l, twoFam (withMBO V) X l))) :
    (PDCBehavior.liftMBO α).1 h = if TaggedMBO h then α.1 (forgetConverterMBO h) else 0 := by
  change behaviorMass (liftPresentation α.2.choose_spec.choose).1 _ _ = _
  rw [behaviorMass_liftPresentation, α.2.choose_spec.choose_spec]

/-- Any presentation of a PDC lifts to a presentation of its lift. -/
theorem PDCBehavior.liftMBO_presents (α : PDCBehavior O J U V X Y E m hE F n hF) {b : ℕ}
    (P : Distribution.ProbDist {a : InsideOutsideSystem O J U V X Y // IsDDCFrom E F b a})
    (hP : ∀ h, behaviorMass P.1 (h.map Prod.fst) (h.map Prod.snd) = α.1 h) (h) :
    behaviorMass (liftPresentation P).1 (h.map Prod.fst) (h.map Prod.snd) =
      (PDCBehavior.liftMBO α).1 h := by
  rw [behaviorMass_liftPresentation, hP, PDCBehavior.liftMBO_apply]

/-- The lift of the behavior of a DDC is the behavior of its lift. -/
theorem PDCBehavior.liftMBO_ofDDC (a : InsideOutsideSystem O J U V X Y) {b : ℕ}
    (ha : IsDDCFrom E F b a) :
    PDCBehavior.liftMBO (PDCBehavior.ofDDC a ha : PDCBehavior O J U V X Y E m hE F n hF) =
      PDCBehavior.ofDDC (SystemAlgebra.liftMBO a) ha.liftMBO := by
  apply PDCBehavior.ext
  intro h
  rw [PDCBehavior.liftMBO_apply, PDCBehavior.ofDDC_apply, PDCBehavior.ofDDC_apply,
    replies_liftMBO_iff]
  by_cases ht : TaggedMBO h <;> simp [ht, forgetConverterMBO]

/-- **The lift of the identity** is the identity. -/
theorem PDCBehavior.liftMBO_id (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p) :
    PDCBehavior.liftMBO (PDCBehavior.id (Y := Y) (m := m) (hE := hE) hE') =
      PDCBehavior.id (Y := withMBO Y) hE' := by
  rw [PDCBehavior.id, PDCBehavior.liftMBO_ofDDC]
  apply PDCBehavior.ext
  intro h
  rw [PDCBehavior.id, PDCBehavior.ofDDC_apply, PDCBehavior.ofDDC_apply,
    liftMBO_filter _ (prefix_or_nil hE'.2)]

end LiftPDC

/-! ## Attaching a lift, and the visible system -/

section Visible

variable {O J : Type} {U V : O → Type} {X Y : J → Type}

/-- Relabeling the outside replies of an attachment relabels those of the converter. -/
theorem relabel_apply_outside {V' : O → Type} (c : InsideOutsideSystem O J U V' X Y)
    (R : InterfaceSystem J X Y) (g : (Σ o, V' o) → (Σ o, V o)) :
    relabel (apply c R) id g = apply (relabel c id (outsideMap g)) R := by
  rw [apply_eq, apply_eq, relabel_interconnect, pair_relabel_left, interconnect_relabel]
  congr 1
  funext y
  rcases y with ⟨_ | ⟨⟩, y⟩
  · rcases y with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩ <;> rfl
  · rfl

/-- A converter relabeling its inside replies, attached to a resource, is the converter attached
to the resource with its replies relabeled. -/
theorem apply_relabel_inside {Y' : J → Type} (c : InsideOutsideSystem O J U V X Y)
    (R : InterfaceSystem J X Y') (k : (Σ j, Y' j) → (Σ j, Y j)) :
    apply (relabel c (insideMap k) id) R = apply c (relabel R id k) := by
  rw [apply_eq, apply_eq, pair_relabel_left, interconnect_relabel, pair_relabel_right,
    interconnect_relabel]
  congr 1
  · funext y
    rcases y with ⟨_ | ⟨⟩, y⟩
    · rcases y with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩ <;> rfl
    · rfl

/-- **Attaching a lift and forgetting the MBO** is attaching the converter to the system with the
MBO forgotten. -/
theorem relabel_trim_apply_liftMBO (a : InsideOutsideSystem O J U V X Y)
    (s : InterfaceSystem J X (withMBO Y)) :
    relabel (trim (apply (liftMBO a) s)) id forgetMBO =
      trim (apply a (relabel s id forgetMBO)) := by
  rw [← trim_relabel, relabel_apply_outside, relabel_liftMBO, apply_relabel_inside]

variable [Fintype O] [Fintype J] [∀ o, Fintype (U o)] [∀ o, Fintype (V o)]
  [∀ j, Fintype (X j)] [∀ j, Fintype (Y j)]
  {E : List (Σ j, X j) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
  {F : List (Σ o, U o) → Prop} {n : ℕ} {hF : ∀ h, F h → h.length ≤ n}

omit [Fintype O] [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] in
/-- The visible systems of a presentation of a game. -/
noncomputable def visiblePresentation
    (Q : Distribution.ProbDist {s : InterfaceSystem J X (withMBO Y) //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ E h}) :
    Distribution.ProbDist {s : InterfaceSystem J X Y //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ E h} :=
  ⟨Distribution.fTransform (fun s => ⟨relabel s.1 id forgetMBO,
      ⟨fun hd => s.2.1.1 (by simpa [relabel] using hd),
        fun _ _ hp hne hd => by
          simp only [relabel, List.map_id, Part.map_Dom] at hd ⊢
          exact s.2.1.2 hp hne hd⟩,
      s.2.2.1.relabel id forgetMBO (fun _ _ h => h),
      fun h => by simpa [relabel] using s.2.2.2 h⟩) Q.1,
    Distribution.fTransform_isProbDist _ Q.2⟩

omit [Fintype O] [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] in
/-- The visible systems of a presentation of a game present its visible system. -/
theorem behaviorMass_visiblePresentation
    (Q : Distribution.ProbDist {s : InterfaceSystem J X (withMBO Y) //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ E h})
    {G : RandomSystem (Σ j, X j) (Σ j, withMBO Y j) (Domain.ofInputs E m hE)}
    (hQ : ∀ h, behaviorMass Q.1 (h.map Prod.fst) (h.map Prod.snd) = G h)
    (h : List ((Σ j, X j) × Σ j, Y j)) :
    behaviorMass (visiblePresentation Q).1 (h.map Prod.fst) (h.map Prod.snd) = G.visible h := by
  rw [RandomSystem.visible_apply]
  have hG : (G : List ((Σ j, X j) × Σ j, withMBO Y j) → ℝ) =
      fun k => ∑ s ∈ Q.1.support, Q.1 s *
        if Replies s.1 (k.map Prod.fst) (k.map Prod.snd) then 1 else 0 := by
    funext k
    rw [← hQ k, behaviorMass, Distribution.mass, Finsupp.sum]
    exact Finset.sum_congr rfl fun s _ => by split_ifs <;> simp
  rw [hG, sumMBO_sum]
  simp only [sumMBO_const_mul, sumMBO_replies]
  rw [visiblePresentation, behaviorMass, Distribution.mass_fTransform, Distribution.mass,
    Finsupp.sum]
  exact Finset.sum_congr rfl fun s _ => by split_ifs <;> simp

/-- **Attaching a lift attaches to the visible system**: `(R g)⁻ = R g⁻`. -/
theorem RandomSystem.visible_attach_liftMBO
    (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (α : PDCBehavior O J U V X Y E m hE F n hF)
    (G : RandomSystem (Σ j, X j) (Σ j, withMBO Y j) (Domain.ofInputs E m hE))
    (hG : G.RepliesAtQueriedInterface) :
    (PDCBehavior.attach hE' hF' (PDCBehavior.liftMBO α) G hG).visible =
      PDCBehavior.attach hE' hF' α G.visible hG.visible := by
  obtain ⟨b, P, hP⟩ := α.2
  obtain ⟨Q, hQ⟩ := RandomSystem.exists_resource_presentation hE' G hG
  ext h
  rw [RandomSystem.visible_apply, PDCBehavior.attach_presents hE' hF' α G.visible hG.visible P
    (visiblePresentation Q) hP (behaviorMass_visiblePresentation Q hQ) h,
    behaviorMass_attachPDS, visiblePresentation, Distribution.fTransform_prod_right,
    Distribution.mass_fTransform]
  have hL : (PDCBehavior.attach hE' hF' (PDCBehavior.liftMBO α) G hG :
      List ((Σ o, U o) × Σ o, withMBO V o) → ℝ) = fun k =>
        ∑ st ∈ (Distribution.prod P.1 Q.1).support, Distribution.prod P.1 Q.1 st *
          if Replies (trim (apply (liftMBO st.1.1) st.2.1)) (k.map Prod.fst) (k.map Prod.snd)
          then 1 else 0 := by
    funext k
    rw [PDCBehavior.attach_presents hE' hF' _ G hG (liftPresentation P) Q
      (PDCBehavior.liftMBO_presents α P hP) hQ k, behaviorMass_attachPDS, liftPresentation,
      Distribution.fTransform_prod_left, Distribution.mass_fTransform, Distribution.mass,
      Finsupp.sum]
    refine Finset.sum_congr rfl fun st _ => ?_
    change (if Replies (trim (apply (liftMBO st.1.1) st.2.1)) _ _ then _ else _) = _
    split_ifs <;> simp
  rw [hL, sumMBO_sum]
  simp only [sumMBO_const_mul, sumMBO_replies, relabel_trim_apply_liftMBO]
  rw [Distribution.mass, Finsupp.sum]
  refine Finset.sum_congr rfl fun st _ => ?_
  change _ = (if Replies (trim (apply st.1.1 (SystemAlgebra.relabel st.2.1 id forgetMBO))) _ _
    then _ else _)
  split_ifs <;> simp

end Visible

/-! ## Attaching a lift to a game gives a game -/

section Monotone

variable {O J : Type} {U V : O → Type} {X Y : J → Type}

theorem latestMBO_eq (l : List (Σ l, twoFam U (withMBO Y) l)) :
    latestMBO l = ((l.filterMap inputMBO).getLast?).getD false := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l z ih =>
    rw [latestMBO_snoc, ih, List.filterMap_append]
    rcases z with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, y⟩ <;> simp [inputMBO]

theorem getLast?_getD_le {l : List Bool} {b : Bool} (hp : (l ++ [b]).Pairwise (· ≤ ·)) :
    (l.getLast?).getD false ≤ b := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l, c, rfl⟩
  · exact Bool.false_le b
  · rw [List.concat_eq_append] at hp ⊢
    rw [List.getLast?_append, List.getLast?_singleton]
    simp only [Option.some_or, Option.getD_some]
    exact (List.pairwise_append.mp hp).2.2 c (by simp) b (by simp)

/-- The MBO of a reply of the resource that is about to be returned to the converter. -/
def pendingMBO (ys : List (Two (Σ l, twoFam (withMBO V) X l) (Σ j, withMBO Y j))) : List Bool :=
  match ys.getLast? with
  | some ⟨some (), r⟩ => [r.2.2]
  | _ => []

/-- **Along an attachment of a converter that tags its outside replies with the latest inside
MBO**, the resource replies with monotone MBOs as the converter receives them, and the exposed
MBOs are monotone and below the latest inside MBO. -/
theorem attach_tags_invariant {c : InsideOutsideSystem O J U (withMBO V) X (withMBO Y)}
    (hc : ∀ h (o : O) (v : withMBO V o), ⟨⟨none, o⟩, v⟩ ∈ c h → v.2 = latestMBO h)
    {R : InterfaceSystem J X (withMBO Y)}
    (hR : ∀ t : List ((Σ j, X j) × Σ j, withMBO Y j), Replies R (t.map Prod.fst) (t.map Prod.snd) →
      (t.map fun z => z.2.2.2).Pairwise (· ≤ ·))
    {us : List (Σ o, U o)} {xs ys}
    (tr : Transcript (pair c R) (connectionQueries resourceRoute resourceInput us) xs ys) :
    Replies R (restrict (some ()) xs) (restrict (some ()) ys) ∧
      (restrict (some ()) ys).map (fun r => r.2.2) =
        (restrict none xs).filterMap inputMBO ++ pendingMBO ys ∧
      ((exposedReplies (resourceRoute (U := U)) ys).map fun v => v.2.2).Pairwise (· ≤ ·) ∧
      ∀ b ∈ (exposedReplies (resourceRoute (U := U)) ys).map (fun v => v.2.2),
        b ≤ latestMBO (restrict none xs) := by
  induction tr with
  | nil => simp [pendingMBO, exposedReplies]
  | @snoc xs ys x y tr hx hy ih =>
    obtain ⟨hr, hbits, hmono, hle⟩ := ih
    -- The resource's transcripts have monotone MBOs.
    have hRmono : ∀ {xs' ys'}, Replies R xs' ys' → (ys'.map fun r => r.2.2).Pairwise (· ≤ ·) := by
      intro xs' ys' hr'
      have hl : xs'.length = ys'.length := hr'.length.symm
      have := hR (xs'.zip ys') (by rwa [List.map_fst_zip (le_of_eq hl),
        List.map_snd_zip (le_of_eq hl.symm)])
      have hm : ((xs'.zip ys').map fun z => z.2.2.2) = (ys'.map fun r => r.2.2) := by
        rw [show (fun z : (Σ j, X j) × (Σ j, withMBO Y j) => z.2.2.2) =
          (fun r : Σ j, withMBO Y j => r.2.2) ∘ Prod.snd from rfl, ← List.map_map,
          List.map_snd_zip (le_of_eq hl.symm)]
      rwa [hm] at this
    -- What the connection feeds next.
    have hfeed : (∃ u, x = resourceInput u ∧ pendingMBO ys = []) ∨
        (∃ ys' : List (Two (Σ l, twoFam (withMBO V) X l) (Σ j, withMBO Y j)),
          ∃ (j : J) (r : withMBO Y j),
            ys = ys' ++ [⟨some (), ⟨j, r⟩⟩] ∧ x = ⟨none, ⟨⟨some (), j⟩, r⟩⟩) ∨
        (∃ ys' : List (Two (Σ l, twoFam (withMBO V) X l) (Σ j, withMBO Y j)),
          ∃ (j : J) (q : X j),
            ys = ys' ++ [⟨none, ⟨⟨some (), j⟩, q⟩⟩] ∧ x = ⟨some (), ⟨j, q⟩⟩) := by
      rcases List.eq_nil_or_concat ys with rfl | ⟨ys', y', rfl⟩
      · left
        rw [connectionQueries_nil] at hx
        cases us with
        | nil => exact absurd hx (by simp)
        | cons u us =>
          refine ⟨u, ?_, rfl⟩
          simpa [eq_comm] using hx
      · rw [List.concat_eq_append] at hx ⊢
        have hd' := connectionQueries_prefix _ _ _ _ _ (Part.dom_iff_mem.mpr ⟨x, hx⟩)
        rcases y' with ⟨_ | ⟨⟩, y'⟩
        · rcases y' with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩
          · left
            have hx' := (connectionQueries_snoc_out resourceRoute resourceInput us ys'
              (y := ⟨none, ⟨⟨none, o⟩, v⟩⟩) (b := ⟨o, v⟩) rfl) ▸ hx
            simp only [Part.mem_ofOption, Option.mem_def, Option.map_eq_some_iff] at hx'
            obtain ⟨u, -, rfl⟩ := hx'
            exact ⟨u, rfl, by simp [pendingMBO]⟩
          · right; right
            have hx' := (connectionQueries_snoc_in resourceRoute resourceInput us ys'
              (y := ⟨none, ⟨⟨some (), o⟩, v⟩⟩) (x := ⟨some (), ⟨o, v⟩⟩) rfl hd') ▸ hx
            exact ⟨ys', o, v, rfl, Part.mem_some_iff.mp hx'⟩
        · right; left
          rcases y' with ⟨j, r⟩
          have hx' := (connectionQueries_snoc_in resourceRoute resourceInput us ys'
            (y := ⟨some (), ⟨j, r⟩⟩) (x := ⟨none, ⟨⟨some (), j⟩, r⟩⟩) rfl hd') ▸ hx
          exact ⟨ys', j, r, rfl, Part.mem_some_iff.mp hx'⟩
    -- The latest inside MBO never decreases.
    have hlatest : ∀ cx, (∀ b, inputMBO cx = some b →
        ((restrict none xs).filterMap inputMBO ++ [b]).Pairwise (· ≤ ·)) →
        latestMBO (restrict none xs) ≤ latestMBO (restrict none xs ++ [cx]) := by
      intro cx hcx
      rw [latestMBO_snoc]
      cases hb : inputMBO cx with
      | none => exact le_rfl
      | some b =>
        rw [latestMBO_eq]
        exact getLast?_getD_le (hcx b hb)
    rcases hfeed with ⟨u, rfl, hpend⟩ | ⟨ys', j, r, rfl, rfl⟩ | ⟨ys', j, q, rfl, rfl⟩
    · -- An outside query of the converter.
      simp only [resourceInput] at hy ⊢
      rw [pair_left] at hy
      obtain ⟨cy, hcy, rfl⟩ := (Part.mem_map_iff _).mp hy
      have hl := hlatest ⟨⟨none, u.1⟩, u.2⟩ (fun b hb => by simp [inputMBO] at hb)
      simp only [restrict_none_snoc_left, restrict_some_snoc_left, List.filterMap_append,
        inputMBO, List.filterMap_cons, List.filterMap_nil, List.append_nil] at hl ⊢
      refine ⟨hr, by rw [hbits, hpend]; simp [pendingMBO], ?_⟩
      rcases cy with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩
      · have hv := hc _ o v hcy
        rw [exposedReplies_snoc_out resourceRoute _ (y := ⟨none, ⟨⟨none, o⟩, v⟩⟩) (b := ⟨o, v⟩) rfl,
          List.map_append, List.map_singleton]
        refine ⟨List.pairwise_append.mpr ⟨hmono, List.pairwise_singleton _ _,
          fun a ha b hb => ?_⟩, fun b hb => ?_⟩
        · rw [List.mem_singleton.mp hb, hv]
          exact (hle a ha).trans hl
        · rcases List.mem_append.mp hb with hb | hb
          · exact (hle b hb).trans hl
          · rw [List.mem_singleton.mp hb, hv]
      · rw [exposedReplies_snoc_in resourceRoute _ (y := ⟨none, ⟨⟨some (), o⟩, v⟩⟩)
          (x := ⟨some (), ⟨o, v⟩⟩) rfl]
        exact ⟨hmono, fun b hb => (hle b hb).trans hl⟩
    · -- A reply of the resource returned to the converter.
      rw [pair_left] at hy
      obtain ⟨cy, hcy, rfl⟩ := (Part.mem_map_iff _).mp hy
      have hpend :
          pendingMBO (ys' ++ [(⟨some (), ⟨j, r⟩⟩ : Two _ (Σ j, withMBO Y j))]) = [r.2] := by
        simp [pendingMBO]
      have hRm := hRmono hr
      rw [hbits, hpend] at hRm
      have hl := hlatest ⟨⟨some (), j⟩, r⟩ (fun b hb => by
        simp only [inputMBO, Option.some.injEq] at hb
        rwa [← hb])
      have hlast : latestMBO (restrict none xs ++ [⟨⟨some (), j⟩, r⟩]) = r.2 := by
        rw [latestMBO_snoc]; rfl
      simp only [restrict_none_snoc_left, restrict_some_snoc_left] at hl hlast ⊢
      refine ⟨by simpa using hr, by
        rw [hbits, hpend]
        simp [pendingMBO, List.filterMap_append, inputMBO], ?_⟩
      rcases cy with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩
      · have hv := hc _ o v hcy
        rw [hlast] at hv
        rw [exposedReplies_snoc_out resourceRoute _ (y := ⟨none, ⟨⟨none, o⟩, v⟩⟩) (b := ⟨o, v⟩) rfl,
          List.map_append, List.map_singleton]
        refine ⟨List.pairwise_append.mpr ⟨hmono, List.pairwise_singleton _ _,
          fun a ha b hb => ?_⟩, fun b hb => ?_⟩
        · rw [List.mem_singleton.mp hb, hv, ← hlast]
          exact (hle a ha).trans hl
        · rw [hlast]
          rcases List.mem_append.mp hb with hb | hb
          · rw [← hlast]; exact (hle b hb).trans hl
          · rw [List.mem_singleton.mp hb, hv]
      · rw [exposedReplies_snoc_in resourceRoute _ (y := ⟨none, ⟨⟨some (), o⟩, v⟩⟩)
          (x := ⟨some (), ⟨o, v⟩⟩) rfl]
        exact ⟨hmono, fun b hb => (hle b hb).trans hl⟩
    · -- An inside query of the converter forwarded to the resource.
      rw [pair_right] at hy
      obtain ⟨r', hr', rfl⟩ := (Part.mem_map_iff _).mp hy
      have hpend :
          pendingMBO (ys' ++ [(⟨none, ⟨⟨some (), j⟩, q⟩⟩ : Two _ (Σ j, withMBO Y j))]) = [] := by
        simp [pendingMBO]
      simp only [restrict_none_snoc_right, restrict_some_snoc_right]
      refine ⟨replies_snoc.mpr ⟨hr, Part.eq_some_iff.mpr hr'⟩, ?_, ?_⟩
      · rw [List.map_append, hbits, hpend]
        simp [pendingMBO]
      · rw [exposedReplies_snoc_in resourceRoute _ (y := ⟨some (), r'⟩)
          (x := ⟨none, ⟨⟨some (), r'.1⟩, r'.2⟩⟩) rfl]
        exact ⟨hmono, hle⟩

/-- **Attaching a converter that tags its outside replies with the latest inside MBO** to a
resource with monotone MBOs gives transcripts with monotone MBOs. -/
theorem replies_apply_monotone {c : InsideOutsideSystem O J U (withMBO V) X (withMBO Y)}
    (hc : ∀ h (o : O) (v : withMBO V o), ⟨⟨none, o⟩, v⟩ ∈ c h → v.2 = latestMBO h)
    {R : InterfaceSystem J X (withMBO Y)}
    (hR : ∀ t : List ((Σ j, X j) × Σ j, withMBO Y j), Replies R (t.map Prod.fst) (t.map Prod.snd) →
      (t.map fun z => z.2.2.2).Pairwise (· ≤ ·))
    {us vs} (hr : Replies (apply c R) us vs) : (vs.map fun v => v.2.2).Pairwise (· ≤ ·) := by
  rw [apply_eq] at hr
  obtain ⟨xs, ys, tr, rfl, -⟩ := (replies_connection_iff us vs).mp hr
  exact (attach_tags_invariant hc hR tr).2.2.1

/-- A lift tags its outside replies with the latest inside MBO. -/
theorem liftMBO_tag (a : InsideOutsideSystem O J U V X Y) (h) (o : O) (v : withMBO V o)
    (hv : ⟨⟨none, o⟩, v⟩ ∈ liftMBO a h) : v.2 = latestMBO h := by
  have he := (mem_liftMBO.mp hv).2
  simp only [outsideMap, forgetMBO, tagMBO, Sigma.mk.inj_iff, heq_eq_eq, true_and] at he
  exact congrArg Prod.snd he

variable [Fintype O] [Fintype J] [∀ o, Fintype (U o)] [∀ o, Fintype (V o)]
  [∀ j, Fintype (X j)] [∀ j, Fintype (Y j)]
  {E : List (Σ j, X j) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
  {F : List (Σ o, U o) → Prop} {n : ℕ} {hF : ∀ h, F h → h.length ≤ n}

/-- **Attaching a lift to a game gives a game**: the outside MBO is the MBO of the latest
inside reply, which, once set, stays set. -/
theorem RandomSystem.MonotoneMBO.attach_liftMBO
    (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (α : PDCBehavior O J U V X Y E m hE F n hF)
    {G : RandomSystem (Σ j, X j) (Σ j, withMBO Y j) (Domain.ofInputs E m hE)}
    (hG : G.RepliesAtQueriedInterface) (hm : G.MonotoneMBO) :
    (PDCBehavior.attach hE' hF' (PDCBehavior.liftMBO α) G hG).MonotoneMBO := by
  obtain ⟨b, P, hP⟩ := α.2
  obtain ⟨Q, hQ⟩ := RandomSystem.exists_resource_presentation hE' G hG
  intro k hk
  rw [PDCBehavior.attach_presents hE' hF' _ G hG (liftPresentation P) Q
    (PDCBehavior.liftMBO_presents α P hP) hQ k, behaviorMass_attachPDS] at hk
  obtain ⟨st, hst, hrep⟩ : ∃ st ∈ (Distribution.prod (liftPresentation P).1 Q.1).support,
      Replies (trim (apply st.1.1 st.2.1)) (k.map Prod.fst) (k.map Prod.snd) := by
    by_contra hn
    push Not at hn
    apply hk
    rw [Distribution.mass_congr_of_support _ (Q := fun _ => False)
      (fun a ha => iff_false_intro (hn a ha))]
    exact Distribution.mass_eq_zero_of_forall_not _ (fun _ h => h)
  have hmem := Finset.mem_product.mp (Distribution.support_prod_subset _ _ hst)
  obtain ⟨a, -, ha⟩ := Distribution.mem_support_fTransform _ _ hmem.1
  -- The sample of the game has transcripts of positive mass, whose MBO is monotone.
  have hs : ∀ t : List ((Σ j, X j) × Σ j, withMBO Y j),
      Replies st.2.1 (t.map Prod.fst) (t.map Prod.snd) →
        (t.map fun z => z.2.2.2).Pairwise (· ≤ ·) := by
    intro t ht
    apply hm t
    have hpos : 0 < Q.1 st.2 :=
      lt_of_le_of_ne (Q.2.1 st.2) (Ne.symm (Finsupp.mem_support_iff.mp hmem.2))
    rw [← hQ t]
    exact ne_of_gt (lt_of_lt_of_le hpos (Distribution.apply_le_mass Q.2.1 ht))
  have hr := (replies_trim_iff _ _ _).mp hrep
  rw [← ha] at hr
  have := replies_apply_monotone (liftMBO_tag _) hs hr
  rwa [List.map_map] at this

end Monotone

/-! ## Tags through an interconnection of two components -/

section TagRouting

/-- The latest bit read by `b` along a history, unset before any. -/
def latestBy {Z : Type} (b : Z → Option Bool) (h : List Z) : Bool :=
  (h.reverse.findSome? b).getD false

theorem latestBy_snoc {Z : Type} (b : Z → Option Bool) (h : List Z) (z : Z) :
    latestBy b (h ++ [z]) = (b z).getD (latestBy b h) := by
  simp only [latestBy, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.findSome?_cons]
  cases b z <;> rfl

theorem latestMBO_eq_latestBy {O J : Type} {U : O → Type} {Y : J → Type}
    (h : List (Σ l, twoFam U (withMBO Y) l)) : latestMBO h = latestBy inputMBO h := rfl

variable {Xβ Yβ Xα Yα A B : Type}

/-- **Routing of bits through two components**: the inner component `α` tags its replies to the
outer component `β` with its latest bit, and these replies carry their tags to `β`; the
outputs of `α` that leave carry no tag, the outputs of `β` to `α` carry no bit, and the outside
inputs carry their bits to `α` only. -/
structure TagRouting (bβ : Xβ → Option Bool) (bα : Xα → Option Bool) (bA : A → Option Bool)
    (tα : Yα → Option Bool) (α : System Xα Yα) (route : Two Yβ Yα → B ⊕ Two Xβ Xα)
    (inj : A → Two Xβ Xα) : Prop where
  α_tag : ∀ h y c, y ∈ α h → tα y = some c → c = latestBy bα h
  α_to_β : ∀ y x, route ⟨some (), y⟩ = .inr ⟨none, x⟩ → bβ x = tα y ∧ (tα y).isSome
  α_out : ∀ y b, route ⟨some (), y⟩ = .inl b → tα y = none
  α_to_α : ∀ y x, route ⟨some (), y⟩ ≠ .inr ⟨some (), x⟩
  β_to_α : ∀ y x, route ⟨none, y⟩ = .inr ⟨some (), x⟩ → bα x = none
  β_to_β : ∀ y x, route ⟨none, y⟩ ≠ .inr ⟨none, x⟩
  inj_α : ∀ u x, inj u = ⟨some (), x⟩ → bα x = bA u
  inj_β : ∀ u x, inj u = ⟨none, x⟩ → bβ x = none ∧ bA u = none

variable {bβ : Xβ → Option Bool} {bα : Xα → Option Bool} {bA : A → Option Bool}
  {tα : Yα → Option Bool} {β : System Xβ Yβ} {α : System Xα Yα}
  {route : Two Yβ Yα → B ⊕ Two Xβ Xα} {inj : A → Two Xβ Xα}

/-- The inner component has answered its latest input with a tagged reply. -/
def TagReady (tα : Yα → Option Bool) (α : System Xα Yα) (h : List Xα) : Prop :=
  h = [] ∨ ∃ y ∈ α h, (tα y).isSome

/-- The bookkeeping along an exchange: the inner component's latest bit is the latest outside
bit, and once the inner component has answered with a tagged reply that has reached the outer
component, both have the same latest bit. -/
def TagInvariant (bβ : Xβ → Option Bool) (bα : Xα → Option Bool) (bA : A → Option Bool)
    (tα : Yα → Option Bool) (α : System Xα Yα) (u : List A) (H : List (Two Xβ Xα)) : Prop :=
  latestBy bα (restrict (some ()) H) = latestBy bA u ∧
    (TagReady tα α (restrict (some ()) H) → (∀ H₀ z, H ≠ H₀ ++ [⟨some (), z⟩]) →
      latestBy bβ (restrict none H) = latestBy bα (restrict (some ()) H))

theorem tagInvariant_feed (hr : TagRouting bβ bα bA tα α route inj) {u G y x}
    (hy : y ∈ pair β α G) (hx : route y = .inr x)
    (hi : TagInvariant bβ bα bA tα α u G) : TagInvariant bβ bα bA tα α u (G ++ [x]) := by
  obtain ⟨h1, h2⟩ := hi
  rcases List.eq_nil_or_concat G with rfl | ⟨G, z, rfl⟩
  · exact absurd hy (by simp [pair])
  simp only [List.concat_eq_append] at hy h1 h2 ⊢
  rcases z with ⟨_ | ⟨⟨⟩⟩, z⟩
  · -- `β` answered; its output goes to `α` without a bit
    rw [pair_left] at hy
    obtain ⟨yβ, -, rfl⟩ := (Part.mem_map_iff _).mp hy
    rcases x with ⟨_ | ⟨⟨⟩⟩, x⟩
    · exact absurd hx (hr.β_to_β yβ x)
    · have hb := hr.β_to_α yβ x hx
      refine ⟨?_, fun _ hn => absurd rfl (hn _ x)⟩
      rw [restrict_some_snoc_right, latestBy_snoc, hb, Option.getD_none]
      exact h1
  · -- `α` answered; its tagged output goes to `β`
    rw [pair_right] at hy
    obtain ⟨yα, hyα, rfl⟩ := (Part.mem_map_iff _).mp hy
    rcases x with ⟨_ | ⟨⟨⟩⟩, x⟩
    · obtain ⟨hb, hs⟩ := hr.α_to_β yα x hx
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
      have hc' := hr.α_tag _ yα c hyα hc
      refine ⟨by rw [restrict_some_snoc_left]; exact h1, fun _ _ => ?_⟩
      rw [restrict_none_snoc_left, latestBy_snoc, hb, hc, Option.getD_some,
        restrict_some_snoc_left, restrict_some_snoc_right]
      exact hc'
    · exact absurd hx (hr.α_to_α yα x)

theorem tagInvariant_exchange (hr : TagRouting bβ bα bA tα α route inj) {u G o G'}
    (l : Exchange (pair β α) route G o G') (hi : TagInvariant bβ bα bA tα α u G) :
    TagInvariant bβ bα bA tα α u G' := by
  induction l with
  | silent => exact hi
  | out => exact hi
  | feed _ y x _ _ hy hx _ ih => exact ih (tagInvariant_feed hr hy hx hi)

/-- At the end of an exchange the inner component is not waiting with a tagged reply. -/
theorem tagInvariant_end (hr : TagRouting bβ bα bA tα α route inj) {u G o G'}
    (l : Exchange (pair β α) route G o G') (hi : TagInvariant bβ bα bA tα α u G) :
    TagReady tα α (restrict (some ()) G') →
      latestBy bβ (restrict none G') = latestBy bα (restrict (some ()) G') := by
  have hend : ∀ {G o G'}, Exchange (pair β α) route G o G' →
      (¬ (pair β α G').Dom) ∨ ∃ y ∈ pair β α G', ∃ b, route y = .inl b := by
    intro G o G' l
    induction l with
    | silent _ hd => exact Or.inl hd
    | out _ y b hy hb => exact Or.inr ⟨y, hy, b, hb⟩
    | feed _ _ _ _ _ _ _ _ ih => exact ih
  have hi' := tagInvariant_exchange hr l hi
  intro hready
  apply hi'.2 hready
  rintro G₀ z rfl
  rcases hready with he | ⟨yα, hyα, hs⟩
  · simp at he
  rcases hend l with hd | ⟨y, hy, b, hb⟩
  · apply hd
    rw [pair_right]
    exact Part.dom_iff_mem.mpr ⟨_, Part.mem_map _ (by simpa using hyα)⟩
  · rw [pair_right] at hy
    obtain ⟨yα', hyα', rfl⟩ := (Part.mem_map_iff _).mp hy
    have he : yα' = yα := Part.mem_unique hyα' (by simpa using hyα)
    subst he
    rw [hr.α_out yα' b hb] at hs
    exact absurd hs (by simp)

/-- **The tag invariant along an interconnection.** -/
theorem tagInvariant_induces (hr : TagRouting bβ bα bA tα α route inj) {u o H}
    (ri : Induces (pair β α) route inj u o H) :
    TagInvariant bβ bα bA tα α u H ∧ (TagReady tα α (restrict (some ()) H) →
      latestBy bβ (restrict none H) = latestBy bα (restrict (some ()) H)) := by
  induction ri with
  | nil =>
    refine ⟨⟨rfl, fun _ _ => ?_⟩, fun _ => ?_⟩ <;> rfl
  | snoc u a o₀ H o H' ri l ih =>
    obtain ⟨⟨h1, _⟩, h3⟩ := ih
    have hstart : TagInvariant bβ bα bA tα α (u ++ [a]) (H ++ [inj a]) := by
      rcases hinj : inj a with ⟨_ | ⟨⟨⟩⟩, x⟩
      · obtain ⟨hb, ha⟩ := hr.inj_β a x hinj
        refine ⟨?_, fun hready _ => ?_⟩
        · rw [restrict_some_snoc_left, latestBy_snoc, ha]
          exact h1
        · rw [restrict_none_snoc_left, latestBy_snoc, hb, restrict_some_snoc_left]
          exact h3 (by simpa only [restrict_some_snoc_left] using hready)
      · have hb := hr.inj_α a x hinj
        refine ⟨?_, fun _ hn => absurd rfl (hn _ x)⟩
        rw [restrict_some_snoc_right, latestBy_snoc, hb, latestBy_snoc, h1]
    exact ⟨tagInvariant_exchange hr l hstart, tagInvariant_end hr l hstart⟩

/-- The final exposed output of an exchange is an output of the pair. -/
theorem Exchange.exists_out {S : Type} {s : System Xβ S} {route' : S → B ⊕ Xβ} {G b G'}
    (l : Exchange s route' G (some b) G') : ∃ y ∈ s G', route' y = .inl b := by
  generalize hb : (some b : Option B) = ob at l
  induction l with
  | silent => cases hb
  | out _ y _ hy hy' => cases hb; exact ⟨y, hy, hy'⟩
  | feed _ _ _ _ _ _ _ _ ih => exact ih hb

/-- **An exposed output of the outer component carries the latest outside bit**, once the inner
component has answered with a tagged reply: the outer component tags its exposed outputs with
its latest bit. -/
theorem tag_of_induces (hr : TagRouting bβ bα bA tα α route inj) (tB : B → Option Bool)
    (hβ : ∀ h y b c, y ∈ β h → route ⟨none, y⟩ = .inl b → tB b = some c → c = latestBy bβ h)
    (hαB : ∀ y b, route ⟨some (), y⟩ = .inl b → tB b = none)
    {u b H} (ri : Induces (pair β α) route inj u (some b) H)
    (hready : TagReady tα α (restrict (some ()) H)) {c} (hc : tB b = some c) :
    c = latestBy bA u := by
  obtain ⟨⟨h1, -⟩, h3⟩ := tagInvariant_induces hr ri
  rcases ri.inv with ⟨-, ho, -⟩ | ⟨u', a, o₀, H₀, rfl, -, l⟩
  · cases ho
  obtain ⟨y, hy, hyb⟩ := l.exists_out
  rcases List.eq_nil_or_concat H with rfl | ⟨H, z, rfl⟩
  · exact absurd hy (by simp [pair])
  simp only [List.concat_eq_append] at hy h3 h1 hready
  rcases z with ⟨_ | ⟨⟨⟩⟩, z⟩
  · rw [pair_left] at hy
    obtain ⟨yβ, hyβ, rfl⟩ := (Part.mem_map_iff _).mp hy
    have h3' := h3 hready
    rw [restrict_none_snoc_left] at h3'
    rw [hβ _ yβ b c hyβ hyb hc, h3', h1]
  · rw [pair_right] at hy
    obtain ⟨yα, -, rfl⟩ := (Part.mem_map_iff _).mp hy
    rw [hαB yα b hyb] at hc
    cases hc

end TagRouting

/-! ## The lift of a serial composition -/

section SerialLift

variable {O M J : Type} {U V : O → Type} {Xm Ym : M → Type} {X Y : J → Type}

/-- The MBO of an output of a converter: that of an outside reply. -/
def outputMBO {O J : Type} {V : O → Type} {X : J → Type} :
    (Σ l, twoFam (withMBO V) X l) → Option Bool
  | ⟨⟨none, _⟩, v⟩ => some v.2
  | ⟨⟨some (), _⟩, _⟩ => none

/-- The MBO of an output of a lift is the latest inside MBO. -/
theorem outputMBO_liftMBO {O J : Type} {U V : O → Type} {X Y : J → Type}
    (a : InsideOutsideSystem O J U V X Y) {h y c} (hy : y ∈ liftMBO a h)
    (hc : outputMBO y = some c) : c = latestMBO h := by
  rcases y with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩
  · simp only [outputMBO, Option.some.injEq] at hc
    rw [← hc]
    exact liftMBO_tag a h o v hy
  · cases hc

/-- **Bits through a serial composition of lifts**: the inner lift tags its outside replies to
the outer lift, its inside queries leave untagged, and the outer lift's queries carry no bit. -/
theorem tagRouting_serialM (α : InsideOutsideSystem M J Xm Ym X Y) :
    TagRouting (inputMBO (U := U) (Y := Ym)) (inputMBO (U := Xm) (Y := Y))
      (inputMBO (U := U) (Y := Y)) outputMBO (liftMBO α)
      (serialRouteM (V := withMBO V) (Ym := withMBO Ym) (Yi := withMBO Y) (Xm := Xm) (Xi := X))
      (serialInjM (U := U) (Yi := withMBO Y) (Ym := withMBO Ym) (Xm := Xm)) where
  α_tag h y c hy hc := outputMBO_liftMBO α hy hc
  α_to_β y x hx := by
    rcases y with ⟨⟨_ | ⟨⟨⟩⟩, m⟩, v⟩
    · simp only [serialRouteM, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hx
      subst hx
      exact ⟨rfl, rfl⟩
    · cases hx
  α_out y b hb := by
    rcases y with ⟨⟨_ | ⟨⟨⟩⟩, m⟩, v⟩
    · cases hb
    · rfl
  α_to_α y x hx := by
    rcases y with ⟨⟨_ | ⟨⟨⟩⟩, m⟩, v⟩ <;> simp [serialRouteM] at hx
  β_to_α y x hx := by
    rcases y with ⟨⟨_ | ⟨⟨⟩⟩, m⟩, v⟩
    · cases hx
    · simp only [serialRouteM, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hx
      subst hx
      rfl
  β_to_β y x hx := by
    rcases y with ⟨⟨_ | ⟨⟨⟩⟩, m⟩, v⟩ <;> simp [serialRouteM] at hx
  inj_α u x hx := by
    rcases u with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, y⟩
    · cases hx
    · simp only [serialInjM, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hx
      subst hx
      rfl
  inj_β u x hx := by
    rcases u with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, y⟩
    · simp only [serialInjM, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hx
      subst hx
      exact ⟨rfl, rfl⟩
    · cases hx

/-- **An outside reply of a serial composition of lifts carries the latest inside MBO**: when the
outer lift replies outside, the inner lift is idle and its latest reply carried its latest
inside MBO to the outer lift. -/
theorem outputMBO_serialM_liftMBO {bβ bα : ℕ} {β : InsideOutsideSystem O M U V Xm Ym}
    {α : InsideOutsideSystem M J Xm Ym X Y} (hβ : IsDDC bβ β) (hα : IsDDC bα α) {u w c}
    (hr : Reach (serialM (liftMBO β) (liftMBO α)) u) (hw : w ∈ serialM (liftMBO β) (liftMBO α) u)
    (hc : outputMBO w = some c) : c = latestMBO u := by
  obtain ⟨o, H, ri, hs, -⟩ := serialM_reach_partial hβ.liftMBO hα.liftMBO u hr
  obtain ⟨H', ri'⟩ := mem_interconnect.mp hw
  obtain ⟨rfl, rfl⟩ := ri.det ri'
  have hready : TagReady outputMBO (liftMBO α) (restrict (some ()) H) := by
    rcases hs.2 with ⟨-, ho, -⟩ | ⟨w', ho, -, -, hidle⟩ | ⟨w', j, m, o', ho, hj, -⟩
    · cases ho
    · rcases eq_or_ne (restrict (some ()) H) [] with he | hne
      · exact Or.inl he
      · right
        obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp (hidle.2.1 hne)
        refine ⟨y, hy, ?_⟩
        have hl := hidle.2.2
        rw [replyLabel_of_mem _ hy] at hl
        rcases y with ⟨⟨_ | ⟨⟨⟩⟩, m⟩, v⟩
        · rfl
        · exact absurd rfl (hl m)
    · cases ho
      rcases w with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩
      · cases hj
      · cases hc
  exact tag_of_induces (tagRouting_serialM α) outputMBO
    (fun h y b c hy hb hc => by
      rcases y with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩
      · simp only [serialRouteM, Sum.inl.injEq] at hb
        subst hb
        exact outputMBO_liftMBO β hy hc
      · cases hb)
    (fun y b hb => by
      rcases y with ⟨⟨_ | ⟨⟨⟩⟩, m⟩, v⟩
      · cases hb
      · simp only [serialRouteM, Sum.inl.injEq] at hb
        subst hb
        rfl)
    ri hready hc

/-- **A serial composition of lifts without its outside MBOs** is the serial composition run on
the inside replies without their MBO. -/
theorem relabel_serialM_liftMBO (β : InsideOutsideSystem O M U V Xm Ym)
    (α : InsideOutsideSystem M J Xm Ym X Y) :
    relabel (serialM (liftMBO β) (liftMBO α)) id (outsideMap forgetMBO) =
      relabel (serialM β α) (insideMap forgetMBO) id := by
  unfold serialM
  rw [relabel_interconnect, relabel_interconnect]
  have e1 : interconnect (pair (relabel (liftMBO β) id (outsideMap forgetMBO)) (liftMBO α))
      serialRouteM serialInjM = interconnect (pair (liftMBO β) (liftMBO α))
        (fun y => (serialRouteM y).map (outsideMap forgetMBO) id) (serialInjM ∘ id) := by
    rw [pair_relabel_left, interconnect_relabel]
    congr 1
    · funext y
      rcases y with ⟨_ | ⟨⟨⟩⟩, y⟩ <;> rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩ <;> rfl
    · funext u
      rcases u with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩ <;> rfl
  rw [← e1, relabel_liftMBO β]
  have e2 : interconnect (pair (relabel β (insideMap forgetMBO) id) (liftMBO α))
      serialRouteM serialInjM =
        interconnect (pair β (relabel (liftMBO α) id (outsideMap forgetMBO)))
          serialRouteM (fun u => twoMap (insideMap forgetMBO) id (serialInjM u)) := by
    rw [pair_relabel_left, interconnect_relabel, pair_relabel_right, interconnect_relabel]
    congr 1
    · funext y
      rcases y with ⟨_ | ⟨⟨⟩⟩, y⟩ <;> rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩ <;> rfl
    · funext u
      rcases u with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩ <;> rfl
  rw [e2, relabel_liftMBO α, pair_relabel_right, interconnect_relabel]
  congr 1
  · funext y
    rcases y with ⟨_ | ⟨⟨⟩⟩, y⟩ <;> rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩ <;> rfl
  · funext u
    rcases u with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩ <;> rfl

/-- An output whose MBO, if any, is `b` is the output without its MBO tagged with `b`. -/
theorem eq_tag_of_outputMBO {O J : Type} {V : O → Type} {X : J → Type}
    {y : Σ l, twoFam (withMBO V) X l} {b : Bool} (hy : ∀ c, outputMBO y = some c → c = b) :
    y = outsideMap (tagMBO b) (outsideMap forgetMBO y) := by
  rcases y with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩
  · have := hy v.2 rfl
    subst this
    rfl
  · rfl

/-- **The serial composition of lifts is the lift of the serial composition.** -/
theorem trim_serialM_liftMBO {bβ bα : ℕ} {β : InsideOutsideSystem O M U V Xm Ym}
    {α : InsideOutsideSystem M J Xm Ym X Y} (hβ : IsDDC bβ β) (hα : IsDDC bα α) :
    trim (serialM (liftMBO β) (liftMBO α)) = liftMBO (trim (serialM β α)) := by
  have hproj := congrArg trim (relabel_serialM_liftMBO β α)
  rw [trim_relabel, trim_relabel] at hproj
  funext h
  have hh := congrFun hproj h
  simp only [relabel, List.map_id] at hh
  apply Part.ext
  intro w
  have htag : ∀ w' ∈ trim (serialM (liftMBO β) (liftMBO α)) h,
      w' = outsideMap (tagMBO (latestMBO h)) (outsideMap forgetMBO w') := by
    intro w' hw'
    have hr : Reach (serialM (liftMBO β) (liftMBO α)) h := by
      by_contra hn
      simp [trim, hn] at hw'
    have hw'' : w' ∈ serialM (liftMBO β) (liftMBO α) h := by
      simpa [trim, hr] using hw'
    exact eq_tag_of_outputMBO fun c hc => outputMBO_serialM_liftMBO hβ hα hr hw'' hc
  have hmem : ∀ z, z ∈ (trim (serialM (liftMBO β) (liftMBO α)) h).map (outsideMap forgetMBO) ↔
      z ∈ trim (serialM β α) (h.map (insideMap forgetMBO)) :=
    fun z => (Part.ext_iff.mp hh z).trans (by simp [Part.mem_map_iff])
  constructor
  · intro hw
    exact (Part.mem_map_iff _).mpr ⟨outsideMap forgetMBO w, (hmem _).mp (Part.mem_map _ hw),
      (htag w hw).symm⟩
  · intro hw
    obtain ⟨w₀, hw₀, rfl⟩ := (Part.mem_map_iff _).mp hw
    obtain ⟨w', hw', rfl⟩ := (Part.mem_map_iff _).mp ((hmem w₀).mpr hw₀)
    rw [← htag w' hw']
    exact hw'

end SerialLift

/-! ## The lift of a composition of PDCs -/

section LiftComp

variable {O J : Type} [Fintype O] [Fintype J] {U V : O → Type} {X Y : J → Type}
  [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] [∀ j, Fintype (X j)] [∀ j, Fintype (Y j)]
  {E : List (Σ j, X j) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
  {F : List (Σ o, U o) → Prop} {n : ℕ} {hF : ∀ h, F h → h.length ≤ n}

/-- **The lift is functorial**: the lift of a serial composition is the composition of the
lifts. -/
theorem PDCBehavior.liftMBO_comp {M : Type} [Fintype M] {Xm Ym : M → Type}
    [∀ k, Fintype (Xm k)] [∀ k, Fintype (Ym k)] {F'' : List (Σ k, Xm k) → Prop} {n'' : ℕ}
    {hF'' : ∀ h, F'' h → h.length ≤ n''}
    (β : PDCBehavior O M U V Xm Ym F'' n'' hF'' F n hF)
    (α : PDCBehavior M J Xm Ym X Y E m hE F'' n'' hF'') :
    PDCBehavior.liftMBO (PDCBehavior.comp β α) =
      PDCBehavior.comp (PDCBehavior.liftMBO β) (PDCBehavior.liftMBO α) := by
  obtain ⟨bβ, P, hP⟩ := β.2
  obtain ⟨bα, Q, hQ⟩ := α.2
  apply PDCBehavior.ext
  intro t
  rw [PDCBehavior.liftMBO_apply, PDCBehavior.comp_presents β α P Q hP hQ,
    PDCBehavior.comp_presents _ _ (liftPresentation P) (liftPresentation Q)
      (PDCBehavior.liftMBO_presents β P hP) (PDCBehavior.liftMBO_presents α Q hQ),
    behaviorMass_compPDC, behaviorMass_compPDC, liftPresentation, liftPresentation,
    ← Distribution.fTransform_prod, Distribution.mass_fTransform]
  have hst : ∀ st : {a : InsideOutsideSystem O M U V Xm Ym // IsDDCFrom F'' F bβ a} ×
      {c : InsideOutsideSystem M J Xm Ym X Y // IsDDCFrom E F'' bα c},
      Replies (trim (serialM (SystemAlgebra.liftMBO st.1.1) (SystemAlgebra.liftMBO st.2.1)))
        (t.map Prod.fst) (t.map Prod.snd) ↔
        Replies (trim (serialM st.1.1 st.2.1)) ((forgetConverterMBO t).map Prod.fst)
          ((forgetConverterMBO t).map Prod.snd) ∧ TaggedMBO t := by
    intro st
    rw [trim_serialM_liftMBO st.1.2.isDDC st.2.2.isDDC, replies_liftMBO_iff]
  simp only [Prod.map_fst, Prod.map_snd]
  rw [Distribution.mass_congr _ hst]
  split_ifs with ht
  · exact Distribution.mass_congr _ fun st => (and_iff_left ht).symm
  · exact (Distribution.mass_eq_zero_of_forall_not _ fun st (hs : _ ∧ TaggedMBO t) => ht hs.2).symm

end LiftComp

/-! ## The winner of a distinguisher -/

section Winner

variable {O : Type} {U V : O → Type}

/-- An input of a distinguisher with the MBO of a reply forgotten. -/
def forgetEnvMBO : (Σ p, dIn (withMBO V) p) → Σ p, dIn V p
  | ⟨.start, u⟩ => ⟨.start, u⟩
  | ⟨.dec, e⟩ => ⟨.dec, e⟩
  | ⟨.res o, v⟩ => ⟨.res o, v.1⟩

/-- The MBO of an input of a distinguisher: that of a reply. -/
def envMBO : (Σ p, dIn (withMBO V) p) → Option Bool
  | ⟨.res _, v⟩ => some v.2
  | _ => none

/-- An output of a distinguisher with its decision replaced by `b`. -/
def tagDecision (b : Bool) : (Σ p, dOut U p) → Σ p, dOut U p
  | ⟨.start, e⟩ => ⟨.start, e⟩
  | ⟨.dec, _⟩ => ⟨.dec, b⟩
  | ⟨.res o, x⟩ => ⟨.res o, x⟩

/-- The decision of an output of a distinguisher. -/
def decisionBit : (Σ p, dOut U p) → Option Bool
  | ⟨.dec, b⟩ => some b
  | _ => none

theorem tagDecision_fst (b : Bool) (z : Σ p, dOut U p) : (tagDecision b z).1 = z.1 := by
  rcases z with ⟨_ | _ | o, v⟩ <;> rfl

theorem forgetEnvMBO_fst (z : Σ p, dIn (withMBO V) p) : (forgetEnvMBO z).1 = z.1 := by
  rcases z with ⟨_ | _ | o, v⟩ <;> rfl

@[simp] theorem tagDecision_tagDecision (b c : Bool) (z : Σ p, dOut U p) :
    tagDecision b (tagDecision c z) = tagDecision b z := by
  rcases z with ⟨_ | _ | o, v⟩ <;> rfl

/-- An output whose decision, if any, is `b` is unchanged by deciding `b`. -/
theorem tagDecision_eq_self {z : Σ p, dOut U p} {b : Bool}
    (hz : ∀ c, decisionBit z = some c → c = b) : tagDecision b z = z := by
  rcases z with ⟨_ | _ | o, v⟩
  · rfl
  · rw [hz v rfl]
    rfl
  · rfl

theorem map_forgetEnvMBO_dHist (ys : List (Σ o, withMBO V o)) :
    (dHist ys).map forgetEnvMBO = dHist (ys.map forgetMBO) := by
  simp only [dHist, List.map_cons, List.map_map]
  rfl

theorem latestBy_envMBO_dHist (ys : List (Σ o, withMBO V o)) :
    latestBy envMBO (dHist ys) = ((ys.getLast?).map fun y => y.2.2).getD false := by
  induction ys using List.reverseRecOn with
  | nil => rfl
  | append_singleton ys y ih =>
    rw [dHist, List.map_append, List.map_singleton, ← List.cons_append, latestBy_snoc,
      List.getLast?_append, List.getLast?_singleton]
    rfl

/-- **The winner of a distinguisher**: it runs the distinguisher on the replies without their MBO
and decides the MBO of the latest reply. -/
def DDD.winner (D : DDD O U V) : DDD O U (withMBO V) :=
  fun h => (D (h.map forgetEnvMBO)).map (tagDecision (latestBy envMBO h))

theorem DDD.winner_dom (D : DDD O U V) (h) :
    (D.winner h).Dom ↔ (D (h.map forgetEnvMBO)).Dom := Iff.rfl

theorem DDD.relabel_winner (D : DDD O U V) :
    relabel D.winner id (tagDecision false) = relabel D forgetEnvMBO (tagDecision false) := by
  funext h
  simp only [relabel, DDD.winner, List.map_id, Part.map_map]
  congr 1
  funext z
  simp

theorem DDD.reach_winner_iff (D : DDD O U V) (h) :
    Reach D.winner h ↔ Reach D (h.map forgetEnvMBO) := by
  rw [← reach_relabel_iff D forgetEnvMBO (id : (Σ p, dOut U p) → _) h]
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h z ih =>
    rw [reach_snoc_iff, ih, reach_snoc_iff]
    simp [DDD.winner, relabel]

theorem DDD.replyLabel_winner (D : DDD O U V) (h) :
    replyLabel D.winner h = replyLabel D (h.map forgetEnvMBO) := by
  unfold replyLabel
  by_cases hd : (D (h.map forgetEnvMBO)).Dom
  · rw [dif_pos hd, dif_pos ((D.winner_dom h).mpr hd)]
    exact congrArg some (tagDecision_fst _ _)
  · rw [dif_neg hd, dif_neg (fun h' => hd ((D.winner_dom h).mp h'))]

/-- The winner of a deterministic distinguisher is a deterministic distinguisher. -/
theorem IsDDD.winner {D : DDD O U V} (hD : IsDDD D) : IsDDD D.winner := by
  obtain ⟨hs, ⟨n, hn⟩, hst, hres, hdec⟩ := hD
  refine ⟨fun hd => hs hd, ⟨n, fun h hd => by simpa using hn _ hd⟩, fun h z hr => ?_,
    fun h z i hr hl => ?_, fun h z hr => ?_⟩
  · have := hst (h.map forgetEnvMBO) (forgetEnvMBO z)
      (by simpa only [List.map_append, List.map_singleton] using (D.reach_winner_iff _).mp hr)
    rw [forgetEnvMBO_fst] at this
    simpa using this
  · have := hres (h.map forgetEnvMBO) (forgetEnvMBO z) i
      (by simpa only [List.map_append, List.map_singleton] using (D.reach_winner_iff _).mp hr)
      (by rwa [← D.replyLabel_winner])
    rwa [forgetEnvMBO_fst] at this
  · rw [D.replyLabel_winner]
    exact hdec (h.map forgetEnvMBO) (forgetEnvMBO z)
      (by simpa only [List.map_append, List.map_singleton] using (D.reach_winner_iff _).mp hr)

theorem DDD.trim_winner (D : DDD O U V) : trim D.winner = DDD.winner (trim D) := by
  funext h
  simp only [trim, DDD.winner, D.reach_winner_iff]
  split_ifs <;> simp

/-- The winner queries as the distinguisher on the replies without their MBO. -/
theorem DDD.envOf_trim_winner (D : DDD O U V) (ys : List (Σ o, withMBO V o)) :
    envOf (trim D.winner) ys = envOf (trim D) (ys.map forgetMBO) := by
  rw [envOf, envOf, DDD.trim_winner]
  simp only [DDD.winner]
  rw [map_forgetEnvMBO_dHist, Part.bind_map]
  congr 1
  funext z
  rcases z with ⟨_ | _ | o, v⟩ <;> rfl

variable [Fintype O] [∀ o, Fintype (U o)] [∀ o, Fintype (V o)]
  {F : List (Σ o, U o) → Prop} {n : ℕ} {hF : ∀ h, F h → h.length ≤ n}

/-- **Winning is deciding with the winner**: the winning probability of a compatible
distinguisher is the decision probability of its winner. -/
theorem RandomSystem.winProbability_eq_decisionProbability_winner (D : DDD O U V) (hD : IsDDD D)
    (hc : (Domain.ofInputs F n hF : Domain (Σ o, U o) (Σ o, V o)).DecisionCompatible D)
    {R : RandomSystem (Σ o, U o) (Σ o, withMBO V o) (Domain.ofInputs F n hF)}
    (hR : R.RepliesAtQueriedInterface) :
    R.winProbability D hD = R.decisionProbability D.winner hD.winner := by
  have he : (ddeOf hD.winner).1 = (DDE.blindMBO (ddeOf hD)).1 :=
    funext fun ys => D.envOf_trim_winner ys
  have hbW := ddeOf_bounded hD.winner
  have hbD := ddeOf_bounded hD
  unfold RandomSystem.winProbability RandomSystem.decisionProbability
  rw [he]
  have hlaw : R.sLaw (DDE.blindMBO (ddeOf hD)).1 hD.winner.2.1.choose =
      R.sLaw (DDE.blindMBO (ddeOf hD)).1 hD.2.1.choose := by
    apply sLaw_eq_of_query_bounds
    · intro h _ _ hd
      have := hbW (h.map Prod.snd) (by rwa [he])
      simpa using this
    · intro h _ _ hd
      have := hbD ((h.map Prod.snd).map forgetMBO) hd
      simpa using this
  rw [hlaw]
  apply Distribution.mass_congr_of_support
  intro h hh
  have hRh : R h ≠ 0 := by
    intro hz
    apply Finsupp.mem_support_iff.mp hh
    simp [sLaw_apply, hz]
  have hg : Good (DDE.blindMBO (ddeOf hD)).1 hD.2.1.choose h := by
    by_contra hg
    apply Finsupp.mem_support_iff.mp hh
    simp [sLaw_apply, hg]
  -- The distinguisher decides on the transcript without the MBO.
  have hvis : forgetMBOs h ∈ (R.visible.sLaw (ddeOf hD).1 hD.2.1.choose).support := by
    rw [Finsupp.mem_support_iff, sLaw_apply, if_pos ((good_blindMBO_iff _ _ h).mp hg)]
    have := le_sumMBO R.mass_nonneg h
    rw [← RandomSystem.visible_apply] at this
    exact ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne (R.mass_nonneg h) (Ne.symm hRh)) this)
  obtain ⟨b, hb⟩ := hc.producesDecision hD hR.visible hvis
  rw [map_snd_forgetMBOs] at hb
  rw [DDD.trim_winner]
  simp only [DDD.winner]
  rw [map_forgetEnvMBO_dHist, latestBy_envMBO_dHist, finalMBO]
  constructor
  · intro hf
    refine (Part.mem_map_iff _).mpr ⟨⟨.dec, b⟩, hb, ?_⟩
    simp only [tagDecision, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    rw [← hf, List.getLast?_map, Option.map_map]
    rfl
  · intro hw
    obtain ⟨z, -, hz⟩ := (Part.mem_map_iff _).mp hw
    rcases z with ⟨_ | _ | o, v⟩
    · exact v.elim
    · simp only [tagDecision, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hz
      rw [← hz, List.getLast?_map, Option.map_map]
      rfl
    · simp [tagDecision] at hz

end Winner

/-! ## Absorbing a lift into a winner -/

section AbsorbWinner

variable {O J : Type} {U V : O → Type} {X Y : J → Type}

/-- **Bits through the absorption of a lift into a winner**: the lift's outside replies carry
their tags to the winner, its inside queries leave untagged, and the winner's queries carry no
bit. -/
theorem tagRouting_absorbAll (a : InsideOutsideSystem O J U V X Y) :
    TagRouting (envMBO (V := V)) (inputMBO (U := U) (Y := Y)) (envMBO (V := Y))
      (outputMBO (V := V) (X := X)) (liftMBO a)
      (absorptionRoute (U := U) (V := withMBO V) (X := X) (Y := withMBO Y))
      (absorptionInput (U := U) (V := withMBO V) (Y := withMBO Y)) where
  α_tag h y c hy hc := outputMBO_liftMBO a hy hc
  α_to_β y x hx := by
    rcases y with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩
    · simp only [absorptionRoute, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hx
      subst hx
      exact ⟨rfl, rfl⟩
    · cases hx
  α_out y b hb := by
    rcases y with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩
    · cases hb
    · rfl
  α_to_α y x hx := by
    rcases y with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩ <;> simp [absorptionRoute] at hx
  β_to_α y x hx := by
    rcases y with ⟨_ | _ | o, v⟩
    · exact v.elim
    · cases hx
    · simp only [absorptionRoute, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hx
      subst hx
      rfl
  β_to_β y x hx := by
    rcases y with ⟨_ | _ | o, v⟩
    · exact v.elim
    · cases hx
    · cases hx
  inj_α u x hx := by
    rcases u with ⟨_ | _ | j, y⟩
    · cases hx
    · exact y.elim
    · simp only [absorptionInput, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hx
      subst hx
      rfl
  inj_β u x hx := by
    rcases u with ⟨_ | _ | j, y⟩
    · simp only [absorptionInput, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hx
      subst hx
      exact ⟨rfl, rfl⟩
    · exact y.elim
    · cases hx

/-- **The decision of a winner with a lift absorbed is the latest MBO**: when the winner
decides, the lift is idle and its latest reply carried its latest inside MBO to the winner. -/
theorem decisionBit_absorbAll_winner {b : ℕ} {D : DDD O U V} (hD : IsDDD D)
    {a : InsideOutsideSystem O J U V X Y} (ha : IsDDC b a) {u w c}
    (hr : Reach (absorbAll D.winner (liftMBO a)) u) (hw : w ∈ absorbAll D.winner (liftMBO a) u)
    (hc : decisionBit w = some c) : c = latestBy envMBO u := by
  obtain ⟨H, ⟨o, ri⟩, -, -, -, hcount, hreply⟩ := absorbAll_history hD.winner ha.liftMBO u hr
  obtain ⟨H', ri'⟩ := mem_interconnect.mp hw
  obtain ⟨rfl, rfl⟩ := ri.det ri'
  have hdec : w.1 = .dec := by
    rcases w with ⟨_ | _ | j, v⟩
    · exact v.elim
    · rfl
    · cases hc
  have hready : TagReady outputMBO (liftMBO a) (restrict (some ()) H) := by
    rcases hreply .dec (by rw [replyLabel_of_mem _ hw, hdec]) with
      ⟨-, -, hidle⟩ | ⟨j, hj, -⟩
    · rcases hcount.2 with he | hd
      · exact Or.inl he
      · right
        obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hd
        refine ⟨y, hy, ?_⟩
        have hl := hidle
        simp only [AbsorptionIdle, replyLabel_of_mem _ hy] at hl
        rcases y with ⟨⟨_ | ⟨⟨⟩⟩, m⟩, v⟩
        · rfl
        · exact absurd rfl (hl m)
    · cases hj
  exact tag_of_induces (tagRouting_absorbAll a) decisionBit
    (fun h y b c hy hb hc => by
      rcases y with ⟨_ | _ | o, v⟩
      · exact v.elim
      · simp only [absorptionRoute, Sum.inl.injEq] at hb
        subst hb
        simp only [decisionBit, Option.some.injEq] at hc
        subst hc
        have hy' : (⟨.dec, v⟩ : Σ p, dOut U p) ∈
            (D (h.map forgetEnvMBO)).map (tagDecision (latestBy envMBO h)) := hy
        obtain ⟨z, -, hz⟩ := (Part.mem_map_iff _).mp hy'
        rcases z with ⟨_ | _ | o', v'⟩
        · exact v'.elim
        · simp only [tagDecision, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hz
          exact hz.symm
        · simp [tagDecision] at hz
      · cases hb)
    (fun y b hb => by
      rcases y with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩
      · cases hb
      · simp only [absorptionRoute, Sum.inl.injEq] at hb
        subst hb
        rfl)
    ri hready hc

/-- **A winner with a lift absorbed, without its decision**, is the distinguisher with the
converter absorbed, on the replies without their MBO. -/
theorem relabel_absorbAll_winner (D : DDD O U V) (a : InsideOutsideSystem O J U V X Y) :
    relabel (absorbAll D.winner (liftMBO a)) id (tagDecision false) =
      relabel (absorbAll D a) forgetEnvMBO (tagDecision false) := by
  unfold absorbAll
  rw [relabel_interconnect, relabel_interconnect]
  have e1 : interconnect (pair (relabel D.winner id (tagDecision false)) (liftMBO a))
      absorptionRoute absorptionInput = interconnect (pair D.winner (liftMBO a))
        (fun y => (absorptionRoute y).map (tagDecision false) id) (absorptionInput ∘ id) := by
    rw [pair_relabel_left, interconnect_relabel]
    congr 1
    · funext y
      rcases y with ⟨_ | ⟨⟨⟩⟩, y⟩
      · rcases y with ⟨_ | _ | o, v⟩ <;> first | exact v.elim | rfl
      · rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩ <;> rfl
    · funext u
      rcases u with ⟨_ | _ | j, v⟩ <;> first | exact v.elim | rfl
  rw [← e1, DDD.relabel_winner]
  have e2 : interconnect (pair (relabel D forgetEnvMBO (tagDecision false)) (liftMBO a))
      absorptionRoute absorptionInput =
      interconnect (pair D (relabel (liftMBO a) id (outsideMap forgetMBO)))
        (fun y => (absorptionRoute y).map (tagDecision false) id)
        (fun u => twoMap forgetEnvMBO id (absorptionInput u)) := by
    rw [pair_relabel_left, interconnect_relabel, pair_relabel_right, interconnect_relabel]
    congr 1
    · funext y
      rcases y with ⟨_ | ⟨⟨⟩⟩, y⟩
      · rcases y with ⟨_ | _ | o, v⟩ <;> first | exact v.elim | rfl
      · rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩ <;> rfl
    · funext u
      rcases u with ⟨_ | _ | j, v⟩ <;> first | exact v.elim | rfl
  rw [e2, relabel_liftMBO a, pair_relabel_right, interconnect_relabel]
  congr 1
  · funext y
    rcases y with ⟨_ | ⟨⟨⟩⟩, y⟩
    · rcases y with ⟨_ | _ | o, v⟩ <;> first | exact v.elim | rfl
    · rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩ <;> rfl
  · funext u
    rcases u with ⟨_ | _ | j, v⟩ <;> first | exact v.elim | rfl

/-- **Absorbing a lift into a winner gives the winner of the absorbed distinguisher.** -/
theorem trim_absorbAll_winner {b : ℕ} {D : DDD O U V} (hD : IsDDD D)
    {a : InsideOutsideSystem O J U V X Y} (ha : IsDDC b a) :
    trim (absorbAll D.winner (liftMBO a)) = DDD.winner (trim (absorbAll D a)) := by
  have hproj := congrArg trim (relabel_absorbAll_winner D a)
  rw [trim_relabel, trim_relabel] at hproj
  funext h
  have hh := congrFun hproj h
  simp only [relabel, List.map_id] at hh
  have htag : ∀ w ∈ trim (absorbAll D.winner (liftMBO a)) h,
      tagDecision (latestBy envMBO h) w = w := by
    intro w hw
    have hr : Reach (absorbAll D.winner (liftMBO a)) h := by
      by_contra hn
      simp [trim, hn] at hw
    have hw' : w ∈ absorbAll D.winner (liftMBO a) h := by
      simpa [trim, hr] using hw
    exact tagDecision_eq_self fun c hc => decisionBit_absorbAll_winner hD ha hr hw' hc
  simp only [DDD.winner]
  apply Part.ext
  intro w
  have hmem : ∀ z, z ∈ (trim (absorbAll D.winner (liftMBO a)) h).map (tagDecision false) ↔
      z ∈ (trim (absorbAll D a) (h.map forgetEnvMBO)).map (tagDecision false) :=
    fun z => Part.ext_iff.mp hh z
  constructor
  · intro hw
    obtain ⟨w₀, hw₀, he⟩ := (Part.mem_map_iff _).mp ((hmem _).mp (Part.mem_map _ hw))
    refine (Part.mem_map_iff _).mpr ⟨w₀, hw₀, ?_⟩
    rw [← tagDecision_tagDecision _ false w₀, he, tagDecision_tagDecision, htag w hw]
  · intro hw
    obtain ⟨w₀, hw₀, rfl⟩ := (Part.mem_map_iff _).mp hw
    obtain ⟨w', hw', he⟩ := (Part.mem_map_iff _).mp ((hmem _).mpr (Part.mem_map _ hw₀))
    rw [← tagDecision_tagDecision _ false w₀, ← he, tagDecision_tagDecision, htag w' hw']
    exact hw'

end AbsorbWinner

/-! ## Absorbing a PDC into a winner, and solver behaviors -/

section Absorption

variable {O J : Type} [Fintype O] [Fintype J] {U V : O → Type} {X Y : J → Type}
  [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] [∀ j, Fintype (X j)] [∀ j, Fintype (Y j)]
  {E : List (Σ j, X j) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
  {F : List (Σ o, U o) → Prop} {n : ℕ} {hF : ∀ h, F h → h.length ≤ n}
  (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
  (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)

omit [Fintype J] [∀ j, Fintype (X j)] [∀ j, Fintype (Y j)] in
theorem RandomSystem.decisionProbability_congr {I : Type} [Fintype I] {X' Y' : I → Type}
    [∀ i, Fintype (X' i)] [∀ i, Fintype (Y' i)] {𝒟 : Domain (Σ i, X' i) (Σ i, Y' i)}
    (R : RandomSystem (Σ i, X' i) (Σ i, Y' i) 𝒟) {D₁ D₂ : DDD I X' Y'} (he : D₁ = D₂)
    (h₁ : IsDDD D₁) (h₂ : IsDDD D₂) :
    R.decisionProbability D₁ h₁ = R.decisionProbability D₂ h₂ := by
  subst he
  rfl

/-- **Attaching a lift averages the absorbed winning probabilities** over a presentation of the
PDC (CR18, proof of Lemma 4.9). -/
theorem RandomSystem.winProbability_attach_liftMBO (D : DDD O U V) (hD : IsDDD D)
    (hc : (Domain.ofInputs F n hF : Domain (Σ o, U o) (Σ o, V o)).DecisionCompatible D)
    (α : PDCBehavior O J U V X Y E m hE F n hF) {b : ℕ}
    (P : Distribution.ProbDist {a : InsideOutsideSystem O J U V X Y // IsDDCFrom E F b a})
    (hP : ∀ h, behaviorMass P.1 (h.map Prod.fst) (h.map Prod.snd) = α.1 h)
    (G : RandomSystem (Σ j, X j) (Σ j, withMBO Y j) (Domain.ofInputs E m hE))
    (hG : G.RepliesAtQueriedInterface) :
    (PDCBehavior.attach hE' hF' (PDCBehavior.liftMBO α) G hG).winProbability D hD =
      ∑ a ∈ P.1.support, P.1 a * G.winProbability (trim (absorbAll D a.1))
        (absorbAll_isDDD hD a.2.isDDC) := by
  rw [RandomSystem.winProbability_eq_decisionProbability_winner D hD hc
      (PDCBehavior.attach_repliesAtQueriedInterface hE' hF' _ G hG),
    RandomSystem.decisionProbability_attach hE' hF' D.winner hD.winner (PDCBehavior.liftMBO α)
      (liftPresentation P) (PDCBehavior.liftMBO_presents α P hP) G hG]
  change (liftPresentation P).1.sum (fun a w => w * _) = P.1.sum (fun a w => w * _)
  rw [liftPresentation, Distribution.sum_fTransform_mul]
  apply Finsupp.sum_congr
  intro a _
  congr 1
  rw [RandomSystem.decisionProbability_congr G (trim_absorbAll_winner hD a.2.isDDC) _
      (absorbAll_isDDD hD a.2.isDDC).winner,
    RandomSystem.winProbability_eq_decisionProbability_winner _ _
      (hc.absorbAll hE' hF' hD a.2) hG]

/-- **Absorbing a PDC into a winner** (CR18, proof of Lemma 4.9, `g(W R) = (R g)(W)`): the
probabilistic distinguisher with a PDC absorbed decides on a random system as the
distinguisher decides on the PDC attached to it, and wins a game as the distinguisher wins the
lift of the PDC attached to it. -/
theorem Domain.Distinguisher.exists_absorbAll_winProbability
    (α : PDCBehavior O J U V X Y E m hE F n hF)
    (P : (Domain.ofInputs F n hF : Domain (Σ o, U o) (Σ o, V o)).Distinguisher) :
    ∃ Q : (Domain.ofInputs E m hE : Domain (Σ j, X j) (Σ j, Y j)).Distinguisher,
      (∀ (R : RandomSystem (Σ j, X j) (Σ j, Y j) (Domain.ofInputs E m hE))
        (hR : R.RepliesAtQueriedInterface),
        Q.probability R = P.probability (PDCBehavior.attach hE' hF' α R hR)) ∧
      ∀ (G : RandomSystem (Σ j, X j) (Σ j, withMBO Y j) (Domain.ofInputs E m hE))
        (hG : G.RepliesAtQueriedInterface),
        Q.winProbability G =
          P.winProbability (PDCBehavior.attach hE' hF' (PDCBehavior.liftMBO α) G hG) := by
  obtain ⟨b, Pα, hPα⟩ := α.2
  refine ⟨⟨Distribution.fTransform (fun p => (⟨trim (absorbAll p.1.1 p.2.1),
      absorbAll_isDDD p.1.2.1 p.2.2.isDDC, p.1.2.2.absorbAll hE' hF' p.1.2.1 p.2.2⟩ :
        {D : DDD J X Y // IsDDD D ∧
          (Domain.ofInputs E m hE : Domain (Σ j, X j) (Σ j, Y j)).DecisionCompatible D}))
      (Distribution.prod P.1 Pα.1),
    Distribution.fTransform_isProbDist _ (Distribution.prod_isProbDist _ _ P.2 Pα.2)⟩,
    fun R hR => ?_, fun G hG => ?_⟩
  · simp only [Domain.Distinguisher.probability, Distribution.sum_fTransform_mul,
      Distribution.sum_prod_mul]
    apply Finsupp.sum_congr
    intro D _
    rw [RandomSystem.decisionProbability_attach hE' hF' D.1 D.2.1 α Pα hPα R hR]
    rfl
  · simp only [Domain.Distinguisher.winProbability, Distribution.sum_fTransform_mul,
      Distribution.sum_prod_mul]
    apply Finsupp.sum_congr
    intro D _
    rw [RandomSystem.winProbability_attach_liftMBO hE' hF' D.1 D.2.1 D.2.2 α Pα hPα G hG]
    rfl

end Absorption

section Solvers

variable {I : Type} [Fintype I] {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

/-- **Solver behaviors** on an input domain: the probability of outputting `1` on each random
system and the winning probability for each game of one probabilistic distinguisher. -/
abbrev Domain.SolverBehavior (E : List (Σ i, X i) → Prop) (m : ℕ)
    (hE : ∀ h, E h → h.length ≤ m) :=
  {s : ({R : RandomSystem (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE) //
      R.RepliesAtQueriedInterface} → ℝ) ×
    ({G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) (Domain.ofInputs E m hE) //
      G.RepliesAtQueriedInterface ∧ G.MonotoneMBO} → ℝ) //
    ∃ P : (Domain.ofInputs E m hE : Domain (Σ i, X i) (Σ i, Y i)).Distinguisher,
      (∀ R, s.1 R = P.probability R.1) ∧ ∀ G, s.2 G = P.winProbability G.1}

end Solvers

section SolverAbsorption

variable {O J : Type} [Fintype O] [Fintype J] {U V : O → Type} {X Y : J → Type}
  [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] [∀ j, Fintype (X j)] [∀ j, Fintype (Y j)]
  {E : List (Σ j, X j) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
  {F : List (Σ o, U o) → Prop} {n : ℕ} {hF : ∀ h, F h → h.length ≤ n}
  (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
  (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)

/-- **A solver with a PDC absorbed**: it decides on a random system as the solver decides on
the PDC attached to it, and wins a game as the solver wins the lift attached to it. -/
noncomputable def Domain.SolverBehavior.absorb (α : PDCBehavior O J U V X Y E m hE F n hF)
    (s : Domain.SolverBehavior (X := U) (Y := V) F n hF) :
    Domain.SolverBehavior (X := X) (Y := Y) E m hE :=
  ⟨(fun R => s.1.1 ⟨PDCBehavior.attach hE' hF' α R.1 R.2,
      PDCBehavior.attach_repliesAtQueriedInterface hE' hF' α R.1 R.2⟩,
    fun G => s.1.2 ⟨PDCBehavior.attach hE' hF' (PDCBehavior.liftMBO α) G.1 G.2.1,
      PDCBehavior.attach_repliesAtQueriedInterface hE' hF' _ G.1 G.2.1,
      G.2.2.attach_liftMBO hE' hF' α G.2.1⟩), by
    obtain ⟨P, hP, hW⟩ := s.2
    obtain ⟨Q, hQ, hQW⟩ := Domain.Distinguisher.exists_absorbAll_winProbability hE' hF' α P
    exact ⟨Q, fun R => (hP _).trans (hQ R.1 R.2).symm,
      fun G => (hW _).trans (hQW G.1 G.2.1).symm⟩⟩

end SolverAbsorption

end SystemAlgebra
