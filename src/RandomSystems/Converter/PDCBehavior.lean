import RandomSystems.Converter.ConverterDomain
import RandomSystems.Cumulative.CumulativeAttachment

/-!
# Behaviors of PDCs

A PDC is a distribution over DDCs (CR18, Definition 3.17, printed p. 64); its behavior
is the behavior of a probabilistic system on the converter alphabets (Definition 3.18). For
DDCs from the inside domain `E` to the outside domain `F` with a common bound on
consecutive inside queries, it is a random system over the converter domain. Serial
composition samples the two PDCs independently and composes the samples (Definitions
3.9, 3.17); it is associative, and the filter on `E` is its identity.

## Main definitions

* `IsPDCBehavior`, `PDCBehavior`: behaviors of PDCs from `E` to `F`
* `PDCBehavior.ofPDC`, `PDCBehavior.ofDDC`: the behavior of a PDC, and of a DDC
* `compPDC`: the composition of two PDCs
* `PDCBehavior.comp`, `PDCBehavior.id`: serial composition and the identity

## Main results

* `IsPDCBehavior.isDDCFrom_realization`: the realizations of possible choices are DDCs
* `isPDCBehavior_of_transcripts`: a random system on the converter domain whose possible
  transcripts obey the DDC discipline is a PDC behavior
  from `E` to `F`
* `PDCBehavior.ofDDC_apply`: a DDC's behavior is one on its transcripts and zero elsewhere
* `PDCBehavior.ofDDC_eq_of_le`: DDCs from `E` to `F` below one system have the same
  behavior
* `PDCBehavior.comp_presents`: the composition of presentations presents the composition
* `PDCBehavior.comp_assoc`, `PDCBehavior.comp_id`, `PDCBehavior.id_comp`
-/

namespace SystemAlgebra

open Classical Probability

instance instFintypeTwoFam {I J : Type} {F : I → Type} {G : J → Type} [∀ i, Fintype (F i)]
    [∀ j, Fintype (G j)] : ∀ l : Two I J, Fintype (twoFam F G l)
  | ⟨none, i⟩ => (inferInstance : Fintype (F i))
  | ⟨some (), j⟩ => (inferInstance : Fintype (G j))

/-- A reached history extends to a transcript. -/
theorem Reach.exists_transcript {A B : Type} {s : System A B} {xs : List A} (hr : Reach s xs) :
    ∃ t : List (A × B), t.map Prod.fst = xs ∧ Replies s (t.map Prod.fst) (t.map Prod.snd) := by
  obtain ⟨ys, hy⟩ := hr.exists_replies
  have hx : (xs.zip ys).map Prod.fst = xs := List.map_fst_zip (by rw [hy.length])
  have hy' : (xs.zip ys).map Prod.snd = ys := List.map_snd_zip (by rw [hy.length])
  exact ⟨xs.zip ys, hx, by rw [hx, hy']; exact hy⟩

variable {O J : Type} [Fintype O] [Fintype J] {U V : O → Type} {X Y : J → Type}
  [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] [∀ j, Fintype (X j)] [∀ j, Fintype (Y j)]

section Carrier

variable (O J U V X Y) (E : List (Σ j, X j) → Prop) (m : ℕ) (hE : ∀ h, E h → h.length ≤ m)
  (F : List (Σ o, U o) → Prop) (n : ℕ) (hF : ∀ h, F h → h.length ≤ n)

/-- `R` is the behavior of a PDC whose samples are DDCs from `E` to `F` with bound `b`. -/
def IsPDCBehavior (b : ℕ)
    (R : RandomSystem (Σ l, twoFam U Y l) (Σ l, twoFam V X l) (Domain.converter E m hE F n hF)) :
    Prop :=
  ∃ P : Distribution.ProbDist {a : InsideOutsideSystem O J U V X Y // IsDDCFrom E F b a},
    ∀ h, behaviorMass P.1 (h.map Prod.fst) (h.map Prod.snd) = R h

/-- The behaviors of PDCs from `E` to `F` (CR18, Definitions 3.17–3.18). -/
abbrev PDCBehavior :=
  {R : RandomSystem (Σ l, twoFam U Y l) (Σ l, twoFam V X l) (Domain.converter E m hE F n hF) //
    ∃ b, IsPDCBehavior O J U V X Y E m hE F n hF b R}

end Carrier

variable {E : List (Σ j, X j) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
  {F : List (Σ o, U o) → Prop} {n : ℕ} {hF : ∀ h, F h → h.length ≤ n}

/-- **Every realization of a possible choice of a PDC behavior is a DDC from `E` to `F`** with
its bound: its transcripts are those of the samples of a presentation. -/
theorem IsPDCBehavior.isDDCFrom_realization {b : ℕ}
    {R : RandomSystem (Σ l, twoFam U Y l) (Σ l, twoFam V X l) (Domain.converter E m hE F n hF)}
    (hR : IsPDCBehavior O J U V X Y E m hE F n hF b R) {g}
    (hg : R.2.isSubprobabilistic.PossibleChoice g) :
    IsDDCFrom E F b (SystemAlgebra.realization g).1 := by
  obtain ⟨P, hP⟩ := hR
  have sample : ∀ h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l)),
      Replies (SystemAlgebra.realization g).1 (h.map Prod.fst) (h.map Prod.snd) →
      ∃ s : {a : InsideOutsideSystem O J U V X Y // IsDDCFrom E F b a},
        Replies s.1 (h.map Prod.fst) (h.map Prod.snd) := by
    intro h hr
    have hm := R.2.isSubprobabilistic.realization_possible g hg hr
    rw [← hP h] at hm
    obtain ⟨s, -, hs⟩ := behaviorMass_ne_zero hm
    exact ⟨s, hs⟩
  have hs := (SystemAlgebra.realization g).2
  have answers := R.hasDomain_realization hg
  refine ⟨⟨hs, fun xs z hd => ?_, fun xs hd => ?_, fun xs y o hy ho => ?_⟩, answers, fun h hr => ?_⟩
  · obtain ⟨t, rfl, ht⟩ := (hs.reach_iff (by simp) |>.mpr hd |> reach_snoc_iff.mp).1.exists_transcript
    have hz := ((answers t z ht).mp hd).2.1
    simpa only [Admits, ht.replyLabel hs.1, converterAdmits] using hz
  · have hn : xs ≠ [] := fun he => hs.1 (he ▸ hd)
    obtain ⟨t, rfl, ht⟩ := ((hs.reach_iff hn).mpr hd).exists_transcript
    obtain ⟨s, hst⟩ := sample t ht
    obtain ⟨p, e, he, hi, hc⟩ := ht.exists_suffix_run IsInside t
    change run IsInside _ _ ≤ b
    rw [hc]
    subst he
    exact (hst.suffix_le_run IsInside p e hi).trans (s.2.isDDC.bound _ (hst.dom (by simpa using hn)))
  · have hn : xs ≠ [] := fun he => hs.1 (he ▸ hy.1)
    obtain ⟨xs, z, rfl⟩ := List.eq_nil_or_concat xs |>.resolve_left hn
    rw [List.concat_eq_append] at hy ⊢
    obtain ⟨t, rfl, ht⟩ :=
      (reach_snoc_iff.mp ((hs.reach_iff (by simp)).mpr hy.1)).1.exists_transcript
    obtain ⟨s, hst⟩ := sample (t ++ [(z, y)]) (by
      simpa only [List.map_append, List.map_singleton] using
        replies_snoc.mpr ⟨ht, Part.eq_some_iff.mpr hy⟩)
    simp only [List.map_append, List.map_singleton] at hst
    exact s.2.isDDC.replies _ y o (Part.eq_some_iff.mp (replies_snoc.mp hst).2) ho
  · obtain ⟨s, hst⟩ := sample h hr
    exact s.2.queries h hst

/-- **A random system on the converter domain whose possible transcripts obey the DDC
discipline is the behavior of a PDC from `E` to `F`**: at most `b` inside queries between
outside replies, every outside reply at the last outside label, and the inside queries
in `E`. The samples are the realizations of its possible choices. -/
theorem isPDCBehavior_of_transcripts {b : ℕ}
    (R : RandomSystem (Σ l, twoFam U Y l) (Σ l, twoFam V X l) (Domain.converter E m hE F n hF))
    (hbound : ∀ p e, R (p ++ e) ≠ 0 → (∀ z ∈ e, IsInside z.2) → e.length ≤ b)
    (hreply : ∀ h x y (o : O), R (h ++ [(x, y)]) ≠ 0 → y.1 = ⟨none, o⟩ →
      lastOuter (h.map Prod.fst ++ [x]) = some o)
    (hqueries : ∀ h, R h ≠ 0 →
      insideQueries (h.map Prod.snd) = [] ∨ E (insideQueries (h.map Prod.snd))) :
    IsPDCBehavior O J U V X Y E m hE F n hF b R := by
  have hp := R.2.isSubprobabilistic
  obtain ⟨P, hP, -⟩ := hp.exists_presentation (n := (Domain.converter E m hE F n hF).bound)
    (fun h hl => R.mass_eq_zero_of_bound_lt hl) (fun a => IsDDCFrom E F b a) (fun g hg => by
      have hs := (SystemAlgebra.realization g).2
      have answers := R.hasDomain_realization hg
      refine ⟨⟨hs, fun xs z hd => ?_, fun xs hd => ?_, fun xs y o hy ho => ?_⟩, answers,
        fun h hr => hqueries h (hp.realization_possible g hg hr)⟩
      · obtain ⟨t, rfl, ht⟩ :=
          (hs.reach_iff (by simp) |>.mpr hd |> reach_snoc_iff.mp).1.exists_transcript
        have hz := ((answers t z ht).mp hd).2.1
        simpa only [Admits, ht.replyLabel hs.1, converterAdmits] using hz
      · have hn : xs ≠ [] := fun he => hs.1 (he ▸ hd)
        obtain ⟨t, rfl, ht⟩ := ((hs.reach_iff hn).mpr hd).exists_transcript
        obtain ⟨p, e, he, hi, hc⟩ := ht.exists_suffix_run IsInside t
        change run IsInside _ _ ≤ b
        rw [hc]
        subst he
        exact hbound p e (hp.realization_possible g hg ht) hi
      · have hn : xs ≠ [] := fun he => hs.1 (he ▸ hy.1)
        obtain ⟨xs, z, rfl⟩ := List.eq_nil_or_concat xs |>.resolve_left hn
        rw [List.concat_eq_append] at hy ⊢
        obtain ⟨t, rfl, ht⟩ :=
          (reach_snoc_iff.mp ((hs.reach_iff (by simp)).mpr hy.1)).1.exists_transcript
        have hr : Replies (SystemAlgebra.realization g).1 ((t ++ [(z, y)]).map Prod.fst)
            ((t ++ [(z, y)]).map Prod.snd) := by
          simpa only [List.map_append, List.map_singleton] using
            replies_snoc.mpr ⟨ht, Part.eq_some_iff.mpr hy⟩
        exact hreply t z y o (hp.realization_possible g hg hr) ho)
  exact ⟨P, hP⟩

namespace PDCBehavior

@[ext] theorem ext {α β : PDCBehavior O J U V X Y E m hE F n hF} (h : ∀ t, α.1 t = β.1 t) :
    α = β :=
  Subtype.ext (RandomSystem.ext h)

/-- The behavior of a PDC of DDCs from `E` to `F`. -/
noncomputable def ofPDC {b : ℕ}
    (P : Distribution.ProbDist {a : InsideOutsideSystem O J U V X Y // IsDDCFrom E F b a}) :
    PDCBehavior O J U V X Y E m hE F n hF :=
  ⟨RandomSystem.ofPDS P.1 P.2 (fun a _ h x hr => a.2.answers h x hr), b, P, fun _ => rfl⟩

/-- A DDC from `E` to `F` as the behavior of its point mass. -/
noncomputable def ofDDC (a : InsideOutsideSystem O J U V X Y) {b : ℕ} (ha : IsDDCFrom E F b a) :
    PDCBehavior O J U V X Y E m hE F n hF :=
  ofPDC ⟨Finsupp.single ⟨a, ha⟩ 1, Distribution.isProbDist_single _⟩

/-- **A DDC's behavior** gives probability one to its transcripts and zero to all others. -/
theorem ofDDC_apply (a : InsideOutsideSystem O J U V X Y) {b : ℕ} (ha : IsDDCFrom E F b a)
    (t : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))) :
    (ofDDC a ha : PDCBehavior O J U V X Y E m hE F n hF).1 t =
      if Replies a (t.map Prod.fst) (t.map Prod.snd) then 1 else 0 := by
  change behaviorMass (Finsupp.single _ 1) _ _ = _
  simp only [behaviorMass, Distribution.mass_single]

/-- **Two DDCs from `E` to `F` below one system have the same behavior.** -/
theorem ofDDC_eq_of_le {a c W : InsideOutsideSystem O J U V X Y} {b b' : ℕ}
    (ha : IsDDCFrom E F b a) (hc : IsDDCFrom E F b' c)
    (haW : ∀ xs ys, Replies a xs ys → Replies W xs ys)
    (hcW : ∀ xs ys, Replies c xs ys → Replies W xs ys) :
    (ofDDC a ha : PDCBehavior O J U V X Y E m hE F n hF) = ofDDC c hc := by
  apply ext
  intro t
  change behaviorMass (Finsupp.single _ 1) _ _ = behaviorMass (Finsupp.single _ 1) _ _
  simp only [behaviorMass, Distribution.mass_single, ha.replies_iff_of_le hc haW hcW t]

end PDCBehavior

/-! ## Serial composition -/

section Serial

variable {M : Type} [Fintype M] {Xm Ym : M → Type} [∀ k, Fintype (Xm k)] [∀ k, Fintype (Ym k)]
  {F' : List (Σ k, Xm k) → Prop} {n' : ℕ} {hF' : ∀ h, F' h → h.length ≤ n'}
  {G : List (Σ o, U o) → Prop} {q : ℕ} {hG : ∀ h, G h → h.length ≤ q}

/-- The composition of two PDCs: independent samples, composed (CR18, Definition 3.17). -/
noncomputable def compPDC {bβ bα : ℕ}
    (P : Distribution.ProbDist {a : InsideOutsideSystem O M U V Xm Ym // IsDDCFrom F' G bβ a})
    (Q : Distribution.ProbDist {c : InsideOutsideSystem M J Xm Ym X Y // IsDDCFrom E F' bα c}) :
    Distribution.ProbDist {a : InsideOutsideSystem O J U V X Y // IsDDCFrom E G (bα * bβ) a} :=
  ⟨Distribution.fTransform (fun st => ⟨trim (serialM st.1.1 st.2.1), st.1.2.comp st.2.2⟩)
    (Distribution.prod P.1 Q.1),
    Distribution.fTransform_isProbDist _ (Distribution.prod_isProbDist P.1 Q.1 P.2 Q.2)⟩

omit [Fintype O] [Fintype J] [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] [∀ j, Fintype (X j)]
  [∀ j, Fintype (Y j)] [Fintype M] [∀ k, Fintype (Xm k)] [∀ k, Fintype (Ym k)] in
theorem behaviorMass_compPDC {bβ bα : ℕ}
    (P : Distribution.ProbDist {a : InsideOutsideSystem O M U V Xm Ym // IsDDCFrom F' G bβ a})
    (Q : Distribution.ProbDist {c : InsideOutsideSystem M J Xm Ym X Y // IsDDCFrom E F' bα c})
    (h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))) :
    behaviorMass (compPDC P Q).1 (h.map Prod.fst) (h.map Prod.snd) =
      (Distribution.prod P.1 Q.1).mass (fun st =>
        Replies (trim (serialM st.1.1 st.2.1)) (h.map Prod.fst) (h.map Prod.snd)) := by
  simp only [compPDC, behaviorMass, Distribution.mass_fTransform]

omit [Fintype O] [Fintype J] [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] [∀ j, Fintype (X j)]
  [∀ j, Fintype (Y j)] [Fintype M] [∀ k, Fintype (Xm k)] [∀ k, Fintype (Ym k)] in
theorem serial_bound {b : ℕ} {a : InsideOutsideSystem O M U V Xm Ym} (ha : IsDDC b a)
    (c : InsideOutsideSystem M J Xm Ym X Y) (us xs ys)
    (tr : Transcript (pair a c) (connectionQueries serialRouteM serialInjM us) xs ys)
    (hd : ¬ (connectionQueries serialRouteM serialInjM us ys).Dom) :
    ys.length ≤ (2 * b + 2) * us.length :=
  tr.connection_length_le cyclesThrough_serial ha.bound hd

/-- On presentations, the serial connection law is the behavior of the composed PDC, for any
valid internal bound `c`. -/
theorem serial_connectionLaw
    {R : RandomSystem (Σ l, twoFam U Ym l) (Σ l, twoFam V Xm l) (Domain.converter F' n' hF' G q hG)}
    {S : RandomSystem (Σ l, twoFam Xm Y l) (Σ l, twoFam Ym X l) (Domain.converter E m hE F' n' hF')}
    {bβ bα c : ℕ} (hc : IsPDCBehavior O M U V Xm Ym F' n' hF' G q hG c R)
    (P : Distribution.ProbDist {a : InsideOutsideSystem O M U V Xm Ym // IsDDCFrom F' G bβ a})
    (Q : Distribution.ProbDist {c : InsideOutsideSystem M J Xm Ym X Y // IsDDCFrom E F' bα c})
    (hP : ∀ h, behaviorMass P.1 (h.map Prod.fst) (h.map Prod.snd) = R h)
    (hQ : ∀ h, behaviorMass Q.1 (h.map Prod.fst) (h.map Prod.snd) = S h)
    (h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))) :
    (RandomSystem.parallel R S).connectionLaw serialRouteM serialInjM (h.map Prod.fst)
        ((2 * c + 2) * (h.map Prod.fst).length) (h.map Prod.snd) =
      behaviorMass (compPDC P Q).1 (h.map Prod.fst) (h.map Prod.snd) := by
  have hbound {b} (hb : IsPDCBehavior O M U V Xm Ym F' n' hF' G q hG b R) :
      ∀ t, Cons (connectionQueries serialRouteM serialInjM (h.map Prod.fst)) t →
        RandomSystem.parallel R S t ≠ 0 →
        ¬ (connectionQueries serialRouteM serialInjM (h.map Prod.fst) (t.map Prod.snd)).Dom →
        t.length ≤ (2 * b + 2) * (h.map Prod.fst).length :=
    fun t ht hm hd => RandomSystem.parallel_connection_length_le R S serialRouteM serialInjM
      (IsDDCFrom F' G b) (fun _ => True) (fun _ hg => hb.isDDCFrom_realization hg)
      (fun _ _ => trivial) (fun us => (2 * b + 2) * us.length)
      (fun a c ha _ => serial_bound ha.isDDC c) ht hm hd
  rw [RandomSystem.connectionLaw_eq_of_bounds _ _ _ _ _ _ (hbound hc) (hbound (b := bβ) ⟨P, hP⟩),
    RandomSystem.connectionLaw_eq_mass _ (Distribution.prod P.1 Q.1) (P.2.1.prod Q.2.1)
      (fun st => pair st.1.1 st.2.1)
      (RandomSystem.parallel_mass_of_presentations R S P.1 Q.1 Subtype.val Subtype.val
        (fun h => (hP h).symm) (fun h => (hQ h).symm)) _ _ _ _
      (fun st hst xs ys tr hd => serial_bound (st.1.2.isDDC) st.2.1 _ xs ys tr hd),
    behaviorMass_compPDC]
  exact Distribution.mass_congr _ (fun st => (replies_trim_iff _ _ _).symm)

namespace PDCBehavior

/-- **Serial composition** (CR18, Definitions 3.9 and 3.17): the two PDCs are sampled
independently and connected, the inside of `β` to the outside of `α`. -/
noncomputable def comp (β : PDCBehavior O M U V Xm Ym F' n' hF' G q hG)
    (α : PDCBehavior M J Xm Ym X Y E m hE F' n' hF') : PDCBehavior O J U V X Y E m hE G q hG :=
  ⟨RandomSystem.connection β.1 α.1 serialRouteM serialInjM
      (fun us => (2 * β.2.choose + 2) * us.length)
      (fun _ hg => β.2.choose_spec.isDDCFrom_realization hg) (fun _ hg => α.2.choose_spec.isDDCFrom_realization hg)
      (fun a c ha _ => serial_bound ha.isDDC c)
      (fun a c ha hc h x hr => by
        have hr' : Replies (trim (serialM a c)) (h.map Prod.fst) (h.map Prod.snd) :=
          (replies_trim_iff _ _ _).mpr hr
        have he := (ha.comp hc).answers h x hr'
        rwa [trim_snoc_of_reach (s := serialM a c) hr.reach] at he),
    α.2.choose * β.2.choose, compPDC β.2.choose_spec.choose α.2.choose_spec.choose, fun h =>
      (serial_connectionLaw β.2.choose_spec _ _ β.2.choose_spec.choose_spec
        α.2.choose_spec.choose_spec h).symm⟩

/-- **The composition of presentations presents the composition.** -/
theorem comp_presents (β : PDCBehavior O M U V Xm Ym F' n' hF' G q hG)
    (α : PDCBehavior M J Xm Ym X Y E m hE F' n' hF') {bβ bα : ℕ}
    (P : Distribution.ProbDist {a : InsideOutsideSystem O M U V Xm Ym // IsDDCFrom F' G bβ a})
    (Q : Distribution.ProbDist {c : InsideOutsideSystem M J Xm Ym X Y // IsDDCFrom E F' bα c})
    (hP : ∀ h, behaviorMass P.1 (h.map Prod.fst) (h.map Prod.snd) = β.1 h)
    (hQ : ∀ h, behaviorMass Q.1 (h.map Prod.fst) (h.map Prod.snd) = α.1 h)
    (h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))) :
    (comp β α).1 h = behaviorMass (compPDC P Q).1 (h.map Prod.fst) (h.map Prod.snd) :=
  serial_connectionLaw β.2.choose_spec P Q hP hQ h

/-- The composition of two DDCs as behaviors is the behavior of their composition. -/
theorem comp_ofDDC {a : InsideOutsideSystem O M U V Xm Ym} {c : InsideOutsideSystem M J Xm Ym X Y}
    {bβ bα : ℕ} (ha : IsDDCFrom F' G bβ a) (hc : IsDDCFrom E F' bα c) :
    comp (ofDDC a ha : PDCBehavior O M U V Xm Ym F' n' hF' G q hG)
        (ofDDC c hc : PDCBehavior M J Xm Ym X Y E m hE F' n' hF') =
      ofDDC (trim (serialM a c)) (ha.comp hc) := by
  apply ext
  intro h
  rw [comp_presents _ _ ⟨Finsupp.single ⟨a, ha⟩ 1, Distribution.isProbDist_single _⟩
    ⟨Finsupp.single ⟨c, hc⟩ 1, Distribution.isProbDist_single _⟩ (fun _ => rfl) (fun _ => rfl),
    behaviorMass_compPDC, Distribution.prod_single_left, Distribution.mass_fTransform]
  change _ = behaviorMass (Finsupp.single _ 1) _ _
  simp only [behaviorMass, Distribution.mass_single]

/-- Composing after a DDC: the behavior is the mass of the composed samples. -/
theorem ofDDC_comp_presents {a : InsideOutsideSystem O M U V Xm Ym} {bβ bα : ℕ}
    (ha : IsDDCFrom F' G bβ a) (α : PDCBehavior M J Xm Ym X Y E m hE F' n' hF')
    (Q : Distribution.ProbDist {c : InsideOutsideSystem M J Xm Ym X Y // IsDDCFrom E F' bα c})
    (hQ : ∀ h, behaviorMass Q.1 (h.map Prod.fst) (h.map Prod.snd) = α.1 h)
    (h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))) :
    (comp (ofDDC a ha : PDCBehavior O M U V Xm Ym F' n' hF' G q hG) α).1 h =
      Q.1.mass (fun c => Replies (trim (serialM a c.1)) (h.map Prod.fst) (h.map Prod.snd)) := by
  rw [comp_presents _ α ⟨Finsupp.single ⟨a, ha⟩ 1, Distribution.isProbDist_single _⟩ Q
    (fun _ => rfl) hQ, behaviorMass_compPDC, Distribution.prod_single_left,
    Distribution.mass_fTransform]

/-- Composing before a DDC: the behavior is the mass of the composed samples. -/
theorem comp_ofDDC_presents (β : PDCBehavior O M U V Xm Ym F' n' hF' G q hG) {bβ bα : ℕ}
    (P : Distribution.ProbDist {a : InsideOutsideSystem O M U V Xm Ym // IsDDCFrom F' G bβ a})
    (hP : ∀ h, behaviorMass P.1 (h.map Prod.fst) (h.map Prod.snd) = β.1 h)
    {c : InsideOutsideSystem M J Xm Ym X Y} (hc : IsDDCFrom E F' bα c)
    (h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))) :
    (comp β (ofDDC c hc : PDCBehavior M J Xm Ym X Y E m hE F' n' hF')).1 h =
      P.1.mass (fun a => Replies (trim (serialM a.1 c)) (h.map Prod.fst) (h.map Prod.snd)) := by
  rw [comp_presents β _ P ⟨Finsupp.single ⟨c, hc⟩ 1, Distribution.isProbDist_single _⟩
    hP (fun _ => rfl), behaviorMass_compPDC, Distribution.prod_single_right,
    Distribution.mass_fTransform]

/-- Serial composition is associative. -/
theorem comp_assoc {L : Type} [Fintype L] {XL YL : L → Type} [∀ k, Fintype (XL k)]
    [∀ k, Fintype (YL k)] {F'' : List (Σ k, XL k) → Prop} {n'' : ℕ}
    {hF'' : ∀ h, F'' h → h.length ≤ n''}
    (γ : PDCBehavior O L U V XL YL F'' n'' hF'' G q hG) (β : PDCBehavior L M XL YL Xm Ym F' n' hF' F'' n'' hF'')
    (α : PDCBehavior M J Xm Ym X Y E m hE F' n' hF') : comp (comp γ β) α = comp γ (comp β α) := by
  obtain ⟨bγ, P, hP⟩ := γ.2
  obtain ⟨bβ, Q, hQ⟩ := β.2
  obtain ⟨bα, T, hT⟩ := α.2
  apply ext
  intro h
  rw [comp_presents (comp γ β) α (compPDC P Q) T (fun h => (comp_presents γ β P Q hP hQ h).symm) hT,
    comp_presents γ (comp β α) P (compPDC Q T) hP (fun h => (comp_presents β α Q T hQ hT h).symm),
    behaviorMass_compPDC, behaviorMass_compPDC]
  simp only [compPDC]
  rw [Distribution.fTransform_prod_left, Distribution.fTransform_prod_right,
    Distribution.mass_fTransform, Distribution.mass_fTransform,
    ← Distribution.fTransform_assoc_prod, Distribution.mass_fTransform]
  apply Distribution.mass_congr
  intro st
  exact iff_of_eq (congrArg (fun s => Replies s (h.map Prod.fst) (h.map Prod.snd))
    (IsDDC.trim_serialM_assoc st.2.2.1 st.1.2.isDDC st.2.1.2.isDDC))

end PDCBehavior

end Serial

/-! ## The identity -/

namespace PDCBehavior

/-- **The identity** from `E` to `E`: the filter forwarding the outside queries in `E`. -/
protected noncomputable def id (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p) :
    PDCBehavior J J X Y X Y E m hE E m hE :=
  ofDDC _ (isDDCFrom_filter (Y := Y) hE')

variable {M : Type} [Fintype M] {Xm Ym : M → Type} [∀ k, Fintype (Xm k)] [∀ k, Fintype (Ym k)]

theorem comp_id (α : PDCBehavior O J U V X Y E m hE F n hF)
    (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p) :
    comp α (PDCBehavior.id (m := m) (hE := hE) hE') = α := by
  obtain ⟨b, P, hP⟩ := α.2
  apply ext
  intro h
  rw [comp_presents α _ P _ hP (fun _ => rfl), behaviorMass_compPDC,
    Distribution.prod_single_right, Distribution.mass_fTransform, ← hP]
  exact Distribution.mass_congr _ (fun s => s.2.replies_serialM_filter hE' h)

theorem id_comp (α : PDCBehavior O J U V X Y E m hE F n hF)
    (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p) :
    comp (PDCBehavior.id (m := n) (hE := hF) hF') α = α := by
  obtain ⟨b, P, hP⟩ := α.2
  apply ext
  intro h
  rw [comp_presents _ α _ P (fun _ => rfl) hP, behaviorMass_compPDC,
    Distribution.prod_single_left, Distribution.mass_fTransform, ← hP]
  exact Distribution.mass_congr _ (fun s => s.2.replies_filter_serialM hF' h)

end PDCBehavior

end SystemAlgebra
