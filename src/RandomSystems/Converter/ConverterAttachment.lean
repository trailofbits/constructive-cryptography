import RandomSystems.Converter.PDCBehavior

/-!
# Attaching PDC behaviors to resources

A resource with domain `E` is a random system on the interface alphabets over the inputs
in `E`, replying at the queried interface. A PDC from `E` to `F` attached to it is sampled
independently of it, and the samples are attached deterministically (CR18, Definitions 3.9
and 3.17, printed pp. 62–64); the result is a resource with domain `F`. Attaching the
identity changes nothing, and attaching a serial composition attaches the inner PDC first.

## Main definitions

* `attachPDS`: the attachment of a PDC to a PDS
* `PDCBehavior.attach`: the attachment of a PDC behavior to a resource

## Main results

* `RandomSystem.isResource_realization`: the realizations of possible choices of a resource
  are deterministic resources with the same domain
* `PDCBehavior.attach_presents`: the attachment of presentations presents the attachment
* `PDCBehavior.attach_id`, `PDCBehavior.attach_comp`
-/

namespace SystemAlgebra

open Classical Probability

variable {O J : Type} [Fintype O] [Fintype J] {U V : O → Type} {X Y : J → Type}
  [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] [∀ j, Fintype (X j)] [∀ j, Fintype (Y j)]
  {E : List (Σ j, X j) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
  {F : List (Σ o, U o) → Prop} {n : ℕ} {hF : ∀ h, F h → h.length ≤ n}

omit [Fintype O] [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] in
/-- **The realizations of possible choices of a resource** are deterministic resources with
its domain, replying at the queried interface. -/
theorem RandomSystem.isResource_realization
    (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    {R : RandomSystem (Σ j, X j) (Σ j, Y j) (Domain.ofInputs E m hE)}
    (hR : R.RepliesAtQueriedInterface) {g} (hg : R.2.isSubprobabilistic.PossibleChoice g) :
    IsDDS (realization g).1 ∧ SystemAlgebra.RepliesAtQueriedInterface (realization g).1 ∧
      ∀ h, ((realization g).1 h).Dom ↔ E h := by
  have hs := (realization g).2
  have answers := R.hasDomain_realization hg
  refine ⟨hs, fun h a y hy => ?_, fun h => ?_⟩
  · obtain ⟨t, rfl, ht⟩ := (reach_snoc_iff.mp ((hs.reach_iff (by simp)).mpr hy.1)).1.exists_transcript
    have hr : Replies (realization g).1 ((t ++ [(a, y)]).map Prod.fst)
        ((t ++ [(a, y)]).map Prod.snd) := by
      simpa only [List.map_append, List.map_singleton] using
        replies_snoc.mpr ⟨ht, Part.eq_some_iff.mpr hy⟩
    by_contra hne
    exact R.2.isSubprobabilistic.realization_possible g hg hr (hR _ _ _ hne)
  · exact (hasDomain_ofInputs_iff hE' hs).mp answers h

omit [Fintype O] [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] in
/-- Every resource is the behavior of a PDS of deterministic resources with its domain. -/
theorem RandomSystem.exists_resource_presentation
    (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (R : RandomSystem (Σ j, X j) (Σ j, Y j) (Domain.ofInputs E m hE))
    (hR : R.RepliesAtQueriedInterface) :
    ∃ Q : Distribution.ProbDist {s : InterfaceSystem J X Y //
        IsDDS s ∧ SystemAlgebra.RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ E h},
      ∀ h, behaviorMass Q.1 (h.map Prod.fst) (h.map Prod.snd) = R h := by
  obtain ⟨Q, hQ, -⟩ := R.2.isSubprobabilistic.exists_presentation (n := m)
    (fun h hl => R.mass_eq_zero_of_bound_lt hl)
    (fun s => IsDDS s ∧ SystemAlgebra.RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ E h)
    (fun _ hg => RandomSystem.isResource_realization hE' hR hg)
  exact ⟨Q, hQ⟩

omit [Fintype O] [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] in
/-- The behavior of a PDS of deterministic resources replies at the queried interface. -/
theorem RandomSystem.ofPDS_repliesAtQueriedInterface
    (Q : Distribution.ProbDist {s : InterfaceSystem J X Y //
      IsDDS s ∧ SystemAlgebra.RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ E h}) :
    (RandomSystem.ofPDS Q.1 Q.2 (fun s _ _ _ _ => s.2.2.2 _) :
      RandomSystem (Σ j, X j) (Σ j, Y j) (Domain.ofInputs E m hE)).RepliesAtQueriedInterface :=
  fun h x y hne => by
    apply Distribution.mass_eq_zero_of_forall_not
    intro s hs
    simp only [List.map_append, List.map_singleton] at hs
    exact hne (s.2.2.1 _ x y (Part.eq_some_iff.mp (replies_snoc.mp hs).2))

omit [Fintype O] [Fintype J] [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] [∀ j, Fintype (X j)]
  [∀ j, Fintype (Y j)] in
/-- The attachment of a PDC to a PDS: independent samples, attached. -/
noncomputable def attachPDS (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p) {b : ℕ}
    (P : Distribution.ProbDist {a : InsideOutsideSystem O J U V X Y // IsDDCFrom E F b a})
    (Q : Distribution.ProbDist {s : InterfaceSystem J X Y //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ E h}) :
    Distribution.ProbDist {s : InterfaceSystem O U V //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ F h} :=
  ⟨Distribution.fTransform (fun st => ⟨trim (apply st.1.1 st.2.1),
      SilentAtEmpty.isDDS_trim (by simp [SilentAtEmpty, apply_eq]),
      (st.1.2.mapsDomain hF') st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2⟩)
    (Distribution.prod P.1 Q.1),
    Distribution.fTransform_isProbDist _ (Distribution.prod_isProbDist P.1 Q.1 P.2 Q.2)⟩

omit [Fintype O] [Fintype J] [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] [∀ j, Fintype (X j)]
  [∀ j, Fintype (Y j)] in
theorem behaviorMass_attachPDS (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p) {b : ℕ}
    (P : Distribution.ProbDist {a : InsideOutsideSystem O J U V X Y // IsDDCFrom E F b a})
    (Q : Distribution.ProbDist {s : InterfaceSystem J X Y //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ E h})
    (h : List ((Σ o, U o) × (Σ o, V o))) :
    behaviorMass (attachPDS hF' P Q).1 (h.map Prod.fst) (h.map Prod.snd) =
      (Distribution.prod P.1 Q.1).mass (fun st =>
        Replies (trim (apply st.1.1 st.2.1)) (h.map Prod.fst) (h.map Prod.snd)) := by
  simp only [attachPDS, behaviorMass, Distribution.mass_fTransform]

omit [Fintype O] [Fintype J] [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] [∀ j, Fintype (X j)]
  [∀ j, Fintype (Y j)] in
theorem resource_bound {b : ℕ} {a : InsideOutsideSystem O J U V X Y} (ha : IsDDC b a)
    (s : InterfaceSystem J X Y) (us xs ys)
    (tr : Transcript (pair a s) (connectionQueries resourceRoute resourceInput us) xs ys)
    (hd : ¬ (connectionQueries resourceRoute resourceInput us ys).Dom) :
    ys.length ≤ (2 * b + 2) * us.length :=
  tr.connection_length_le cyclesThrough_resource ha.bound hd

/-- On presentations, the attachment law is the behavior of the attached PDS, for any valid
internal bound `c`. -/
theorem resource_connectionLaw (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    {α : RandomSystem (Σ l, twoFam U Y l) (Σ l, twoFam V X l) (Domain.converter E m hE F n hF)}
    {R : RandomSystem (Σ j, X j) (Σ j, Y j) (Domain.ofInputs E m hE)}
    {b c : ℕ} (hc : IsPDCBehavior O J U V X Y E m hE F n hF c α)
    (P : Distribution.ProbDist {a : InsideOutsideSystem O J U V X Y // IsDDCFrom E F b a})
    (Q : Distribution.ProbDist {s : InterfaceSystem J X Y //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ E h})
    (hP : ∀ h, behaviorMass P.1 (h.map Prod.fst) (h.map Prod.snd) = α h)
    (hQ : ∀ h, behaviorMass Q.1 (h.map Prod.fst) (h.map Prod.snd) = R h)
    (h : List ((Σ o, U o) × (Σ o, V o))) :
    (RandomSystem.parallel α R).connectionLaw resourceRoute resourceInput (h.map Prod.fst)
        ((2 * c + 2) * (h.map Prod.fst).length) (h.map Prod.snd) =
      behaviorMass (attachPDS hF' P Q).1 (h.map Prod.fst) (h.map Prod.snd) := by
  have hbound {b} (hb : IsPDCBehavior O J U V X Y E m hE F n hF b α) :
      ∀ t, Cons (connectionQueries resourceRoute resourceInput (h.map Prod.fst)) t →
        RandomSystem.parallel α R t ≠ 0 →
        ¬ (connectionQueries resourceRoute resourceInput (h.map Prod.fst) (t.map Prod.snd)).Dom →
        t.length ≤ (2 * b + 2) * (h.map Prod.fst).length :=
    fun t ht hm hd => RandomSystem.parallel_connection_length_le α R resourceRoute resourceInput
      (IsDDCFrom E F b) (fun _ => True) (fun _ hg => hb.isDDCFrom_realization hg)
      (fun _ _ => trivial) (fun us => (2 * b + 2) * us.length)
      (fun a s ha _ => resource_bound ha.isDDC s) ht hm hd
  rw [RandomSystem.connectionLaw_eq_of_bounds _ _ _ _ _ _ (hbound hc) (hbound (b := b) ⟨P, hP⟩),
    RandomSystem.connectionLaw_eq_mass _ (Distribution.prod P.1 Q.1) (P.2.1.prod Q.2.1)
      (fun st => pair st.1.1 st.2.1)
      (RandomSystem.parallel_mass_of_presentations α R P.1 Q.1 Subtype.val Subtype.val
        (fun h => (hP h).symm) (fun h => (hQ h).symm)) _ _ _ _
      (fun st hst xs ys tr hd => resource_bound st.1.2.isDDC st.2.1 _ xs ys tr hd),
    behaviorMass_attachPDS]
  exact Distribution.mass_congr _ (fun st => by rw [replies_trim_iff, apply_eq])

namespace PDCBehavior

/-- **Attachment** (CR18, Definitions 3.9 and 3.17): the PDC and the resource are
sampled independently and connected. The result is a resource with domain `F`. -/
noncomputable def attach (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (α : PDCBehavior O J U V X Y E m hE F n hF)
    (R : RandomSystem (Σ j, X j) (Σ j, Y j) (Domain.ofInputs E m hE))
    (hR : R.RepliesAtQueriedInterface) :
    RandomSystem (Σ o, U o) (Σ o, V o) (Domain.ofInputs F n hF) :=
  RandomSystem.connection α.1 R resourceRoute resourceInput
    (fun us => (2 * α.2.choose + 2) * us.length) (p := IsDDCFrom E F α.2.choose)
    (q := fun s => IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ E h)
    (fun _ hg => α.2.choose_spec.isDDCFrom_realization hg)
    (fun _ hg => RandomSystem.isResource_realization hE' hR hg)
    (fun a s ha _ => resource_bound ha.isDDC s)
    (fun a s ha hs h x hr => by
      have he := (ha.mapsDomain hF').admits hs.1 hs.2.1 hs.2.2 h x
        (by simpa only [apply_eq] using hr)
      rw [apply_eq] at he
      exact he)

variable (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
  (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)

/-- **The attachment of presentations presents the attachment.** -/
theorem attach_presents (α : PDCBehavior O J U V X Y E m hE F n hF)
    (R : RandomSystem (Σ j, X j) (Σ j, Y j) (Domain.ofInputs E m hE))
    (hR : R.RepliesAtQueriedInterface) {b : ℕ}
    (P : Distribution.ProbDist {a : InsideOutsideSystem O J U V X Y // IsDDCFrom E F b a})
    (Q : Distribution.ProbDist {s : InterfaceSystem J X Y //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ E h})
    (hP : ∀ h, behaviorMass P.1 (h.map Prod.fst) (h.map Prod.snd) = α.1 h)
    (hQ : ∀ h, behaviorMass Q.1 (h.map Prod.fst) (h.map Prod.snd) = R h)
    (h : List ((Σ o, U o) × (Σ o, V o))) :
    attach hE' hF' α R hR h = behaviorMass (attachPDS hF' P Q).1 (h.map Prod.fst) (h.map Prod.snd) :=
  resource_connectionLaw hF' α.2.choose_spec P Q hP hQ h

/-- **A completed internal transcript of probability one** gives its outside transcript
probability one. -/
theorem attach_mass_eq_one (α : PDCBehavior O J U V X Y E m hE F n hF)
    (R : RandomSystem (Σ j, X j) (Σ j, Y j) (Domain.ofInputs E m hE))
    (hR : R.RepliesAtQueriedInterface) (h : List ((Σ o, U o) × (Σ o, V o)))
    (H : List (Two (Σ l, twoFam U Y l) (Σ j, X j) × Two (Σ l, twoFam V X l) (Σ j, Y j)))
    (hc : Cons (connectionQueries resourceRoute resourceInput (h.map Prod.fst)) H)
    (he : exposedReplies (resourceRoute (U := U)) (H.map Prod.snd) = h.map Prod.snd)
    (hm : RandomSystem.parallel α.1 R H = 1) :
    attach hE' hF' α R hR h = 1 := by
  have hd : ¬ (connectionQueries resourceRoute resourceInput (h.map Prod.fst)
      (H.map Prod.snd)).Dom := by
    rw [connectionQueries_dom, he, List.length_map, List.length_map]
    exact Nat.lt_irrefl _
  have hn : H.length ≤ (2 * α.2.choose + 2) * (h.map Prod.fst).length :=
    RandomSystem.parallel_connection_length_le α.1 R resourceRoute resourceInput
      (IsDDCFrom E F α.2.choose) (fun _ => True)
      (fun _ hg => α.2.choose_spec.isDDCFrom_realization hg) (fun _ _ => trivial)
      (fun us => (2 * α.2.choose + 2) * us.length)
      (fun a s ha _ => resource_bound ha.isDDC s) hc (by rw [hm]; exact one_ne_zero) hd
  apply le_antisymm
  · simpa only [List.nil_append, RandomSystem.mass_nil] using
      (attach hE' hF' α R hR).mass_append_le [] h
  · have lower := (RandomSystem.parallel α.1 R).mass_le_connectionLaw resourceRoute
      resourceInput (h.map Prod.fst) _ H hc hn hd
    rw [hm, he] at lower
    exact lower

/-- The attachment replies at the queried interface. -/
theorem attach_repliesAtQueriedInterface (α : PDCBehavior O J U V X Y E m hE F n hF)
    (R : RandomSystem (Σ j, X j) (Σ j, Y j) (Domain.ofInputs E m hE))
    (hR : R.RepliesAtQueriedInterface) : (attach hE' hF' α R hR).RepliesAtQueriedInterface := by
  obtain ⟨b, P, hP⟩ := α.2
  obtain ⟨Q, hQ⟩ := RandomSystem.exists_resource_presentation hE' R hR
  intro h x y hne
  have hm := attach_presents hE' hF' α R hR P Q hP hQ (h ++ [(x, y)])
  rw [hm]
  apply Distribution.mass_eq_zero_of_forall_not
  intro s hs
  simp only [List.map_append, List.map_singleton] at hs
  exact hne (s.2.2.1 _ x y (Part.eq_some_iff.mp (replies_snoc.mp hs).2))

/-- **Attaching the identity** leaves a resource unchanged. -/
theorem attach_id (R : RandomSystem (Σ j, X j) (Σ j, Y j) (Domain.ofInputs E m hE))
    (hR : R.RepliesAtQueriedInterface) :
    attach hE' hE' (PDCBehavior.id (m := m) (hE := hE) hE') R hR = R := by
  obtain ⟨Q, hQ⟩ := RandomSystem.exists_resource_presentation hE' R hR
  apply RandomSystem.ext
  intro h
  rw [attach_presents hE' hE' _ R hR _ Q (fun _ => rfl) hQ, behaviorMass_attachPDS,
    Distribution.prod_single_left, Distribution.mass_fTransform, ← hQ]
  exact Distribution.mass_congr _ (fun s => by
    rw [trim_apply_filter_of_dom hE' s.2.1 s.2.2.1 s.2.2.2])

/-- **Serial attachment** (MR16 §3.3: `(β ∘ α)ⁱR = βⁱ(αⁱR)`): attaching a serial composition
attaches the inner PDC first. -/
theorem attach_comp {M : Type} [Fintype M] {Xm Ym : M → Type} [∀ k, Fintype (Xm k)]
    [∀ k, Fintype (Ym k)] {F'' : List (Σ k, Xm k) → Prop} {n'' : ℕ}
    {hF'' : ∀ h, F'' h → h.length ≤ n''}
    (hF''' : ¬ F'' [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F'' h → F'' p)
    (β : PDCBehavior O M U V Xm Ym F'' n'' hF'' F n hF) (α : PDCBehavior M J Xm Ym X Y E m hE F'' n'' hF'')
    (R : RandomSystem (Σ j, X j) (Σ j, Y j) (Domain.ofInputs E m hE))
    (hR : R.RepliesAtQueriedInterface) :
    attach hE' hF' (comp β α) R hR =
      attach hF''' hF' β (attach hE' hF''' α R hR)
        (attach_repliesAtQueriedInterface hE' hF''' α R hR) := by
  obtain ⟨bβ, P, hP⟩ := β.2
  obtain ⟨bα, Q, hQ⟩ := α.2
  obtain ⟨T, hT⟩ := RandomSystem.exists_resource_presentation hE' R hR
  apply RandomSystem.ext
  intro h
  rw [attach_presents hE' hF' _ R hR (compPDC P Q) T
      (fun h => (comp_presents β α P Q hP hQ h).symm) hT,
    attach_presents hF''' hF' β _ _ P (attachPDS hF''' Q T) hP
      (fun h => (attach_presents hE' hF''' α R hR Q T hQ hT h).symm),
    behaviorMass_attachPDS, behaviorMass_attachPDS]
  simp only [compPDC, attachPDS]
  rw [Distribution.fTransform_prod_left, Distribution.fTransform_prod_right,
    Distribution.mass_fTransform, Distribution.mass_fTransform,
    ← Distribution.fTransform_assoc_prod, Distribution.mass_fTransform]
  apply Distribution.mass_congr
  intro st
  exact iff_of_eq (congrArg (fun s => Replies s (h.map Prod.fst) (h.map Prod.snd))
    (IsDDC.trim_apply_serialM st.1.2.isDDC st.2.1.2.isDDC st.2.2.1))

end PDCBehavior

end SystemAlgebra
