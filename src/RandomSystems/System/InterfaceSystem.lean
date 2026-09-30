import RandomSystems.System.Basic

/-!
# Interface systems and connection by labels

An interface system has inputs and outputs tagged by a label `i` with alphabets
`X i` and `Y i`. Connecting a set of labels wires their outputs to other labels'
inputs; attachment, converters and closing with a distinguisher are connections.

## Main definitions

* `InterfaceSystem I X Y`
* `connect s C r`: connection of the labels `C` along the routing `r`
* `relabelI`: renaming labels and alphabets
* `pairI`, `attach`: two systems side by side, and attached at a pair of labels
* `InsideOutsideSystem`, `attachAlong`: converters with outside and inside labels,
  attached along an injection
* `close`: a system closed with a distinguisher

## Main results

* `connect_connect`, `connect_comm`, `connect_relabelI`: connections compose,
  commute when disjoint, and commute with relabeling
* `attach_assoc`: regrouping of attachments
* `attachAlong_eq`, `attachAlong_comm`, `attachAlong_protocol`
* `close_pair`, `partialClose_isDDD`
-/

-- The case analyses below share one simp set per law; not every case uses every rule.
set_option linter.unusedSimpArgs false

namespace SystemAlgebra

open Classical

/-- An interface system with local labels `I`. -/
abbrev InterfaceSystem (I : Type) (X Y : I → Type) := System (Σ i, X i) (Σ i, Y i)

section ParI

variable {K : Type} {I : K → Type} {X Y : ∀ k, I k → Type}

end ParI

/-! ## Connection by labels (spec §4) -/

section Connect

variable {I : Type} {X Y : I → Type}

/-- The free labels after connecting `C`. -/
abbrev Free (C : Set I) := {i // i ∉ C}

/-- A routing of the connected labels: each output at a connected label is
delivered as an input at a connected label. -/
abbrev Routing (C : Set I) (X Y : I → Type) := ∀ p : C, Y p → Σ q : C, X q

/-- Forget that a label is connected. -/
def liftC {C : Set I} {F : I → Type} (z : Σ q : C, F q) : Σ i, F i := ⟨z.1.1, z.2⟩

/-- The routing table of `connect` for the engine. -/
noncomputable def connectRoute (C : Set I) (r : Routing C X Y) :
    (Σ i, Y i) → (Σ i : Free C, Y i.1) ⊕ (Σ i, X i) := fun p =>
  if h : p.1 ∈ C then .inr (liftC (r ⟨p.1, h⟩ p.2)) else .inl ⟨⟨p.1, h⟩, p.2⟩

/-- External inputs keep their label. -/
def connectInj (C : Set I) : (Σ i : Free C, X i.1) → Σ i, X i := fun p => ⟨p.1.1, p.2⟩

/-- Connect the labels `C` of `s` according to `r`. -/
noncomputable def connect (s : InterfaceSystem I X Y) (C : Set I) (r : Routing C X Y) :
    InterfaceSystem (Free C) (fun i => X i.1) (fun i => Y i.1) :=
  interconnect s (connectRoute C r) (connectInj C)

theorem connectRoute_of_mem {C : Set I} (r : Routing C X Y) {p : Σ i, Y i} (h : p.1 ∈ C) :
    connectRoute C r p = .inr (liftC (r ⟨p.1, h⟩ p.2)) := dif_pos h

theorem connectRoute_of_not_mem {C : Set I} (r : Routing C X Y) {p : Σ i, Y i} (h : p.1 ∉ C) :
    connectRoute C r p = .inl ⟨⟨p.1, h⟩, p.2⟩ := dif_neg h

/-! ### Vanishing at the level of labels (C1) -/

variable (C : Set I) (C' : Set (Free C))

/-- The labels connected by two successive connections. -/
def unionSet : Set I := C ∪ Subtype.val '' C'

theorem mem_unionSet_left {i : I} (h : i ∈ C) : i ∈ unionSet C C' := Or.inl h

theorem mem_unionSet_right {i : Free C} (h : i ∈ C') : i.1 ∈ unionSet C C' :=
  Or.inr ⟨i, h, rfl⟩

theorem mem_of_mem_unionSet {i : I} (hu : i ∈ unionSet C C') (h : i ∉ C) :
    (⟨i, h⟩ : Free C) ∈ C' := by
  rcases hu with hp | ⟨q, hq, e⟩
  · exact (h hp).elim
  · have : q = ⟨i, h⟩ := Subtype.ext e
    exact this ▸ hq

/-- The union of two routings. -/
noncomputable def unionRouting (r : Routing C X Y)
    (r' : Routing C' (fun i => X i.1) (fun i => Y i.1)) : Routing (unionSet C C') X Y :=
  fun p y =>
    if h : p.1 ∈ C then
      ⟨⟨(r ⟨p.1, h⟩ y).1.1, mem_unionSet_left C C' (r ⟨p.1, h⟩ y).1.2⟩, (r ⟨p.1, h⟩ y).2⟩
    else
      let q := r' ⟨⟨p.1, h⟩, mem_of_mem_unionSet C C' p.2 h⟩ y
      ⟨⟨q.1.1.1, mem_unionSet_right C C' q.1.2⟩, q.2⟩

/-- Canonical map of inputs: free labels of the nested connection to free
labels of the union. -/
def unionIn : (Σ i : Free C', X i.1.1) → Σ i : Free (unionSet C C'), X i.1
  | ⟨i, x⟩ => ⟨⟨i.1.1, fun hu => i.2 (mem_of_mem_unionSet C C' hu i.1.2)⟩, x⟩

/-- Canonical map of outputs: free labels of the union to free labels of the
nested connection. -/
def unionOut : (Σ i : Free (unionSet C C'), Y i.1) → Σ i : Free C', Y i.1.1
  | ⟨i, y⟩ => ⟨⟨⟨i.1, fun h => i.2 (Or.inl h)⟩, fun h => i.2 (Or.inr ⟨_, h, rfl⟩)⟩, y⟩

theorem unionRouting_left (r : Routing C X Y)
    (r' : Routing C' (fun i => X i.1) (fun i => Y i.1)) (p : unionSet C C') (h : p.1 ∈ C)
    (y : Y p) : unionRouting C C' r r' p y =
      ⟨⟨(r ⟨p.1, h⟩ y).1.1, mem_unionSet_left C C' (r ⟨p.1, h⟩ y).1.2⟩, (r ⟨p.1, h⟩ y).2⟩ :=
  dif_pos h

theorem unionRouting_right (r : Routing C X Y)
    (r' : Routing C' (fun i => X i.1) (fun i => Y i.1)) (p : unionSet C C') (h : p.1 ∉ C)
    (y : Y p) : unionRouting C C' r r' p y =
      ⟨⟨(r' ⟨⟨p.1, h⟩, mem_of_mem_unionSet C C' p.2 h⟩ y).1.1.1,
        mem_unionSet_right C C' (r' ⟨⟨p.1, h⟩, mem_of_mem_unionSet C C' p.2 h⟩ y).1.2⟩,
        (r' ⟨⟨p.1, h⟩, mem_of_mem_unionSet C C' p.2 h⟩ y).2⟩ :=
  dif_neg h

theorem connectRoute_union_left (r : Routing C X Y)
    (r' : Routing C' (fun i => X i.1) (fun i => Y i.1)) {i : I} (h : i ∈ C) (y : Y i) :
    connectRoute (unionSet C C') (unionRouting C C' r r') ⟨i, y⟩ =
      .inr (liftC (r ⟨i, h⟩ y)) := by
  simp only [connectRoute, dif_pos (mem_unionSet_left C C' h)]
  rw [unionRouting_left C C' r r' ⟨i, _⟩ h]
  rfl

theorem connectRoute_union_right (r : Routing C X Y)
    (r' : Routing C' (fun i => X i.1) (fun i => Y i.1)) {i : I} (h : i ∉ C)
    (h' : (⟨i, h⟩ : Free C) ∈ C') (y : Y i) :
    connectRoute (unionSet C C') (unionRouting C C' r r') ⟨i, y⟩ =
      .inr (liftC (liftC (r' ⟨⟨i, h⟩, h'⟩ y))) := by
  simp only [connectRoute, dif_pos (mem_unionSet_right C C' h')]
  rw [unionRouting_right C C' r r' ⟨i, _⟩ h]
  rfl

/-- **C1, vanishing.** Two successive connections are one connection of the
union of the connected labels, after the canonical relabeling. -/
theorem connect_connect (s : InterfaceSystem I X Y) (r : Routing C X Y)
    (r' : Routing C' (fun i => X i.1) (fun i => Y i.1)) :
    connect (connect s C r) C' r' =
      relabel (connect s (unionSet C C') (unionRouting C C' r r'))
        (unionIn C C') (unionOut C C') := by
  unfold connect
  rw [interconnect_interconnect, relabel_interconnect]
  congr 1
  · funext ⟨i, y⟩
    by_cases h : i ∈ C
    · rw [connectRoute_union_left C C' r r' h]
      simp [routeComp, connectRoute, h]
    · by_cases h' : (⟨i, h⟩ : Free C) ∈ C'
      · rw [connectRoute_union_right C C' r r' h h']
        simp [routeComp, connectRoute, h, h', connectInj]
        rfl
      · have hu : i ∉ unionSet C C' := fun hu => h' (mem_of_mem_unionSet C C' hu h)
        simp [routeComp, connectRoute, h, h', hu, unionOut]

/-! ### Connection depends only on the connected labels and their routing -/

section Congr

variable {C₁ C₂ : Set I}

/-- Free labels of `C₁` as free labels of an equal set `C₂`. -/
def freeCast (hC : ∀ i, i ∈ C₁ ↔ i ∈ C₂) : (Σ i : Free C₁, X i.1) → Σ i : Free C₂, X i.1
  | ⟨i, x⟩ => ⟨⟨i.1, fun h => i.2 ((hC _).2 h)⟩, x⟩

/-- Connecting along equal label sets with agreeing routings gives the same system. -/
theorem connect_congr (s : InterfaceSystem I X Y) (r₁ : Routing C₁ X Y) (r₂ : Routing C₂ X Y)
    (hC : ∀ i, i ∈ C₁ ↔ i ∈ C₂)
    (hr : ∀ i (h₁ : i ∈ C₁) (y : Y i), liftC (r₁ ⟨i, h₁⟩ y) = liftC (r₂ ⟨i, (hC i).1 h₁⟩ y)) :
    connect s C₁ r₁ = relabel (connect s C₂ r₂) (freeCast hC) (freeCast (fun i => (hC i).symm)) := by
  unfold connect
  rw [relabel_interconnect]
  congr 1
  funext ⟨i, y⟩
  by_cases h : i ∈ C₁
  · rw [connectRoute_of_mem r₁ (p := ⟨i, y⟩) h, connectRoute_of_mem r₂ (p := ⟨i, y⟩) ((hC i).1 h)]
    simp [hr i h y]
  · rw [connectRoute_of_not_mem r₁ (p := ⟨i, y⟩) h,
      connectRoute_of_not_mem r₂ (p := ⟨i, y⟩) (fun h' => h ((hC i).2 h'))]
    rfl

end Congr

/-! ### Disjoint connections commute (C4) -/

section Commute

variable (C C' : Set I) (hd : ∀ i, i ∈ C → i ∉ C')

/-- The labels `C'`, disjoint from `C`, seen among the free labels of `C`. -/
def freeSet : Set (Free C) := {i | i.1 ∈ C'}

/-- A routing of `C'`, disjoint from `C`, seen on the free labels of `C`. -/
def freeRouting (r' : Routing C' X Y) :
    Routing (freeSet C C') (fun i => X i.1) (fun i => Y i.1) := fun p y =>
  let q := r' ⟨p.1.1, p.2⟩ y
  ⟨⟨⟨q.1.1, fun h => hd _ h q.1.2⟩, q.1.2⟩, q.2⟩

/-- Free labels of `C` then `C'` as free labels of `C'` then `C`. -/
def swapFree : (Σ i : Free (freeSet C C'), X i.1.1) →
    Σ i : Free (freeSet C' C), X i.1.1
  | ⟨⟨⟨i, h₁⟩, h₂⟩, x⟩ => ⟨⟨⟨i, h₂⟩, h₁⟩, x⟩

theorem union_freeSet_iff (i : I) :
    i ∈ unionSet C (freeSet C C') ↔ i ∈ unionSet C' (freeSet C' C) := by
  simp only [unionSet, freeSet, Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Subtype.exists,
    exists_and_right, exists_eq_right]
  constructor
  · rintro (h | ⟨_, h⟩) <;> tauto
  · rintro (h | ⟨_, h⟩) <;> tauto

/-- **C4.** Connections of disjoint label sets commute, after the canonical relabeling. -/
theorem connect_comm (s : InterfaceSystem I X Y) (r : Routing C X Y) (r' : Routing C' X Y) :
    connect (connect s C r) (freeSet C C') (freeRouting C C' hd r') =
      relabel (connect (connect s C' r') (freeSet C' C)
          (freeRouting C' C (fun i h h' => hd i h' h) r))
        (swapFree C C') (swapFree C' C) := by
  rw [connect_connect, connect_connect,
    connect_congr s _ _ (union_freeSet_iff C C') ?_, relabel_relabel, relabel_relabel]
  · congr 1
  · intro i h₁ y
    by_cases hC : i ∈ C
    · have hC' : i ∉ C' := hd i hC
      rw [unionRouting_left _ _ _ _ ⟨i, h₁⟩ hC, unionRouting_right _ _ _ _ _ hC']
      rfl
    · have hC' : i ∈ C' := by
        rcases h₁ with h | ⟨q, hq, rfl⟩
        · exact (hC h).elim
        · exact hq
      rw [unionRouting_right _ _ _ _ ⟨i, h₁⟩ hC, unionRouting_left _ _ _ _ _ hC']
      rfl

end Commute

/-! ### Relabeling and connection (C2) -/

section Natural

variable {J : Type} {U V : J → Type}

/-- Relabeling along `τ : I ≃ J` and equivalences of the message families (spec §2). -/
def relabelI (s : InterfaceSystem I X Y) (τ : I ≃ J) (φ : ∀ i, X i ≃ U (τ i)) (ψ : ∀ i, Y i ≃ V (τ i)) :
    InterfaceSystem J U V :=
  relabel s (Equiv.sigmaCongr τ φ).symm (Equiv.sigmaCongr τ ψ)

/-- **C2.** Relabeling commutes with connection: if `r'` corresponds to `r` under
the relabeling, connecting the relabeled system is relabeling the connected one. -/
theorem connect_relabelI (s : InterfaceSystem I X Y) (τ : I ≃ J) (φ : ∀ i, X i ≃ U (τ i))
    (ψ : ∀ i, Y i ≃ V (τ i)) (C : Set I) (r : Routing C X Y) (C' : Set J)
    (hC : ∀ i, i ∈ C ↔ τ i ∈ C') (r' : Routing C' U V)
    (hr : ∀ i (h : i ∈ C) (y : Y i),
      liftC (r' ⟨τ i, (hC i).1 h⟩ (ψ i y)) = Equiv.sigmaCongr τ φ (liftC (r ⟨i, h⟩ y))) :
    connect (relabelI s τ φ ψ) C' r' =
      relabelI (U := fun j : Free C' => U j.1) (V := fun j : Free C' => V j.1) (connect s C r)
        (τ.subtypeEquiv fun i => not_congr (hC i)) (fun i => φ i.1) (fun i => ψ i.1) := by
  unfold connect relabelI
  rw [interconnect_relabel, relabel_interconnect]
  congr 1
  · funext ⟨i, y⟩
    by_cases h : i ∈ C
    · have e : Equiv.sigmaCongr τ ψ ⟨i, y⟩ = ⟨τ i, ψ i y⟩ := rfl
      rw [e, connectRoute_of_mem r' (p := ⟨τ i, ψ i y⟩) ((hC i).1 h),
        connectRoute_of_mem r (p := ⟨i, y⟩) h]
      simp [hr i h y]
    · have e : Equiv.sigmaCongr τ ψ ⟨i, y⟩ = ⟨τ i, ψ i y⟩ := rfl
      rw [e, connectRoute_of_not_mem r' (p := ⟨τ i, ψ i y⟩) (fun h' => h ((hC i).2 h')),
        connectRoute_of_not_mem r (p := ⟨i, y⟩) h]
      rfl
  · funext a
    apply (Equiv.sigmaCongr τ φ).injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    generalize hz : (Equiv.sigmaCongr (β₂ := fun j : Free C' => U j.1)
      (τ.subtypeEquiv fun i => not_congr (hC i)) (fun i => φ i.1)).symm a = z
    have hz' := congrArg (Equiv.sigmaCongr (β₂ := fun j : Free C' => U j.1)
      (τ.subtypeEquiv fun i => not_congr (hC i)) (fun i => φ i.1)) hz
    rw [Equiv.apply_symm_apply] at hz'
    subst hz'
    rfl

end Natural

end Connect

/-! ## Two interface systems, single connections, attachment (spec §§3–5.1) -/

section Attach

variable {I J L : Type} {X₁ Y₁ : I → Type} {X₂ Y₂ : J → Type} {X₃ Y₃ : L → Type}

/-- The message family of a two-component interface system. -/
@[reducible] def twoFam (F : I → Type) (G : J → Type) : Two I J → Type
  | ⟨none, i⟩ => F i
  | ⟨some (), j⟩ => G j

/-- Split an interface message of `[s, t]` by component. -/
def splitIn {F : I → Type} {G : J → Type} : (Σ p : Two I J, twoFam F G p) → Two (Σ i, F i) (Σ j, G j)
  | ⟨⟨none, i⟩, x⟩ => ⟨none, ⟨i, x⟩⟩
  | ⟨⟨some (), j⟩, x⟩ => ⟨some (), ⟨j, x⟩⟩

/-- Tag a component's interface message with its label in `[s, t]`. -/
def joinOut {F : I → Type} {G : J → Type} : Two (Σ i, F i) (Σ j, G j) → Σ p : Two I J, twoFam F G p
  | ⟨none, ⟨i, x⟩⟩ => ⟨⟨none, i⟩, x⟩
  | ⟨some (), ⟨j, x⟩⟩ => ⟨⟨some (), j⟩, x⟩

/-- Two interface systems side by side; ports `⟨none, i⟩` and `⟨some (), j⟩`. -/
noncomputable def pairI (s : InterfaceSystem I X₁ Y₁) (t : InterfaceSystem J X₂ Y₂) :
    InterfaceSystem (Two I J) (twoFam X₁ X₂) (twoFam Y₁ Y₂) :=
  relabel (pair s t) splitIn joinOut

variable {X Y : I → Type}

/-- The routing of a single connection `p ↔ q`. -/
noncomputable def pairRouting (p q : I) (c₁ : Y p → X q) (c₂ : Y q → X p) :
    Routing ({p, q} : Set I) X Y := fun p' y =>
  if h : p'.1 = p then ⟨⟨q, by simp⟩, c₁ (h ▸ y)⟩
  else
    have hq : p'.1 = q := by
      rcases p'.2 with e | e
      · exact (h e).elim
      · exact e
    ⟨⟨p, by simp⟩, c₂ (hq ▸ y)⟩

theorem liftC_pairRouting_p (p q : I) (c₁ : Y p → X q) (c₂ : Y q → X p)
    (p' : ({p, q} : Set I)) (h : p'.1 = p) (y : Y p') :
    liftC (pairRouting p q c₁ c₂ p' y) = ⟨q, c₁ (cast (congrArg Y h) y)⟩ := by
  obtain ⟨p', hp'⟩ := p'
  dsimp only at h
  subst p'
  unfold pairRouting
  rw [dif_pos rfl]
  rfl

theorem liftC_pairRouting_q (p q : I) (hpq : q ≠ p) (c₁ : Y p → X q) (c₂ : Y q → X p)
    (p' : ({p, q} : Set I)) (h : p'.1 = q) (y : Y p') :
    liftC (pairRouting p q c₁ c₂ p' y) = ⟨p, c₂ (cast (congrArg Y h) y)⟩ := by
  obtain ⟨p', hp'⟩ := p'
  dsimp only at h
  subst p'
  unfold pairRouting
  rw [dif_neg hpq]
  rfl

/-- Connect `p` with `q`. -/
noncomputable def connectPair (s : InterfaceSystem I X Y) (p q : I) (c₁ : Y p → X q) (c₂ : Y q → X p) :
    InterfaceSystem (Free ({p, q} : Set I)) (fun i => X i.1) (fun i => Y i.1) :=
  connect s {p, q} (pairRouting p q c₁ c₂)

/-- Attachment `s ⋈_{p,q} t` (spec §5.1). -/
noncomputable def attach (s : InterfaceSystem I X₁ Y₁) (t : InterfaceSystem J X₂ Y₂) (p : I) (q : J)
    (c₁ : Y₁ p → X₂ q) (c₂ : Y₂ q → X₁ p) :=
  connectPair (pairI s t) ⟨none, p⟩ ⟨some (), q⟩ c₁ c₂

end Attach

/-! ## Regrouping of attachments (spec §6, A1) -/

section Regroup

variable {I J L : Type} {X₁ Y₁ : I → Type} {X₂ Y₂ : J → Type} {X₃ Y₃ : L → Type}
variable (p : I) (q q' : J) (x : L)

/-- The labels connected by `s ⋈_{p,q} t`. -/
abbrev setST : Set (Two I J) := {⟨none, p⟩, ⟨some (), q⟩}

/-- The labels connected by `t ⋈_{q',x} u`. -/
abbrev setTU : Set (Two J L) := {⟨none, q'⟩, ⟨some (), x⟩}

theorem q'_free (hqq : q ≠ q') : (⟨some (), q'⟩ : Two I J) ∉ setST p q := by
  simp [setST, Ne.symm hqq]

theorem q_free (hqq : q ≠ q') : (⟨none, q⟩ : Two J L) ∉ setTU q' x := by
  simp [setTU, hqq]

/-- The labels connected in the second step of `(s ⋈ t) ⋈ u`. -/
abbrev setL (hqq : q ≠ q') : Set (Two (Free (setST p q)) L) :=
  {⟨none, ⟨⟨some (), q'⟩, q'_free p q q' hqq⟩⟩, ⟨some (), x⟩}

/-- The labels connected in the second step of `s ⋈ (t ⋈ u)`. -/
abbrev setR (hqq : q ≠ q') : Set (Two I (Free (setTU q' x))) :=
  {⟨none, p⟩, ⟨some (), ⟨⟨none, q⟩, q_free q q' x hqq⟩⟩}

theorem notMem_ST_none {i : I} : (⟨none, i⟩ : Two I J) ∉ setST p q ↔ i ≠ p := by simp [setST]
theorem notMem_ST_some {j : J} : (⟨some (), j⟩ : Two I J) ∉ setST p q ↔ j ≠ q := by simp [setST]
theorem notMem_TU_none {j : J} : (⟨none, j⟩ : Two J L) ∉ setTU q' x ↔ j ≠ q' := by simp [setTU]
theorem notMem_TU_some {k : L} : (⟨some (), k⟩ : Two J L) ∉ setTU q' x ↔ k ≠ x := by simp [setTU]
theorem notMem_L_none (hqq : q ≠ q') {z : Free (setST p q)} :
    (⟨none, z⟩ : Two _ L) ∉ setL p q q' x hqq ↔ z.1 ≠ ⟨some (), q'⟩ := by
  simp [setL, Subtype.ext_iff]
theorem notMem_L_some (hqq : q ≠ q') {k : L} :
    (⟨some (), k⟩ : Two (Free (setST p q)) L) ∉ setL p q q' x hqq ↔ k ≠ x := by simp [setL]
theorem notMem_R_none (hqq : q ≠ q') {i : I} :
    (⟨none, i⟩ : Two I _) ∉ setR p q q' x hqq ↔ i ≠ p := by simp [setR]
theorem notMem_R_some (hqq : q ≠ q') {z : Free (setTU q' x)} :
    (⟨some (), z⟩ : Two I _) ∉ setR p q q' x hqq ↔ z.1 ≠ ⟨none, q⟩ := by
  simp [setR, Subtype.ext_iff]

/-- The canonical relabeling of inputs, from `(s ⋈ t) ⋈ u` to `s ⋈ (t ⋈ u)`. -/
def regroupIn (hqq : q ≠ q') :
    (Σ l : Free (setL p q q' x hqq), twoFam (fun i : Free (setST p q) => twoFam X₁ X₂ i.1) X₃ l.1) →
      Σ l : Free (setR p q q' x hqq), twoFam X₁ (fun i : Free (setTU q' x) => twoFam X₂ X₃ i.1) l.1
  | ⟨⟨⟨none, ⟨⟨none, i⟩, h₁⟩⟩, _⟩, v⟩ =>
      ⟨⟨⟨none, i⟩, (notMem_R_none p q q' x hqq).2 ((notMem_ST_none p q).1 h₁)⟩, v⟩
  | ⟨⟨⟨none, ⟨⟨some (), j⟩, h₁⟩⟩, h₂⟩, v⟩ =>
      have hj' : j ≠ q' := fun e => (notMem_L_none p q q' x hqq).1 h₂ (by simp [e])
      ⟨⟨⟨some (), ⟨⟨none, j⟩, (notMem_TU_none q' x).2 hj'⟩⟩,
        (notMem_R_some p q q' x hqq).2 (by simpa using (notMem_ST_some p q).1 h₁)⟩, v⟩
  | ⟨⟨⟨some (), k⟩, h₂⟩, v⟩ =>
      ⟨⟨⟨some (), ⟨⟨some (), k⟩, (notMem_TU_some q' x).2 ((notMem_L_some p q q' x hqq).1 h₂)⟩⟩,
        (notMem_R_some p q q' x hqq).2 (by simp)⟩, v⟩

/-- The canonical relabeling of outputs, from `s ⋈ (t ⋈ u)` to `(s ⋈ t) ⋈ u`. -/
def regroupOut (hqq : q ≠ q') :
    (Σ l : Free (setR p q q' x hqq), twoFam Y₁ (fun i : Free (setTU q' x) => twoFam Y₂ Y₃ i.1) l.1) →
      Σ l : Free (setL p q q' x hqq), twoFam (fun i : Free (setST p q) => twoFam Y₁ Y₂ i.1) Y₃ l.1
  | ⟨⟨⟨none, i⟩, h⟩, v⟩ =>
      ⟨⟨⟨none, ⟨⟨none, i⟩, (notMem_ST_none p q).2 ((notMem_R_none p q q' x hqq).1 h)⟩⟩,
        (notMem_L_none p q q' x hqq).2 (by simp)⟩, v⟩
  | ⟨⟨⟨some (), ⟨⟨none, j⟩, h₁⟩⟩, h₂⟩, v⟩ =>
      have hjq : j ≠ q := fun e => (notMem_R_some p q q' x hqq).1 h₂ (by simp [e])
      have hj' : j ≠ q' := (notMem_TU_none q' x).1 h₁
      ⟨⟨⟨none, ⟨⟨some (), j⟩, (notMem_ST_some p q).2 hjq⟩⟩,
        (notMem_L_none p q q' x hqq).2 (by simpa using hj')⟩, v⟩
  | ⟨⟨⟨some (), ⟨⟨some (), k⟩, h₁⟩⟩, _⟩, v⟩ =>
      ⟨⟨⟨some (), k⟩, (notMem_L_some p q q' x hqq).2 ((notMem_TU_some q' x).1 h₁)⟩, v⟩

/-- **A1, regrouping.** `(s ⋈_{p,q} t) ⋈_{q',x} u = s ⋈_{p,q} (t ⋈_{q',x} u)` after
the canonical relabeling, for terminating components. -/
theorem attach_assoc (s : InterfaceSystem I X₁ Y₁) (t : InterfaceSystem J X₂ Y₂) (u : InterfaceSystem L X₃ Y₃)
    (hqq : q ≠ q') (c₁ : Y₁ p → X₂ q) (c₂ : Y₂ q → X₁ p) (d₁ : Y₂ q' → X₃ x)
    (d₂ : Y₃ x → X₂ q') (hs : Terminating s) (ht : Terminating t) (hu : Terminating u) :
    attach (attach s t p q c₁ c₂) u ⟨⟨some (), q'⟩, q'_free p q q' hqq⟩ x d₁ d₂ =
      relabel (attach s (attach t u q' x d₁ d₂) p ⟨⟨none, q⟩, q_free q q' x hqq⟩ c₁ c₂)
        (regroupIn p q q' x hqq) (regroupOut p q q' x hqq) := by
  unfold attach connectPair connect pairI
  simp only [interconnect_relabel]
  rw [pair_interconnect_left ((hs.pair ht).converges _ _), interconnect_interconnect, pair_interconnect_right s ((ht.pair hu).converges _ _), interconnect_interconnect,
    pair_assoc', interconnect_relabel, relabel_interconnect]
  congr 1
  · funext o
    rcases o with ⟨_ | ⟨⟩, o⟩
    · rcases o with ⟨_ | ⟨⟩, ⟨i, y⟩⟩
      · by_cases hi : i = p
        · subst hi
          simp only [routeComp, routeOpt, routeRight, twoMap, twoAssoc, joinOut, splitIn,
            Function.comp_def]
          simp [connectRoute_of_mem, connectRoute_of_not_mem, liftC_pairRouting_p,
            liftC_pairRouting_q, splitIn, joinOut, twoAssoc', regroupOut, connectInj, injOpt]
        · simp only [routeComp, routeOpt, routeRight, twoMap, twoAssoc, joinOut, splitIn,
            Function.comp_def]
          simp [connectRoute_of_mem, connectRoute_of_not_mem, liftC_pairRouting_p,
            liftC_pairRouting_q, splitIn, joinOut, twoAssoc', regroupOut, connectInj, injOpt, hi]
      · by_cases hj : i = q
        · subst hj
          simp only [routeComp, routeOpt, routeRight, twoMap, twoAssoc, joinOut, splitIn,
            Function.comp_def]
          simp [connectRoute_of_mem, connectRoute_of_not_mem, liftC_pairRouting_p,
            liftC_pairRouting_q, splitIn, joinOut, twoAssoc', regroupOut, connectInj, injOpt, hqq]
        · by_cases hj' : i = q'
          · subst hj'
            simp only [routeComp, routeOpt, routeRight, twoMap, twoAssoc, joinOut, splitIn,
              Function.comp_def]
            simp [connectRoute_of_mem, connectRoute_of_not_mem, liftC_pairRouting_p,
              liftC_pairRouting_q, splitIn, joinOut, twoAssoc', regroupOut, connectInj, injOpt, hj]
          · simp only [routeComp, routeOpt, routeRight, twoMap, twoAssoc, joinOut, splitIn,
              Function.comp_def]
            simp [connectRoute_of_mem, connectRoute_of_not_mem, liftC_pairRouting_p,
              liftC_pairRouting_q, splitIn, joinOut, twoAssoc', regroupOut, connectInj, injOpt, hj, hj']
    · rcases o with ⟨k, y⟩
      by_cases hk : k = x
      · subst hk
        simp only [routeComp, routeOpt, routeRight, twoMap, twoAssoc, joinOut, splitIn,
          Function.comp_def]
        simp [connectRoute_of_mem, connectRoute_of_not_mem, liftC_pairRouting_p,
          liftC_pairRouting_q, splitIn, joinOut, twoAssoc', regroupOut, connectInj, injOpt]
      · simp only [routeComp, routeOpt, routeRight, twoMap, twoAssoc, joinOut, splitIn,
          Function.comp_def]
        simp [connectRoute_of_mem, connectRoute_of_not_mem, liftC_pairRouting_p,
          liftC_pairRouting_q, splitIn, joinOut, twoAssoc', regroupOut, connectInj, injOpt, hk]
  · funext l
    rcases l with ⟨⟨⟨_ | ⟨⟩, z⟩, hz⟩, v⟩
    · rcases z with ⟨⟨_ | ⟨⟩, i⟩, hi⟩ <;> rfl
    · rfl
end Regroup

/-! ## Converters on several interfaces (spec §5.2) -/

section Along

variable {I O J : Type} {X Y : I → Type} {U V : O → Type}

/-- A converter with outside labels `O` and inside labels `J`: port `⟨none, o⟩` is
outside, port `⟨some (), j⟩` is inside. -/
abbrev InsideOutsideSystem (O J : Type) (U V : O → Type) (Xi Yi : J → Type) :=
  InterfaceSystem (Two O J) (twoFam U Yi) (twoFam V Xi)

/-- The labels connected when applying a converter along `ι`. -/
def alongSet (ι : J → I) : Set (Two (Two O J) I)
  | ⟨none, ⟨some (), _⟩⟩ => True
  | ⟨some (), i⟩ => i ∈ Set.range ι
  | _ => False

theorem inside_mem_alongSet (ι : J → I) (j : J) :
    (⟨none, ⟨some (), j⟩⟩ : Two (Two O J) I) ∈ alongSet ι := trivial
theorem image_mem_alongSet (ι : J → I) (j : J) :
    (⟨some (), ι j⟩ : Two (Two O J) I) ∈ alongSet (O := O) ι := ⟨j, rfl⟩
theorem outside_not_mem_alongSet (ι : J → I) (o : O) :
    (⟨none, ⟨none, o⟩⟩ : Two (Two O J) I) ∉ alongSet ι := id
theorem sys_not_mem_alongSet (ι : J → I) {i : I} (h : i ∉ Set.range ι) :
    (⟨some (), i⟩ : Two (Two O J) I) ∉ alongSet (O := O) ι := h
theorem sys_mem_alongSet_iff (ι : J → I) (i : I) :
    (⟨some (), i⟩ : Two (Two O J) I) ∈ alongSet (O := O) ι ↔ i ∈ Set.range ι := Iff.rfl

/-- Queries at inside port `j` go to interface `ι j`; replies at `ι j` go back to `j`. -/
noncomputable def alongRouting (ι : J → I) :
    Routing (alongSet (O := O) ι) (twoFam (twoFam U (Y ∘ ι)) X) (twoFam (twoFam V (X ∘ ι)) Y)
  | ⟨⟨none, ⟨some (), j⟩⟩, _⟩, x => ⟨⟨⟨some (), ι j⟩, image_mem_alongSet ι j⟩, x⟩
  | ⟨⟨some (), _⟩, h⟩, y =>
      ⟨⟨⟨none, ⟨some (), Classical.choose h⟩⟩, inside_mem_alongSet ι _⟩,
        cast (congrArg Y (Classical.choose_spec h).symm) y⟩
  | ⟨⟨none, ⟨none, o⟩⟩, h⟩, _ => absurd h (outside_not_mem_alongSet ι o)

theorem liftC_alongRouting_inside (ι : J → I) (j : J) (h) (x : X (ι j)) :
    liftC (alongRouting (U := U) (V := V) (Y := Y) ι ⟨⟨none, ⟨some (), j⟩⟩, h⟩ x) =
      ⟨⟨some (), ι j⟩, x⟩ := rfl

theorem liftC_alongRouting_image (ι : J → I) (hι : Function.Injective ι) (j : J) (h)
    (y : Y (ι j)) :
    liftC (alongRouting (U := U) (V := V) (X := X) ι ⟨⟨some (), ι j⟩, h⟩ y) =
      ⟨⟨none, ⟨some (), j⟩⟩, y⟩ := by
  have key : ∀ (c : J) (hc : ι c = ι j), c = j →
      (⟨⟨none, ⟨some (), c⟩⟩, cast (congrArg Y hc.symm) y⟩ :
        Σ l : Two (Two O J) I, twoFam (twoFam U (Y ∘ ι)) X l) = ⟨⟨none, ⟨some (), j⟩⟩, y⟩ := by
    rintro c hc rfl; rfl
  exact key _ (Classical.choose_spec h) (hι (Classical.choose_spec h))

/-- Converter application along an injective `ι` (JosMau20 p. 7): inside port `j`
of `α` is connected with interface `ι j` of `R`. -/
noncomputable def attachAlong (ι : J → I) (α : InsideOutsideSystem O J U V (X ∘ ι) (Y ∘ ι)) (R : InterfaceSystem I X Y) :=
  connect (pairI α R) (alongSet ι) (alongRouting ι)

/-- The routing table of `attachAlong ι α R` on `[α, R]`. -/
noncomputable abbrev alongRoute (ι : J → I) :=
  fun y : Two (Σ l, twoFam V (X ∘ ι) l) (Σ i, Y i) =>
    (connectRoute (alongSet (O := O) ι) (alongRouting (U := U) ι) (joinOut y)).map id splitIn

/-- External inputs of `attachAlong ι α R`. -/
abbrev alongInj (ι : J → I) :=
  (splitIn (F := twoFam U (Y ∘ ι)) (G := X)) ∘ connectInj (X := twoFam (twoFam U (Y ∘ ι)) X)
    (alongSet (O := O) ι)

theorem attachAlong_eq (ι : J → I) (α : InsideOutsideSystem O J U V (X ∘ ι) (Y ∘ ι)) (R : InterfaceSystem I X Y) :
    attachAlong ι α R = interconnect (pair α R) (alongRoute ι) (alongInj ι) := by
  unfold attachAlong connect pairI
  rw [interconnect_relabel]

@[simp] theorem connectRoute_along_outside (ι : J → I) (o : O) (v : V o) :
    connectRoute (alongSet (O := O) ι) (alongRouting (U := U) (X := X) (Y := Y) ι)
        ⟨⟨none, ⟨none, o⟩⟩, v⟩ = .inl ⟨⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet ι o⟩, v⟩ :=
  connectRoute_of_not_mem _ (outside_not_mem_alongSet ι o)

@[simp] theorem connectRoute_along_inside (ι : J → I) (j : J) (x : X (ι j)) :
    connectRoute (alongSet (O := O) ι) (alongRouting (U := U) (V := V) (Y := Y) ι)
        ⟨⟨none, ⟨some (), j⟩⟩, x⟩ = .inr ⟨⟨some (), ι j⟩, x⟩ :=
  connectRoute_of_mem _ (inside_mem_alongSet ι j)

end Along

/-! ## Converters along injections with disjoint images commute (A2) -/

section AlongComm

variable {I O J O' J' : Type} {X Y : I → Type} {U V : O → Type} {U' V' : O' → Type}

/-- The interfaces `ι j`, disjoint from the image of `κ`, among the free labels of `β^κ R`. -/
@[reducible] def liftAlong (κ : J' → I) (ι : J → I) (hd : ∀ j, ι j ∉ Set.range κ) :
    J → Free (alongSet (O := O') κ) := fun j => ⟨⟨some (), ι j⟩, hd j⟩

theorem liftAlong_injective (κ : J' → I) {ι : J → I} (hι : Function.Injective ι)
    (hd : ∀ j, ι j ∉ Set.range κ) : Function.Injective (liftAlong (O' := O') κ ι hd) :=
  fun a b e => hι (by simpa [liftAlong] using congrArg (fun z => z.1) e)

theorem sys_mem_alongSet_lift_iff (κ : J' → I) (ι : J → I) (hd : ∀ j, ι j ∉ Set.range κ)
    (i : I) (h) : (⟨some (), ⟨⟨some (), i⟩, h⟩⟩ : Two (Two O J) (Free (alongSet (O := O') κ))) ∈
      alongSet (liftAlong κ ι hd) ↔ i ∈ Set.range ι := by
  simp only [alongSet, Set.mem_range, liftAlong]
  constructor
  · rintro ⟨j, e⟩
    have e' := congrArg (fun z => z.1) e
    simp only [liftAlong] at e'
    exact ⟨j, by simpa using e'⟩
  · rintro ⟨j, rfl⟩; exact ⟨j, rfl⟩

theorem liftC_alongRouting_lift (κ : J' → I) {ι : J → I} (hι : Function.Injective ι)
    (hd : ∀ j, ι j ∉ Set.range κ) (j : J) (h₁ h₂)
    (y : twoFam (twoFam V' (X ∘ κ)) Y ⟨some (), ι j⟩) :
    liftC (alongRouting (O := O) (U := U) (V := V)
        (X := fun l : Free (alongSet (O := O') κ) => twoFam (twoFam U' (Y ∘ κ)) X l.1)
        (Y := fun l : Free (alongSet (O := O') κ) => twoFam (twoFam V' (X ∘ κ)) Y l.1)
        (liftAlong κ ι hd) ⟨⟨some (), ⟨⟨some (), ι j⟩, h₁⟩⟩, h₂⟩ y) =
      ⟨⟨none, ⟨some (), j⟩⟩, y⟩ :=
  liftC_alongRouting_image (O := O) (U := U) (V := V)
    (X := fun l : Free (alongSet (O := O') κ) => twoFam (twoFam U' (Y ∘ κ)) X l.1)
    (Y := fun l : Free (alongSet (O := O') κ) => twoFam (twoFam V' (X ∘ κ)) Y l.1)
    (liftAlong κ ι hd) (liftAlong_injective κ hι hd) j h₂ y

theorem outside_not_mem_alongSet_lift (κ : J' → I) (ι : J → I) (hd : ∀ j, ι j ∉ Set.range κ)
    (o : O') (h) : (⟨some (), ⟨⟨none, ⟨none, o⟩⟩, h⟩⟩ :
      Two (Two O J) (Free (alongSet (O := O') κ))) ∉ alongSet (liftAlong κ ι hd) := by
  rintro ⟨j, e⟩
  have e' := congrArg (fun z => z.1) e
  simp [liftAlong] at e'

theorem inside_not_mem_alongSet_lift (κ : J' → I) (ι : J → I) (hd : ∀ j, ι j ∉ Set.range κ)
    (k : J') (h) : (⟨some (), ⟨⟨none, ⟨some (), k⟩⟩, h⟩⟩ :
      Two (Two O J) (Free (alongSet (O := O') κ))) ∉ alongSet (liftAlong κ ι hd) := by
  rintro ⟨j, e⟩
  have e' := congrArg (fun z => z.1) e
  simp [liftAlong] at e'

variable (ι : J → I) (κ : J' → I) (hι : ∀ j, ι j ∉ Set.range κ) (hκ : ∀ k, κ k ∉ Set.range ι)

/-- Canonical map of inputs, from `α^ι (β^κ R)` to `β^κ (α^ι R)`. -/
def alongCommIn :
    (Σ l : Free (alongSet (O := O) (liftAlong (O' := O') κ ι hι)),
      twoFam (twoFam U (fun j => twoFam (twoFam V' (X ∘ κ)) Y ⟨some (), ι j⟩))
        (fun l : Free (alongSet (O := O') κ) => twoFam (twoFam U' (Y ∘ κ)) X l.1) l.1) →
    Σ l : Free (alongSet (O := O') (liftAlong (O' := O) ι κ hκ)),
      twoFam (twoFam U' (fun k => twoFam (twoFam V (X ∘ ι)) Y ⟨some (), κ k⟩))
        (fun l : Free (alongSet (O := O) ι) => twoFam (twoFam U (Y ∘ ι)) X l.1) l.1
  | ⟨⟨⟨none, ⟨none, o⟩⟩, _⟩, v⟩ =>
      ⟨⟨⟨some (), ⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet ι o⟩⟩,
        outside_not_mem_alongSet_lift ι κ hκ o _⟩, v⟩
  | ⟨⟨⟨none, ⟨some (), j⟩⟩, h⟩, _⟩ => absurd (inside_mem_alongSet _ j) h
  | ⟨⟨⟨some (), ⟨⟨none, ⟨none, o⟩⟩, _⟩⟩, _⟩, v⟩ =>
      ⟨⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet _ o⟩, v⟩
  | ⟨⟨⟨some (), ⟨⟨none, ⟨some (), k⟩⟩, h⟩⟩, _⟩, _⟩ => absurd (inside_mem_alongSet κ k) h
  | ⟨⟨⟨some (), ⟨⟨some (), i⟩, h₁⟩⟩, h₂⟩, x⟩ =>
      ⟨⟨⟨some (), ⟨⟨some (), i⟩, fun h => h₂ ((sys_mem_alongSet_lift_iff κ ι hι i h₁).2 h)⟩⟩,
        fun h => h₁ ((sys_mem_alongSet_lift_iff ι κ hκ i _).1 h)⟩, x⟩

/-- Canonical map of outputs, from `β^κ (α^ι R)` to `α^ι (β^κ R)`. -/
def alongCommOut :
    (Σ l : Free (alongSet (O := O') (liftAlong (O' := O) ι κ hκ)),
      twoFam (twoFam V' (fun k => twoFam (twoFam U (Y ∘ ι)) X ⟨some (), κ k⟩))
        (fun l : Free (alongSet (O := O) ι) => twoFam (twoFam V (X ∘ ι)) Y l.1) l.1) →
    Σ l : Free (alongSet (O := O) (liftAlong (O' := O') κ ι hι)),
      twoFam (twoFam V (fun j => twoFam (twoFam U' (Y ∘ κ)) X ⟨some (), ι j⟩))
        (fun l : Free (alongSet (O := O') κ) => twoFam (twoFam V' (X ∘ κ)) Y l.1) l.1
  | ⟨⟨⟨none, ⟨none, o⟩⟩, _⟩, v⟩ =>
      ⟨⟨⟨some (), ⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet κ o⟩⟩,
        outside_not_mem_alongSet_lift κ ι hι o _⟩, v⟩
  | ⟨⟨⟨none, ⟨some (), k⟩⟩, h⟩, _⟩ => absurd (inside_mem_alongSet _ k) h
  | ⟨⟨⟨some (), ⟨⟨none, ⟨none, o⟩⟩, _⟩⟩, _⟩, v⟩ =>
      ⟨⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet _ o⟩, v⟩
  | ⟨⟨⟨some (), ⟨⟨none, ⟨some (), j⟩⟩, h⟩⟩, _⟩, _⟩ => absurd (inside_mem_alongSet ι j) h
  | ⟨⟨⟨some (), ⟨⟨some (), i⟩, h₁⟩⟩, h₂⟩, x⟩ =>
      ⟨⟨⟨some (), ⟨⟨some (), i⟩, fun h => h₂ ((sys_mem_alongSet_lift_iff ι κ hκ i h₁).2 h)⟩⟩,
        fun h => h₁ ((sys_mem_alongSet_lift_iff κ ι hι i _).1 h)⟩, x⟩

/-- **A2.** Converters applied along injections with disjoint images commute, after
the canonical relabeling (JosMau20 Proposition 1, CR18 Lemma 3.1). -/
theorem attachAlong_comm (hιi : Function.Injective ι) (hκi : Function.Injective κ)
    (α : InsideOutsideSystem O J U V (X ∘ ι) (Y ∘ ι)) (β : InsideOutsideSystem O' J' U' V' (X ∘ κ) (Y ∘ κ))
    (R : InterfaceSystem I X Y) (hαR : Converges (pair α R) (alongRoute ι) (alongInj ι))
    (hβR : Converges (pair β R) (alongRoute κ) (alongInj κ)) :
    attachAlong (liftAlong κ ι hι) α (attachAlong κ β R) =
      relabel (attachAlong (liftAlong ι κ hκ) β (attachAlong ι α R))
        (alongCommIn (U := U) (V := V) (U' := U') (V' := V') (X := X) (Y := Y) ι κ hι hκ)
        (alongCommOut (U := U) (V := V) (U' := U') (V' := V') (X := X) (Y := Y) ι κ hι hκ) := by
  unfold attachAlong connect pairI
  simp only [interconnect_relabel]
  rw [pair_interconnect_right α hβR, interconnect_interconnect, pair_interconnect_right β hαR,
    interconnect_interconnect, pair_left_comm α β R, interconnect_relabel, relabel_interconnect]
  congr 1
  · funext o
    rcases o with ⟨_ | ⟨⟨⟩⟩, o⟩
    · rcases o with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩
      · simp only [alongRoute, alongInj, routeComp, routeRight, twoMap, twoLComm, joinOut, splitIn, Function.comp_def]
        simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, liftC_alongRouting_inside, liftC_alongRouting_image ι hιi, liftC_alongRouting_image κ hκi, liftC_alongRouting_lift κ hιi hι, liftC_alongRouting_lift ι hκi hκ, alongCommOut, splitIn, joinOut, twoLComm, connectInj, twoMap, Set.mem_range, Subtype.ext_iff, liftAlong]
      · simp only [alongRoute, alongInj, routeComp, routeRight, twoMap, twoLComm, joinOut, splitIn, Function.comp_def]
        simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, liftC_alongRouting_inside, liftC_alongRouting_image ι hιi, liftC_alongRouting_image κ hκi, liftC_alongRouting_lift κ hιi hι, liftC_alongRouting_lift ι hκi hκ, alongCommOut, splitIn, joinOut, twoLComm, connectInj, twoMap, Set.mem_range, Subtype.ext_iff, liftAlong]
    · rcases o with ⟨_ | ⟨⟨⟩⟩, o⟩
      · rcases o with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩
        · simp only [alongRoute, alongInj, routeComp, routeRight, twoMap, twoLComm, joinOut, splitIn, Function.comp_def]
          simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, liftC_alongRouting_inside, liftC_alongRouting_image ι hιi, liftC_alongRouting_image κ hκi, liftC_alongRouting_lift κ hιi hι, liftC_alongRouting_lift ι hκi hκ, alongCommOut, splitIn, joinOut, twoLComm, connectInj, twoMap, Set.mem_range, Subtype.ext_iff, liftAlong]
        · simp only [alongRoute, alongInj, routeComp, routeRight, twoMap, twoLComm, joinOut, splitIn, Function.comp_def]
          simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, liftC_alongRouting_inside, liftC_alongRouting_image ι hιi, liftC_alongRouting_image κ hκi, liftC_alongRouting_lift κ hιi hι, liftC_alongRouting_lift ι hκi hκ, alongCommOut, splitIn, joinOut, twoLComm, connectInj, twoMap, Set.mem_range, Subtype.ext_iff, liftAlong]
      · rcases o with ⟨i, y⟩
        by_cases h₁ : i ∈ Set.range ι
        · obtain ⟨j, rfl⟩ := h₁
          simp only [alongRoute, alongInj, routeComp, routeRight, twoMap, twoLComm, joinOut, splitIn, Function.comp_def]
          simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, liftC_alongRouting_inside, liftC_alongRouting_image ι hιi, liftC_alongRouting_image κ hκi, liftC_alongRouting_lift κ hιi hι, liftC_alongRouting_lift ι hκi hκ, alongCommOut, splitIn, joinOut, twoLComm, connectInj, twoMap, Set.mem_range, Subtype.ext_iff, liftAlong, hι j]
        · by_cases h₂ : i ∈ Set.range κ
          · obtain ⟨k, rfl⟩ := h₂
            simp only [alongRoute, alongInj, routeComp, routeRight, twoMap, twoLComm, joinOut, splitIn, Function.comp_def]
            simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, liftC_alongRouting_inside, liftC_alongRouting_image ι hιi, liftC_alongRouting_image κ hκi, liftC_alongRouting_lift κ hιi hι, liftC_alongRouting_lift ι hκi hκ, alongCommOut, splitIn, joinOut, twoLComm, connectInj, twoMap, Set.mem_range, Subtype.ext_iff, liftAlong, hκ k]
          · simp only [Set.mem_range] at h₁ h₂
            simp only [alongRoute, alongInj, routeComp, routeRight, twoMap, twoLComm, joinOut, splitIn, Function.comp_def]
            simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, liftC_alongRouting_inside, liftC_alongRouting_image ι hιi, liftC_alongRouting_image κ hκi, liftC_alongRouting_lift κ hιi hι, liftC_alongRouting_lift ι hκi hκ, alongCommOut, splitIn, joinOut, twoLComm, connectInj, twoMap, Set.mem_range, Subtype.ext_iff, liftAlong, h₁, h₂]
  · funext l
    rcases l with ⟨⟨⟨_ | ⟨⟨⟩⟩, z⟩, hz⟩, v⟩
    · rcases z with ⟨_ | ⟨⟨⟩⟩, o⟩
      · rfl
      · exact absurd (inside_mem_alongSet _ o) hz
    · rcases z with ⟨⟨_ | ⟨⟨⟩⟩, w⟩, hw⟩
      · rcases w with ⟨_ | ⟨⟨⟩⟩, o⟩
        · rfl
        · exact absurd (inside_mem_alongSet κ o) hw
      · rfl

end AlongComm

/-! ## Protocol application (spec §5.5) -/

section Protocol

variable {I O J O' J' : Type} {X Y : I → Type} {U V : O → Type} {U' V' : O' → Type}

/-- The interfaces of two converters together. -/
@[reducible] def jointAlong (ι : J → I) (κ : J' → I) : Two J J' → I
  | ⟨none, j⟩ => ι j
  | ⟨some (), k⟩ => κ k

variable (ι : J → I) (κ : J' → I)

/-- Inputs of the protocol, read at the ports of its two converters. -/
def protoIn : (Σ l : Two (Two O O') (Two J J'), twoFam (twoFam U U') (Y ∘ jointAlong ι κ) l) →
    Σ l : Two (Two O J) (Two O' J'), twoFam (twoFam U (Y ∘ ι)) (twoFam U' (Y ∘ κ)) l
  | ⟨⟨none, ⟨none, o⟩⟩, v⟩ => ⟨⟨none, ⟨none, o⟩⟩, v⟩
  | ⟨⟨none, ⟨some (), o⟩⟩, v⟩ => ⟨⟨some (), ⟨none, o⟩⟩, v⟩
  | ⟨⟨some (), ⟨none, j⟩⟩, y⟩ => ⟨⟨none, ⟨some (), j⟩⟩, y⟩
  | ⟨⟨some (), ⟨some (), k⟩⟩, y⟩ => ⟨⟨some (), ⟨some (), k⟩⟩, y⟩

/-- Outputs at the ports of the two converters, read as outputs of the protocol. -/
def protoOut : (Σ l : Two (Two O J) (Two O' J'), twoFam (twoFam V (X ∘ ι)) (twoFam V' (X ∘ κ)) l) →
    Σ l : Two (Two O O') (Two J J'), twoFam (twoFam V V') (X ∘ jointAlong ι κ) l
  | ⟨⟨none, ⟨none, o⟩⟩, v⟩ => ⟨⟨none, ⟨none, o⟩⟩, v⟩
  | ⟨⟨some (), ⟨none, o⟩⟩, v⟩ => ⟨⟨none, ⟨some (), o⟩⟩, v⟩
  | ⟨⟨none, ⟨some (), j⟩⟩, x⟩ => ⟨⟨some (), ⟨none, j⟩⟩, x⟩
  | ⟨⟨some (), ⟨some (), k⟩⟩, x⟩ => ⟨⟨some (), ⟨some (), k⟩⟩, x⟩

/-- A protocol of two converters, as one converter on the union of their interfaces. -/
noncomputable def protocol (α : InsideOutsideSystem O J U V (X ∘ ι) (Y ∘ ι))
    (β : InsideOutsideSystem O' J' U' V' (X ∘ κ) (Y ∘ κ)) :
    InsideOutsideSystem (Two O O') (Two J J') (twoFam U U') (twoFam V V') (X ∘ jointAlong ι κ)
      (Y ∘ jointAlong ι κ) :=
  relabel (pairI α β) (protoIn ι κ) (protoOut ι κ)

variable {ι κ} (hι : ∀ j, ι j ∉ Set.range κ)

theorem jointAlong_injective (hι : ∀ j, ι j ∉ Set.range κ) (hιi : Function.Injective ι)
    (hκi : Function.Injective κ) :
    Function.Injective (jointAlong ι κ) := by
  rintro ⟨_ | ⟨⟨⟩⟩, a⟩ ⟨_ | ⟨⟨⟩⟩, b⟩ e
  · simp [hιi e]
  · exact absurd ⟨b, e.symm⟩ (hι a)
  · exact absurd ⟨a, e⟩ (hι b)
  · simp [hκi e]

theorem sys_mem_alongSet_joint_iff (i : I) :
    (⟨some (), i⟩ : Two (Two (Two O O') (Two J J')) I) ∈ alongSet (jointAlong ι κ) ↔
      i ∈ Set.range ι ∨ i ∈ Set.range κ := by
  show i ∈ Set.range (jointAlong ι κ) ↔ _
  constructor
  · rintro ⟨⟨_ | ⟨⟨⟩⟩, j⟩, rfl⟩
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr ⟨j, rfl⟩
  · rintro (⟨j, rfl⟩ | ⟨k, rfl⟩)
    · exact ⟨⟨none, j⟩, rfl⟩
    · exact ⟨⟨some (), k⟩, rfl⟩

/-- Canonical map of inputs, from `(α, β)^{ι,κ} R` to `α^ι (β^κ R)`. -/
def protoAppIn :
    (Σ l : Free (alongSet (O := Two O O') (jointAlong ι κ)),
      twoFam (twoFam (twoFam U U') (Y ∘ jointAlong ι κ)) X l.1) →
    Σ l : Free (alongSet (O := O) (liftAlong (O' := O') κ ι hι)),
      twoFam (twoFam U (fun j => twoFam (twoFam V' (X ∘ κ)) Y ⟨some (), ι j⟩))
        (fun l : Free (alongSet (O := O') κ) => twoFam (twoFam U' (Y ∘ κ)) X l.1) l.1
  | ⟨⟨⟨none, ⟨none, ⟨none, o⟩⟩⟩, _⟩, v⟩ => ⟨⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet _ o⟩, v⟩
  | ⟨⟨⟨none, ⟨none, ⟨some (), o⟩⟩⟩, _⟩, v⟩ =>
      ⟨⟨⟨some (), ⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet κ o⟩⟩,
        outside_not_mem_alongSet_lift κ ι hι o _⟩, v⟩
  | ⟨⟨⟨none, ⟨some (), j⟩⟩, h⟩, _⟩ => absurd (inside_mem_alongSet _ j) h
  | ⟨⟨⟨some (), i⟩, h⟩, x⟩ =>
      have h' := fun e => h ((sys_mem_alongSet_joint_iff i).2 e)
      ⟨⟨⟨some (), ⟨⟨some (), i⟩, fun e => h' (Or.inr e)⟩⟩,
        fun e => h' (Or.inl ((sys_mem_alongSet_lift_iff κ ι hι i _).1 e))⟩, x⟩

/-- Canonical map of outputs, from `α^ι (β^κ R)` to `(α, β)^{ι,κ} R`. -/
def protoAppOut :
    (Σ l : Free (alongSet (O := O) (liftAlong (O' := O') κ ι hι)),
      twoFam (twoFam V (fun j => twoFam (twoFam U' (Y ∘ κ)) X ⟨some (), ι j⟩))
        (fun l : Free (alongSet (O := O') κ) => twoFam (twoFam V' (X ∘ κ)) Y l.1) l.1) →
    Σ l : Free (alongSet (O := Two O O') (jointAlong ι κ)),
      twoFam (twoFam (twoFam V V') (X ∘ jointAlong ι κ)) Y l.1
  | ⟨⟨⟨none, ⟨none, o⟩⟩, _⟩, v⟩ => ⟨⟨⟨none, ⟨none, ⟨none, o⟩⟩⟩, outside_not_mem_alongSet _ _⟩, v⟩
  | ⟨⟨⟨none, ⟨some (), j⟩⟩, h⟩, _⟩ => absurd (inside_mem_alongSet _ j) h
  | ⟨⟨⟨some (), ⟨⟨none, ⟨none, o⟩⟩, _⟩⟩, _⟩, v⟩ =>
      ⟨⟨⟨none, ⟨none, ⟨some (), o⟩⟩⟩, outside_not_mem_alongSet _ _⟩, v⟩
  | ⟨⟨⟨some (), ⟨⟨none, ⟨some (), k⟩⟩, h⟩⟩, _⟩, _⟩ => absurd (inside_mem_alongSet κ k) h
  | ⟨⟨⟨some (), ⟨⟨some (), i⟩, h₁⟩⟩, h₂⟩, y⟩ =>
      ⟨⟨⟨some (), i⟩, fun e => by
        rcases (sys_mem_alongSet_joint_iff i).1 e with e | e
        · exact h₂ ((sys_mem_alongSet_lift_iff κ ι hι i h₁).2 e)
        · exact h₁ e⟩, y⟩

/-- **Protocol application.** Applying a protocol of two converters at once is
applying them one after the other, after the canonical relabeling. -/
theorem attachAlong_protocol (hιi : Function.Injective ι) (hκi : Function.Injective κ)
    (α : InsideOutsideSystem O J U V (X ∘ ι) (Y ∘ ι)) (β : InsideOutsideSystem O' J' U' V' (X ∘ κ) (Y ∘ κ))
    (R : InterfaceSystem I X Y) (hβR : Converges (pair β R) (alongRoute κ) (alongInj κ)) :
    attachAlong (jointAlong ι κ) (protocol ι κ α β) R =
      relabel (attachAlong (liftAlong κ ι hι) α (attachAlong κ β R))
        (protoAppIn (U := U) (U' := U') (V' := V') (X := X) (Y := Y) hι)
        (protoAppOut (V := V) (U' := U') (V' := V') (X := X) (Y := Y) hι) := by
  unfold attachAlong protocol connect pairI
  simp only [interconnect_relabel, pair_relabel_left]
  rw [pair_interconnect_right α hβR, interconnect_interconnect, pair_assoc' α β R,
    interconnect_relabel, relabel_interconnect]
  congr 1
  · funext o
    rcases o with ⟨_ | ⟨⟨⟩⟩, o⟩
    · rcases o with ⟨_ | ⟨⟨⟩⟩, ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩⟩
      · simp only [alongRoute, alongInj, routeComp, routeRight, twoMap, twoAssoc, joinOut, splitIn, Function.comp_def]
        simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, sys_mem_alongSet_joint_iff, liftC_alongRouting_inside, liftC_alongRouting_image κ hκi, liftC_alongRouting_image (jointAlong ι κ) (jointAlong_injective hι hιi hκi), liftC_alongRouting_lift κ hιi hι, protoIn, protoOut, protoAppOut, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, Set.mem_range, Subtype.ext_iff, liftAlong]
      · simp only [alongRoute, alongInj, routeComp, routeRight, twoMap, twoAssoc, joinOut, splitIn, Function.comp_def]
        simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, sys_mem_alongSet_joint_iff, liftC_alongRouting_inside, liftC_alongRouting_image κ hκi, liftC_alongRouting_image (jointAlong ι κ) (jointAlong_injective hι hιi hκi), liftC_alongRouting_lift κ hιi hι, protoIn, protoOut, protoAppOut, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, Set.mem_range, Subtype.ext_iff, liftAlong]
      · simp only [alongRoute, alongInj, routeComp, routeRight, twoMap, twoAssoc, joinOut, splitIn, Function.comp_def]
        simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, sys_mem_alongSet_joint_iff, liftC_alongRouting_inside, liftC_alongRouting_image κ hκi, liftC_alongRouting_image (jointAlong ι κ) (jointAlong_injective hι hιi hκi), liftC_alongRouting_lift κ hιi hι, protoIn, protoOut, protoAppOut, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, Set.mem_range, Subtype.ext_iff, liftAlong]
      · simp only [alongRoute, alongInj, routeComp, routeRight, twoMap, twoAssoc, joinOut, splitIn, Function.comp_def]
        simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, sys_mem_alongSet_joint_iff, liftC_alongRouting_inside, liftC_alongRouting_image κ hκi, liftC_alongRouting_image (jointAlong ι κ) (jointAlong_injective hι hιi hκi), liftC_alongRouting_lift κ hιi hι, protoIn, protoOut, protoAppOut, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, Set.mem_range, Subtype.ext_iff, liftAlong]
    · rcases o with ⟨i, y⟩
      by_cases h₁ : i ∈ Set.range ι
      · obtain ⟨j, rfl⟩ := h₁
        have m₁ : (⟨some (), ι j⟩ : Two (Two (Two O O') (Two J J')) I) ∈
            alongSet (jointAlong ι κ) := image_mem_alongSet (jointAlong ι κ) ⟨none, j⟩
        have m₂ : (⟨some (), ι j⟩ : Two (Two O' J') I) ∉ alongSet κ := sys_not_mem_alongSet κ (hι j)
        simp only [alongRoute, alongInj, routeComp, routeRight, twoMap, twoAssoc, joinOut, splitIn, Function.comp_def]
        simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, liftC_alongRouting_inside, liftC_alongRouting_image κ hκi, liftC_alongRouting_image (jointAlong ι κ) (jointAlong_injective hι hιi hκi), liftC_alongRouting_lift κ hιi hι, protoIn, protoOut, protoAppOut, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, m₁, m₂, liftC_alongRouting_image (jointAlong ι κ) (jointAlong_injective hι hιi hκi) ⟨none, j⟩]
      · by_cases h₂ : i ∈ Set.range κ
        · obtain ⟨k, rfl⟩ := h₂
          have m₁ : (⟨some (), κ k⟩ : Two (Two (Two O O') (Two J J')) I) ∈
              alongSet (jointAlong ι κ) := image_mem_alongSet (jointAlong ι κ) ⟨some (), k⟩
          simp only [alongRoute, alongInj, routeComp, routeRight, twoMap, twoAssoc, joinOut, splitIn, Function.comp_def]
          simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, liftC_alongRouting_inside, liftC_alongRouting_image κ hκi, liftC_alongRouting_image (jointAlong ι κ) (jointAlong_injective hι hιi hκi), liftC_alongRouting_lift κ hιi hι, protoIn, protoOut, protoAppOut, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, m₁, liftC_alongRouting_image (jointAlong ι κ) (jointAlong_injective hι hιi hκi) ⟨some (), k⟩]
        · have m₁ : (⟨some (), i⟩ : Two (Two (Two O O') (Two J J')) I) ∉
              alongSet (jointAlong ι κ) := fun e => by
            rcases (sys_mem_alongSet_joint_iff i).1 e with e | e
            · exact h₁ e
            · exact h₂ e
          have m₂ : (⟨some (), i⟩ : Two (Two O' J') I) ∉ alongSet κ := sys_not_mem_alongSet κ h₂
          have m₃ : ∀ h, (⟨some (), ⟨⟨some (), i⟩, h⟩⟩ : Two (Two O J) (Free (alongSet (O := O') κ))) ∉
              alongSet (liftAlong κ ι hι) := fun h e => h₁ ((sys_mem_alongSet_lift_iff κ ι hι i h).1 e)
          simp only [alongRoute, alongInj, routeComp, routeRight, twoMap, twoAssoc, joinOut, splitIn, Function.comp_def]
          simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, liftC_alongRouting_inside, liftC_alongRouting_image κ hκi, liftC_alongRouting_image (jointAlong ι κ) (jointAlong_injective hι hιi hκi), liftC_alongRouting_lift κ hιi hι, protoIn, protoOut, protoAppOut, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, m₁, m₂, m₃]
  · funext l
    rcases l with ⟨⟨⟨_ | ⟨⟨⟩⟩, z⟩, hz⟩, v⟩
    · rcases z with ⟨_ | ⟨⟨⟩⟩, w⟩
      · rcases w with ⟨_ | ⟨⟨⟩⟩, o⟩ <;> rfl
      · exact absurd (inside_mem_alongSet _ w) hz
    · rfl

end Protocol

/-! ## Environments and distinguishers (spec §5.6) -/

section DDD

/-- Labels of an environment for systems with labels `I`: the trigger, the
decision, and one port facing each interface of the system. -/
inductive DPort (I : Type)
  | start
  | dec
  | res (i : I)

variable {I J : Type} {X Y : I → Type}

/-- Input family of an environment: a trigger, nothing at `dec`, replies at `res i`. -/
@[reducible] def dIn (Y : I → Type) : DPort I → Type
  | .start => Unit
  | .dec => Empty
  | .res i => Y i

/-- Output family of an environment: nothing at `start`, a bit at `dec`, queries at `res i`. -/
@[reducible] def dOut (X : I → Type) : DPort I → Type
  | .start => Empty
  | .dec => Bool
  | .res i => X i

/-- The history-function type with trigger, resource and decision interfaces.
`IsDDD` supplies the finite interaction discipline. Decision production also
needs responsiveness along the tested interaction: `Domain.DecisionCompatible`
states it for the resources on a domain, and
`Domain.DecisionCompatible.producesDecision` proves the decision. This
abbreviation alone imposes none of those properties. Environments without a
decision interface use `DDE`. -/
abbrev DDD (I : Type) (X Y : I → Type) := InterfaceSystem (DPort I) (dIn Y) (dOut X)

/-- The labels connected when closing: every `res` port and every interface. -/
def closeSet (I : Type) : Set (Two (DPort I) I)
  | ⟨none, .res _⟩ => True
  | ⟨some (), _⟩ => True
  | _ => False

theorem res_mem_closeSet (i : I) : (⟨none, .res i⟩ : Two (DPort I) I) ∈ closeSet I := trivial
theorem sys_mem_closeSet (i : I) : (⟨some (), i⟩ : Two (DPort I) I) ∈ closeSet I := trivial
theorem start_not_mem_closeSet : (⟨none, .start⟩ : Two (DPort I) I) ∉ closeSet I := id
theorem dec_not_mem_closeSet : (⟨none, .dec⟩ : Two (DPort I) I) ∉ closeSet I := id

/-- Queries at `res i` go to interface `i`; replies at `i` go back to `res i`. -/
def closeRouting : Routing (closeSet I) (twoFam (dIn Y) X) (twoFam (dOut X) Y)
  | ⟨⟨none, .res i⟩, _⟩, x => ⟨⟨⟨some (), i⟩, sys_mem_closeSet i⟩, x⟩
  | ⟨⟨some (), i⟩, _⟩, y => ⟨⟨⟨none, .res i⟩, res_mem_closeSet i⟩, y⟩
  | ⟨⟨none, .start⟩, h⟩, _ => absurd h start_not_mem_closeSet
  | ⟨⟨none, .dec⟩, h⟩, _ => absurd h dec_not_mem_closeSet

/-- Closing a system with an environment, `D ▹ R`. -/
noncomputable def close (D : DDD I X Y) (R : InterfaceSystem I X Y) :=
  connect (pairI D R) (closeSet I) closeRouting

theorem liftC_closeRouting_res (i : I) (h) (x : X i) :
    liftC (closeRouting (X := X) (Y := Y) ⟨⟨none, .res i⟩, h⟩ x) = ⟨⟨some (), i⟩, x⟩ := rfl

theorem liftC_closeRouting_sys (i : I) (h) (y : Y i) :
    liftC (closeRouting (X := X) (Y := Y) ⟨⟨some (), i⟩, h⟩ y) = ⟨⟨none, .res i⟩, y⟩ := rfl

end DDD

/-! ## The environment predicate (spec §5.6) -/

section EnvironmentPredicate

variable {L : Type} {F G : DPort L → Type}

/-- The label at which `s` replies after `h`, if it replies. -/
noncomputable def replyLabel {K : Type} {F G : K → Type} (s : InterfaceSystem K F G) (h : List (Σ l, F l)) :
    Option K :=
  if hd : (s h).Dom then some ((s h).get hd).1 else none

theorem replyLabel_of_mem {K : Type} {F G : K → Type} (s : InterfaceSystem K F G) {h} {y : Σ l, G l}
    (hy : y ∈ s h) : replyLabel s h = some y.1 := by
  have hd : (s h).Dom := Part.dom_iff_mem.mpr ⟨y, hy⟩
  simp [replyLabel, hd, Part.get_eq_of_mem hy hd]

theorem replyLabel_trim {K : Type} {F G : K → Type} (s : InterfaceSystem K F G) {h} (hr : Reach s h) :
    replyLabel (trim s) h = replyLabel s h := by
  simp [replyLabel, trim, hr]

/-- Finite decision-observer discipline: reactive, started once by the trigger,
a query at `res i` is followed by the reply at `res i`, and nothing follows a
decision. This predicate does not assert responsiveness; the compatible
decision-observer class requires it separately before proving a final bit. -/
def IsDDD (D : InterfaceSystem (DPort L) F G) : Prop :=
  SilentAtEmpty D ∧ (∃ n, Finite n D) ∧
  (∀ h z, Reach D (h ++ [z]) → (h = [] ↔ z.1 = .start)) ∧
  (∀ h z i, Reach D (h ++ [z]) → replyLabel D h = some (.res i) → z.1 = .res i) ∧
  (∀ h z, Reach D (h ++ [z]) → replyLabel D h ≠ some .dec)

end EnvironmentPredicate

/-! ## Partial closing and law E2 -/

section PartialClose

variable {I J : Type} {X₁ Y₁ : I → Type} {X₂ Y₂ : J → Type}

/-- The labels connected by `D[·, S]`: `D`'s ports facing `S`, and `S`'s interfaces. -/
def pcSet (I J : Type) : Set (Two (DPort (Two I J)) J)
  | ⟨none, .res ⟨some (), _⟩⟩ => True
  | ⟨some (), _⟩ => True
  | _ => False

theorem pc_res_mem (k : J) : (⟨none, .res ⟨some (), k⟩⟩ : Two (DPort (Two I J)) J) ∈ pcSet I J :=
  trivial
theorem pc_sys_mem (k : J) : (⟨some (), k⟩ : Two (DPort (Two I J)) J) ∈ pcSet I J := trivial
theorem pc_res_none_not_mem (i : I) :
    (⟨none, .res ⟨none, i⟩⟩ : Two (DPort (Two I J)) J) ∉ pcSet I J := id
theorem pc_start_not_mem : (⟨none, .start⟩ : Two (DPort (Two I J)) J) ∉ pcSet I J := id
theorem pc_dec_not_mem : (⟨none, .dec⟩ : Two (DPort (Two I J)) J) ∉ pcSet I J := id

/-- Queries of `D` towards `S` go to `S`, and back. -/
def pcRouting : Routing (pcSet I J) (twoFam (dIn (twoFam Y₁ Y₂)) X₂) (twoFam (dOut (twoFam X₁ X₂)) Y₂)
  | ⟨⟨none, .res ⟨some (), k⟩⟩, _⟩, x => ⟨⟨⟨some (), k⟩, pc_sys_mem k⟩, x⟩
  | ⟨⟨some (), k⟩, _⟩, y => ⟨⟨⟨none, .res ⟨some (), k⟩⟩, pc_res_mem k⟩, y⟩
  | ⟨⟨none, .res ⟨none, _⟩⟩, h⟩, _ => absurd h id
  | ⟨⟨none, .start⟩, h⟩, _ => absurd h id
  | ⟨⟨none, .dec⟩, h⟩, _ => absurd h id

/-- Inputs of the partially closed environment, read at the free labels. -/
def pcIn : (Σ p : DPort I, dIn Y₁ p) →
    Σ l : Free (pcSet I J), twoFam (dIn (twoFam Y₁ Y₂)) X₂ l.1
  | ⟨.start, u⟩ => ⟨⟨⟨none, .start⟩, id⟩, u⟩
  | ⟨.dec, e⟩ => e.elim
  | ⟨.res i, y⟩ => ⟨⟨⟨none, .res ⟨none, i⟩⟩, id⟩, y⟩

/-- Outputs at the free labels, read as outputs of the partially closed environment. -/
def pcOut : (Σ l : Free (pcSet I J), twoFam (dOut (twoFam X₁ X₂)) Y₂ l.1) →
    Σ p : DPort I, dOut X₁ p
  | ⟨⟨⟨none, .start⟩, _⟩, e⟩ => ⟨.start, e⟩
  | ⟨⟨⟨none, .dec⟩, _⟩, b⟩ => ⟨.dec, b⟩
  | ⟨⟨⟨none, .res ⟨none, i⟩⟩, _⟩, x⟩ => ⟨.res i, x⟩
  | ⟨⟨⟨none, .res ⟨some (), k⟩⟩, h⟩, _⟩ => absurd (pc_res_mem k) h
  | ⟨⟨⟨some (), k⟩, h⟩, _⟩ => absurd (pc_sys_mem k) h

/-- `D[·, S]`: the environment `D` for `[R, S]` with `S` absorbed. -/
noncomputable def partialClose (D : DDD (Two I J) (twoFam X₁ X₂) (twoFam Y₁ Y₂))
    (S : InterfaceSystem J X₂ Y₂) : DDD I X₁ Y₁ :=
  relabel (connect (pairI D S) (pcSet I J) pcRouting) pcIn pcOut

theorem liftC_pcRouting_res (k : J) (h) (x : X₂ k) :
    liftC (pcRouting (X₁ := X₁) (Y₁ := Y₁) (Y₂ := Y₂) ⟨⟨none, .res ⟨some (), k⟩⟩, h⟩ x) =
      ⟨⟨some (), k⟩, x⟩ := rfl

theorem liftC_pcRouting_sys (k : J) (h) (y : Y₂ k) :
    liftC (pcRouting (X₁ := X₁) (Y₁ := Y₁) (X₂ := X₂) ⟨⟨some (), k⟩, h⟩ y) =
      ⟨⟨none, .res ⟨some (), k⟩⟩, y⟩ := rfl

/-- Canonical map of inputs of the two closed systems (only the trigger). -/
def e2In : (Σ l : Free (closeSet (Two I J)), twoFam (dIn (twoFam Y₁ Y₂)) (twoFam X₁ X₂) l.1) →
    Σ l : Free (closeSet I), twoFam (dIn Y₁) X₁ l.1
  | ⟨⟨⟨none, .start⟩, _⟩, u⟩ => ⟨⟨⟨none, .start⟩, id⟩, u⟩
  | ⟨⟨⟨none, .dec⟩, _⟩, e⟩ => e.elim
  | ⟨⟨⟨none, .res i⟩, h⟩, _⟩ => absurd (res_mem_closeSet i) h
  | ⟨⟨⟨some (), i⟩, h⟩, _⟩ => absurd (sys_mem_closeSet i) h

/-- Canonical map of outputs of the two closed systems (only the decision). -/
def e2Out : (Σ l : Free (closeSet I), twoFam (dOut X₁) Y₁ l.1) →
    Σ l : Free (closeSet (Two I J)), twoFam (dOut (twoFam X₁ X₂)) (twoFam Y₁ Y₂) l.1
  | ⟨⟨⟨none, .start⟩, _⟩, e⟩ => e.elim
  | ⟨⟨⟨none, .dec⟩, _⟩, b⟩ => ⟨⟨⟨none, .dec⟩, id⟩, b⟩
  | ⟨⟨⟨none, .res i⟩, h⟩, _⟩ => absurd (res_mem_closeSet i) h
  | ⟨⟨⟨some (), i⟩, h⟩, _⟩ => absurd (sys_mem_closeSet i) h

/-- Every internal cycle of `D[·, S]` passes through `D`: a reply of `S` goes back to `D`. -/
theorem pc_cyclesThrough :
    CyclesThrough (fun _ => True) (fun y : Two (Σ p, dOut (twoFam X₁ X₂) p) (Σ k, Y₂ k) =>
      Sum.map id splitIn (connectRoute (pcSet I J)
        (pcRouting (X₁ := X₁) (Y₁ := Y₁) (X₂ := X₂) (Y₂ := Y₂)) (joinOut y))) := by
  refine ⟨fun _ h => absurd trivial h, fun y _ => ?_, fun y => ?_⟩
  · rcases y with ⟨_ | _ | ⟨_ | ⟨⟨⟩⟩, i⟩, v⟩
    · exact v.elim
    all_goals simp [connectRoute_of_mem, connectRoute_of_not_mem, pc_res_mem, pc_sys_mem,
      pc_res_none_not_mem, pc_start_not_mem, pc_dec_not_mem, liftC_pcRouting_res,
      liftC_pcRouting_sys, joinOut, splitIn]
  · rcases y with ⟨k, y⟩
    simp [connectRoute_of_mem, pc_sys_mem, liftC_pcRouting_sys, joinOut, splitIn]

/-- **E2.** Testing `[R, S]` with `D` is testing `R` with `D[·, S]`. Only `D` must
terminate: every internal cycle passes through `D`, so `S` is arbitrary. -/
theorem close_pair (D : DDD (Two I J) (twoFam X₁ X₂) (twoFam Y₁ Y₂)) (R : InterfaceSystem I X₁ Y₁)
    (S : InterfaceSystem J X₂ Y₂) (hD : Terminating D) :
    close D (pairI R S) = relabel (close (partialClose D S) R) e2In e2Out := by
  unfold close partialClose connect pairI
  simp only [interconnect_relabel, pair_relabel_left, pair_relabel_right]
  rw [pair_interconnect_left (converges_pair_of_terminating pc_cyclesThrough hD), interconnect_interconnect, pair_assoc D S R, pair_swap R S,
    pair_relabel_right, relabel_relabel, interconnect_relabel, relabel_interconnect]
  congr 1
  · funext o
    rcases o with ⟨_ | ⟨⟨⟩⟩, o⟩
    · rcases o with ⟨_ | _ | ⟨_ | ⟨⟨⟩⟩, i⟩, v⟩
      · exact v.elim
      · simp only [routeComp, routeOpt, twoMap, twoAssoc, twoSwap, joinOut, splitIn, Function.comp_def]
        simp [connectRoute_of_mem, connectRoute_of_not_mem, res_mem_closeSet, sys_mem_closeSet, start_not_mem_closeSet, dec_not_mem_closeSet, pc_res_mem, pc_sys_mem, pc_res_none_not_mem, pc_start_not_mem, pc_dec_not_mem, liftC_closeRouting_res, liftC_closeRouting_sys, liftC_pcRouting_res, liftC_pcRouting_sys, pcIn, pcOut, e2Out, splitIn, joinOut, connectInj, injOpt, twoMap, twoAssoc', twoSwap]
      · simp only [routeComp, routeOpt, twoMap, twoAssoc, twoSwap, joinOut, splitIn, Function.comp_def]
        simp [connectRoute_of_mem, connectRoute_of_not_mem, res_mem_closeSet, sys_mem_closeSet, start_not_mem_closeSet, dec_not_mem_closeSet, pc_res_mem, pc_sys_mem, pc_res_none_not_mem, pc_start_not_mem, pc_dec_not_mem, liftC_closeRouting_res, liftC_closeRouting_sys, liftC_pcRouting_res, liftC_pcRouting_sys, pcIn, pcOut, e2Out, splitIn, joinOut, connectInj, injOpt, twoMap, twoAssoc', twoSwap]
      · simp only [routeComp, routeOpt, twoMap, twoAssoc, twoSwap, joinOut, splitIn, Function.comp_def]
        simp [connectRoute_of_mem, connectRoute_of_not_mem, res_mem_closeSet, sys_mem_closeSet, start_not_mem_closeSet, dec_not_mem_closeSet, pc_res_mem, pc_sys_mem, pc_res_none_not_mem, pc_start_not_mem, pc_dec_not_mem, liftC_closeRouting_res, liftC_closeRouting_sys, liftC_pcRouting_res, liftC_pcRouting_sys, pcIn, pcOut, e2Out, splitIn, joinOut, connectInj, injOpt, twoMap, twoAssoc', twoSwap]
    · rcases o with ⟨_ | ⟨⟨⟩⟩, ⟨i, y⟩⟩
      · simp only [routeComp, routeOpt, twoMap, twoAssoc, twoSwap, joinOut, splitIn, Function.comp_def]
        simp [connectRoute_of_mem, connectRoute_of_not_mem, res_mem_closeSet, sys_mem_closeSet, start_not_mem_closeSet, dec_not_mem_closeSet, pc_res_mem, pc_sys_mem, pc_res_none_not_mem, pc_start_not_mem, pc_dec_not_mem, liftC_closeRouting_res, liftC_closeRouting_sys, liftC_pcRouting_res, liftC_pcRouting_sys, pcIn, pcOut, e2Out, splitIn, joinOut, connectInj, injOpt, twoMap, twoAssoc', twoSwap]
      · simp only [routeComp, routeOpt, twoMap, twoAssoc, twoSwap, joinOut, splitIn, Function.comp_def]
        simp [connectRoute_of_mem, connectRoute_of_not_mem, res_mem_closeSet, sys_mem_closeSet, start_not_mem_closeSet, dec_not_mem_closeSet, pc_res_mem, pc_sys_mem, pc_res_none_not_mem, pc_start_not_mem, pc_dec_not_mem, liftC_closeRouting_res, liftC_closeRouting_sys, liftC_pcRouting_res, liftC_pcRouting_sys, pcIn, pcOut, e2Out, splitIn, joinOut, connectInj, injOpt, twoMap, twoAssoc', twoSwap]
  · funext l
    rcases l with ⟨⟨⟨_ | ⟨⟩, z⟩, hz⟩, v⟩
    · rcases z with _ | _ | i
      · rfl
      · exact v.elim
      · exact absurd (res_mem_closeSet i) hz
    · exact absurd (sys_mem_closeSet z) hz

end PartialClose

/-! ## Partial closing preserves the environment predicate -/

section PartialCloseClosure

variable {I J : Type} {X₁ Y₁ : I → Type} {X₂ Y₂ : J → Type}

/-- The routing table of `D[·, S]` on `[D, S]`. -/
def pcRoute : Two (Σ p, dOut (twoFam X₁ X₂) p) (Σ k, Y₂ k) →
    (Σ p : DPort I, dOut X₁ p) ⊕ Two (Σ p, dIn (twoFam Y₁ Y₂) p) (Σ k, X₂ k)
  | ⟨none, ⟨.start, e⟩⟩ => e.elim
  | ⟨none, ⟨.dec, b⟩⟩ => .inl ⟨.dec, b⟩
  | ⟨none, ⟨.res ⟨none, i⟩, x⟩⟩ => .inl ⟨.res i, x⟩
  | ⟨none, ⟨.res ⟨some (), k⟩, x⟩⟩ => .inr ⟨some (), ⟨k, x⟩⟩
  | ⟨some (), ⟨k, y⟩⟩ => .inr ⟨none, ⟨.res ⟨some (), k⟩, y⟩⟩

/-- External inputs of `D[·, S]` go to `D`. -/
def pcInj : (Σ p : DPort I, dIn Y₁ p) → Two (Σ p, dIn (twoFam Y₁ Y₂) p) (Σ k, X₂ k)
  | ⟨.start, u⟩ => ⟨none, ⟨.start, u⟩⟩
  | ⟨.dec, e⟩ => e.elim
  | ⟨.res i, y⟩ => ⟨none, ⟨.res ⟨none, i⟩, y⟩⟩

theorem partialClose_eq (D : DDD (Two I J) (twoFam X₁ X₂) (twoFam Y₁ Y₂)) (S : InterfaceSystem J X₂ Y₂) :
    partialClose D S = interconnect (pair D S) pcRoute pcInj := by
  unfold partialClose connect pairI
  rw [relabel_interconnect, interconnect_relabel]
  congr 1
  · funext o
    rcases o with ⟨_ | ⟨⟨⟩⟩, o⟩
    · rcases o with ⟨_ | _ | ⟨_ | ⟨⟨⟩⟩, i⟩, v⟩
      · exact v.elim
      all_goals simp [connectRoute_of_mem, connectRoute_of_not_mem, pc_res_mem, pc_sys_mem,
        pc_res_none_not_mem, pc_start_not_mem, pc_dec_not_mem, liftC_pcRouting_res,
        liftC_pcRouting_sys, joinOut, splitIn, pcOut, pcRoute]
    · rcases o with ⟨k, y⟩
      simp [connectRoute_of_mem, pc_sys_mem, liftC_pcRouting_sys, joinOut, splitIn, pcRoute]
  · funext a
    rcases a with ⟨_ | _ | i, v⟩
    · rfl
    · exact v.elim
    · rfl

/-- The label of the environment `D` that the label of `D[·, S]` stands for. -/
def liftLab : DPort I → DPort (Two I J)
  | .start => .start
  | .dec => .dec
  | .res i => .res ⟨none, i⟩

variable {D : DDD (Two I J) (twoFam X₁ X₂) (twoFam Y₁ Y₂)} {S : InterfaceSystem J X₂ Y₂}

theorem pc_exchange {G o G'} (l : Exchange (pair D S) pcRoute G o G') :
    ∀ out, o = some out →
      ((∃ G₁ x, G = G₁ ++ [⟨none, x⟩] ∧ Reach D (restrict none G₁)) ∨
        (∃ G₁ x, G = G₁ ++ [⟨some (), x⟩] ∧ Reach D (restrict none G₁) ∧
          restrict none G₁ ≠ [])) →
      Reach D (restrict none G') ∧
        replyLabel D (restrict none G') = some (liftLab (J := J) out.1) ∧ restrict none G' ≠ [] := by
  induction l with
  | silent => intro out e; cases e
  | out G y b hy hr =>
    intro out e hm
    obtain rfl : b = out := Option.some_inj.mp e
    rcases hm with ⟨G₁, x, rfl, hDr⟩ | ⟨G₁, x, rfl, hDr, hne⟩
    · rw [pair_left] at hy
      obtain ⟨y', hy', rfl⟩ := Part.mem_map_iff _ |>.mp hy
      have hr' := reach_snoc_iff.mpr ⟨hDr, Part.dom_iff_mem.mpr ⟨_, hy'⟩⟩
      have hl := replyLabel_of_mem D hy'
      rcases y' with ⟨_ | _ | ⟨_ | ⟨⟨⟩⟩, i⟩, v⟩
      · exact v.elim
      · simp only [pcRoute, Sum.inl.injEq] at hr
        subst hr
        exact ⟨by simpa using hr', by simpa [liftLab] using hl, by simp⟩
      · simp only [pcRoute, Sum.inl.injEq] at hr
        subst hr
        exact ⟨by simpa using hr', by simpa [liftLab] using hl, by simp⟩
      · exact absurd hr (by simp [pcRoute])
    · rw [pair_right] at hy
      obtain ⟨y', -, rfl⟩ := Part.mem_map_iff _ |>.mp hy
      exact absurd hr (by simp [pcRoute])
  | feed G y x' o G'' hy hr _ ih =>
    intro out e hm
    rcases hm with ⟨G₁, x, rfl, hDr⟩ | ⟨G₁, x, rfl, hDr, hne⟩
    · rw [pair_left] at hy
      obtain ⟨y', hy', rfl⟩ := Part.mem_map_iff _ |>.mp hy
      rcases y' with ⟨_ | _ | ⟨_ | ⟨⟨⟩⟩, i⟩, v⟩
      · exact v.elim
      · exact absurd hr (by simp [pcRoute])
      · exact absurd hr (by simp [pcRoute])
      · simp only [pcRoute, Sum.inr.injEq] at hr
        subst hr
        refine ih out e (Or.inr ⟨_, _, rfl, ?_, by simp⟩)
        simpa using reach_snoc_iff.mpr ⟨hDr, Part.dom_iff_mem.mpr ⟨_, hy'⟩⟩
    · rw [pair_right] at hy
      obtain ⟨y', -, rfl⟩ := Part.mem_map_iff _ |>.mp hy
      simp only [pcRoute, Sum.inr.injEq] at hr
      subst hr
      exact ih out e (Or.inl ⟨_, _, rfl, by simpa using hDr⟩)

variable (D S) in
/-- The invariant of `D[·, S]`: `D`'s part of the internal history is reachable, empty
exactly when nothing happened, and its last reply is the composite's last reply. -/
def PcInv (u : List (Σ p : DPort I, dIn Y₁ p))
    (H : List (Two (Σ p, dIn (twoFam Y₁ Y₂) p) (Σ k, X₂ k))) : Prop :=
  (∃ o, Induces (pair D S) pcRoute pcInj u o H) ∧ Reach D (restrict none H) ∧
  (u = [] ↔ restrict none H = []) ∧
  ∀ l, replyLabel (interconnect (pair D S) pcRoute pcInj) u = some l →
    replyLabel D (restrict none H) = some (liftLab (J := J) l)

theorem pc_step (hD : IsDDD D) {u H} (inv : PcInv D S u H) {z : Σ p : DPort I, dIn Y₁ p}
    (hr : Reach (interconnect (pair D S) pcRoute pcInj) (u ++ [z])) :
    (u = [] ↔ z.1 = .start) ∧
      (∀ i, replyLabel (interconnect (pair D S) pcRoute pcInj) u = some (.res i) → z.1 = .res i) ∧
      replyLabel (interconnect (pair D S) pcRoute pcInj) u ≠ some .dec ∧
      ∃ H', PcInv D S (u ++ [z]) H' := by
  obtain ⟨⟨o, rH⟩, hDr, hemp, hlab⟩ := inv
  obtain ⟨-, hd⟩ := reach_snoc_iff.mp hr
  have hout := Part.get_mem hd
  obtain ⟨H', r'⟩ := mem_interconnect.mp hout
  obtain ⟨_, H₀, r₀, l⟩ := induces_snoc_iff.mp r'
  obtain ⟨-, e⟩ := rH.det r₀
  subst e
  have hstart := exchange_start_dom l _ rfl
  -- the query that reaches `D`
  obtain ⟨x', hx', hzx⟩ : ∃ x', pcInj z = ⟨none, x'⟩ ∧ (x'.1 = liftLab (J := J) z.1) := by
    rcases z with ⟨_ | _ | i, v⟩
    · exact ⟨_, rfl, rfl⟩
    · exact v.elim
    · exact ⟨_, rfl, rfl⟩
  rw [hx', pair_left] at hstart
  have hDr' : Reach D (restrict none H ++ [x']) := reach_snoc_iff.mpr ⟨hDr, by simpa using hstart⟩
  have hliftS : ∀ p : DPort I, liftLab (J := J) p = .start ↔ p = .start := by
    intro p; cases p <;> simp [liftLab]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hemp, (hD.2.2.1 _ _ hDr'), hzx, hliftS]
  · intro i hi
    have := hD.2.2.2.1 _ _ _ hDr' (hlab _ hi)
    rw [hzx] at this
    rcases z with ⟨_ | _ | i', v⟩ <;> simp_all [liftLab]
  · intro hi
    exact hD.2.2.2.2 _ _ hDr' (hlab _ hi)
  · rw [hx'] at l
    obtain ⟨h1, h2, h3⟩ := pc_exchange l _ rfl (Or.inl ⟨_, _, rfl, hDr⟩)
    refine ⟨H', ⟨_, r'⟩, h1, ⟨fun e => absurd e (by simp), fun e => absurd e h3⟩, fun lab hl => ?_⟩
    rw [replyLabel_of_mem _ hout] at hl
    cases hl
    exact h2

theorem length_le_restrict_none {A B Xa Xb Y : Type} {s : System (Two Xa Xb) Y}
    {route : Y → B ⊕ Two Xa Xb} {inj : A → Two Xa Xb} (hinj : ∀ a, ∃ x, inj a = ⟨none, x⟩)
    {u o H} (r : Induces s route inj u o H) : u.length ≤ (restrict none H).length := by
  induction r with
  | nil => simp
  | snoc u a o₀ H₀ o H' _ l ih =>
    obtain ⟨e, rfl⟩ := l.extends
    obtain ⟨x, hx⟩ := hinj a
    rw [hx]
    simp only [List.length_append, List.length_singleton, restrict_append]
    rw [restrict_two_none_cons_none]
    simp only [restrict_nil, List.length_cons, List.length_nil]
    omega

/-- **`D[·, S]` is an environment** (spec §5.6): the reachable part of an environment
with any system absorbed is an environment. The query bound is the bound of `D`. -/
theorem partialClose_isDDD (hD : IsDDD D) : IsDDD (trim (partialClose D S)) := by
  rw [partialClose_eq]
  set γ := interconnect (pair D S) pcRoute pcInj
  have inv : ∀ u, Reach γ u → ∃ H, PcInv D S u H := by
    intro u
    induction u using List.reverseRecOn with
    | nil =>
      intro _
      refine ⟨[], ⟨none, Induces.nil⟩, reach_nil D, by simp, fun l hl => ?_⟩
      simp [replyLabel, γ] at hl
    | append_singleton u z ih =>
      intro hr
      obtain ⟨H, hinv⟩ := ih (reach_snoc_iff.mp hr).1
      exact (pc_step hD hinv hr).2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [SilentAtEmpty, trim, γ]
  · obtain ⟨nD, hnD⟩ := hD.2.1
    refine ⟨nD, fun u hd => ?_⟩
    have hr : Reach γ u := by by_contra hr; simp [trim, hr] at hd
    obtain ⟨H, ⟨o, rH⟩, hDr, hemp, -⟩ := inv u hr
    have hle := length_le_restrict_none (fun a => by
      rcases a with ⟨_ | _ | i, v⟩
      · exact ⟨_, rfl⟩
      · exact v.elim
      · exact ⟨_, rfl⟩) rH
    rcases eq_or_ne (restrict none H) [] with he | hne
    · rw [he] at hle; simp at hle; simp [hle]
    · exact hle.trans (hnD _ (hDr _ [] (by simp) hne))
  · intro h z hr
    have hr' : Reach γ (h ++ [z]) := ((trim_behEq γ).1 _).mp hr
    obtain ⟨H, hinv⟩ := inv h (reach_snoc_iff.mp hr').1
    exact (pc_step hD hinv hr').1
  · intro h z i hr
    have hr' : Reach γ (h ++ [z]) := ((trim_behEq γ).1 _).mp hr
    obtain ⟨H, hinv⟩ := inv h (reach_snoc_iff.mp hr').1
    rw [replyLabel_trim γ (reach_snoc_iff.mp hr').1]
    exact (pc_step hD hinv hr').2.1 i
  · intro h z hr
    have hr' : Reach γ (h ++ [z]) := ((trim_behEq γ).1 _).mp hr
    obtain ⟨H, hinv⟩ := inv h (reach_snoc_iff.mp hr').1
    rw [replyLabel_trim γ (reach_snoc_iff.mp hr').1]
    exact (pc_step hD hinv hr').2.2.1

end PartialCloseClosure

end SystemAlgebra
