module

public import RandomSystems.Typed.GameRouting

/-!
# MBO routing regression

The router forwards Boolean queries, discards the visible inside reply, and returns `false`.
Its two-query domain is retained after lifting. A fixed inside function supplies successive
bits `false`, then `true`; the second call is also checked before its reply arrives.
-/

@[expose] public section

namespace SystemAlgebra.Tests.GameQueryRouting

/-- At most two nonempty Boolean queries at the single port. -/
def domain (xs : List (Σ _ : Unit, Bool)) : Prop := xs ≠ [] ∧ xs.length ≤ 2

lemma domain_prefix {p h} (hp : p <+: h) (hn : p ≠ []) (hh : domain h) : domain p :=
  ⟨hn, hp.length_le.trans hh.2⟩

/-- The visible answer discards the inside reply. -/
def visibleAnswer (_ : Σ _ : Unit, Bool) (_ : Σ _ : Unit, Bool) : Bool := false

/-- The lifted answer discards the visible reply and forwards its MBO. -/
def taggedAnswer (_ : Σ _ : Unit, Bool) (r : Σ _ : Unit, Bool × Bool) : Bool × Bool :=
  (false, r.2.2)

lemma visible_certified : IsDDCFrom domain domain 1
    (routingConverter (V := fun _ => Bool) id visibleAnswer domain) := by
  apply routingConverter_isDDCFrom (V := fun _ => Bool) id visibleAnswer domain_prefix
  intro xs hx
  simpa only [List.map_id] using hx

lemma tagged_certified : IsDDCFrom domain domain 1
    (routingConverter (V := fun _ => Bool × Bool) id taggedAnswer domain) := by
  apply routingConverter_isDDCFrom (V := fun _ => Bool × Bool) id taggedAnswer domain_prefix
  intro xs hx
  simpa only [List.map_id] using hx

/-- The original router as a deterministic converter behavior. -/
noncomputable def visible :
    PDCBehavior Unit Unit (fun _ => Bool) (fun _ => Bool) (fun _ => Bool) (fun _ => Bool)
      domain 2 (fun _ h => h.2) domain 2 (fun _ h => h.2) :=
  PDCBehavior.ofDDC (routingConverter (V := fun _ => Bool) id visibleAnswer domain)
    visible_certified

/-- The same router with the inside bit on each outside reply. -/
noncomputable def tagged :
    PDCBehavior Unit Unit (fun _ => Bool) (fun _ => Bool × Bool)
      (fun _ => Bool) (fun _ => Bool × Bool)
      domain 2 (fun _ h => h.2) domain 2 (fun _ h => h.2) :=
  PDCBehavior.ofDDC (routingConverter (V := fun _ => Bool × Bool) id taggedAnswer domain)
    tagged_certified

lemma lifted : PDCBehavior.liftMBO visible = tagged :=
  PDCBehavior.liftMBO_ofDDC_routingConverter (V := fun _ => Bool) id visibleAnswer
    visible_certified tagged_certified

/-- Outside queries and inside replies on the lifted converter. -/
abbrev Input := Σ l : Two Unit Unit, twoFam (fun _ => Bool) (fun _ => Bool × Bool) l

/-- Outside replies and inside queries on the lifted converter. -/
abbrev Output := Σ l : Two Unit Unit, twoFam (fun _ => Bool × Bool) (fun _ => Bool) l

/-- Outside query `b`. -/
def query (b : Bool) : Input := ⟨⟨none, ()⟩, b⟩

/-- Inside reply `(y, bit)`. -/
def reply (y bit : Bool) : Input := ⟨⟨some (), ()⟩, (y, bit)⟩

/-- Inside query `b`. -/
def request (b : Bool) : Output := ⟨⟨some (), ()⟩, b⟩

/-- Outside reply `(y, bit)`. -/
def answer (y bit : Bool) : Output := ⟨⟨none, ()⟩, (y, bit)⟩

/-- Two calls carry different successive monitor bits. -/
def completed : List (Input × Output) :=
  [(query false, request false), (reply false false, answer false false),
    (query true, request true), (reply false true, answer false true)]

lemma completed_replies :
    Replies (routingConverter (V := fun _ => Bool × Bool) id taggedAnswer domain)
    (completed.map Prod.fst) (completed.map Prod.snd) := by
  have h := replies_routingConverter_ofFunction (V := fun _ => Bool × Bool)
    id taggedAnswer domain_prefix
    (fun _ b => (false, b)) [⟨(), false⟩, ⟨(), true⟩]
    ⟨List.cons_ne_nil _ _, le_refl _⟩
  simpa only [completed, query, reply, request, answer, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
    callTranscript, callSteps, id_eq, taggedAnswer] using h

example : (PDCBehavior.liftMBO visible).1 completed = 1 := by
  classical
  rw [lifted, tagged, PDCBehavior.ofDDC_apply, ite_eq_left completed_replies]

/-- The second request is already counted while its new monitor bit has not arrived. -/
example : (PDCBehavior.liftMBO visible).1
    [(query false, request false), (reply false false, answer false false),
      (query true, request true)] = 1 := by
  classical
  have hr : Replies (routingConverter (V := fun _ => Bool × Bool) id taggedAnswer domain)
      ([query false, reply false false, query true] ++ [reply false true])
      ([request false, answer false false, request true] ++ [answer false true]) :=
    completed_replies
  rw [lifted, tagged, PDCBehavior.ofDDC_apply]
  exact ite_eq_left (by simpa only [List.map_cons, List.map_nil] using (replies_snoc.mp hr).1)

/-- The lifted behavior gives zero mass to a third outside call. -/
example : (PDCBehavior.liftMBO visible).1
    (completed ++ [(query false, request false)]) = 0 := by
  classical
  rw [lifted, tagged, PDCBehavior.ofDDC_apply]
  apply ite_eq_right
  intro hr
  have next : routingConverter (V := fun _ => Bool × Bool) id taggedAnswer domain
      (completed.map Prod.fst ++ [query false]) = Part.some (request false) :=
    (replies_snoc.mp (by simpa only [List.map_append, List.map_singleton] using hr)).2
  have hd := Part.dom_iff_mem.mpr ⟨request false, Part.eq_some_iff.mp next⟩
  have hf := ((tagged_certified.answers completed (query false)
    completed_replies).mp hd).2.2.1
  have bound := hf.2
  simp only [completed, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    query, reply, outsideInputs, splitIn, restrict_cons_self,
    restrict_cons_ne (by simp : some () ≠ (none : Option Unit)), restrict_nil,
    List.length_cons, List.length_nil] at bound
  omega

/-- A two-query interface for the typed attachment test. -/
abbrev ports : Interface := Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) 2

lemma ports_map (xs : List (Σ i, ports.X i)) (h : ports.domain xs) :
    ports.domain (xs.map id) := by
  simpa only [List.map_id] using h

/-- Typed routing discards the visible reply while preserving its bit under attachment. -/
example :
    TypedConverter.attach (A := ports.withMBO) (B := ports.withMBO)
      (PDCBehavior.liftMBO (TypedConverter.routing (A := ports) (B := ports)
        id (fun _ _ => false) ports_map))
      (TypedSystem.ofFunction (A := ports.withMBO) (fun _ b => (false, b))) =
      TypedSystem.ofFunction (A := ports.withMBO) (fun _ b => (false, b)) := by
  rw [TypedConverter.liftMBO_routing]
  exact TypedConverter.routing_smul_ofFunction (A := ports.withMBO)
    (B := ports.withMBO) id (fun _ r => (false, r.2.2)) ports_map
    (fun _ b => (false, b))

#print axioms PDCBehavior.liftMBO_ofDDC_routingConverter
#print axioms TypedConverter.liftMBO_routing

end SystemAlgebra.Tests.GameQueryRouting
