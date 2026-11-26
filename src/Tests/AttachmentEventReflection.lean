module

public import RandomSystems.Converter.EventReflection
public import RandomSystems.Typed.GameRouting
public import RandomSystems.Typed.Functional

/-!
# Attachment outside a reflected event

One fair retained bit controls the monitor. The two systems agree when it is false and
return different visible replies when it is true. A routing converter negates the visible
reply and preserves the monitor, leaving a good outside atom of mass `1/2`.
-/

@[expose] public section

namespace SystemAlgebra.Tests.AttachmentEventReflection

open Probability Probability.Distribution

/-- One unit query returns a Boolean reply. -/
abbrev ports : Interface := Interface.queryBudget Unit (fun _ => Unit) (fun _ => Bool) 1

/-- Tagged exchanges on the one-query interface. -/
abbrev History := List ((Σ i, ports.X i) × (Σ i, ports.withMBO.Y i))

/-- The transcript contains a set monitor bit. -/
def bad (h : History) : Prop := ∃ z ∈ h, z.2.2.2 = true

/-- A single observed reply with visible bit `v` and monitor bit `b`. -/
def observation (v b : Bool) : History := [(⟨(), ()⟩, ⟨(), (v, b)⟩)]

/-- Retain a fair bit `b`; return `(false,b)` on the left and `(b,b)` on the right. -/
noncomputable def monitoredReply (right : Bool) : TypedSystem ports.withMBO :=
  TypedSystem.sample (uniform Bool) fun b =>
    TypedSystem.ofFunction (fun _ _ => (right && b, b))

lemma unchanged_queries (xs : List (Σ i, ports.X i)) (h : ports.domain xs) :
    ports.domain (xs.map id) := by
  simpa only [List.map_id] using h

/-- The primitive router sends the same query and negates the visible reply. -/
noncomputable def negate : TypedConverter ports ports :=
  TypedConverter.routing id (fun _ r => !r.2) unchanged_queries

/-- The monitor-preserving lift of the same primitive router. -/
noncomputable def taggedNegate : TypedConverter ports.withMBO ports.withMBO :=
  PDCBehavior.liftMBO negate

lemma same_off_bad (h : History) (good : ¬ bad h) :
    (monitoredReply false).1 h = (monitoredReply true).1 h := by
  classical
  simp only [monitoredReply, TypedSystem.sample_ofFunction_mass_eq]
  apply mass_congr
  intro b
  cases b with
  | false => rfl
  | true =>
    constructor <;> rintro ⟨domain, answers⟩ <;> refine ⟨domain, ?_⟩ <;>
      intro z hz
    · exact False.elim (good ⟨z, hz, congrArg (fun y => y.2.2) (answers z hz)⟩)
    · exact False.elim (good ⟨z, hz, congrArg (fun y => y.2.2) (answers z hz)⟩)

/-- A one-query system has a monotone monitor because its supported traces have at most one bit. -/
lemma monitoredReply_monotone (right : Bool) : (monitoredReply right).1.MonotoneMBO := by
  intro h nonzero
  have bound : h.length ≤ 1 := by
    by_contra tooLong
    exact nonzero ((monitoredReply right).1.mass_eq_zero_of_bound_lt (Nat.lt_of_not_ge tooLong))
  rcases h with _ | ⟨a, h⟩
  · exact List.Pairwise.nil
  · rcases h with _ | ⟨b, h⟩
    · simp only [List.map_cons, List.map_nil, List.pairwise_singleton]
    · simp only [List.length_cons] at bound
      omega

/-- Every supported completed interaction carries a set inside monitor to the outside. -/
lemma reflects (h : History) (t)
    (follows : FollowsStrategy
      (connectionQueries resourceRoute resourceInput (h.map Prod.fst)) t)
    (stopped : ¬ (connectionQueries resourceRoute resourceInput (h.map Prod.fst)
      (t.map Prod.snd)).Dom)
    (exposed : exposedReplies (resourceRoute (U := ports.X)) (t.map Prod.snd) = h.map Prod.snd)
    (supported : RandomSystem.parallel taggedNegate.1 (monitoredReply false).1 t ≠ 0 ∨
      RandomSystem.parallel taggedNegate.1 (monitoredReply true).1 t ≠ 0)
    (insideBad : bad (RandomSystem.parallelRight t)) : bad h := by
  classical
  by_contra good
  have coefficient : ∃ right, RandomSystem.parallel taggedNegate.1 (monitoredReply right).1 t ≠ 0 :=
    supported.elim (fun hr => ⟨false, hr⟩) (fun hr => ⟨true, hr⟩)
  obtain ⟨right, nonzero⟩ := coefficient
  rw [RandomSystem.parallel_mass] at nonzero
  split_ifs at nonzero with consistent
  · obtain ⟨converter, component⟩ := mul_ne_zero_iff.mp nonzero
    rw [taggedNegate, PDCBehavior.liftMBO_apply] at converter
    split_ifs at converter with tagged
    · have outsideUnset : ∀ v ∈ exposedReplies (resourceRoute (U := ports.X))
          (t.map Prod.snd), v.2.2 = false := by
        intro v hv
        rw [exposed] at hv
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
        cases bit : z.2.2.2 with
        | false => rfl
        | true => exact False.elim (good ⟨z, hz, bit⟩)
      have erased := parallelRight_eq_unsetMBOs_of_completed follows consistent stopped
        tagged outsideUnset (monitoredReply_monotone right _ component)
      rw [erased] at insideBad
      obtain ⟨z, hz, hb⟩ := insideBad
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hz
      exact Bool.false_ne_true hb
    · exact converter rfl
  · exact nonzero rfl

/-- The generic event law applies to the concrete router with its reflection obligation proved. -/
theorem attached_same_off_bad (h : History) (good : ¬ bad h) :
    (TypedConverter.attach taggedNegate (monitoredReply false)).1 h =
      (TypedConverter.attach taggedNegate (monitoredReply true)).1 h := by
  apply PDCBehavior.attach_apply_eq_of_not_bad ports.nonempty_prefix ports.nonempty_prefix
    taggedNegate (monitoredReply false).1 (monitoredReply true).1
    (monitoredReply false).2 (monitoredReply true).2
    bad bad same_off_bad h
  · intro t follows _ stopped exposed supported
    exact reflects h t follows stopped exposed supported
  · exact good

/-- Attachment preserves the retained draw and negates only its visible answer. -/
lemma attached_presentation (right : Bool) :
    TypedConverter.attach taggedNegate (monitoredReply right) =
      TypedSystem.sample (uniform Bool) (fun b =>
        TypedSystem.ofFunction (fun _ _ => (!(right && b), b))) := by
  change taggedNegate • monitoredReply right = _
  rw [monitoredReply, TypedConverter.smul_sample]
  apply congrArg (TypedSystem.sample (uniform Bool))
  funext b
  rw [taggedNegate, negate, TypedConverter.liftMBO_routing]
  exact TypedConverter.routing_smul_ofFunction (A := ports.withMBO) (B := ports.withMBO)
    id (fun _ r => (!r.2.1, r.2.2))
    unchanged_queries (fun _ _ => (right && b, b))

/-- Good probability is positive, while the two bad reply atoms really differ. -/
example :
    (TypedConverter.attach taggedNegate (monitoredReply false)).1 (observation true false) = 1 / 2 ∧
    (TypedConverter.attach taggedNegate (monitoredReply true)).1 (observation true false) = 1 / 2 ∧
    (TypedConverter.attach taggedNegate (monitoredReply false)).1 (observation true true) = 1 / 2 ∧
    (TypedConverter.attach taggedNegate (monitoredReply true)).1 (observation true true) = 0 := by
  rw [attached_presentation, attached_presentation]
  norm_num [TypedSystem.sample_ofFunction_mass_eq, observation, Interface.queryBudget,
    uniform_mass_eq_card_filter, Prod.mk.injEq]
  have h₁ : (true, false) ≠ ((true, true) : Bool × Bool) := by
    intro eq
    cases eq
  have h₂ : (true, false) ≠ ((false, true) : Bool × Bool) := by
    intro eq
    cases eq
  have h₃ : (true, true) ≠ ((true, false) : Bool × Bool) := Ne.symm h₁
  have h₄ : (true, true) ≠ ((false, true) : Bool × Bool) := by
    intro eq
    cases eq
  norm_num [Finset.filter_insert, Finset.filter_singleton, h₁, h₂, h₃, h₄]

/-- The good atom used above is outside the monitor event. -/
example : ¬ bad (observation true false) := by
  simp only [bad, observation, List.mem_singleton, exists_eq_left, Bool.false_eq_true,
    not_false_eq_true]

/-- Both systems retain the empty transcript and reject a second query. -/
example : (monitoredReply false).1 [] = 1 ∧
    (monitoredReply true).1 (observation true true ++ observation true true) = 0 := by
  constructor
  · exact (monitoredReply false).1.mass_nil
  · apply RandomSystem.mass_eq_zero_of_bound_lt
    change 1 < 2
    omega

/-- Two normalized deterministic systems with different replies at the same one-query domain. -/
noncomputable def constantReply (b : Bool) : TypedSystem ports.withMBO :=
  TypedSystem.ofFunction (fun _ _ => (b, b))

/-- The identity converter leaves the differing `true` atom unchanged. -/
lemma constant_atom :
    (TypedConverter.attach (TypedConverter.id ports.withMBO) (constantReply false)).1
      (observation true true) = 0 ∧
    (TypedConverter.attach (TypedConverter.id ports.withMBO) (constantReply true)).1
      (observation true true) = 1 := by
  have left := congrArg (fun R : TypedSystem ports.withMBO => R.1 (observation true true))
    (TypedConverter.identity_attach (constantReply false))
  have right := congrArg (fun R : TypedSystem ports.withMBO => R.1 (observation true true))
    (TypedConverter.identity_attach (constantReply true))
  constructor
  · apply left.trans
    norm_num [constantReply, TypedSystem.ofFunction_mass, observation, Interface.queryBudget]
    intro eq
    cases eq
  · exact right.trans (by
      norm_num [constantReply, TypedSystem.ofFunction_mass, observation, Interface.queryBudget])

/-- Equality off the event "some exchange occurred" compares exactly the empty history. -/
example (h : History) (good : ¬ h ≠ []) :
    (constantReply false).1 h = (constantReply true).1 h := by
  have empty : h = [] := Classical.not_not.mp good
  rw [empty, RandomSystem.mass_nil, RandomSystem.mass_nil]

/-- On the selected `true` outside atom, left-supported completed fibers are impossible.
Hence any left-only reflection premise holds, but `constant_atom` gives unequal outside masses. -/
lemma left_only_reflection (t)
    (follows : FollowsStrategy (connectionQueries resourceRoute resourceInput
      ((observation true true).map Prod.fst)) t)
    (bounded : t.length ≤ (2 * (TypedConverter.id ports.withMBO).2.choose + 2) *
      ((observation true true).map Prod.fst).length)
    (stopped : ¬ (connectionQueries resourceRoute resourceInput
      ((observation true true).map Prod.fst) (t.map Prod.snd)).Dom)
    (exposed : exposedReplies (resourceRoute (U := ports.X)) (t.map Prod.snd) =
      (observation true true).map Prod.snd)
    (supported : RandomSystem.parallel (TypedConverter.id ports.withMBO).1
      (constantReply false).1 t ≠ 0) : False := by
  have lower := RandomSystem.mass_le_connectionLaw
    (RandomSystem.parallel (TypedConverter.id ports.withMBO).1 (constantReply false).1)
    resourceRoute resourceInput ((observation true true).map Prod.fst)
    ((2 * (TypedConverter.id ports.withMBO).2.choose + 2) *
      ((observation true true).map Prod.fst).length) t follows bounded stopped
  rw [exposed] at lower
  change RandomSystem.parallel (TypedConverter.id ports.withMBO).1 (constantReply false).1 t ≤
    (TypedConverter.attach (TypedConverter.id ports.withMBO) (constantReply false)).1
      (observation true true) at lower
  rw [constant_atom.1] at lower
  exact supported (le_antisymm lower (RandomSystem.mass_nonneg _ _))

/-- The one-sided premise above cannot force equality at this outside atom. -/
example :
    (TypedConverter.attach (TypedConverter.id ports.withMBO) (constantReply false)).1
      (observation true true) ≠
    (TypedConverter.attach (TypedConverter.id ports.withMBO) (constantReply true)).1
      (observation true true) := by
  rw [constant_atom.1, constant_atom.2]
  norm_num

#print axioms PDCBehavior.attach_apply_eq_of_not_bad
#print axioms attached_same_off_bad

end SystemAlgebra.Tests.AttachmentEventReflection
