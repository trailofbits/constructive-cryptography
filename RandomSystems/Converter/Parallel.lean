/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.Relabel
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Ordered parallel composition of DDCs

Jost, printed p. 17, identifies the underlying resource construction:
“A finite set of resources with disjoint interface sets can be viewed as a
single one”. Proposition 2.2.3 (printed p. 18) gives the attachment law
`pi [R, S] = [pi R, S]`. The tagged query sum below is the functional DDC
realization of that routing: each joint history projects to its two component
histories, and exactly one component is active in each outer round.

The construction is ordered.  This module proves forwarding, attachment, and
serial laws; it does not postulate or prove a symmetry law.
-/

namespace RandomSystems.Ambient

universe u v w z

open DDC.Internal

namespace DDC

private noncomputable abbrev selectReply
    {A : Interface.{u, v}} (query : A.query)
    (reply : DDC.History.InnerReply A) : Option (A.answer query) :=
  Attachment.selectReply query reply

private theorem mem_forwardingRaw_iff
    {A : Interface.{u, v}} (history : DDC.History A A)
    (response : DDC.Response history) :
    response ∈ forwardingRaw A history ↔
      match history.lastInput with
      | Sum.inl query => response = Sum.inl query
      | Sum.inr ⟨query, reply⟩ =>
          ∃ equal : query = history.lastOuter,
            response = Sum.inr (equal ▸ reply) :=
  DDC.Internal.mem_forwardingRaw_iff A history response

private theorem mem_forwarding_with_raw_iff (A : Interface.{u, v})
    (history : DDC.History A A) (response : DDC.Response history) :
    response ∈ forwarding A history ↔
      DDC.Raw.Admissible (forwardingRaw A) history ∧
        match history.lastInput with
        | Sum.inl query => response = Sum.inl query
        | Sum.inr ⟨query, reply⟩ =>
            ∃ equal : query = history.lastOuter,
              response = Sum.inr (equal ▸ reply) := by
  rw [mem_forwarding_iff]
  constructor
  · rintro ⟨admissible, responseEqual⟩
    exact ⟨(admissible_forwardingRaw_iff history).mpr admissible,
      responseEqual⟩
  · rintro ⟨admissible, responseEqual⟩
    exact ⟨(admissible_forwardingRaw_iff history).mp admissible,
      responseEqual⟩

private def parallelLeftQueries {A B : Interface.{u, v}}
    (queries : List (Interface.parallel A B).query) : List A.query :=
  queries.filterMap fun
    | Sum.inl query => some query
    | Sum.inr _ => none

private def parallelRightQueries {A B : Interface.{u, v}}
    (queries : List (Interface.parallel A B).query) : List B.query :=
  queries.filterMap fun
    | Sum.inl _ => none
    | Sum.inr query => some query
end DDC

namespace DDC

/-- The component whose outer round is current in an ordered parallel history. -/
private inductive ParallelSide where
  | left
  | right
  deriving DecidableEq

/-- Append a new outer query to an optional component history. -/
private def appendOuter {A : Interface.{u, v}} {B : Interface.{w, z}}
    (history : Option (DDC.History A B)) (query : A.query) :
    DDC.History A B :=
  match history with
  | none => DDC.History.singleton query
  | some previous => previous.snocOuter query

/-- The two component histories projected from one joint history. -/
private structure ParallelProjection
    (A₁ : Interface.{u, v}) (B₁ : Interface.{w, z})
    (A₂ : Interface.{u, v}) (B₂ : Interface.{w, z}) where
  active : Option ParallelSide
  left : Option (DDC.History A₁ B₁)
  right : Option (DDC.History A₂ B₂)

/-- Extend the component projection by one received joint input.  A dependent
inner reply is sent to the component named by its retained query tag. -/
private def extendParallelProjection
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (projection : ParallelProjection A₁ B₁ A₂ B₂)
    (input : DDC.History.Input (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)) :
    ParallelProjection A₁ B₁ A₂ B₂ :=
  match input with
  | Sum.inl (Sum.inl query) =>
      { projection with
        active := some .left
        left := some (appendOuter projection.left query) }
  | Sum.inl (Sum.inr query) =>
      { projection with
        active := some .right
        right := some (appendOuter projection.right query) }
  | Sum.inr ⟨Sum.inl query, reply⟩ =>
      { projection with
        left := projection.left.map fun history =>
          history.snocInner query reply }
  | Sum.inr ⟨Sum.inr query, reply⟩ =>
      { projection with
        right := projection.right.map fun history =>
          history.snocInner query reply }

/-- Pure fold projection of a complete component received history. -/
private def projectParallel
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)) :
    ParallelProjection A₁ B₁ A₂ B₂ :=
  history.inputs.1.foldl extendParallelProjection
    { active := none, left := none, right := none }

@[simp]
private theorem projectParallel_singleton_left
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}} (query : A₁.query) :
    projectParallel
        (DDC.History.singleton (B := Interface.parallel B₁ B₂)
          (Sum.inl query : (Interface.parallel A₁ A₂).query)) =
      { active := some .left
        left := some (DDC.History.singleton query)
        right := (none : Option (DDC.History A₂ B₂)) } :=
  rfl

@[simp]
private theorem projectParallel_singleton_right
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}} (query : A₂.query) :
    projectParallel
        (DDC.History.singleton (B := Interface.parallel B₁ B₂)
          (Sum.inr query : (Interface.parallel A₁ A₂).query)) =
      { active := some .right
        left := (none : Option (DDC.History A₁ B₁))
        right := some (DDC.History.singleton query) } :=
  rfl

@[simp]
private theorem projectParallel_snocOuter_left
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)) (query : A₁.query) :
    projectParallel (history.snocOuter (Sum.inl query)) =
      extendParallelProjection (projectParallel history) (Sum.inl (Sum.inl query)) := by
  change List.foldl extendParallelProjection
      { active := none, left := none, right := none }
      ((show List (DDC.History.Input
          (Interface.parallel A₁ A₂) (Interface.parallel B₁ B₂)) from
          history.inputs.queries) ++
        [(Sum.inl (Sum.inl query) : DDC.History.Input
          (Interface.parallel A₁ A₂) (Interface.parallel B₁ B₂))]) = _
  exact List.foldl_concat _ _ _ _

@[simp]
private theorem projectParallel_snocOuter_right
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)) (query : A₂.query) :
    projectParallel (history.snocOuter (Sum.inr query)) =
      extendParallelProjection (projectParallel history) (Sum.inl (Sum.inr query)) := by
  change List.foldl extendParallelProjection
      { active := none, left := none, right := none }
      ((show List (DDC.History.Input
          (Interface.parallel A₁ A₂) (Interface.parallel B₁ B₂)) from
          history.inputs.queries) ++
        [(Sum.inl (Sum.inr query) : DDC.History.Input
          (Interface.parallel A₁ A₂) (Interface.parallel B₁ B₂))]) = _
  exact List.foldl_concat _ _ _ _

@[simp]
private theorem projectParallel_snocInner_left
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)) (query : B₁.query)
    (reply : Option (B₁.answer query)) :
    projectParallel (history.snocInner (Sum.inl query) reply) =
      extendParallelProjection (projectParallel history)
        (Sum.inr ⟨Sum.inl query, reply⟩) := by
  change List.foldl extendParallelProjection
      { active := none, left := none, right := none }
      ((show List (DDC.History.Input
          (Interface.parallel A₁ A₂) (Interface.parallel B₁ B₂)) from
          history.inputs.queries) ++
        [(Sum.inr ⟨Sum.inl query, reply⟩ : DDC.History.Input
          (Interface.parallel A₁ A₂) (Interface.parallel B₁ B₂))]) = _
  exact List.foldl_concat _ _ _ _

@[simp]
private theorem projectParallel_snocInner_right
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)) (query : B₂.query)
    (reply : Option (B₂.answer query)) :
    projectParallel (history.snocInner (Sum.inr query) reply) =
      extendParallelProjection (projectParallel history)
        (Sum.inr ⟨Sum.inr query, reply⟩) := by
  change List.foldl extendParallelProjection
      { active := none, left := none, right := none }
      ((show List (DDC.History.Input
          (Interface.parallel A₁ A₂) (Interface.parallel B₁ B₂)) from
          history.inputs.queries) ++
        [(Sum.inr ⟨Sum.inr query, reply⟩ : DDC.History.Input
          (Interface.parallel A₁ A₂) (Interface.parallel B₁ B₂))]) = _
  exact List.foldl_concat _ _ _ _

/-- The active-left component together with the exact final outer-query
fibre selected by the joint history. -/
private def ActiveLeft
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₁ B₁) : Prop :=
  (projectParallel history).active = some .left ∧
  (projectParallel history).left = some component ∧
  history.lastOuter = Sum.inl component.lastOuter

/-- Right-hand counterpart of `ActiveLeft`. -/
private def ActiveRight
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₂ B₂) : Prop :=
  (projectParallel history).active = some .right ∧
  (projectParallel history).right = some component ∧
  history.lastOuter = Sum.inr component.lastOuter

/-- Tag a left component response in the exact answer fibre selected by the
joint history. -/
private def tagLeftResponse
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₁ B₁)
    (outerEqual : history.lastOuter = Sum.inl component.lastOuter) :
    DDC.Response component → DDC.Response history
  | Sum.inl query => Sum.inl (Sum.inl query)
  | Sum.inr reply => Sum.inr (cast
      (congrArg (fun selected =>
        Option ((Interface.parallel A₁ A₂).answer selected))
        outerEqual.symm) reply)

/-- Tag a right component response in the exact answer fibre selected by the
joint history. -/
private def tagRightResponse
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₂ B₂)
    (outerEqual : history.lastOuter = Sum.inr component.lastOuter) :
    DDC.Response component → DDC.Response history
  | Sum.inl query => Sum.inl (Sum.inr query)
  | Sum.inr reply => Sum.inr (cast
      (congrArg (fun selected =>
        Option ((Interface.parallel A₁ A₂).answer selected))
        outerEqual.symm) reply)

private theorem activeLeft_unique
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    {history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {left right : DDC.History A₁ B₁}
    (leftActive : ActiveLeft history left)
    (rightActive : ActiveLeft history right) : left = right := by
  exact Option.some.inj (leftActive.2.1.symm.trans rightActive.2.1)

private theorem activeRight_unique
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    {history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {left right : DDC.History A₂ B₂}
    (leftActive : ActiveRight history left)
    (rightActive : ActiveRight history right) : left = right := by
  exact Option.some.inj (leftActive.2.1.symm.trans rightActive.2.1)

private theorem not_activeRight_of_activeLeft
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    {history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {left : DDC.History A₁ B₁}
    (active : ActiveLeft history left) :
    ¬ ∃ right : DDC.History A₂ B₂, ActiveRight history right := by
  rintro ⟨right, rightActive⟩
  have impossible : (some ParallelSide.left : Option ParallelSide) =
      some ParallelSide.right := active.1.symm.trans rightActive.1
  simp at impossible

private theorem not_activeLeft_of_activeRight
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    {history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {right : DDC.History A₂ B₂}
    (active : ActiveRight history right) :
    ¬ ∃ left : DDC.History A₁ B₁, ActiveLeft history left := by
  rintro ⟨left, leftActive⟩

  have impossible : (some ParallelSide.right : Option ParallelSide) =
      some ParallelSide.left := active.1.symm.trans leftActive.1
  simp at impossible

/-- Raw ordered parallel is evaluation of the uniquely active component
component graph followed by dependent response tagging. -/
private noncomputable def parallelRaw
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂) :
    DDC.Raw (Interface.parallel A₁ A₂) (Interface.parallel B₁ B₂) := by
  classical
  intro history
  let projection := projectParallel history
  exact match projection.active, projection.left, projection.right with
    | some .left, some component, _ =>
        if outerEqual : history.lastOuter = Sum.inl component.lastOuter then
          Part.map (tagLeftResponse history component outerEqual)
            (left component)
        else Part.none
    | some .right, _, some component =>
        if outerEqual : history.lastOuter = Sum.inr component.lastOuter then
          Part.map (tagRightResponse history component outerEqual)
            (right component)
        else Part.none
    | _, _, _ => Part.none

private theorem mem_parallelRaw_left_iff
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₁ B₁)
    (active : ActiveLeft history component)
    (response : DDC.Response history) :
    response ∈ parallelRaw left right history ↔
      ∃ componentResponse ∈ left component,
        tagLeftResponse history component active.2.2 componentResponse =
          response := by
  classical
  simp only [parallelRaw, active.1, active.2.1, active.2.2, dif_pos]
  rw [Part.mem_map_iff]

private theorem mem_parallelRaw_right_iff
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₂ B₂)
    (active : ActiveRight history component)
    (response : DDC.Response history) :
    response ∈ parallelRaw left right history ↔
      ∃ componentResponse ∈ right component,
        tagRightResponse history component active.2.2 componentResponse =
          response := by
  classical
  simp only [parallelRaw, active.1, active.2.1, active.2.2, dif_pos]
  rw [Part.mem_map_iff]

private structure ProjectionValid
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)) : Prop where
  leftAdmissible : ∀ component,
    (projectParallel history).left = some component →
      DDC.Raw.Admissible left.toFun component
  rightAdmissible : ∀ component,
    (projectParallel history).right = some component →
      DDC.Raw.Admissible right.toFun component
  activeLeftPresent :
    (projectParallel history).active = some .left →
      ∃ component, ActiveLeft history component
  activeRightPresent :
    (projectParallel history).active = some .right →
      ∃ component, ActiveRight history component
  leftClosed : (projectParallel history).active ≠ some .left →
    ∀ component, (projectParallel history).left = some component →
      ∃ reply, Sum.inr reply ∈ left component
  rightClosed : (projectParallel history).active ≠ some .right →
    ∀ component, (projectParallel history).right = some component →
      ∃ reply, Sum.inr reply ∈ right component

private theorem parallelRaw_admissible_projection
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    {history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    (admissible : DDC.Raw.Admissible (parallelRaw left right) history) :
    ProjectionValid left right history := by
  induction admissible with
  | start outerQuery =>
      cases outerQuery with
      | inl query =>
          constructor
          · intro component equal
            simp only [projectParallel_singleton_left, Option.some.injEq]
              at equal
            subst component
            exact .start query
          · intro component equal
            simp at equal
          · intro _
            exact ⟨DDC.History.singleton query, rfl, rfl, rfl⟩
          · simp
          · simp
          · intro _ component equal
            simp at equal
      | inr query =>
          constructor
          · intro component equal
            simp at equal
          · intro component equal
            simp only [projectParallel_singleton_right, Option.some.injEq]
              at equal
            subst component
            exact .start query
          · simp
          · intro _
            exact ⟨DDC.History.singleton query, rfl, rfl, rfl⟩
          · intro _ component equal
            simp at equal
          · simp
  | @afterInner history query prior responds reply inductionHypothesis =>
      let projection := projectParallel history
      have valid := inductionHypothesis
      cases activeEqual : projection.active with
      | none =>
          have impossible : False := by
            exact Part.notMem_none _ (by
              simpa only [parallelRaw, projection, activeEqual] using responds)
          exact impossible.elim
      | some side =>
          cases side with
          | left =>
              obtain ⟨component, active⟩ := valid.activeLeftPresent activeEqual
              obtain ⟨componentResponse, componentResponds, taggedEqual⟩ :=
                (mem_parallelRaw_left_iff left right history component active
                  (Sum.inl query)).mp responds
              cases componentResponse with
              | inr componentReply =>
                  simp [tagLeftResponse] at taggedEqual
              | inl componentQuery =>
                  have queryEqual : query = Sum.inl componentQuery := by
                    simpa [tagLeftResponse] using taggedEqual.symm
                  subst query
                  constructor <;> simp only [ActiveLeft, ActiveRight,
                    projectParallel_snocInner_left, projection, activeEqual,
                    active.2.1, extendParallelProjection, Option.map]
                  · intro next equal
                    simp only [Option.some.injEq] at equal
                    subst next
                    exact .afterInner
                      (valid.leftAdmissible component active.2.1)
                      componentResponds reply
                  · exact valid.rightAdmissible
                  · intro _
                    refine ⟨component.snocInner componentQuery reply,
                      True.intro, rfl, ?_⟩
                    simpa using active.2.2
                  · simp
                  · simp
                  · intro _ other equal
                    exact valid.rightClosed (by
                      change projection.active ≠ some .right
                      rw [activeEqual]
                      simp) other equal
          | right =>
              obtain ⟨component, active⟩ := valid.activeRightPresent activeEqual
              obtain ⟨componentResponse, componentResponds, taggedEqual⟩ :=
                (mem_parallelRaw_right_iff left right history component active
                  (Sum.inl query)).mp responds
              cases componentResponse with
              | inl componentQuery =>
                  have queryEqual : query = Sum.inr componentQuery := by
                    simpa [tagRightResponse] using taggedEqual.symm
                  subst query
                  constructor <;> simp only [ActiveLeft, ActiveRight,
                    projectParallel_snocInner_right, projection, activeEqual,
                    active.2.1, extendParallelProjection, Option.map]
                  · exact valid.leftAdmissible
                  · intro next equal
                    simp only [Option.some.injEq] at equal
                    subst next
                    exact .afterInner
                      (valid.rightAdmissible component active.2.1)
                      componentResponds reply
                  · simp
                  · intro _
                    refine ⟨component.snocInner componentQuery reply,
                      True.intro, rfl, ?_⟩
                    simpa using active.2.2
                  · intro _ other equal
                    exact valid.leftClosed (by
                      change projection.active ≠ some .left
                      rw [activeEqual]
                      simp) other equal
                  · simp
              | inr componentReply =>
                  simp [tagRightResponse] at taggedEqual
  | @afterOuter history prior outerReply responds outerQuery
      inductionHypothesis =>
      let projection := projectParallel history
      have valid := inductionHypothesis
      have bothClosed :
          (∀ component, projection.left = some component →
            ∃ reply, Sum.inr reply ∈ left component) ∧
          (∀ component, projection.right = some component →
            ∃ reply, Sum.inr reply ∈ right component) := by
        cases activeEqual : projection.active with
        | none =>
            have impossible : False := by
              exact Part.notMem_none _ (by
                simpa only [parallelRaw, projection, activeEqual] using responds)
            exact impossible.elim
        | some side =>
            cases side with
            | left =>
                obtain ⟨component, active⟩ := valid.activeLeftPresent activeEqual
                obtain ⟨componentResponse, componentResponds, taggedEqual⟩ :=
                  (mem_parallelRaw_left_iff left right history component active
                    (Sum.inr outerReply)).mp responds
                cases componentResponse with
                | inl componentQuery =>
                    simp [tagLeftResponse] at taggedEqual
                | inr componentReply =>
                    constructor
                    · intro other equal
                      have same := Option.some.inj
                        (equal.symm.trans active.2.1)
                      subst other
                      exact ⟨componentReply, componentResponds⟩
                    · exact valid.rightClosed (by
                        change projection.active ≠ some .right
                        rw [activeEqual]
                        simp)
            | right =>
                obtain ⟨component, active⟩ := valid.activeRightPresent activeEqual
                obtain ⟨componentResponse, componentResponds, taggedEqual⟩ :=
                  (mem_parallelRaw_right_iff left right history component active
                    (Sum.inr outerReply)).mp responds
                cases componentResponse with
                | inl componentQuery =>
                    simp [tagRightResponse] at taggedEqual
                | inr componentReply =>
                    constructor
                    · exact valid.leftClosed (by
                        change projection.active ≠ some .left
                        rw [activeEqual]
                        simp)
                    · intro other equal

                      have same := Option.some.inj
                        (equal.symm.trans active.2.1)
                      subst other
                      exact ⟨componentReply, componentResponds⟩
      cases outerQuery with
      | inl query =>
          cases leftEqual : projection.left with
          | none =>
              constructor <;> simp only [ActiveLeft, ActiveRight,
                projectParallel_snocOuter_left, projection,
                extendParallelProjection, leftEqual]
              · intro component equal
                simp only [appendOuter, Option.some.injEq] at equal
                subst component
                exact .start query
              · exact valid.rightAdmissible
              · intro _
                refine ⟨DDC.History.singleton query, True.intro, rfl, ?_⟩
                simp
              · simp
              · simp
              · intro _ component equal
                exact bothClosed.2 component equal
          | some previous =>
              obtain ⟨reply, previousResponds⟩ :=
                bothClosed.1 previous leftEqual
              constructor <;> simp only [ActiveLeft, ActiveRight,
                projectParallel_snocOuter_left, projection,
                extendParallelProjection, leftEqual]
              · intro component equal
                simp only [appendOuter, Option.some.injEq] at equal
                subst component
                exact .afterOuter
                  (valid.leftAdmissible previous leftEqual)
                  previousResponds query
              · exact valid.rightAdmissible
              · intro _
                refine ⟨previous.snocOuter query, True.intro, rfl, ?_⟩
                simp
              · simp
              · simp
              · intro _ component equal
                exact bothClosed.2 component equal
      | inr query =>
          cases rightEqual : projection.right with
          | none =>
              constructor <;> simp only [ActiveLeft, ActiveRight,
                projectParallel_snocOuter_right, projection,
                extendParallelProjection, rightEqual]
              · exact valid.leftAdmissible
              · intro component equal
                simp only [appendOuter, Option.some.injEq] at equal
                subst component
                exact .start query
              · simp
              · intro _
                refine ⟨DDC.History.singleton query, True.intro, rfl, ?_⟩
                simp
              · intro _ component equal
                exact bothClosed.1 component equal
              · simp
          | some previous =>
              obtain ⟨reply, previousResponds⟩ :=
                bothClosed.2 previous rightEqual
              constructor <;> simp only [ActiveLeft, ActiveRight,
                projectParallel_snocOuter_right, projection,
                extendParallelProjection, rightEqual]
              · exact valid.leftAdmissible
              · intro component equal
                simp only [appendOuter, Option.some.injEq] at equal
                subst component
                exact .afterOuter
                  (valid.rightAdmissible previous rightEqual)
                  previousResponds query
              · simp
              · intro _
                refine ⟨previous.snocOuter query, True.intro, rfl, ?_⟩
                simp
              · intro _ component equal
                exact bothClosed.1 component equal
              · simp

private theorem parallelRaw_admissible_activeSide
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    {history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    (admissible : DDC.Raw.Admissible (parallelRaw left right) history) :
    ∃ side, (projectParallel history).active = some side := by
  induction admissible with
  | start query =>
      cases query with
      | inl query => exact ⟨.left, rfl⟩
      | inr query => exact ⟨.right, rfl⟩
  | @afterInner previous query prior responds reply inductionHypothesis =>
      obtain ⟨side, activeEqual⟩ := inductionHypothesis
      refine ⟨side, ?_⟩
      cases query with
      | inl query =>
          rw [projectParallel_snocInner_left]
          cases side <;> simp [extendParallelProjection, activeEqual]
      | inr query =>
          rw [projectParallel_snocInner_right]
          cases side <;> simp [extendParallelProjection, activeEqual]
  | @afterOuter previous prior reply responds query inductionHypothesis =>
      cases query with
      | inl query =>
          exact ⟨.left, by
            rw [projectParallel_snocOuter_left]
            simp [extendParallelProjection]⟩
      | inr query =>
          exact ⟨.right, by
            rw [projectParallel_snocOuter_right]
            simp [extendParallelProjection]⟩

private theorem parallelRaw_admissible_active
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    {history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    (admissible : DDC.Raw.Admissible (parallelRaw left right) history) :
    (∃ component, ActiveLeft history component) ∨
      ∃ component, ActiveRight history component := by
  have valid := parallelRaw_admissible_projection left right admissible
  obtain ⟨side, activeEqual⟩ :=
    parallelRaw_admissible_activeSide left right admissible
  cases side with
  | left => exact Or.inl (valid.activeLeftPresent activeEqual)
  | right => exact Or.inr (valid.activeRightPresent activeEqual)

private theorem parallelRaw_complete
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂) :
    DDC.Raw.Complete (parallelRaw left right) := by
  intro history admissible
  have valid := parallelRaw_admissible_projection left right admissible
  rcases parallelRaw_admissible_active left right admissible with
    ⟨component, active⟩ | ⟨component, active⟩
  · have componentAdmissible := valid.leftAdmissible component active.2.1
    let response := left.response component componentAdmissible
    exact ((mem_parallelRaw_left_iff left right history component active
      (tagLeftResponse history component active.2.2 response)).mpr
        ⟨response, left.response_mem component componentAdmissible, rfl⟩).1
  · have componentAdmissible := valid.rightAdmissible component active.2.1
    let response := right.response component componentAdmissible
    exact ((mem_parallelRaw_right_iff left right history component active
      (tagRightResponse history component active.2.2 response)).mpr
        ⟨response, right.response_mem component componentAdmissible, rfl⟩).1

private theorem parallelRaw_accessible_left
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    (before : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₁ B₁)
    (active : ActiveLeft before component) :
    Acc (DDC.Raw.InnerContinuation (parallelRaw left right)) before := by
  induction component using left.branchFinite.induction generalizing before with
  | h component inductionHypothesis =>
      apply Acc.intro
      intro after continues
      rcases continues with ⟨jointQuery, jointReply, responds, rfl⟩
      obtain ⟨componentResponse, componentResponds, taggedEqual⟩ :=
        (mem_parallelRaw_left_iff left right before component active
          (Sum.inl jointQuery)).mp responds
      cases componentResponse with
      | inr componentReply =>
          simp [tagLeftResponse] at taggedEqual
      | inl query =>
          have queryEqual : jointQuery = Sum.inl query := by
            simpa [tagLeftResponse] using taggedEqual.symm
          subst jointQuery
          let next := component.snocInner query jointReply
          have componentContinues : DDC.Raw.InnerContinuation left.toFun
              next component := ⟨query, jointReply, componentResponds, rfl⟩
          apply inductionHypothesis next componentContinues
          refine ⟨?_, ?_, ?_⟩
          · rw [projectParallel_snocInner_left]
            simp [extendParallelProjection, active.1]
          · rw [projectParallel_snocInner_left]
            simp [extendParallelProjection, active.1, active.2.1, next]
          · simpa [next] using active.2.2

private theorem parallelRaw_accessible_right
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    (before : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₂ B₂)
    (active : ActiveRight before component) :
    Acc (DDC.Raw.InnerContinuation (parallelRaw left right)) before := by
  induction component using right.branchFinite.induction generalizing before with
  | h component inductionHypothesis =>
      apply Acc.intro
      intro after continues
      rcases continues with ⟨jointQuery, jointReply, responds, rfl⟩
      obtain ⟨componentResponse, componentResponds, taggedEqual⟩ :=
        (mem_parallelRaw_right_iff left right before component active
          (Sum.inl jointQuery)).mp responds
      cases componentResponse with
      | inl query =>
          have queryEqual : jointQuery = Sum.inr query := by
            simpa [tagRightResponse] using taggedEqual.symm
          subst jointQuery
          let next := component.snocInner query jointReply
          have componentContinues : DDC.Raw.InnerContinuation right.toFun
              next component := ⟨query, jointReply, componentResponds, rfl⟩
          apply inductionHypothesis next componentContinues
          refine ⟨?_, ?_, ?_⟩
          · rw [projectParallel_snocInner_right]
            simp [extendParallelProjection, active.1]
          · rw [projectParallel_snocInner_right]
            simp [extendParallelProjection, active.1, active.2.1, next]
          · simpa [next] using active.2.2
      | inr componentReply =>
          simp [tagRightResponse] at taggedEqual

private theorem parallelRaw_branchFinite
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂) :
    DDC.Raw.BranchFinite (parallelRaw left right) := by
  apply WellFounded.intro
  intro history
  by_cases activeLeft : ∃ component, ActiveLeft history component
  · obtain ⟨component, active⟩ := activeLeft
    exact parallelRaw_accessible_left left right history component active
  · by_cases activeRight : ∃ component, ActiveRight history component
    · obtain ⟨component, active⟩ := activeRight
      exact parallelRaw_accessible_right left right history component active
    · apply Acc.intro
      intro after continues
      rcases continues with ⟨query, reply, responds, rfl⟩
      let projection := projectParallel history
      cases activeEqual : projection.active with
      | none =>
          exact False.elim (Part.notMem_none _ (by
            simpa only [parallelRaw, projection, activeEqual] using responds))
      | some side =>
          cases side with
          | left =>
              cases leftEqual : projection.left with
              | none =>
                  exact False.elim (Part.notMem_none _ (by
                    simpa only [parallelRaw, projection, activeEqual, leftEqual]
                      using responds))
              | some component =>
                  by_cases outerEqual : history.lastOuter =
                      Sum.inl component.lastOuter
                  · exact (activeLeft ⟨component, activeEqual, leftEqual,
                      outerEqual⟩).elim

                  · exact False.elim (Part.notMem_none _ (by
                      simpa only [parallelRaw, projection, activeEqual,
                        leftEqual, dif_neg outerEqual] using responds))
          | right =>
              cases rightEqual : projection.right with
              | none =>
                  exact False.elim (Part.notMem_none _ (by
                    simpa only [parallelRaw, projection, activeEqual, rightEqual]
                      using responds))
              | some component =>
                  by_cases outerEqual : history.lastOuter =
                      Sum.inr component.lastOuter
                  · exact (activeRight ⟨component, activeEqual, rightEqual,
                      outerEqual⟩).elim
                  · exact False.elim (Part.notMem_none _ (by
                      simpa only [parallelRaw, projection, activeEqual,
                        rightEqual, dif_neg outerEqual] using responds))

/-- Ordered parallel of branch-finite DDCs. -/
noncomputable def parallel
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂) :
    DDC (Interface.parallel A₁ A₂) (Interface.parallel B₁ B₂) :=
  RandomSystems.Ambient.DDC.ofRaw
    (parallelRaw left right) (parallelRaw_complete left right)
    (parallelRaw_branchFinite left right)

private theorem mem_parallel_iff
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (response : DDC.Response history) :
    response ∈ parallel left right history ↔
      DDC.Raw.Admissible (parallelRaw left right) history ∧
        response ∈ parallelRaw left right history :=
  by
    change response ∈ DDC.Raw.canonicalize
        (parallelRaw left right) history ↔ _
    exact DDC.Raw.mem_canonicalize_iff _ _ _

private theorem identity_query_mem_of_lastInput_outer
    {A : Interface.{u, v}} (history : DDC.History A A)
    (admissible : DDC.Raw.Admissible (forwardingRaw A) history)
    (query : A.query) (lastInput : history.lastInput = Sum.inl query) :
    Sum.inl query ∈ forwarding A history := by
  rw [mem_forwarding_with_raw_iff]
  refine ⟨admissible, ?_⟩
  rw [lastInput]

private theorem admissible_lastOuter_eq_of_lastInput_outer
    {A B : Interface.{u, v}} {raw : DDC.Raw A B}
    {history : DDC.History A B}
    (admissible : DDC.Raw.Admissible raw history) {query : A.query}
    (lastInput : history.lastInput = Sum.inl query) :
    history.lastOuter = query := by
  induction admissible with
  | start outerQuery => simpa using Sum.inl.inj lastInput
  | afterInner prior responds reply inductionHypothesis =>
      simp at lastInput
  | afterOuter prior responds outerQuery inductionHypothesis =>
      have equal : (Sum.inl outerQuery : DDC.History.Input A B) =
          Sum.inl query := by simpa using lastInput
      simpa using Sum.inl.inj equal

private theorem not_mem_forwardingRaw_of_lastInput_inner_local
    (A : Interface.{u, v}) (history : DDC.History A A)
    (inner : DDC.History.InnerReply A) (equal : history.lastInput = Sum.inr inner)
    (query : A.query) :
    ¬ Sum.inl query ∈ forwardingRaw A history := by
  intro responds
  have table := (mem_forwardingRaw_iff history _).mp responds
  rw [equal] at table
  simp at table

private theorem identity_lastInput_eq_of_query_mem
    {A : Interface.{u, v}} (history : DDC.History A A)
    (admissible : DDC.Raw.Admissible (forwardingRaw A) history)
    (query : A.query) (queryResponds : Sum.inl query ∈ forwarding A history) :
    history.lastInput = Sum.inl query := by
  classical
  have rawQuery := (mem_forwarding_with_raw_iff A history _).mp queryResponds |>.2
  induction admissible with
  | start outerQuery =>
      have queryEqual : query = outerQuery := by
        simpa using rawQuery
      subst query
      simp
  | @afterInner previous innerQuery prior responds reply inductionHypothesis =>
      simp at rawQuery
  | @afterOuter previous prior reply responds outerQuery inductionHypothesis =>
      have queryEqual : query = outerQuery := by
        simpa using rawQuery
      subst query
      simp

private theorem identity_reply_mem_afterInner
    {A : Interface.{u, v}} (history : DDC.History A A)
    (admissible : DDC.Raw.Admissible (forwardingRaw A) history)
    (query : A.query) (queryResponds : Sum.inl query ∈ forwarding A history)
    (reply : Option (A.answer query)) :
    ∃ equal : query = history.lastOuter,
      Sum.inr (equal ▸ reply) ∈ forwarding A
        (history.snocInner query reply) := by
  classical
  have rawQuery := (mem_forwarding_with_raw_iff A history _).mp queryResponds |>.2
  have inputEqual :=
    identity_lastInput_eq_of_query_mem history admissible query queryResponds
  have queryEqual : query = history.lastOuter :=
    (admissible_lastOuter_eq_of_lastInput_outer admissible inputEqual).symm
  refine ⟨queryEqual, ?_⟩
  rw [mem_forwarding_with_raw_iff]
  refine ⟨.afterInner admissible
      ((mem_forwardingRaw_iff history _).mpr rawQuery) reply, ?_⟩
  simp [queryEqual]

/-- The literal mathematical response table of forwarding at one complete
received history. -/
private def ForwardingResponse {A : Interface.{u, v}}
    (history : DDC.History A A) (response : DDC.Response history) :
    Prop :=
  match history.lastInput with
  | Sum.inl query => response = Sum.inl query
  | Sum.inr ⟨query, reply⟩ =>
      ∃ equal : query = history.lastOuter,
        response = Sum.inr (equal ▸ reply)

private theorem mem_forwardingRaw_table_iff
    {A : Interface.{u, v}} (history : DDC.History A A)
    (response : DDC.Response history) :
    response ∈ forwardingRaw A history ↔
      ForwardingResponse history response := by
  simpa only [ForwardingResponse] using
    mem_forwardingRaw_iff history response

private theorem ForwardingResponse.unique
    {A : Interface.{u, v}} {history : DDC.History A A}
    {left right : DDC.Response history}
    (leftForwards : ForwardingResponse history left)
    (rightForwards : ForwardingResponse history right) : left = right := by
  cases inputEqual : history.lastInput with
  | inl query =>
      have leftEqual : left = Sum.inl query := by
        simpa [ForwardingResponse, inputEqual] using leftForwards
      have rightEqual : right = Sum.inl query := by
        simpa [ForwardingResponse, inputEqual] using rightForwards
      exact leftEqual.trans rightEqual.symm
  | inr inner =>
      rcases inner with ⟨query, reply⟩
      obtain ⟨leftQueryEqual, leftEqual⟩ :
          ∃ equal : query = history.lastOuter,
            left = Sum.inr (equal ▸ reply) := by
        simpa [ForwardingResponse, inputEqual] using leftForwards

      obtain ⟨rightQueryEqual, rightEqual⟩ :
          ∃ equal : query = history.lastOuter,
            right = Sum.inr (equal ▸ reply) := by
        simpa [ForwardingResponse, inputEqual] using rightForwards
      exact leftEqual.trans rightEqual.symm

private theorem activeLeft_snocOuter_lastInput
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)) (query : A₁.query)
    (component : DDC.History A₁ B₁)
    (active : ActiveLeft (history.snocOuter (Sum.inl query)) component) :
    component.lastInput = Sum.inl query := by
  unfold ActiveLeft at active
  rw [projectParallel_snocOuter_left] at active
  simp only [extendParallelProjection] at active
  cases previousEqual : (projectParallel history).left with
  | none =>
      simp [previousEqual, appendOuter] at active
      rw [← active.1]
      simp
  | some previous =>
      simp [previousEqual, appendOuter] at active
      rw [← active.1]
      simp

private theorem activeRight_snocOuter_lastInput
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)) (query : A₂.query)
    (component : DDC.History A₂ B₂)
    (active : ActiveRight (history.snocOuter (Sum.inr query)) component) :
    component.lastInput = Sum.inl query := by
  unfold ActiveRight at active
  rw [projectParallel_snocOuter_right] at active
  simp only [extendParallelProjection] at active
  cases previousEqual : (projectParallel history).right with
  | none =>
      simp [previousEqual, appendOuter] at active
      rw [← active.1]
      simp
  | some previous =>
      simp [previousEqual, appendOuter] at active
      rw [← active.1]
      simp

private theorem response_iff_of_mem_and_forwarding
    {A : Interface.{u, v}} {history : DDC.History A A}
    {raw : DDC.Raw A A} {expected response : DDC.Response history}
    (expectedMem : expected ∈ raw history)
    (expectedForwards : ForwardingResponse history expected) :
    response ∈ raw history ↔ ForwardingResponse history response := by
  constructor
  · intro membership
    have equal : response = expected := Part.mem_unique membership expectedMem
    exact equal ▸ expectedForwards
  · intro forwards
    have equal : response = expected := forwards.unique expectedForwards
    exact equal.symm ▸ expectedMem

private theorem query_eq_lastOuter_of_forwarding
    {A : Interface.{u, v}} {raw : DDC.Raw A A}
    {history : DDC.History A A} {query : A.query}
    (admissible : DDC.Raw.Admissible raw history)
    (forwards : ForwardingResponse history (Sum.inl query)) :
    query = history.lastOuter := by
  cases inputEqual : history.lastInput with
  | inl outerQuery =>
      have queryEqual : query = outerQuery := by
        simpa [ForwardingResponse, inputEqual] using forwards
      exact queryEqual.trans
        (admissible_lastOuter_eq_of_lastInput_outer admissible inputEqual).symm
  | inr inner =>
      rcases inner with ⟨innerQuery, reply⟩
      obtain ⟨equal, impossible⟩ :
          ∃ equal : innerQuery = history.lastOuter,
            (Sum.inl query : DDC.Response history) =
              Sum.inr (equal ▸ reply) := by
        simp [ForwardingResponse, inputEqual] at forwards
      cases impossible

private theorem parallel_forwarding_response_iff
    {A B : Interface.{u, v}}
    {history : DDC.History (Interface.parallel A B)
      (Interface.parallel A B)}
    (admissible : DDC.Raw.Admissible
      (parallelRaw (forwarding A) (forwarding B)) history)
    (response : DDC.Response history) :
    response ∈ parallelRaw (forwarding A) (forwarding B) history ↔
      ForwardingResponse history response := by
  induction admissible with
  | start outerQuery =>
      cases outerQuery with
      | inl query =>
          let component := DDC.History.singleton (B := A) query
          have active : ActiveLeft

              (DDC.History.singleton
                (B := Interface.parallel A B)
                (Sum.inl query : (Interface.parallel A B).query)) component :=
            ⟨rfl, rfl, rfl⟩
          have componentAdmissible : DDC.Raw.Admissible
              (forwardingRaw A) component := .start query
          have componentResponds : Sum.inl query ∈ forwarding A component :=
            identity_query_mem_of_lastInput_outer component
              componentAdmissible query (by simp [component])
          have expectedMem : Sum.inl (Sum.inl query) ∈
              parallelRaw (forwarding A) (forwarding B)
                (DDC.History.singleton
                  (B := Interface.parallel A B) (Sum.inl query)) :=
            (mem_parallelRaw_left_iff _ _ _ component active _).mpr
              ⟨Sum.inl query, componentResponds, rfl⟩
          apply response_iff_of_mem_and_forwarding expectedMem
          simp [ForwardingResponse]
          rfl
      | inr query =>
          let component := DDC.History.singleton (B := B) query
          have active : ActiveRight
              (DDC.History.singleton
                (B := Interface.parallel A B)
                (Sum.inr query : (Interface.parallel A B).query)) component :=
            ⟨rfl, rfl, rfl⟩
          have componentAdmissible : DDC.Raw.Admissible
              (forwardingRaw B) component := .start query
          have componentResponds : Sum.inl query ∈ forwarding B component :=
            identity_query_mem_of_lastInput_outer component
              componentAdmissible query (by simp [component])
          have expectedMem : Sum.inl (Sum.inr query) ∈
              parallelRaw (forwarding A) (forwarding B)
                (DDC.History.singleton
                  (B := Interface.parallel A B) (Sum.inr query)) :=
            (mem_parallelRaw_right_iff _ _ _ component active _).mpr
              ⟨Sum.inl query, componentResponds, rfl⟩
          apply response_iff_of_mem_and_forwarding expectedMem
          simp [ForwardingResponse]
          rfl
  | @afterOuter previous prior outerReply responds outerQuery
      inductionHypothesis =>
      have valid := parallelRaw_admissible_projection
        (forwarding A) (forwarding B)
        (.afterOuter prior responds outerQuery)
      cases outerQuery with
      | inl query =>
          obtain ⟨component, active⟩ := valid.activeLeftPresent (by
            rw [projectParallel_snocOuter_left]
            simp [extendParallelProjection])
          have componentAdmissible :=
            valid.leftAdmissible component active.2.1
          have componentRawAdmissible : DDC.Raw.Admissible
              (forwardingRaw A) component :=
            (admissible_forwardingRaw_iff component).mpr componentAdmissible
          have componentResponds : Sum.inl query ∈ forwarding A component :=
            identity_query_mem_of_lastInput_outer component
              componentRawAdmissible query
              (activeLeft_snocOuter_lastInput previous query component active)
          have expectedMem : Sum.inl (Sum.inl query) ∈
              parallelRaw (forwarding A) (forwarding B)
                (previous.snocOuter (Sum.inl query)) :=
            (mem_parallelRaw_left_iff _ _ _ component active _).mpr
              ⟨Sum.inl query, componentResponds, rfl⟩
          apply response_iff_of_mem_and_forwarding expectedMem
          simp [ForwardingResponse]
          rfl
      | inr query =>
          obtain ⟨component, active⟩ := valid.activeRightPresent (by
            rw [projectParallel_snocOuter_right]
            simp [extendParallelProjection])
          have componentAdmissible :=
            valid.rightAdmissible component active.2.1
          have componentRawAdmissible : DDC.Raw.Admissible
              (forwardingRaw B) component :=
            (admissible_forwardingRaw_iff component).mpr componentAdmissible
          have componentResponds : Sum.inl query ∈ forwarding B component :=
            identity_query_mem_of_lastInput_outer component
              componentRawAdmissible query
              (activeRight_snocOuter_lastInput previous query component active)
          have expectedMem : Sum.inl (Sum.inr query) ∈
              parallelRaw (forwarding A) (forwarding B)
                (previous.snocOuter (Sum.inr query)) :=
            (mem_parallelRaw_right_iff _ _ _ component active _).mpr
              ⟨Sum.inl query, componentResponds, rfl⟩
          apply response_iff_of_mem_and_forwarding expectedMem
          simp [ForwardingResponse]
          rfl
  | @afterInner previous jointQuery prior responds reply inductionHypothesis =>
      have priorForwards :=
        (inductionHypothesis (Sum.inl jointQuery)).mp responds
      have jointQueryEqual : jointQuery = previous.lastOuter :=
        query_eq_lastOuter_of_forwarding prior priorForwards
      have valid := parallelRaw_admissible_projection
        (forwarding A) (forwarding B) prior
      obtain ⟨side, activeEqual⟩ :=
        parallelRaw_admissible_activeSide (forwarding A) (forwarding B) prior
      cases side with
      | left =>
          obtain ⟨component, active⟩ := valid.activeLeftPresent activeEqual
          obtain ⟨componentResponse, componentResponds, taggedEqual⟩ :=
            (mem_parallelRaw_left_iff _ _ previous component active
              (Sum.inl jointQuery)).mp responds
          cases componentResponse with
          | inr componentReply =>
              simp [tagLeftResponse] at taggedEqual
          | inl componentQuery =>
              have queryTagEqual : jointQuery = Sum.inl componentQuery := by
                simpa [tagLeftResponse] using taggedEqual.symm
              cases queryTagEqual
              have componentAdmissible :=
                valid.leftAdmissible component active.2.1
              have componentRawAdmissible : DDC.Raw.Admissible
                  (forwardingRaw A) component :=
                (admissible_forwardingRaw_iff component).mpr componentAdmissible
              obtain ⟨componentQueryEqual, componentReplyResponds⟩ :=
                identity_reply_mem_afterInner component componentRawAdmissible
                  componentQuery componentResponds reply
              let nextComponent := component.snocInner componentQuery reply
              have nextActive : ActiveLeft
                  (previous.snocInner (Sum.inl componentQuery) reply)
                  nextComponent := by
                refine ⟨?_, ?_, ?_⟩
                · rw [projectParallel_snocInner_left]
                  simp [extendParallelProjection, active.1]
                · rw [projectParallel_snocInner_left]
                  simp [extendParallelProjection, active.1, active.2.1,
                    nextComponent]
                · simpa [nextComponent] using active.2.2
              let expected : DDC.Response
                  (previous.snocInner (Sum.inl componentQuery) reply) :=
                Sum.inr (jointQueryEqual ▸ reply)
              have expectedMem : expected ∈
                  parallelRaw (forwarding A) (forwarding B)
                    (previous.snocInner (Sum.inl componentQuery) reply) := by
                apply (mem_parallelRaw_left_iff _ _ _ nextComponent
                  nextActive expected).mpr
                refine ⟨Sum.inr (componentQueryEqual ▸ reply),
                  componentReplyResponds, ?_⟩
                apply congrArg Sum.inr
                apply eq_of_heq
                have leftToComponent :
                    (cast (congrArg (fun selected =>
                        Option ((Interface.parallel A B).answer selected))
                      nextActive.2.2.symm)
                      (componentQueryEqual ▸ reply)) ≍
                      (componentQueryEqual ▸ reply) := cast_heq _ _
                have componentToReply :
                    (componentQueryEqual ▸ reply) ≍ reply :=
                  eqRec_heq (φ := fun selected => Option (A.answer selected))
                    componentQueryEqual reply
                have rightToReply :
                    (jointQueryEqual ▸ reply) ≍ reply :=
                  eqRec_heq (φ := fun selected =>
                    Option ((Interface.parallel A B).answer selected))
                    jointQueryEqual reply
                exact leftToComponent.trans
                  (componentToReply.trans rightToReply.symm)
              apply response_iff_of_mem_and_forwarding expectedMem
              simp [expected, ForwardingResponse]
              exact ⟨jointQueryEqual, rfl⟩
      | right =>
          obtain ⟨component, active⟩ := valid.activeRightPresent activeEqual
          obtain ⟨componentResponse, componentResponds, taggedEqual⟩ :=
            (mem_parallelRaw_right_iff _ _ previous component active
              (Sum.inl jointQuery)).mp responds
          cases componentResponse with
          | inl componentQuery =>
              have queryTagEqual : jointQuery = Sum.inr componentQuery := by
                simpa [tagRightResponse] using taggedEqual.symm
              cases queryTagEqual
              have componentAdmissible :=
                valid.rightAdmissible component active.2.1
              have componentRawAdmissible : DDC.Raw.Admissible
                  (forwardingRaw B) component :=
                (admissible_forwardingRaw_iff component).mpr componentAdmissible
              obtain ⟨componentQueryEqual, componentReplyResponds⟩ :=
                identity_reply_mem_afterInner component componentRawAdmissible
                  componentQuery componentResponds reply
              let nextComponent := component.snocInner componentQuery reply
              have nextActive : ActiveRight
                  (previous.snocInner (Sum.inr componentQuery) reply)
                  nextComponent := by
                refine ⟨?_, ?_, ?_⟩
                · rw [projectParallel_snocInner_right]
                  simp [extendParallelProjection, active.1]
                · rw [projectParallel_snocInner_right]
                  simp [extendParallelProjection, active.1, active.2.1,
                    nextComponent]
                · simpa [nextComponent] using active.2.2
              let expected : DDC.Response
                  (previous.snocInner (Sum.inr componentQuery) reply) :=
                Sum.inr (jointQueryEqual ▸ reply)
              have expectedMem : expected ∈
                  parallelRaw (forwarding A) (forwarding B)
                    (previous.snocInner (Sum.inr componentQuery) reply) := by
                apply (mem_parallelRaw_right_iff _ _ _ nextComponent
                  nextActive expected).mpr
                refine ⟨Sum.inr (componentQueryEqual ▸ reply),
                  componentReplyResponds, ?_⟩
                apply congrArg Sum.inr
                apply eq_of_heq
                have leftToComponent :
                    (cast (congrArg (fun selected =>
                        Option ((Interface.parallel A B).answer selected))
                      nextActive.2.2.symm)
                      (componentQueryEqual ▸ reply)) ≍
                      (componentQueryEqual ▸ reply) := cast_heq _ _
                have componentToReply :
                    (componentQueryEqual ▸ reply) ≍ reply :=
                  eqRec_heq (φ := fun selected => Option (B.answer selected))
                    componentQueryEqual reply
                have rightToReply :
                    (jointQueryEqual ▸ reply) ≍ reply :=
                  eqRec_heq (φ := fun selected =>
                    Option ((Interface.parallel A B).answer selected))
                    jointQueryEqual reply
                exact leftToComponent.trans
                  (componentToReply.trans rightToReply.symm)
              apply response_iff_of_mem_and_forwarding expectedMem
              simp [expected, ForwardingResponse]
              exact ⟨jointQueryEqual, rfl⟩
          | inr componentReply =>
              simp [tagRightResponse] at taggedEqual

private theorem parallel_forwarding_admissible
    {A B : Interface.{u, v}}
    {history : DDC.History (Interface.parallel A B)
      (Interface.parallel A B)}
    (admissible : DDC.Raw.Admissible
      (parallelRaw (forwarding A) (forwarding B)) history) :
    DDC.Raw.Admissible (forwardingRaw (Interface.parallel A B)) history := by
  induction admissible with
  | start query => exact .start query
  | @afterInner previous query prior responds reply inductionHypothesis =>
      have forwards :=
        (parallel_forwarding_response_iff prior (Sum.inl query)).mp responds
      have forwardingResponds :=
        (mem_forwardingRaw_table_iff previous (Sum.inl query)).mpr forwards
      exact .afterInner inductionHypothesis forwardingResponds reply
  | @afterOuter previous prior reply responds query inductionHypothesis =>
      have forwards :=
        (parallel_forwarding_response_iff prior (Sum.inr reply)).mp responds
      have forwardingResponds :=
        (mem_forwardingRaw_table_iff previous (Sum.inr reply)).mpr forwards
      exact .afterOuter inductionHypothesis forwardingResponds query

private theorem forwarding_admissible_to_parallel
    {A B : Interface.{u, v}}
    {history : DDC.History (Interface.parallel A B)
      (Interface.parallel A B)}

    (admissible : DDC.Raw.Admissible
      (forwardingRaw (Interface.parallel A B)) history) :
    DDC.Raw.Admissible
      (parallelRaw (forwarding A) (forwarding B)) history := by
  induction admissible with
  | start query => exact .start query
  | @afterInner previous query prior responds reply inductionHypothesis =>
      have forwards :=
        (mem_forwardingRaw_table_iff previous (Sum.inl query)).mp responds
      have parallelResponds :=
        (parallel_forwarding_response_iff inductionHypothesis
          (Sum.inl query)).mpr forwards
      exact .afterInner inductionHypothesis parallelResponds reply
  | @afterOuter previous prior reply responds query inductionHypothesis =>
      have forwards :=
        (mem_forwardingRaw_table_iff previous (Sum.inr reply)).mp responds
      have parallelResponds :=
        (parallel_forwarding_response_iff inductionHypothesis
          (Sum.inr reply)).mpr forwards
      exact .afterOuter inductionHypothesis parallelResponds query

/-- Ordered parallel preserves component forwarding exactly. -/
@[simp]
theorem parallel_forwarding_eq (A B : Interface.{u, v}) :
    parallel (forwarding A) (forwarding B) =
      forwarding (Interface.parallel A B) := by
  apply DDC.ext
  intro history response
  rw [mem_parallel_iff, mem_forwarding_with_raw_iff]
  constructor
  · rintro ⟨parallelAdmissible, parallelResponds⟩
    have forwardingAdmissible :=
      parallel_forwarding_admissible parallelAdmissible
    have forwards :=
      (parallel_forwarding_response_iff parallelAdmissible response).mp
        parallelResponds
    exact ⟨forwardingAdmissible, forwards⟩
  · rintro ⟨forwardingAdmissible, forwardingResponds⟩
    have parallelAdmissible :=
      forwarding_admissible_to_parallel forwardingAdmissible
    exact ⟨parallelAdmissible,
      (parallel_forwarding_response_iff parallelAdmissible response).mpr
        forwardingResponds⟩


private def parallelLeftAnswer
    {A B : Interface.{u, v}} (system : DDS A)
    (history : _root_.RandomSystems.Ambient.History (Interface.parallel A B)) (query : A.query)
    (equal : history.last = Sum.inl query) : Option (A.answer query) :=
  cast (congrArg (fun selected => Option (A.answer selected))
    (DDS.last_leftHistory history query equal))
    (system (DDS.leftHistory history query equal))

private def parallelRightAnswer
    {A B : Interface.{u, v}} (system : DDS B)
    (history : _root_.RandomSystems.Ambient.History (Interface.parallel A B)) (query : B.query)
    (equal : history.last = Sum.inr query) : Option (B.answer query) :=
  cast (congrArg (fun selected => Option (B.answer selected))
    (DDS.last_rightHistory history query equal))
    (system (DDS.rightHistory history query equal))

private theorem DDS_parallel_cast_left
    {A B : Interface.{u, v}} (left : DDS A) (right : DDS B)
    (history : _root_.RandomSystems.Ambient.History (Interface.parallel A B)) (query : A.query)
    (equal : history.last = Sum.inl query) :
    cast (congrArg (fun selected =>
        Option ((Interface.parallel A B).answer selected)) equal)
        (DDS.parallel left right history) =
      parallelLeftAnswer left history query equal := by
  exact DDS.parallel_apply_left left right history query equal

private theorem DDS_parallel_cast_right
    {A B : Interface.{u, v}} (left : DDS A) (right : DDS B)
    (history : _root_.RandomSystems.Ambient.History (Interface.parallel A B)) (query : B.query)
    (equal : history.last = Sum.inr query) :
    cast (congrArg (fun selected =>
        Option ((Interface.parallel A B).answer selected)) equal)
        (DDS.parallel left right history) =
      parallelRightAnswer right history query equal := by
  exact DDS.parallel_apply_right left right history query equal

private theorem DDS_apply_heq_of_history_eq
    {A : Interface.{u, v}} (system : DDS A) {left right : _root_.RandomSystems.Ambient.History A}
    (equal : left = right) : system left ≍ system right := by
  subst right
  rfl

private theorem innerReplyAt_parallel_left
    {A B : Interface.{u, v}} (left : DDS A) (right : DDS B)
    (prior : List (Interface.parallel A B).query) (query : A.query) :
    innerReplyAt (DDS.parallel left right) prior (Sum.inl query) =
      innerReplyAt left (parallelLeftQueries prior) query := by
  change List (A.query ⊕ B.query) at prior
  have lastEqual :
      (DDC.Internal.innerHistory (A := Interface.parallel A B) prior
        (Sum.inl query)).last = Sum.inl query :=
    by simp [DDC.Internal.innerHistory, History.last]
  unfold innerReplyAt
  apply eq_of_heq
  refine (cast_heq _ _).trans ?_
  have parallelHeq :
      DDS.parallel left right
          (DDC.Internal.innerHistory (A := Interface.parallel A B) prior (Sum.inl query)) ≍
        parallelLeftAnswer left
          (DDC.Internal.innerHistory (A := Interface.parallel A B) prior (Sum.inl query)) query
          lastEqual := by
    have evaluated := DDS_parallel_cast_left left right
      (DDC.Internal.innerHistory (A := Interface.parallel A B) prior (Sum.inl query)) query
      lastEqual
    exact (cast_heq _ _).symm.trans evaluated.heq
  refine parallelHeq.trans ?_
  unfold parallelLeftAnswer
  refine (cast_heq _ _).trans ?_
  have historiesEqual :
      DDS.leftHistory
          (DDC.Internal.innerHistory (A := Interface.parallel A B) prior
            (Sum.inl query)) query
            lastEqual =
        DDC.Internal.innerHistory (parallelLeftQueries prior) query := by
    apply _root_.RandomSystems.Ambient.History.ext
    change parallelLeftQueries (prior ++ [Sum.inl query]) =
      parallelLeftQueries prior ++ [query]
    unfold parallelLeftQueries
    apply Eq.trans List.filterMap_append
    rfl
  exact (DDS_apply_heq_of_history_eq left historiesEqual).trans
    (cast_heq _ _).symm

private theorem innerReplyAt_parallel_right
    {A B : Interface.{u, v}} (left : DDS A) (right : DDS B)
    (prior : List (Interface.parallel A B).query) (query : B.query) :
    innerReplyAt (DDS.parallel left right) prior (Sum.inr query) =
      innerReplyAt right (parallelRightQueries prior) query := by
  change List (A.query ⊕ B.query) at prior
  have lastEqual :
      (DDC.Internal.innerHistory (A := Interface.parallel A B) prior
        (Sum.inr query)).last = Sum.inr query :=
    by simp [DDC.Internal.innerHistory, History.last]
  unfold innerReplyAt
  apply eq_of_heq
  refine (cast_heq _ _).trans ?_
  have parallelHeq :
      DDS.parallel left right
          (DDC.Internal.innerHistory (A := Interface.parallel A B) prior (Sum.inr query)) ≍
        parallelRightAnswer right
          (DDC.Internal.innerHistory (A := Interface.parallel A B) prior (Sum.inr query)) query
          lastEqual := by
    have evaluated := DDS_parallel_cast_right left right
      (DDC.Internal.innerHistory (A := Interface.parallel A B) prior (Sum.inr query)) query
      lastEqual
    exact (cast_heq _ _).symm.trans evaluated.heq
  refine parallelHeq.trans ?_
  unfold parallelRightAnswer
  refine (cast_heq _ _).trans ?_
  have historiesEqual :
      DDS.rightHistory
          (DDC.Internal.innerHistory (A := Interface.parallel A B) prior
            (Sum.inr query)) query
            lastEqual =
        DDC.Internal.innerHistory (parallelRightQueries prior) query := by
    apply _root_.RandomSystems.Ambient.History.ext
    change parallelRightQueries (prior ++ [Sum.inr query]) =
      parallelRightQueries prior ++ [query]
    unfold parallelRightQueries
    apply Eq.trans List.filterMap_append
    rfl
  exact (DDS_apply_heq_of_history_eq right historiesEqual).trans
    (cast_heq _ _).symm

private def sideOfOuterQuery
    {A₁ A₂ : Interface.{u, v}} :
    (Interface.parallel A₁ A₂).query → ParallelSide
  | Sum.inl _ => .left
  | Sum.inr _ => .right

private def lastOuterQuery
    {Q : Type u} (current : Q) (remaining : List Q) : Q :=
  (current :: remaining).getLast (by simp)

@[simp]
private theorem lastOuterQuery_nil
    {Q : Type u} (current : Q) :
    lastOuterQuery current [] = current := rfl

@[simp]
private theorem lastOuterQuery_cons
    {Q : Type u} (current next : Q) (remaining : List Q) :
    lastOuterQuery current (next :: remaining) =
      lastOuterQuery next remaining := by
  simp [lastOuterQuery]

private def tagLeftInnerReply
    {A₁ A₂ : Interface.{u, v}} :
    DDC.History.InnerReply A₁ → DDC.History.InnerReply (Interface.parallel A₁ A₂)
  | ⟨query, reply⟩ => ⟨Sum.inl query, reply⟩

private def tagRightInnerReply
    {A₁ A₂ : Interface.{u, v}} :
    DDC.History.InnerReply A₂ → DDC.History.InnerReply (Interface.parallel A₁ A₂)
  | ⟨query, reply⟩ => ⟨Sum.inr query, reply⟩

private theorem leftQueries_append_left
    {A B : Interface.{u, v}} (prior : List (A.query ⊕ B.query))
    (query : A.query) :
    parallelLeftQueries (prior ++ [Sum.inl query]) =
      parallelLeftQueries prior ++ [query] := by
  unfold parallelLeftQueries
  apply Eq.trans List.filterMap_append
  rfl

private theorem leftQueries_append_right
    {A B : Interface.{u, v}} (prior : List (A.query ⊕ B.query))
    (query : B.query) :
    parallelLeftQueries (prior ++ [Sum.inr query]) =
      parallelLeftQueries prior := by
  unfold parallelLeftQueries
  apply Eq.trans List.filterMap_append
  exact List.append_nil _

private theorem rightQueries_append_left
    {A B : Interface.{u, v}} (prior : List (A.query ⊕ B.query))
    (query : A.query) :
    parallelRightQueries (prior ++ [Sum.inl query]) =
      parallelRightQueries prior := by
  unfold parallelRightQueries
  apply Eq.trans List.filterMap_append
  exact List.append_nil _

private theorem rightQueries_append_right
    {A B : Interface.{u, v}} (prior : List (A.query ⊕ B.query))
    (query : B.query) :
    parallelRightQueries (prior ++ [Sum.inr query]) =
      parallelRightQueries prior ++ [query] := by
  unfold parallelRightQueries
  apply Eq.trans List.filterMap_append
  rfl

@[simp]
private theorem leftQueries_cons_left
    {A B : Interface.{u, v}} (query : A.query)
    (remaining : List (A.query ⊕ B.query)) :
    parallelLeftQueries (Sum.inl query :: remaining) =
      query :: parallelLeftQueries remaining := by
  rfl

@[simp]
private theorem leftQueries_cons_right
    {A B : Interface.{u, v}} (query : B.query)
    (remaining : List (A.query ⊕ B.query)) :
    parallelLeftQueries (Sum.inr query :: remaining) =

      parallelLeftQueries remaining := by
  rfl

@[simp]
private theorem rightQueries_cons_left
    {A B : Interface.{u, v}} (query : A.query)
    (remaining : List (A.query ⊕ B.query)) :
    parallelRightQueries (Sum.inl query :: remaining) =
      parallelRightQueries remaining := by
  rfl

@[simp]
private theorem rightQueries_cons_right
    {A B : Interface.{u, v}} (query : B.query)
    (remaining : List (A.query ⊕ B.query)) :
    parallelRightQueries (Sum.inr query :: remaining) =
      query :: parallelRightQueries remaining := by
  rfl

private theorem mem_parallel_active_left_iff
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₁ B₁)
    (active : ActiveLeft history component)
    (admissible : DDC.Raw.Admissible (parallelRaw left right) history)
    (response : DDC.Response history) :
    response ∈ parallel left right history ↔
      ∃ componentResponse ∈ left component,
        tagLeftResponse history component active.2.2 componentResponse =
          response := by
  rw [mem_parallel_iff, mem_parallelRaw_left_iff left right history component
    active response]
  simp only [admissible, true_and]

private theorem mem_parallel_active_right_iff
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₂ B₂)
    (active : ActiveRight history component)
    (admissible : DDC.Raw.Admissible (parallelRaw left right) history)
    (response : DDC.Response history) :
    response ∈ parallel left right history ↔
      ∃ componentResponse ∈ right component,
        tagRightResponse history component active.2.2 componentResponse =
          response := by
  rw [mem_parallel_iff, mem_parallelRaw_right_iff left right history component
    active response]
  simp only [admissible, true_and]

private def LeftGraphProjection
    {A₁ A₂ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    (leftConverter : DDC A₁ B₁) (leftSystem : DDS B₁)
    (current : (Interface.parallel A₁ A₂).query)
    (leftState : Option (DDC.History A₁ B₁))
    (leftPrior : List B₁.query)
    (remainingOuter : List (Interface.parallel A₁ A₂).query)
    (jointFinal : DDC.History.InnerReply (Interface.parallel A₁ A₂)) : Prop :=
  ∃ first remaining start inputs responses final,
    parallelLeftQueries (current :: remainingOuter) =
        first :: remaining ∧
      (match current with
      | Sum.inl outerQuery =>
          first = outerQuery ∧ leftState = some start
      | Sum.inr _ => start = appendOuter leftState first) ∧
      Attachment.CompatibleFrom leftConverter leftSystem start leftPrior remaining
        inputs responses final ∧
      jointFinal = tagLeftInnerReply final

private def RightGraphProjection
    {A₁ A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (rightConverter : DDC A₂ B₂) (rightSystem : DDS B₂)
    (current : (Interface.parallel A₁ A₂).query)
    (rightState : Option (DDC.History A₂ B₂))
    (rightPrior : List B₂.query)
    (remainingOuter : List (Interface.parallel A₁ A₂).query)
    (jointFinal : DDC.History.InnerReply (Interface.parallel A₁ A₂)) : Prop :=
  ∃ first remaining start inputs responses final,
    parallelRightQueries (current :: remainingOuter) =
        first :: remaining ∧
      (match current with
      | Sum.inl _ => start = appendOuter rightState first
      | Sum.inr outerQuery =>
          first = outerQuery ∧ rightState = some start) ∧
      Attachment.CompatibleFrom rightConverter rightSystem start rightPrior remaining
        inputs responses final ∧
      jointFinal = tagRightInnerReply final

private theorem compatibleFrom_parallel_left
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (leftConverter : DDC A₁ B₁) (rightConverter : DDC A₂ B₂)
    (leftSystem : DDS B₁) (rightSystem : DDS B₂)
    {history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {jointPrior : List (Interface.parallel B₁ B₂).query}
    {remainingOuter : List (Interface.parallel A₁ A₂).query}
    {inputs : List (DDC.History.Input (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))}
    {responses : List (Attachment.Response (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))}
    {jointFinal : DDC.History.InnerReply (Interface.parallel A₁ A₂)}
    (compatible : Attachment.CompatibleFrom (parallel leftConverter rightConverter)
      (DDS.parallel leftSystem rightSystem) history jointPrior remainingOuter
      inputs responses jointFinal)
    (current : (Interface.parallel A₁ A₂).query) (lastLeft : A₁.query)
    (finalEqual : lastOuterQuery current remainingOuter = Sum.inl lastLeft)
    (leftState : Option (DDC.History A₁ B₁))
    (activeEqual : (projectParallel history).active =
      some (sideOfOuterQuery current))
    (leftEqual : (projectParallel history).left = leftState)
    (leftPrior : List B₁.query)
    (priorEqual : parallelLeftQueries jointPrior =
      leftPrior) :
    LeftGraphProjection leftConverter leftSystem current leftState leftPrior
      remainingOuter jointFinal := by
  change List (B₁.query ⊕ B₂.query) at jointPrior
  induction compatible generalizing current leftState leftPrior with
  | @innerQuery history jointPrior remainingOuter query tailInputs
      tailResponses jointFinal responds tail inductionHypothesis =>
      change List (B₁.query ⊕ B₂.query) at jointPrior
      have admissible :=
        ((mem_parallel_iff leftConverter rightConverter history
          (Sum.inl query)).mp responds).1
      have valid := parallelRaw_admissible_projection leftConverter
        rightConverter admissible
      cases current with
      | inl currentLeft =>
          have activeLeft : (projectParallel history).active = some .left := by
            simpa [sideOfOuterQuery] using activeEqual
          obtain ⟨component, active⟩ := valid.activeLeftPresent activeLeft
          have leftStateEqual : leftState = some component :=
            leftEqual.symm.trans active.2.1
          obtain ⟨componentResponse, componentResponds, taggedEqual⟩ :=
            (mem_parallel_active_left_iff leftConverter rightConverter history
              component active admissible (Sum.inl query)).mp responds
          cases componentResponse with
          | inr componentReply =>
              simp [tagLeftResponse] at taggedEqual
          | inl componentQuery =>
              have queryEqual : query = Sum.inl componentQuery := by
                simpa [tagLeftResponse] using taggedEqual.symm
              subst query
              let componentReply :=
                innerReplyAt leftSystem leftPrior componentQuery
              have nextActive :
                  (projectParallel (history.snocInner (Sum.inl componentQuery)
                    (innerReplyAt (DDS.parallel leftSystem rightSystem)
                      jointPrior (Sum.inl componentQuery)))).active =
                    some .left := by
                rw [projectParallel_snocInner_left]
                simp [extendParallelProjection, activeLeft]
              have nextLeft :
                  (projectParallel (history.snocInner (Sum.inl componentQuery)
                    (innerReplyAt (DDS.parallel leftSystem rightSystem)
                      jointPrior (Sum.inl componentQuery)))).left =
                    some (component.snocInner componentQuery componentReply) := by
                rw [projectParallel_snocInner_left]
                simp only [extendParallelProjection, activeLeft, active.2.1,
                  Option.map, Option.some.injEq]
                unfold componentReply
                rw [innerReplyAt_parallel_left, priorEqual]
              have nextPrior :
                  parallelLeftQueries
                      (jointPrior ++ [(Sum.inl componentQuery :
                        (Interface.parallel B₁ B₂).query)]) =
                    leftPrior ++ [componentQuery] := by
                calc
                  _ = parallelLeftQueries jointPrior ++ [componentQuery] :=
                    leftQueries_append_left jointPrior componentQuery
                  _ = leftPrior ++ [componentQuery] :=
                    congrArg (fun queries => queries ++ [componentQuery])
                      priorEqual
              obtain ⟨first, remaining, start, componentInputs,
                  componentResponses, final, outerProjection, startProjection,
                  componentCompatible, finalProjection⟩ :=
                inductionHypothesis (Sum.inl currentLeft) finalEqual
                  (some (component.snocInner componentQuery componentReply))
                  nextActive nextLeft (leftPrior ++ [componentQuery]) nextPrior
              refine ⟨first, remaining, component,
                component.lastInput :: componentInputs,
                Sum.inl componentQuery :: componentResponses, final,
                outerProjection, ?_, ?_, finalProjection⟩
              · exact ⟨startProjection.1, leftStateEqual⟩
              · have startEqual : start =
                    component.snocInner componentQuery componentReply :=
                  Option.some.inj startProjection.2.symm
                subst start
                exact Attachment.CompatibleFrom.innerQuery componentResponds
                  componentCompatible
      | inr currentRight =>
          have activeRight : (projectParallel history).active = some .right := by
            simpa [sideOfOuterQuery] using activeEqual
          obtain ⟨component, active⟩ := valid.activeRightPresent activeRight
          obtain ⟨componentResponse, componentResponds, taggedEqual⟩ :=
            (mem_parallel_active_right_iff leftConverter rightConverter history
              component active admissible (Sum.inl query)).mp responds
          cases componentResponse with
          | inr componentReply =>
              simp [tagRightResponse] at taggedEqual
          | inl componentQuery =>
              have queryEqual : query = Sum.inr componentQuery := by
                simpa [tagRightResponse] using taggedEqual.symm
              subst query
              have nextActive :
                  (projectParallel (history.snocInner (Sum.inr componentQuery)
                    (innerReplyAt (DDS.parallel leftSystem rightSystem)
                      jointPrior (Sum.inr componentQuery)))).active =
                    some .right := by
                rw [projectParallel_snocInner_right]
                simp [extendParallelProjection, activeRight]
              have nextLeft :
                  (projectParallel (history.snocInner (Sum.inr componentQuery)
                    (innerReplyAt (DDS.parallel leftSystem rightSystem)
                      jointPrior (Sum.inr componentQuery)))).left = leftState := by
                rw [projectParallel_snocInner_right]
                simp [extendParallelProjection, activeRight, leftEqual]
              have nextPrior :
                  parallelLeftQueries
                      (jointPrior ++ [(Sum.inr componentQuery :
                        (Interface.parallel B₁ B₂).query)]) = leftPrior := by
                exact (leftQueries_append_right jointPrior componentQuery).trans
                  priorEqual
              exact inductionHypothesis (Sum.inr currentRight) finalEqual
                leftState nextActive nextLeft leftPrior nextPrior
  | @outerLast history jointPrior reply responds =>
      cases current with
      | inr currentRight => simp [lastOuterQuery] at finalEqual
      | inl currentLeft =>
          have admissible :=
            ((mem_parallel_iff leftConverter rightConverter history
              (Sum.inr reply)).mp responds).1
          have valid := parallelRaw_admissible_projection leftConverter
            rightConverter admissible
          have activeLeft : (projectParallel history).active = some .left := by
            simpa [sideOfOuterQuery] using activeEqual
          obtain ⟨component, active⟩ := valid.activeLeftPresent activeLeft
          have leftStateEqual : leftState = some component :=
            leftEqual.symm.trans active.2.1
          obtain ⟨componentResponse, componentResponds, taggedEqual⟩ :=
            (mem_parallel_active_left_iff leftConverter rightConverter history
              component active admissible (Sum.inr reply)).mp responds
          cases componentResponse with
          | inl componentQuery =>
              simp [tagLeftResponse] at taggedEqual
          | inr componentReply =>
              refine ⟨currentLeft, [], component, [component.lastInput],
                [Sum.inr ⟨component.lastOuter, componentReply⟩],

                ⟨component.lastOuter, componentReply⟩, ?_,
                ⟨rfl, leftStateEqual⟩,
                Attachment.CompatibleFrom.outerLast componentResponds, ?_⟩
              · rfl

              · unfold tagLeftInnerReply
                apply Sigma.ext active.2.2
                have replyEqual := Sum.inr.inj taggedEqual
                exact replyEqual.symm.heq.trans (cast_heq _ _)
  | @outerNext history jointPrior reply nextOuter remainingOuter tailInputs
      tailResponses jointFinal responds tail inductionHypothesis =>
      have tailFinalEqual : lastOuterQuery nextOuter remainingOuter =
          Sum.inl lastLeft := by
        simpa using finalEqual
      cases current with
      | inr currentRight =>
          cases nextOuter with
          | inl nextLeft =>
              have nextActive :
                  (projectParallel (history.snocOuter (Sum.inl nextLeft))).active =
                    some .left := by
                rw [projectParallel_snocOuter_left]
                simp [extendParallelProjection]
              have nextLeftState :
                  (projectParallel (history.snocOuter (Sum.inl nextLeft))).left =
                    some (appendOuter leftState nextLeft) := by
                rw [projectParallel_snocOuter_left]
                simp [extendParallelProjection, leftEqual]
              obtain ⟨first, remaining, start, componentInputs,
                  componentResponses, final, outerProjection, startProjection,
                  componentCompatible, finalProjection⟩ :=
                inductionHypothesis (Sum.inl nextLeft) tailFinalEqual
                  (some (appendOuter leftState nextLeft)) nextActive
                  nextLeftState leftPrior priorEqual
              refine ⟨first, remaining, start, componentInputs,
                componentResponses, final, ?_, ?_, componentCompatible,
                finalProjection⟩
              · exact outerProjection
              · rcases startProjection with ⟨firstEqual, stateEqual⟩
                subst first
                exact Option.some.inj stateEqual.symm
          | inr nextRight =>
              have nextActive :
                  (projectParallel (history.snocOuter (Sum.inr nextRight))).active =
                    some .right := by
                rw [projectParallel_snocOuter_right]
                simp [extendParallelProjection]
              have nextLeftState :
                  (projectParallel (history.snocOuter (Sum.inr nextRight))).left =
                    leftState := by
                rw [projectParallel_snocOuter_right]
                simp [extendParallelProjection, leftEqual]
              obtain ⟨first, remaining, start, componentInputs,
                  componentResponses, final, outerProjection, startProjection,
                  componentCompatible, finalProjection⟩ :=
                inductionHypothesis (Sum.inr nextRight) tailFinalEqual leftState
                  nextActive nextLeftState leftPrior priorEqual
              exact ⟨first, remaining, start, componentInputs,
                componentResponses, final, outerProjection, startProjection,
                componentCompatible, finalProjection⟩
      | inl currentLeft =>
          have admissible :=
            ((mem_parallel_iff leftConverter rightConverter history
              (Sum.inr reply)).mp responds).1
          have valid := parallelRaw_admissible_projection leftConverter
            rightConverter admissible
          have activeLeft : (projectParallel history).active = some .left := by
            simpa [sideOfOuterQuery] using activeEqual
          obtain ⟨component, active⟩ := valid.activeLeftPresent activeLeft
          have leftStateEqual : leftState = some component :=
            leftEqual.symm.trans active.2.1
          obtain ⟨componentResponse, componentResponds, taggedEqual⟩ :=
            (mem_parallel_active_left_iff leftConverter rightConverter history
              component active admissible (Sum.inr reply)).mp responds
          cases componentResponse with
          | inl componentQuery =>
              simp [tagLeftResponse] at taggedEqual
          | inr componentReply =>
              cases nextOuter with
              | inl nextLeft =>
                  have nextActive :
                      (projectParallel
                        (history.snocOuter (Sum.inl nextLeft))).active =
                        some .left := by
                    rw [projectParallel_snocOuter_left]
                    simp [extendParallelProjection]
                  have nextLeftState :
                      (projectParallel
                        (history.snocOuter (Sum.inl nextLeft))).left =
                        some (component.snocOuter nextLeft) := by
                    rw [projectParallel_snocOuter_left]
                    simp [extendParallelProjection, leftEqual, leftStateEqual,
                      appendOuter]
                  obtain ⟨first, remaining, start, componentInputs,
                      componentResponses, final, outerProjection,
                      startProjection, componentCompatible,
                      finalProjection⟩ :=
                    inductionHypothesis (Sum.inl nextLeft) tailFinalEqual
                      (some (component.snocOuter nextLeft)) nextActive
                      nextLeftState leftPrior priorEqual
                  have firstEqual : first = nextLeft := by
                    exact startProjection.1
                  have startEqual : start = component.snocOuter first := by
                    subst first
                    exact Option.some.inj startProjection.2.symm
                  refine ⟨currentLeft, first :: remaining, component,
                    component.lastInput :: componentInputs,
                    Sum.inr ⟨component.lastOuter, componentReply⟩ ::
                      componentResponses,
                    final, ?_, ⟨rfl, leftStateEqual⟩, ?_, finalProjection⟩
                  · rw [leftQueries_cons_left]
                    exact congrArg (List.cons currentLeft) outerProjection
                  · apply Attachment.CompatibleFrom.outerNext componentResponds
                    simpa [startEqual] using componentCompatible

              | inr nextRight =>
                  have nextActive :
                      (projectParallel
                        (history.snocOuter (Sum.inr nextRight))).active =
                        some .right := by
                    rw [projectParallel_snocOuter_right]
                    simp [extendParallelProjection]
                  have nextLeftState :
                      (projectParallel
                        (history.snocOuter (Sum.inr nextRight))).left =
                        some component := by
                    rw [projectParallel_snocOuter_right]
                    simp [extendParallelProjection, leftEqual, leftStateEqual]
                  obtain ⟨first, remaining, start, componentInputs,
                      componentResponses, final, outerProjection,
                      startProjection, componentCompatible,
                      finalProjection⟩ :=
                    inductionHypothesis (Sum.inr nextRight) tailFinalEqual
                      (some component) nextActive nextLeftState leftPrior
                      priorEqual
                  have startEqual : start = component.snocOuter first := by
                    simpa [appendOuter] using startProjection
                  refine ⟨currentLeft, first :: remaining, component,
                    component.lastInput :: componentInputs,
                    Sum.inr ⟨component.lastOuter, componentReply⟩ ::
                      componentResponses,
                    final, ?_, ⟨rfl, leftStateEqual⟩, ?_, finalProjection⟩
                  · rw [leftQueries_cons_left]
                    exact congrArg (List.cons currentLeft) outerProjection
                  · apply Attachment.CompatibleFrom.outerNext componentResponds
                    simpa [startEqual] using componentCompatible

private theorem compatible_parallel_left
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (leftConverter : DDC A₁ B₁) (rightConverter : DDC A₂ B₂)
    (leftSystem : DDS B₁) (rightSystem : DDS B₂)
    (outerHistory : _root_.RandomSystems.Ambient.History (Interface.parallel A₁ A₂))
    (lastLeft : A₁.query)
    (lastEqual : outerHistory.last = Sum.inl lastLeft)
    (jointTranscript : Attachment.Transcript (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (compatible : Attachment.Compatible (parallel leftConverter rightConverter)
      (DDS.parallel leftSystem rightSystem) outerHistory jointTranscript) :
    ∃ componentTranscript : Attachment.Transcript A₁ B₁,
      Attachment.Compatible leftConverter leftSystem
          (DDS.leftHistory outerHistory lastLeft
            lastEqual)
          componentTranscript ∧
        jointTranscript.final = tagLeftInnerReply componentTranscript.final := by
  let current := outerHistory.head
  let leftState : Option (DDC.History A₁ B₁) :=
    match current with
    | Sum.inl outerQuery => some (DDC.History.singleton outerQuery)
    | Sum.inr _ => none
  have activeEqual :
      (projectParallel
        (DDC.History.singleton (B := Interface.parallel B₁ B₂)
          current)).active = some (sideOfOuterQuery current) := by
    cases current <;> rfl
  have leftEqual :
      (projectParallel
        (DDC.History.singleton (B := Interface.parallel B₁ B₂)
          current)).left = leftState := by
    cases currentEqual : current <;>
      simp [leftState, currentEqual]
  have finalEqual : lastOuterQuery current outerHistory.tail =
      Sum.inl lastLeft := by
    have reconstruct : current :: outerHistory.tail = outerHistory.1 :=
      List.cons_head_tail outerHistory.2
    unfold lastOuterQuery
    change (current :: outerHistory.tail).getLast (by simp) = Sum.inl lastLeft
    exact (List.getLast_congr (by simp) outerHistory.2 reconstruct).trans
      lastEqual
  obtain ⟨first, remaining, start, componentInputs, componentResponses,
      componentFinal, outerProjection, startProjection, componentCompatible,
      finalProjection⟩ :=
    compatibleFrom_parallel_left leftConverter rightConverter leftSystem
      rightSystem compatible current lastLeft finalEqual leftState activeEqual
      leftEqual [] rfl
  have startEqual : start = DDC.History.singleton first := by
    cases currentEqual : current with
    | inl currentLeft =>
        simp only [currentEqual] at startProjection
        rcases startProjection with ⟨firstEqual, stateEqual⟩
        subst first
        exact Option.some.inj (by simpa [leftState, currentEqual] using stateEqual.symm)
    | inr currentRight =>
        simpa [leftState, currentEqual, appendOuter] using startProjection
  let componentOuter : _root_.RandomSystems.Ambient.History A₁ := ⟨first :: remaining, by simp⟩
  have componentOuterEqual : componentOuter =
      DDS.leftHistory outerHistory lastLeft lastEqual := by
    apply _root_.RandomSystems.Ambient.History.ext
    change first :: remaining =
      parallelLeftQueries outerHistory.1
    rw [← outerProjection]
    have reconstruct : current :: outerHistory.tail = outerHistory.1 :=
      List.cons_head_tail outerHistory.2
    exact congrArg parallelLeftQueries reconstruct
  let componentTranscript : Attachment.Transcript A₁ B₁ :=
    { inputs := componentInputs
      responses := componentResponses
      final := componentFinal }
  refine ⟨componentTranscript, ?_, finalProjection⟩
  rw [← componentOuterEqual]
  change Attachment.CompatibleFrom leftConverter leftSystem
    (DDC.History.singleton first) [] remaining componentInputs
      componentResponses componentFinal
  rw [← startEqual]
  exact componentCompatible

private theorem applySystem_parallel_at_left
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (leftConverter : DDC A₁ B₁) (rightConverter : DDC A₂ B₂)
    (leftSystem : DDS B₁) (rightSystem : DDS B₂)
    (outerHistory : _root_.RandomSystems.Ambient.History (Interface.parallel A₁ A₂))
    (lastLeft : A₁.query)
    (lastEqual : outerHistory.last = Sum.inl lastLeft) :
    applySystem (parallel leftConverter rightConverter)
        (DDS.parallel leftSystem rightSystem) outerHistory =
      DDS.parallel (applySystem leftConverter leftSystem)
        (applySystem rightConverter rightSystem) outerHistory := by
  obtain ⟨jointTranscript, jointCompatible⟩ :=
    Attachment.exists_compatible (parallel leftConverter rightConverter)
      (DDS.parallel leftSystem rightSystem) outerHistory
  obtain ⟨componentTranscript, componentCompatible, finalProjection⟩ :=
    compatible_parallel_left leftConverter rightConverter leftSystem
      rightSystem outerHistory lastLeft lastEqual jointTranscript
      jointCompatible
  let componentHistory :=
    DDS.leftHistory outerHistory lastLeft lastEqual
  have componentOutput :
      applySystem leftConverter leftSystem componentHistory =
        selectReply componentHistory.last componentTranscript.final := by
    apply (applySystem_eq_iff leftConverter leftSystem componentHistory _).mpr
    have finalQuery :=
      Attachment.Compatible.final_query_eq_last
        (compatible := componentCompatible)
    exact ⟨componentTranscript, componentCompatible,
      (Attachment.selectReply_heq_second componentHistory.last
        componentTranscript.final finalQuery).symm⟩
  have jointOutput :
      applySystem (parallel leftConverter rightConverter)
          (DDS.parallel leftSystem rightSystem) outerHistory =
        selectReply outerHistory.last jointTranscript.final := by
    apply (applySystem_eq_iff (parallel leftConverter rightConverter)
      (DDS.parallel leftSystem rightSystem) outerHistory _).mpr
    have finalQuery :=
      Attachment.Compatible.final_query_eq_last
        (compatible := jointCompatible)
    exact ⟨jointTranscript, jointCompatible,
      (Attachment.selectReply_heq_second outerHistory.last
        jointTranscript.final finalQuery).symm⟩
  rw [jointOutput]
  let typeEqual := congrArg (fun selected =>
    Option ((Interface.parallel A₁ A₂).answer selected)) lastEqual
  apply (cast_inj typeEqual).mp
  rw [DDS_parallel_cast_left
    (applySystem leftConverter leftSystem)
    (applySystem rightConverter rightSystem) outerHistory lastLeft lastEqual]
  unfold parallelLeftAnswer
  rw [componentOutput]
  have componentFinalEqual :=
    Attachment.Compatible.final_query_eq_last (compatible := componentCompatible)
  have componentQueryEqual : componentTranscript.final.1 = lastLeft :=
    componentFinalEqual.trans
      (DDS.last_leftHistory outerHistory lastLeft
        lastEqual)
  have jointQueryEqual : Sum.inl componentTranscript.final.1 =
      outerHistory.last :=
    (congrArg Sum.inl componentQueryEqual).trans lastEqual.symm
  rw [finalProjection]
  apply eq_of_heq
  have leftHeq :
      cast typeEqual
          (selectReply outerHistory.last
            (tagLeftInnerReply componentTranscript.final)) ≍
        componentTranscript.final.2 :=
    (cast_heq _ _).trans
      (Attachment.selectReply_heq_second outerHistory.last
        (tagLeftInnerReply componentTranscript.final) jointQueryEqual)
  have rightHeq :
      cast (congrArg (fun selected => Option (A₁.answer selected))
          (DDS.last_leftHistory outerHistory lastLeft
            lastEqual))
          (selectReply componentHistory.last componentTranscript.final) ≍
        componentTranscript.final.2 :=
    (cast_heq _ _).trans
      (Attachment.selectReply_heq_second componentHistory.last componentTranscript.final
        componentFinalEqual)
  exact leftHeq.trans rightHeq.symm

private theorem compatibleFrom_parallel_right
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (leftConverter : DDC A₁ B₁) (rightConverter : DDC A₂ B₂)
    (leftSystem : DDS B₁) (rightSystem : DDS B₂)
    {history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {jointPrior : List (Interface.parallel B₁ B₂).query}
    {remainingOuter : List (Interface.parallel A₁ A₂).query}
    {inputs : List (DDC.History.Input (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))}
    {responses : List (Attachment.Response (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))}
    {jointFinal : DDC.History.InnerReply (Interface.parallel A₁ A₂)}
    (compatible : Attachment.CompatibleFrom (parallel leftConverter rightConverter)
      (DDS.parallel leftSystem rightSystem) history jointPrior remainingOuter
      inputs responses jointFinal)
    (current : (Interface.parallel A₁ A₂).query) (lastRight : A₂.query)
    (finalEqual : lastOuterQuery current remainingOuter = Sum.inr lastRight)
    (rightState : Option (DDC.History A₂ B₂))
    (activeEqual : (projectParallel history).active =
      some (sideOfOuterQuery current))
    (rightEqual : (projectParallel history).right = rightState)
    (rightPrior : List B₂.query)
    (priorEqual : parallelRightQueries jointPrior =
      rightPrior) :
    RightGraphProjection rightConverter rightSystem current rightState rightPrior
      remainingOuter jointFinal := by
  change List (B₁.query ⊕ B₂.query) at jointPrior
  induction compatible generalizing current rightState rightPrior with
  | @innerQuery history jointPrior remainingOuter query tailInputs
      tailResponses jointFinal responds tail inductionHypothesis =>
      change List (B₁.query ⊕ B₂.query) at jointPrior
      have admissible :=
        ((mem_parallel_iff leftConverter rightConverter history
          (Sum.inl query)).mp responds).1
      have valid := parallelRaw_admissible_projection leftConverter
        rightConverter admissible
      cases current with
      | inr currentRight =>
          have activeRight : (projectParallel history).active = some .right := by
            simpa [sideOfOuterQuery] using activeEqual
          obtain ⟨component, active⟩ := valid.activeRightPresent activeRight
          have rightStateEqual : rightState = some component :=
            rightEqual.symm.trans active.2.1
          obtain ⟨componentResponse, componentResponds, taggedEqual⟩ :=
            (mem_parallel_active_right_iff leftConverter rightConverter history
              component active admissible (Sum.inl query)).mp responds
          cases componentResponse with
          | inr componentReply =>
              simp [tagRightResponse] at taggedEqual
          | inl componentQuery =>
              have queryEqual : query = Sum.inr componentQuery := by
                simpa [tagRightResponse] using taggedEqual.symm
              subst query
              let componentReply :=
                innerReplyAt rightSystem rightPrior componentQuery
              have nextActive :
                  (projectParallel (history.snocInner (Sum.inr componentQuery)
                    (innerReplyAt (DDS.parallel leftSystem rightSystem)
                      jointPrior (Sum.inr componentQuery)))).active =
                    some .right := by
                rw [projectParallel_snocInner_right]
                simp [extendParallelProjection, activeRight]
              have nextRight :
                  (projectParallel (history.snocInner (Sum.inr componentQuery)
                    (innerReplyAt (DDS.parallel leftSystem rightSystem)
                      jointPrior (Sum.inr componentQuery)))).right =
                    some (component.snocInner componentQuery componentReply) := by
                rw [projectParallel_snocInner_right]
                simp only [extendParallelProjection, activeRight, active.2.1,
                  Option.map, Option.some.injEq]
                unfold componentReply
                rw [innerReplyAt_parallel_right, priorEqual]
              have nextPrior :
                  parallelRightQueries
                      (jointPrior ++ [(Sum.inr componentQuery :
                        (Interface.parallel B₁ B₂).query)]) =
                    rightPrior ++ [componentQuery] := by
                calc
                  _ = parallelRightQueries jointPrior ++ [componentQuery] :=
                    rightQueries_append_right jointPrior componentQuery
                  _ = rightPrior ++ [componentQuery] :=
                    congrArg (fun queries => queries ++ [componentQuery])
                      priorEqual
              obtain ⟨first, remaining, start, componentInputs,
                  componentResponses, final, outerProjection, startProjection,
                  componentCompatible, finalProjection⟩ :=
                inductionHypothesis (Sum.inr currentRight) finalEqual
                  (some (component.snocInner componentQuery componentReply))
                  nextActive nextRight (rightPrior ++ [componentQuery]) nextPrior
              refine ⟨first, remaining, component,
                component.lastInput :: componentInputs,
                Sum.inl componentQuery :: componentResponses, final,
                outerProjection, ?_, ?_, finalProjection⟩
              · exact ⟨startProjection.1, rightStateEqual⟩
              · have startEqual : start =
                    component.snocInner componentQuery componentReply :=
                  Option.some.inj startProjection.2.symm
                subst start
                exact Attachment.CompatibleFrom.innerQuery componentResponds
                  componentCompatible
      | inl currentLeft =>
          have activeLeft : (projectParallel history).active = some .left := by
            simpa [sideOfOuterQuery] using activeEqual
          obtain ⟨component, active⟩ := valid.activeLeftPresent activeLeft
          obtain ⟨componentResponse, componentResponds, taggedEqual⟩ :=
            (mem_parallel_active_left_iff leftConverter rightConverter history
              component active admissible (Sum.inl query)).mp responds
          cases componentResponse with
          | inr componentReply =>
              simp [tagLeftResponse] at taggedEqual
          | inl componentQuery =>
              have queryEqual : query = Sum.inl componentQuery := by
                simpa [tagLeftResponse] using taggedEqual.symm
              subst query
              have nextActive :
                  (projectParallel (history.snocInner (Sum.inl componentQuery)
                    (innerReplyAt (DDS.parallel leftSystem rightSystem)
                      jointPrior (Sum.inl componentQuery)))).active =
                    some .left := by
                rw [projectParallel_snocInner_left]
                simp [extendParallelProjection, activeLeft]
              have nextRight :
                  (projectParallel (history.snocInner (Sum.inl componentQuery)
                    (innerReplyAt (DDS.parallel leftSystem rightSystem)
                      jointPrior (Sum.inl componentQuery)))).right = rightState := by
                rw [projectParallel_snocInner_left]
                simp [extendParallelProjection, activeLeft, rightEqual]
              have nextPrior :
                  parallelRightQueries
                      (jointPrior ++ [(Sum.inl componentQuery :
                        (Interface.parallel B₁ B₂).query)]) = rightPrior := by
                exact (rightQueries_append_left jointPrior componentQuery).trans
                  priorEqual
              exact inductionHypothesis (Sum.inl currentLeft) finalEqual
                rightState nextActive nextRight rightPrior nextPrior
  | @outerLast history jointPrior reply responds =>
      cases current with
      | inl currentLeft => simp [lastOuterQuery] at finalEqual
      | inr currentRight =>
          have admissible :=
            ((mem_parallel_iff leftConverter rightConverter history
              (Sum.inr reply)).mp responds).1
          have valid := parallelRaw_admissible_projection leftConverter
            rightConverter admissible
          have activeRight : (projectParallel history).active = some .right := by
            simpa [sideOfOuterQuery] using activeEqual
          obtain ⟨component, active⟩ := valid.activeRightPresent activeRight
          have rightStateEqual : rightState = some component :=
            rightEqual.symm.trans active.2.1
          obtain ⟨componentResponse, componentResponds, taggedEqual⟩ :=
            (mem_parallel_active_right_iff leftConverter rightConverter history
              component active admissible (Sum.inr reply)).mp responds
          cases componentResponse with
          | inl componentQuery =>
              simp [tagRightResponse] at taggedEqual
          | inr componentReply =>
              refine ⟨currentRight, [], component, [component.lastInput],
                [Sum.inr ⟨component.lastOuter, componentReply⟩],
                ⟨component.lastOuter, componentReply⟩, ?_,
                ⟨rfl, rightStateEqual⟩,
                Attachment.CompatibleFrom.outerLast componentResponds, ?_⟩
              · rfl
              · unfold tagRightInnerReply
                apply Sigma.ext active.2.2
                have replyEqual := Sum.inr.inj taggedEqual
                exact replyEqual.symm.heq.trans (cast_heq _ _)
  | @outerNext history jointPrior reply nextOuter remainingOuter tailInputs
      tailResponses jointFinal responds tail inductionHypothesis =>
      have tailFinalEqual : lastOuterQuery nextOuter remainingOuter =
          Sum.inr lastRight := by
        simpa using finalEqual
      cases current with
      | inl currentLeft =>
          cases nextOuter with
          | inr nextRight =>
              have nextActive :
                  (projectParallel (history.snocOuter (Sum.inr nextRight))).active =
                    some .right := by
                rw [projectParallel_snocOuter_right]
                simp [extendParallelProjection]
              have nextRightState :
                  (projectParallel (history.snocOuter (Sum.inr nextRight))).right =
                    some (appendOuter rightState nextRight) := by
                rw [projectParallel_snocOuter_right]
                simp [extendParallelProjection, rightEqual]
              obtain ⟨first, remaining, start, componentInputs,
                  componentResponses, final, outerProjection, startProjection,
                  componentCompatible, finalProjection⟩ :=
                inductionHypothesis (Sum.inr nextRight) tailFinalEqual
                  (some (appendOuter rightState nextRight)) nextActive
                  nextRightState rightPrior priorEqual
              refine ⟨first, remaining, start, componentInputs,
                componentResponses, final, ?_, ?_, componentCompatible,
                finalProjection⟩
              · exact outerProjection
              · rcases startProjection with ⟨firstEqual, stateEqual⟩
                subst first
                exact Option.some.inj stateEqual.symm
          | inl nextLeft =>
              have nextActive :
                  (projectParallel (history.snocOuter (Sum.inl nextLeft))).active =
                    some .left := by
                rw [projectParallel_snocOuter_left]
                simp [extendParallelProjection]

              have nextRightState :
                  (projectParallel (history.snocOuter (Sum.inl nextLeft))).right =
                    rightState := by
                rw [projectParallel_snocOuter_left]
                simp [extendParallelProjection, rightEqual]
              obtain ⟨first, remaining, start, componentInputs,
                  componentResponses, final, outerProjection, startProjection,
                  componentCompatible, finalProjection⟩ :=
                inductionHypothesis (Sum.inl nextLeft) tailFinalEqual rightState
                  nextActive nextRightState rightPrior priorEqual
              exact ⟨first, remaining, start, componentInputs,
                componentResponses, final, outerProjection, startProjection,
                componentCompatible, finalProjection⟩
      | inr currentRight =>
          have admissible :=
            ((mem_parallel_iff leftConverter rightConverter history
              (Sum.inr reply)).mp responds).1
          have valid := parallelRaw_admissible_projection leftConverter
            rightConverter admissible
          have activeRight : (projectParallel history).active = some .right := by
            simpa [sideOfOuterQuery] using activeEqual
          obtain ⟨component, active⟩ := valid.activeRightPresent activeRight
          have rightStateEqual : rightState = some component :=
            rightEqual.symm.trans active.2.1
          obtain ⟨componentResponse, componentResponds, taggedEqual⟩ :=
            (mem_parallel_active_right_iff leftConverter rightConverter history
              component active admissible (Sum.inr reply)).mp responds
          cases componentResponse with
          | inl componentQuery =>
              simp [tagRightResponse] at taggedEqual
          | inr componentReply =>
              cases nextOuter with
              | inr nextRight =>
                  have nextActive :
                      (projectParallel
                        (history.snocOuter (Sum.inr nextRight))).active =
                        some .right := by
                    rw [projectParallel_snocOuter_right]
                    simp [extendParallelProjection]
                  have nextRightState :
                      (projectParallel
                        (history.snocOuter (Sum.inr nextRight))).right =
                        some (component.snocOuter nextRight) := by
                    rw [projectParallel_snocOuter_right]
                    simp [extendParallelProjection, rightEqual, rightStateEqual,
                      appendOuter]
                  obtain ⟨first, remaining, start, componentInputs,
                      componentResponses, final, outerProjection,
                      startProjection, componentCompatible,
                      finalProjection⟩ :=
                    inductionHypothesis (Sum.inr nextRight) tailFinalEqual
                      (some (component.snocOuter nextRight)) nextActive
                      nextRightState rightPrior priorEqual
                  have firstEqual : first = nextRight := by
                    exact startProjection.1
                  have startEqual : start = component.snocOuter first := by
                    subst first
                    exact Option.some.inj startProjection.2.symm
                  refine ⟨currentRight, first :: remaining, component,
                    component.lastInput :: componentInputs,
                    Sum.inr ⟨component.lastOuter, componentReply⟩ ::
                      componentResponses,
                    final, ?_, ⟨rfl, rightStateEqual⟩, ?_, finalProjection⟩
                  · rw [rightQueries_cons_right]
                    exact congrArg (List.cons currentRight) outerProjection
                  · apply Attachment.CompatibleFrom.outerNext componentResponds
                    simpa [startEqual] using componentCompatible
              | inl nextLeft =>
                  have nextActive :
                      (projectParallel
                        (history.snocOuter (Sum.inl nextLeft))).active =
                        some .left := by
                    rw [projectParallel_snocOuter_left]
                    simp [extendParallelProjection]
                  have nextRightState :
                      (projectParallel
                        (history.snocOuter (Sum.inl nextLeft))).right =
                        some component := by
                    rw [projectParallel_snocOuter_left]
                    simp [extendParallelProjection, rightEqual, rightStateEqual]
                  obtain ⟨first, remaining, start, componentInputs,
                      componentResponses, final, outerProjection,
                      startProjection, componentCompatible,
                      finalProjection⟩ :=
                    inductionHypothesis (Sum.inl nextLeft) tailFinalEqual
                      (some component) nextActive nextRightState rightPrior
                      priorEqual
                  have startEqual : start = component.snocOuter first := by
                    simpa [appendOuter] using startProjection
                  refine ⟨currentRight, first :: remaining, component,
                    component.lastInput :: componentInputs,
                    Sum.inr ⟨component.lastOuter, componentReply⟩ ::
                      componentResponses,
                    final, ?_, ⟨rfl, rightStateEqual⟩, ?_, finalProjection⟩
                  · rw [rightQueries_cons_right]
                    exact congrArg (List.cons currentRight) outerProjection
                  · apply Attachment.CompatibleFrom.outerNext componentResponds
                    simpa [startEqual] using componentCompatible

private theorem compatible_parallel_right
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (leftConverter : DDC A₁ B₁) (rightConverter : DDC A₂ B₂)
    (leftSystem : DDS B₁) (rightSystem : DDS B₂)
    (outerHistory : _root_.RandomSystems.Ambient.History (Interface.parallel A₁ A₂))
    (lastRight : A₂.query)
    (lastEqual : outerHistory.last = Sum.inr lastRight)
    (jointTranscript : Attachment.Transcript (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (compatible : Attachment.Compatible (parallel leftConverter rightConverter)
      (DDS.parallel leftSystem rightSystem) outerHistory jointTranscript) :
    ∃ componentTranscript : Attachment.Transcript A₂ B₂,
      Attachment.Compatible rightConverter rightSystem
          (DDS.rightHistory outerHistory lastRight
            lastEqual)
          componentTranscript ∧
        jointTranscript.final = tagRightInnerReply componentTranscript.final := by
  let current := outerHistory.head
  let rightState : Option (DDC.History A₂ B₂) :=
    match current with
    | Sum.inl _ => none
    | Sum.inr outerQuery => some (DDC.History.singleton outerQuery)
  have activeEqual :
      (projectParallel
        (DDC.History.singleton (B := Interface.parallel B₁ B₂)
          current)).active = some (sideOfOuterQuery current) := by
    cases current <;> rfl
  have rightEqual :
      (projectParallel
        (DDC.History.singleton (B := Interface.parallel B₁ B₂)
          current)).right = rightState := by
    cases currentEqual : current <;>
      simp [rightState, currentEqual]
  have finalEqual : lastOuterQuery current outerHistory.tail =
      Sum.inr lastRight := by
    have reconstruct : current :: outerHistory.tail = outerHistory.1 :=
      List.cons_head_tail outerHistory.2
    unfold lastOuterQuery
    change (current :: outerHistory.tail).getLast (by simp) = Sum.inr lastRight
    exact (List.getLast_congr (by simp) outerHistory.2 reconstruct).trans
      lastEqual
  obtain ⟨first, remaining, start, componentInputs, componentResponses,
      componentFinal, outerProjection, startProjection, componentCompatible,
      finalProjection⟩ :=
    compatibleFrom_parallel_right leftConverter rightConverter leftSystem
      rightSystem compatible current lastRight finalEqual rightState activeEqual
      rightEqual [] rfl
  have startEqual : start = DDC.History.singleton first := by
    cases currentEqual : current with
    | inl currentLeft =>
        simpa [rightState, currentEqual, appendOuter] using startProjection
    | inr currentRight =>
        simp only [currentEqual] at startProjection
        rcases startProjection with ⟨firstEqual, stateEqual⟩
        subst first
        exact Option.some.inj
          (by simpa [rightState, currentEqual] using stateEqual.symm)
  let componentOuter : _root_.RandomSystems.Ambient.History A₂ := ⟨first :: remaining, by simp⟩
  have componentOuterEqual : componentOuter =
      DDS.rightHistory outerHistory lastRight lastEqual := by
    apply _root_.RandomSystems.Ambient.History.ext
    change first :: remaining =
      parallelRightQueries outerHistory.1
    rw [← outerProjection]
    have reconstruct : current :: outerHistory.tail = outerHistory.1 :=
      List.cons_head_tail outerHistory.2
    exact congrArg parallelRightQueries reconstruct
  let componentTranscript : Attachment.Transcript A₂ B₂ :=
    { inputs := componentInputs
      responses := componentResponses
      final := componentFinal }
  refine ⟨componentTranscript, ?_, finalProjection⟩
  rw [← componentOuterEqual]
  change Attachment.CompatibleFrom rightConverter rightSystem
    (DDC.History.singleton first) [] remaining componentInputs
      componentResponses componentFinal
  rw [← startEqual]
  exact componentCompatible

private theorem selectReply_tagRight
    {A B : Interface.{u, v}} (query : B.query) (reply : DDC.History.InnerReply B) :
    selectReply (A := Interface.parallel A B) (Sum.inr query)
        (tagRightInnerReply reply) =
      selectReply query reply := by
  rcases reply with ⟨replyQuery, reply⟩
  change selectReply (Sum.inr query)
      (⟨Sum.inr replyQuery, reply⟩ : DDC.History.InnerReply (Interface.parallel A B)) =
    selectReply query (⟨replyQuery, reply⟩ : DDC.History.InnerReply B)
  by_cases equal : replyQuery = query
  · subst replyQuery
    simp [selectReply, Attachment.selectReply]
  · have taggedUnequal : (Sum.inr replyQuery : A.query ⊕ B.query) ≠
        Sum.inr query := fun taggedEqual => equal (Sum.inr.inj taggedEqual)
    unfold selectReply Attachment.selectReply
    split
    · rename_i taggedEqual
      exact (taggedUnequal taggedEqual).elim
    · rfl

private theorem cast_selectReply_tagRight
    {A B : Interface.{u, v}}
    (selected : (Interface.parallel A B).query) (query : B.query)
    (equal : selected = Sum.inr query) (reply : DDC.History.InnerReply B) :
    cast (congrArg (fun current =>
        Option ((Interface.parallel A B).answer current)) equal)
        (selectReply selected (tagRightInnerReply reply)) =
      selectReply query reply := by
  subst selected
  rw [cast_eq, selectReply_tagRight]

private theorem applySystem_parallel_at_right
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (leftConverter : DDC A₁ B₁) (rightConverter : DDC A₂ B₂)
    (leftSystem : DDS B₁) (rightSystem : DDS B₂)
    (outerHistory : _root_.RandomSystems.Ambient.History (Interface.parallel A₁ A₂))
    (lastRight : A₂.query)
    (lastEqual : outerHistory.last = Sum.inr lastRight) :
    applySystem (parallel leftConverter rightConverter)
        (DDS.parallel leftSystem rightSystem) outerHistory =
      DDS.parallel (applySystem leftConverter leftSystem)
        (applySystem rightConverter rightSystem) outerHistory := by
  obtain ⟨jointTranscript, jointCompatible⟩ :=
    Attachment.exists_compatible (parallel leftConverter rightConverter)
      (DDS.parallel leftSystem rightSystem) outerHistory
  obtain ⟨componentTranscript, componentCompatible, finalProjection⟩ :=
    compatible_parallel_right leftConverter rightConverter leftSystem
      rightSystem outerHistory lastRight lastEqual jointTranscript
      jointCompatible
  let componentHistory :=
    DDS.rightHistory outerHistory lastRight lastEqual
  have componentOutput :
      applySystem rightConverter rightSystem componentHistory =
        selectReply componentHistory.last componentTranscript.final := by
    apply (applySystem_eq_iff rightConverter rightSystem componentHistory _).mpr
    have finalQuery :=
      Attachment.Compatible.final_query_eq_last
        (compatible := componentCompatible)
    exact ⟨componentTranscript, componentCompatible,
      (Attachment.selectReply_heq_second componentHistory.last
        componentTranscript.final finalQuery).symm⟩
  have jointOutput :
      applySystem (parallel leftConverter rightConverter)
          (DDS.parallel leftSystem rightSystem) outerHistory =
        selectReply outerHistory.last jointTranscript.final := by
    apply (applySystem_eq_iff (parallel leftConverter rightConverter)
      (DDS.parallel leftSystem rightSystem) outerHistory _).mpr
    have finalQuery :=
      Attachment.Compatible.final_query_eq_last
        (compatible := jointCompatible)
    exact ⟨jointTranscript, jointCompatible,
      (Attachment.selectReply_heq_second outerHistory.last
        jointTranscript.final finalQuery).symm⟩
  rw [jointOutput]
  let typeEqual := congrArg (fun selected =>
    Option ((Interface.parallel A₁ A₂).answer selected)) lastEqual
  apply (cast_inj typeEqual).mp
  rw [DDS_parallel_cast_right
    (applySystem leftConverter leftSystem)
    (applySystem rightConverter rightSystem) outerHistory lastRight lastEqual]
  unfold parallelRightAnswer
  rw [componentOutput]
  have componentFinalEqual :=
    Attachment.Compatible.final_query_eq_last (compatible := componentCompatible)
  have componentQueryEqual : componentTranscript.final.1 = lastRight :=
    componentFinalEqual.trans
      (DDS.last_rightHistory outerHistory lastRight
        lastEqual)
  have jointQueryEqual : Sum.inr componentTranscript.final.1 =
      outerHistory.last :=
    (congrArg Sum.inr componentQueryEqual).trans lastEqual.symm
  rw [finalProjection]
  apply eq_of_heq
  have leftHeq :
      cast typeEqual
          (selectReply outerHistory.last
            (tagRightInnerReply componentTranscript.final)) ≍
        componentTranscript.final.2 :=
    (cast_heq _ _).trans
      (Attachment.selectReply_heq_second outerHistory.last
        (tagRightInnerReply componentTranscript.final) jointQueryEqual)
  have rightHeq :
      cast (congrArg (fun selected => Option (A₂.answer selected))
          (DDS.last_rightHistory outerHistory lastRight
            lastEqual))
          (selectReply componentHistory.last componentTranscript.final) ≍
        componentTranscript.final.2 :=
    (cast_heq _ _).trans
      (Attachment.selectReply_heq_second componentHistory.last componentTranscript.final
        componentFinalEqual)
  exact leftHeq.trans rightHeq.symm

/--
Attachment acts componentwise on ordered parallel. Jost, Proposition 2.2.3
(printed p. 18), states the corresponding resource equation
`pi [R, S] = [pi R, S]`.
-/
theorem applySystem_parallel_eq
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (leftConverter : DDC A₁ B₁) (rightConverter : DDC A₂ B₂)
    (leftSystem : DDS B₁) (rightSystem : DDS B₂) :
    applySystem (parallel leftConverter rightConverter)
        (DDS.parallel leftSystem rightSystem) =
      DDS.parallel (applySystem leftConverter leftSystem)
        (applySystem rightConverter rightSystem) := by
  -- Compare the attached DDSs as functions of a complete tagged history.
  apply DDS.ext
  intro outerHistory
  -- The final query tag selects the component whose attachment is evaluated.
  have lastCase :
      (∃ lastLeft, outerHistory.last = Sum.inl lastLeft) ∨
        ∃ lastRight, outerHistory.last = Sum.inr lastRight := by
    exact match outerHistory.last with
    | Sum.inl lastLeft => Or.inl ⟨lastLeft, rfl⟩
    | Sum.inr lastRight => Or.inr ⟨lastRight, rfl⟩
  rcases lastCase with ⟨lastLeft, lastEqual⟩ | ⟨lastRight, lastEqual⟩
  -- Project a left-tagged history to the left attachment equation.
  · exact applySystem_parallel_at_left leftConverter rightConverter
      leftSystem rightSystem outerHistory lastLeft lastEqual
  -- Project a right-tagged history to the right attachment equation.
  · exact applySystem_parallel_at_right leftConverter rightConverter
      leftSystem rightSystem outerHistory lastRight lastEqual

namespace Internal

private theorem eq_of_graph_subset_parallel
    {A B : Interface.{u, v}} (left right : DDC A B)
    (subset : ∀ history response,
      response ∈ right history → response ∈ left history) :
    left = right := by
  have admissible : ∀ {history},
      DDC.Raw.Admissible left.toFun history →
        DDC.Raw.Admissible right.toFun history := by
    intro history legal
    induction legal with
    | start query => exact .start query
    | afterInner leftPrior leftResponds reply inductionHypothesis =>
        rename_i history query
        have rightResponds := right.response_mem history inductionHypothesis
        have responseEqual : right.response history inductionHypothesis =
            Sum.inl query :=
          Part.mem_unique (subset history _ rightResponds) leftResponds
        exact .afterInner inductionHypothesis
          (responseEqual ▸ rightResponds) reply
    | afterOuter leftPrior leftResponds query inductionHypothesis =>
        rename_i history reply
        have rightResponds := right.response_mem history inductionHypothesis
        have responseEqual : right.response history inductionHypothesis =
            Sum.inr reply :=
          Part.mem_unique (subset history _ rightResponds) leftResponds
        exact .afterOuter inductionHypothesis
          (responseEqual ▸ rightResponds) query
  apply DDC.ext
  intro history response
  constructor
  · intro leftResponds
    have rightAdmissible := admissible
      ((left.exactDomain history).mp leftResponds.1)
    have rightResponds := right.response_mem history rightAdmissible
    have responseEqual : right.response history rightAdmissible = response :=
      Part.mem_unique (subset history _ rightResponds) leftResponds
    exact responseEqual ▸ rightResponds
  · exact subset history response

private def OptionalComponentHistories
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (joint : Option (DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)))
    (left : Option (DDC.History A₁ B₁))
    (right : Option (DDC.History A₂ B₂)) : Prop :=
  match joint with
  | none => left = none ∧ right = none
  | some history =>
      (projectParallel history).left = left ∧
        (projectParallel history).right = right

private def LeftProjection
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (joint : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₁ B₁) : Prop :=
  (projectParallel joint).active = some .left ∧
    (projectParallel joint).left = some component

private def RightProjection
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (joint : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₂ B₂) : Prop :=

  (projectParallel joint).active = some .right ∧
    (projectParallel joint).right = some component

private def OptionalLeftProjection
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}} :
    Option (DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)) →
      Option (DDC.History A₁ B₁) → Prop
  | none, none => True
  | some joint, some component => LeftProjection joint component
  | _, _ => False

private def OptionalRightProjection
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}} :
    Option (DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)) →
      Option (DDC.History A₂ B₂) → Prop
  | none, none => True
  | some joint, some component => RightProjection joint component
  | _, _ => False

private def LeftHistoryProjection
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}} :
    Option (DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)) →
      Option (DDC.History A₁ B₁) → Prop
  | none, none => True
  | some joint, component => (projectParallel joint).left = component
  | none, some _ => False

private def RightHistoryProjection
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}} :
    Option (DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)) →
      Option (DDC.History A₂ B₂) → Prop
  | none, none => True
  | some joint, component => (projectParallel joint).right = component
  | none, some _ => False

private theorem component_mem_of_left
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    {joint : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {component : DDC.History A₁ B₁}
    (projection : LeftProjection joint component)
    {response : DDC.Response joint}
    (responds : response ∈ parallel left right joint) :
    ∃ componentResponse ∈ left component,
      ∃ outerEqual : joint.lastOuter = Sum.inl component.lastOuter,
        tagLeftResponse joint component outerEqual componentResponse = response := by
  have admissible := ((mem_parallel_iff left right joint response).mp responds).1
  let active : ActiveLeft joint component :=
    ⟨projection.1, projection.2, by
      have valid := parallelRaw_admissible_projection left right admissible
      obtain ⟨actual, actualActive⟩ := valid.activeLeftPresent projection.1
      have equal : actual = component :=
        Option.some.inj (actualActive.2.1.symm.trans projection.2)
      subst actual
      exact actualActive.2.2⟩
  obtain ⟨componentResponse, componentResponds, responseEqual⟩ :=
    (mem_parallel_active_left_iff left right joint component active
      admissible response).mp responds
  exact ⟨componentResponse, componentResponds, active.2.2, responseEqual⟩

private theorem component_mem_of_right
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    {joint : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {component : DDC.History A₂ B₂}
    (projection : RightProjection joint component)
    {response : DDC.Response joint}
    (responds : response ∈ parallel left right joint) :
    ∃ componentResponse ∈ right component,
      ∃ outerEqual : joint.lastOuter = Sum.inr component.lastOuter,
        tagRightResponse joint component outerEqual componentResponse = response := by
  have admissible := ((mem_parallel_iff left right joint response).mp responds).1
  let active : ActiveRight joint component :=
    ⟨projection.1, projection.2, by
      have valid := parallelRaw_admissible_projection left right admissible
      obtain ⟨actual, actualActive⟩ := valid.activeRightPresent projection.1
      have equal : actual = component :=
        Option.some.inj (actualActive.2.1.symm.trans projection.2)
      subst actual
      exact actualActive.2.2⟩
  obtain ⟨componentResponse, componentResponds, responseEqual⟩ :=
    (mem_parallel_active_right_iff left right joint component active
      admissible response).mp responds
  exact ⟨componentResponse, componentResponds, active.2.2, responseEqual⟩

private def tagLeftPacked
    {A₁ C₁ A₂ C₂ : Interface.{u, v}} :
    PackedResponse A₁ C₁ →
      PackedResponse (Interface.parallel A₁ A₂)
        (Interface.parallel C₁ C₂)
  | Sum.inl query => Sum.inl (Sum.inl query)
  | Sum.inr ⟨query, reply⟩ => Sum.inr ⟨Sum.inl query, reply⟩

private def tagRightPacked
    {A₁ C₁ A₂ C₂ : Interface.{u, v}} :
    PackedResponse A₂ C₂ →
      PackedResponse (Interface.parallel A₁ A₂)
        (Interface.parallel C₁ C₂)
  | Sum.inl query => Sum.inl (Sum.inr query)
  | Sum.inr ⟨query, reply⟩ => Sum.inr ⟨Sum.inr query, reply⟩

private theorem packResponse_tagLeft
    {A₁ C₁ A₂ C₂ : Interface.{u, v}}
    (joint : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel C₁ C₂))
    (component : DDC.History A₁ C₁)
    (outerEqual : joint.lastOuter = Sum.inl component.lastOuter)
    (response : DDC.Response component) :
    packResponse joint
        (tagLeftResponse joint component outerEqual response) =
      tagLeftPacked (packResponse component response) := by
  cases response with
  | inl query => rfl
  | inr reply =>
      apply congrArg Sum.inr
      apply Sigma.ext outerEqual
      exact cast_heq

        (congrArg (fun selected =>
          Option ((Interface.parallel A₁ A₂).answer selected))
          outerEqual.symm) reply

private theorem packResponse_tagRight
    {A₁ C₁ A₂ C₂ : Interface.{u, v}}
    (joint : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel C₁ C₂))
    (component : DDC.History A₂ C₂)
    (outerEqual : joint.lastOuter = Sum.inr component.lastOuter)
    (response : DDC.Response component) :
    packResponse joint
        (tagRightResponse joint component outerEqual response) =
      tagRightPacked (packResponse component response) := by
  cases response with
  | inl query => rfl
  | inr reply =>
      apply congrArg Sum.inr
      apply Sigma.ext outerEqual
      exact cast_heq
        (congrArg (fun selected =>
          Option ((Interface.parallel A₁ A₂).answer selected))
          outerEqual.symm) reply

private def OuterPrefixFactorization.LeftResult
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    (outerLeft : DDC A₁ B₁) (outerRight : DDC A₂ B₂)
    (innerLeft : DDC B₁ C₁) (innerRight : DDC B₂ C₂)
    {jointOuter jointInner jointResponse finalJointOuter finalJointInner}
    (_factorization : OuterPrefixFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      jointOuter jointInner jointResponse finalJointOuter finalJointInner)
    (componentOuter : DDC.History A₁ B₁)
    (componentInner : Option (DDC.History B₁ C₁)) : Prop :=
  ∃ componentResponse finalComponentOuter finalComponentInner,
    OuterPrefixFactorization outerLeft innerLeft componentOuter componentInner
        componentResponse finalComponentOuter finalComponentInner ∧
      tagLeftPacked componentResponse = jointResponse ∧
      LeftProjection finalJointOuter finalComponentOuter ∧
      LeftHistoryProjection finalJointInner finalComponentInner

private def InnerPrefixFactorization.LeftResult
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    (outerLeft : DDC A₁ B₁) (outerRight : DDC A₂ B₂)
    (innerLeft : DDC B₁ C₁) (innerRight : DDC B₂ C₂)
    {jointOuter jointInner jointResponse finalJointOuter finalJointInner}
    (_factorization : InnerPrefixFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      jointOuter jointInner jointResponse finalJointOuter finalJointInner)
    (componentOuter : DDC.History A₁ B₁)
    (componentInner : DDC.History B₁ C₁) : Prop :=
  ∃ componentResponse finalComponentOuter finalComponentInner,
    InnerPrefixFactorization outerLeft innerLeft componentOuter componentInner
        componentResponse finalComponentOuter finalComponentInner ∧
      tagLeftPacked componentResponse = jointResponse ∧
      LeftProjection finalJointOuter finalComponentOuter ∧
      LeftHistoryProjection finalJointInner finalComponentInner

private def OuterPrefixFactorization.RightResult
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    (outerLeft : DDC A₁ B₁) (outerRight : DDC A₂ B₂)
    (innerLeft : DDC B₁ C₁) (innerRight : DDC B₂ C₂)
    {jointOuter jointInner jointResponse finalJointOuter finalJointInner}
    (_factorization : OuterPrefixFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      jointOuter jointInner jointResponse finalJointOuter finalJointInner)
    (componentOuter : DDC.History A₂ B₂)
    (componentInner : Option (DDC.History B₂ C₂)) : Prop :=
  ∃ componentResponse finalComponentOuter finalComponentInner,
    OuterPrefixFactorization outerRight innerRight componentOuter componentInner
        componentResponse finalComponentOuter finalComponentInner ∧
      tagRightPacked componentResponse = jointResponse ∧
      RightProjection finalJointOuter finalComponentOuter ∧
      RightHistoryProjection finalJointInner finalComponentInner

private def InnerPrefixFactorization.RightResult
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    (outerLeft : DDC A₁ B₁) (outerRight : DDC A₂ B₂)
    (innerLeft : DDC B₁ C₁) (innerRight : DDC B₂ C₂)
    {jointOuter jointInner jointResponse finalJointOuter finalJointInner}
    (_factorization : InnerPrefixFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      jointOuter jointInner jointResponse finalJointOuter finalJointInner)
    (componentOuter : DDC.History A₂ B₂)
    (componentInner : DDC.History B₂ C₂) : Prop :=
  ∃ componentResponse finalComponentOuter finalComponentInner,
    InnerPrefixFactorization outerRight innerRight componentOuter componentInner
        componentResponse finalComponentOuter finalComponentInner ∧
      tagRightPacked componentResponse = jointResponse ∧
      RightProjection finalJointOuter finalComponentOuter ∧
      RightHistoryProjection finalJointInner finalComponentInner

private theorem LeftProjection.snoc_outer
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    {joint : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {component : DDC.History A₁ B₁}
    (projection : LeftProjection joint component) (query : A₁.query) :
    LeftProjection (joint.snocOuter (Sum.inl query))
      (component.snocOuter query) := by
  constructor
  · rw [projectParallel_snocOuter_left]
    simp [extendParallelProjection]
  · rw [projectParallel_snocOuter_left]
    simp [extendParallelProjection, projection.2, appendOuter]

private theorem LeftProjection.snoc_inner
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    {joint : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {component : DDC.History A₁ B₁}
    (projection : LeftProjection joint component)
    (query : B₁.query) (reply : Option (B₁.answer query)) :
    LeftProjection (joint.snocInner (Sum.inl query) reply)
      (component.snocInner query reply) := by
  constructor
  · rw [projectParallel_snocInner_left]
    simp [extendParallelProjection, projection.1]
  · rw [projectParallel_snocInner_left]
    simp [extendParallelProjection, projection.1, projection.2]

private theorem RightProjection.snoc_outer
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    {joint : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {component : DDC.History A₂ B₂}
    (projection : RightProjection joint component) (query : A₂.query) :
    RightProjection (joint.snocOuter (Sum.inr query))
      (component.snocOuter query) := by
  constructor
  · rw [projectParallel_snocOuter_right]
    simp [extendParallelProjection]
  · rw [projectParallel_snocOuter_right]
    simp [extendParallelProjection, projection.2, appendOuter]

private theorem RightProjection.snoc_inner
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    {joint : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {component : DDC.History A₂ B₂}
    (projection : RightProjection joint component)
    (query : B₂.query) (reply : Option (B₂.answer query)) :
    RightProjection (joint.snocInner (Sum.inr query) reply)
      (component.snocInner query reply) := by
  constructor
  · rw [projectParallel_snocInner_right]
    simp [extendParallelProjection, projection.1]
  · rw [projectParallel_snocInner_right]
    simp [extendParallelProjection, projection.1, projection.2]

private theorem InnerClosed.left_of_parallel
    {B₁ C₁ B₂ C₂ : Interface.{u, v}}
    (left : DDC B₁ C₁) (right : DDC B₂ C₂)
    {joint : DDC.History (Interface.parallel B₁ B₂)
      (Interface.parallel C₁ C₂)}
    {component : DDC.History B₁ C₁}
    (projection : LeftProjection joint component)
    (closed : InnerClosed (parallel left right) (some joint)) :
    InnerClosed left (some component) := by
  obtain ⟨reply, responds⟩ := closed
  obtain ⟨componentResponse, componentResponds, outerEqual,
      responseEqual⟩ := component_mem_of_left left right projection responds
  cases componentResponse with
  | inl query => simp [tagLeftResponse] at responseEqual
  | inr componentReply => exact ⟨componentReply, componentResponds⟩

private theorem InnerClosed.right_of_parallel
    {B₁ C₁ B₂ C₂ : Interface.{u, v}}
    (left : DDC B₁ C₁) (right : DDC B₂ C₂)
    {joint : DDC.History (Interface.parallel B₁ B₂)
      (Interface.parallel C₁ C₂)}
    {component : DDC.History B₂ C₂}
    (projection : RightProjection joint component)
    (closed : InnerClosed (parallel left right) (some joint)) :
    InnerClosed right (some component) := by
  obtain ⟨reply, responds⟩ := closed
  obtain ⟨componentResponse, componentResponds, _outerEqual,
      responseEqual⟩ := component_mem_of_right left right projection responds
  cases componentResponse with
  | inl query => simp [tagRightResponse] at responseEqual
  | inr componentReply => exact ⟨componentReply, componentResponds⟩

private theorem LeftProjection.snoc_inner_of_eq
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    {joint : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {component : DDC.History A₁ B₁}
    (projection : LeftProjection joint component)
    {jointQuery : (Interface.parallel B₁ B₂).query}
    {componentQuery : B₁.query}
    (queryEqual : jointQuery = Sum.inl componentQuery)
    (jointReply : Option ((Interface.parallel B₁ B₂).answer jointQuery))
    (componentReply : Option (B₁.answer componentQuery))
    (replyEqual : cast
      (congrArg (fun selected =>
        Option ((Interface.parallel B₁ B₂).answer selected))
        queryEqual.symm) componentReply = jointReply) :
    LeftProjection (joint.snocInner jointQuery jointReply)
      (component.snocInner componentQuery componentReply) := by
  subst jointQuery
  simp at replyEqual
  subst jointReply
  exact projection.snoc_inner componentQuery componentReply

private theorem RightProjection.snoc_inner_of_eq
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    {joint : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {component : DDC.History A₂ B₂}
    (projection : RightProjection joint component)
    {jointQuery : (Interface.parallel B₁ B₂).query}
    {componentQuery : B₂.query}
    (queryEqual : jointQuery = Sum.inr componentQuery)
    (jointReply : Option ((Interface.parallel B₁ B₂).answer jointQuery))
    (componentReply : Option (B₂.answer componentQuery))
    (replyEqual : cast
      (congrArg (fun selected =>
        Option ((Interface.parallel B₁ B₂).answer selected))
        queryEqual.symm) componentReply = jointReply) :
    RightProjection (joint.snocInner jointQuery jointReply)
      (component.snocInner componentQuery componentReply) := by
  subst jointQuery
  simp at replyEqual
  subst jointReply
  exact projection.snoc_inner componentQuery componentReply

private theorem OuterPrefixFactorization.projectLeft
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    (outerLeft : DDC A₁ B₁) (outerRight : DDC A₂ B₂)
    (innerLeft : DDC B₁ C₁) (innerRight : DDC B₂ C₂)
    {jointOuter finalJointOuter jointInner finalJointInner jointResponse}
    (factorization : OuterPrefixFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      jointOuter jointInner jointResponse finalJointOuter finalJointInner)
    {componentOuter : DDC.History A₁ B₁}
    {componentInner : Option (DDC.History B₁ C₁)}
    (outerProjection : LeftProjection jointOuter componentOuter)
    (innerProjection : LeftHistoryProjection jointInner componentInner)
    (innerClosed : InnerClosed innerLeft componentInner) :
    factorization.LeftResult outerLeft outerRight innerLeft innerRight
      componentOuter componentInner := by
  induction factorization using OuterPrefixFactorization.rec
      (motive_2 := fun jointOuter jointInner jointResponse finalJointOuter
        finalJointInner factorization =>
          ∀ (componentOuter : DDC.History A₁ B₁)
            (componentInner : DDC.History B₁ C₁),
            LeftProjection jointOuter componentOuter →
            LeftProjection jointInner componentInner →
            factorization.LeftResult outerLeft outerRight innerLeft innerRight
              componentOuter componentInner)

      generalizing componentOuter componentInner with
  | outerReply responds =>
      rename_i currentOuter currentInner jointReply
      obtain ⟨componentResponse, componentResponds, outerEqual,
          responseEqual⟩ :=
        component_mem_of_left outerLeft outerRight outerProjection responds
      cases componentResponse with
      | inl query => simp [tagLeftResponse] at responseEqual
      | inr componentReply =>
          refine ⟨Sum.inr ⟨componentOuter.lastOuter, componentReply⟩,
            componentOuter, componentInner, .outerReply componentResponds,
            ?_, outerProjection, innerProjection⟩
          apply congrArg Sum.inr
          apply Sigma.ext outerEqual.symm
          have replyEqual := Sum.inr.inj responseEqual
          exact (cast_heq
            (congrArg (fun selected =>
              Option ((Interface.parallel A₁ A₂).answer selected))
              outerEqual.symm) componentReply).symm.trans replyEqual.heq
  | outerQueryFirst responds tail inductionHypothesis =>
      rename_i currentOuter jointQuery currentResponse currentFinalOuter
        currentFinalInner
      cases componentInner with
      | some componentInner =>
          simp [LeftHistoryProjection] at innerProjection
      | none =>
          obtain ⟨componentResponse, componentResponds, _outerEqual,
              responseEqual⟩ :=
            component_mem_of_left outerLeft outerRight outerProjection responds
          cases componentResponse with
          | inr componentReply => simp [tagLeftResponse] at responseEqual
          | inl componentQuery =>
              have queryEqual : jointQuery = Sum.inl componentQuery := by
                simpa [tagLeftResponse] using responseEqual.symm
              subst jointQuery
              have innerStart : @LeftProjection B₁ C₁ B₂ C₂
                  (DDC.History.singleton
                    (B := Interface.parallel C₁ C₂)
                    (Sum.inl componentQuery :
                      (Interface.parallel B₁ B₂).query))
                  (DDC.History.singleton (B := C₁) componentQuery) := by
                exact ⟨rfl, rfl⟩
              obtain ⟨componentFinal, finalOuter, finalInner,
                  componentTail, finalEqual, finalOuterProjection,
                  finalInnerProjection⟩ :=
                inductionHypothesis componentOuter
                  (DDC.History.singleton (B := C₁) componentQuery)
                  outerProjection
                  innerStart
              exact ⟨componentFinal, finalOuter, finalInner,
                .outerQueryFirst componentResponds componentTail, finalEqual,
                finalOuterProjection, finalInnerProjection⟩
  | outerQueryNext closed responds tail inductionHypothesis =>
      rename_i currentOuter currentInner jointQuery jointResponse
        currentFinalOuter currentFinalInner
      cases componentInner with
      | none =>
          change (projectParallel currentInner).left = none at innerProjection
          obtain ⟨componentResponse, componentResponds, outerEqual,
              responseEqual⟩ :=
            component_mem_of_left outerLeft outerRight outerProjection responds
          cases componentResponse with
          | inr componentReply => simp [tagLeftResponse] at responseEqual
          | inl componentQuery =>
              have jointQueryEqual : jointQuery = Sum.inl componentQuery := by
                simpa [tagLeftResponse] using responseEqual.symm
              subst jointQuery
              have nextInner : @LeftProjection B₁ C₁ B₂ C₂
                  (currentInner.snocOuter
                    (Sum.inl componentQuery :
                      (Interface.parallel B₁ B₂).query))
                  (DDC.History.singleton (B := C₁) componentQuery) := by
                constructor
                · rw [projectParallel_snocOuter_left]
                  simp [extendParallelProjection]
                · rw [projectParallel_snocOuter_left]
                  simp [extendParallelProjection, innerProjection, appendOuter]
              obtain ⟨componentFinal, finalOuter, finalInner,
                  componentTail, finalEqual, finalOuterProjection,
                  finalInnerProjection⟩ :=
                inductionHypothesis componentOuter
                  (DDC.History.singleton (B := C₁) componentQuery)
                  outerProjection nextInner
              exact ⟨componentFinal, finalOuter, finalInner,
                .outerQueryFirst componentResponds componentTail, finalEqual,
                finalOuterProjection, finalInnerProjection⟩
      | some componentInner =>
          change (projectParallel currentInner).left = some componentInner
            at innerProjection
          obtain ⟨componentResponse, componentResponds, _outerEqual,
              responseEqual⟩ :=
            component_mem_of_left outerLeft outerRight outerProjection responds
          cases componentResponse with
          | inr componentReply => simp [tagLeftResponse] at responseEqual
          | inl componentQuery =>
              have jointQueryEqual : jointQuery = Sum.inl componentQuery := by
                simpa [tagLeftResponse] using responseEqual.symm
              subst jointQuery
              have nextInner : @LeftProjection B₁ C₁ B₂ C₂
                  (currentInner.snocOuter
                    (Sum.inl componentQuery :
                      (Interface.parallel B₁ B₂).query))
                  (componentInner.snocOuter componentQuery) := by
                constructor
                · rw [projectParallel_snocOuter_left]
                  simp [extendParallelProjection]
                · rw [projectParallel_snocOuter_left]
                  simp [extendParallelProjection, innerProjection, appendOuter]
              obtain ⟨componentFinal, finalOuter, finalInner,
                  componentTail, finalEqual, finalOuterProjection,
                  finalInnerProjection⟩ :=
                inductionHypothesis componentOuter
                  (componentInner.snocOuter componentQuery)
                  outerProjection nextInner
              exact ⟨componentFinal, finalOuter, finalInner,
                .outerQueryNext innerClosed componentResponds componentTail,
                finalEqual, finalOuterProjection, finalInnerProjection⟩
  | innerQuery linked responds componentOuter componentInner
      outerProjection innerProjection =>
      rename_i currentOuter currentInner jointQuery
      obtain ⟨componentOuterResponse, componentLinked, _outerEqual,
          linkedEqual⟩ :=
        component_mem_of_left outerLeft outerRight outerProjection linked
      cases componentOuterResponse with
      | inr componentReply => simp [tagLeftResponse] at linkedEqual
      | inl componentMiddleQuery =>
          obtain ⟨componentInnerResponse, componentResponds, innerOuterEqual,
              responseEqual⟩ :=
            component_mem_of_left innerLeft innerRight innerProjection responds
          cases componentInnerResponse with
          | inr componentReply => simp [tagLeftResponse] at responseEqual
          | inl componentQuery =>
              have middleQueryEqual : currentInner.lastOuter =
                  Sum.inl componentMiddleQuery := by
                simpa [tagLeftResponse] using linkedEqual.symm
              have componentMiddleEqual : componentMiddleQuery =
                  componentInner.lastOuter :=
                Sum.inl.inj (middleQueryEqual.symm.trans innerOuterEqual)
              subst componentMiddleQuery
              have finalEqual : @tagLeftPacked A₁ C₁ A₂ C₂
                  (Sum.inl componentQuery : PackedResponse A₁ C₁) =
                  (Sum.inl jointQuery : PackedResponse
                    (Interface.parallel A₁ A₂)
                    (Interface.parallel C₁ C₂)) := by
                simpa [tagLeftResponse, tagLeftPacked] using responseEqual
              exact ⟨Sum.inl componentQuery, componentOuter,
                some componentInner,
                .innerQuery componentLinked componentResponds, finalEqual,
                outerProjection, innerProjection.2⟩
  | innerReply linked responds tail inductionHypothesis componentOuter
      componentInner outerProjection innerProjection =>
      rename_i currentOuter currentInner jointReply jointResponse
        currentFinalOuter currentFinalInner
      obtain ⟨componentOuterResponse, componentLinked, _outerEqual,
          linkedEqual⟩ :=
        component_mem_of_left outerLeft outerRight outerProjection linked
      cases componentOuterResponse with
      | inr componentReply => simp [tagLeftResponse] at linkedEqual
      | inl componentMiddleQuery =>
          obtain ⟨componentInnerResponse, componentResponds, innerOuterEqual,
              responseEqual⟩ :=
            component_mem_of_left innerLeft innerRight innerProjection responds
          cases componentInnerResponse with
          | inl componentQuery => simp [tagLeftResponse] at responseEqual
          | inr componentReply =>
              have middleQueryEqual : currentInner.lastOuter =
                  Sum.inl componentMiddleQuery := by
                simpa [tagLeftResponse] using linkedEqual.symm
              have componentMiddleEqual : componentMiddleQuery =
                  componentInner.lastOuter :=
                Sum.inl.inj (middleQueryEqual.symm.trans innerOuterEqual)
              subst componentMiddleQuery
              have replyEqual : cast
                  (congrArg (fun selected => Option
                    ((Interface.parallel B₁ B₂).answer selected))
                    innerOuterEqual.symm) componentReply = jointReply := by
                exact Sum.inr.inj responseEqual
              have nextOuter : LeftProjection
                  (currentOuter.snocInner currentInner.lastOuter jointReply)
                  (componentOuter.snocInner componentInner.lastOuter
                    componentReply) :=
                outerProjection.snoc_inner_of_eq innerOuterEqual jointReply
                  componentReply replyEqual
              have projectedInner : LeftHistoryProjection (some currentInner)
                  (some componentInner) := innerProjection.2
              obtain ⟨componentFinal, finalOuter, finalInner,
                  componentTail, finalEqual, finalOuterProjection,
                  finalInnerProjection⟩ :=
                inductionHypothesis nextOuter projectedInner
                  ⟨componentReply, componentResponds⟩
              exact ⟨componentFinal, finalOuter, finalInner,
                .innerReply componentLinked componentResponds componentTail,
                finalEqual, finalOuterProjection, finalInnerProjection⟩

private theorem OuterPrefixFactorization.projectRight
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    (outerLeft : DDC A₁ B₁) (outerRight : DDC A₂ B₂)
    (innerLeft : DDC B₁ C₁) (innerRight : DDC B₂ C₂)
    {jointOuter finalJointOuter jointInner finalJointInner jointResponse}
    (factorization : OuterPrefixFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      jointOuter jointInner jointResponse finalJointOuter finalJointInner)
    {componentOuter : DDC.History A₂ B₂}
    {componentInner : Option (DDC.History B₂ C₂)}
    (outerProjection : RightProjection jointOuter componentOuter)
    (innerProjection : RightHistoryProjection jointInner componentInner)
    (innerClosed : InnerClosed innerRight componentInner) :
    factorization.RightResult outerLeft outerRight innerLeft innerRight
      componentOuter componentInner := by
  induction factorization using OuterPrefixFactorization.rec
      (motive_2 := fun jointOuter jointInner jointResponse finalJointOuter
        finalJointInner factorization =>
          ∀ (componentOuter : DDC.History A₂ B₂)
            (componentInner : DDC.History B₂ C₂),
            RightProjection jointOuter componentOuter →
            RightProjection jointInner componentInner →
            factorization.RightResult outerLeft outerRight innerLeft innerRight
              componentOuter componentInner)
      generalizing componentOuter componentInner with
  | outerReply responds =>
      rename_i currentOuter currentInner jointReply
      obtain ⟨componentResponse, componentResponds, outerEqual,
          responseEqual⟩ :=
        component_mem_of_right outerLeft outerRight outerProjection responds
      cases componentResponse with
      | inl query => simp [tagRightResponse] at responseEqual
      | inr componentReply =>
          refine ⟨Sum.inr ⟨componentOuter.lastOuter, componentReply⟩,
            componentOuter, componentInner, .outerReply componentResponds,
            ?_, outerProjection, innerProjection⟩
          apply congrArg Sum.inr
          apply Sigma.ext outerEqual.symm
          have replyEqual := Sum.inr.inj responseEqual
          exact (cast_heq
            (congrArg (fun selected =>
              Option ((Interface.parallel A₁ A₂).answer selected))
              outerEqual.symm) componentReply).symm.trans replyEqual.heq
  | outerQueryFirst responds tail inductionHypothesis =>
      rename_i currentOuter jointQuery currentResponse currentFinalOuter
        currentFinalInner
      cases componentInner with
      | some componentInner =>
          simp [RightHistoryProjection] at innerProjection
      | none =>
          obtain ⟨componentResponse, componentResponds, _outerEqual,
              responseEqual⟩ :=
            component_mem_of_right outerLeft outerRight outerProjection responds
          cases componentResponse with
          | inr componentReply => simp [tagRightResponse] at responseEqual
          | inl componentQuery =>

              have queryEqual : jointQuery = Sum.inr componentQuery := by
                simpa [tagRightResponse] using responseEqual.symm
              subst jointQuery
              have innerStart : @RightProjection B₁ C₁ B₂ C₂
                  (DDC.History.singleton
                    (B := Interface.parallel C₁ C₂)
                    (Sum.inr componentQuery :
                      (Interface.parallel B₁ B₂).query))
                  (DDC.History.singleton (B := C₂) componentQuery) := by
                exact ⟨rfl, rfl⟩
              obtain ⟨componentFinal, finalOuter, finalInner,
                  componentTail, finalEqual, finalOuterProjection,
                  finalInnerProjection⟩ :=
                inductionHypothesis componentOuter
                  (DDC.History.singleton (B := C₂) componentQuery)
                  outerProjection
                  innerStart
              exact ⟨componentFinal, finalOuter, finalInner,
                .outerQueryFirst componentResponds componentTail, finalEqual,
                finalOuterProjection, finalInnerProjection⟩
  | outerQueryNext closed responds tail inductionHypothesis =>
      rename_i currentOuter currentInner jointQuery jointResponse
        currentFinalOuter currentFinalInner
      cases componentInner with
      | none =>
          change (projectParallel currentInner).right = none at innerProjection
          obtain ⟨componentResponse, componentResponds, outerEqual,
              responseEqual⟩ :=
            component_mem_of_right outerLeft outerRight outerProjection responds
          cases componentResponse with
          | inr componentReply => simp [tagRightResponse] at responseEqual
          | inl componentQuery =>
              have jointQueryEqual : jointQuery = Sum.inr componentQuery := by
                simpa [tagRightResponse] using responseEqual.symm
              subst jointQuery
              have nextInner : @RightProjection B₁ C₁ B₂ C₂
                  (currentInner.snocOuter
                    (Sum.inr componentQuery :
                      (Interface.parallel B₁ B₂).query))
                  (DDC.History.singleton (B := C₂) componentQuery) := by
                constructor
                · rw [projectParallel_snocOuter_right]
                  simp [extendParallelProjection]
                · rw [projectParallel_snocOuter_right]
                  simp [extendParallelProjection, innerProjection, appendOuter]
              obtain ⟨componentFinal, finalOuter, finalInner,
                  componentTail, finalEqual, finalOuterProjection,
                  finalInnerProjection⟩ :=
                inductionHypothesis componentOuter
                  (DDC.History.singleton (B := C₂) componentQuery)
                  outerProjection nextInner
              exact ⟨componentFinal, finalOuter, finalInner,
                .outerQueryFirst componentResponds componentTail, finalEqual,
                finalOuterProjection, finalInnerProjection⟩
      | some componentInner =>
          change (projectParallel currentInner).right = some componentInner
            at innerProjection
          obtain ⟨componentResponse, componentResponds, _outerEqual,
              responseEqual⟩ :=
            component_mem_of_right outerLeft outerRight outerProjection responds
          cases componentResponse with
          | inr componentReply => simp [tagRightResponse] at responseEqual
          | inl componentQuery =>
              have jointQueryEqual : jointQuery = Sum.inr componentQuery := by
                simpa [tagRightResponse] using responseEqual.symm
              subst jointQuery
              have nextInner : @RightProjection B₁ C₁ B₂ C₂
                  (currentInner.snocOuter
                    (Sum.inr componentQuery :
                      (Interface.parallel B₁ B₂).query))
                  (componentInner.snocOuter componentQuery) := by
                constructor
                · rw [projectParallel_snocOuter_right]
                  simp [extendParallelProjection]
                · rw [projectParallel_snocOuter_right]
                  simp [extendParallelProjection, innerProjection, appendOuter]
              obtain ⟨componentFinal, finalOuter, finalInner,
                  componentTail, finalEqual, finalOuterProjection,
                  finalInnerProjection⟩ :=
                inductionHypothesis componentOuter
                  (componentInner.snocOuter componentQuery)
                  outerProjection nextInner
              exact ⟨componentFinal, finalOuter, finalInner,
                .outerQueryNext innerClosed componentResponds componentTail,
                finalEqual, finalOuterProjection, finalInnerProjection⟩
  | innerQuery linked responds componentOuter componentInner
      outerProjection innerProjection =>
      rename_i currentOuter currentInner jointQuery
      obtain ⟨componentOuterResponse, componentLinked, _outerEqual,
          linkedEqual⟩ :=
        component_mem_of_right outerLeft outerRight outerProjection linked
      cases componentOuterResponse with
      | inr componentReply => simp [tagRightResponse] at linkedEqual
      | inl componentMiddleQuery =>
          obtain ⟨componentInnerResponse, componentResponds, innerOuterEqual,
              responseEqual⟩ :=
            component_mem_of_right innerLeft innerRight innerProjection responds
          cases componentInnerResponse with
          | inr componentReply => simp [tagRightResponse] at responseEqual
          | inl componentQuery =>
              have middleQueryEqual : currentInner.lastOuter =
                  Sum.inr componentMiddleQuery := by
                simpa [tagRightResponse] using linkedEqual.symm
              have componentMiddleEqual : componentMiddleQuery =
                  componentInner.lastOuter :=
                Sum.inr.inj (middleQueryEqual.symm.trans innerOuterEqual)
              subst componentMiddleQuery
              have finalEqual : @tagRightPacked A₁ C₁ A₂ C₂
                  (Sum.inl componentQuery : PackedResponse A₂ C₂) =
                  (Sum.inl jointQuery : PackedResponse
                    (Interface.parallel A₁ A₂)
                    (Interface.parallel C₁ C₂)) := by
                simpa [tagRightResponse, tagRightPacked] using responseEqual
              exact ⟨Sum.inl componentQuery, componentOuter,
                some componentInner,
                .innerQuery componentLinked componentResponds, finalEqual,
                outerProjection, innerProjection.2⟩
  | innerReply linked responds tail inductionHypothesis componentOuter
      componentInner outerProjection innerProjection =>
      rename_i currentOuter currentInner jointReply jointResponse
        currentFinalOuter currentFinalInner
      obtain ⟨componentOuterResponse, componentLinked, _outerEqual,
          linkedEqual⟩ :=
        component_mem_of_right outerLeft outerRight outerProjection linked
      cases componentOuterResponse with
      | inr componentReply => simp [tagRightResponse] at linkedEqual
      | inl componentMiddleQuery =>
          obtain ⟨componentInnerResponse, componentResponds, innerOuterEqual,
              responseEqual⟩ :=
            component_mem_of_right innerLeft innerRight innerProjection responds
          cases componentInnerResponse with
          | inl componentQuery => simp [tagRightResponse] at responseEqual
          | inr componentReply =>
              have middleQueryEqual : currentInner.lastOuter =
                  Sum.inr componentMiddleQuery := by
                simpa [tagRightResponse] using linkedEqual.symm
              have componentMiddleEqual : componentMiddleQuery =
                  componentInner.lastOuter :=
                Sum.inr.inj (middleQueryEqual.symm.trans innerOuterEqual)
              subst componentMiddleQuery
              have replyEqual : cast
                  (congrArg (fun selected => Option
                    ((Interface.parallel B₁ B₂).answer selected))
                    innerOuterEqual.symm) componentReply = jointReply := by
                exact Sum.inr.inj responseEqual
              have nextOuter : RightProjection
                  (currentOuter.snocInner currentInner.lastOuter jointReply)
                  (componentOuter.snocInner componentInner.lastOuter
                    componentReply) :=
                outerProjection.snoc_inner_of_eq innerOuterEqual jointReply
                  componentReply replyEqual
              have projectedInner : RightHistoryProjection (some currentInner)
                  (some componentInner) := innerProjection.2
              obtain ⟨componentFinal, finalOuter, finalInner,
                  componentTail, finalEqual, finalOuterProjection,
                  finalInnerProjection⟩ :=
                inductionHypothesis nextOuter projectedInner
                  ⟨componentReply, componentResponds⟩
              exact ⟨componentFinal, finalOuter, finalInner,
                .innerReply componentLinked componentResponds componentTail,
                finalEqual, finalOuterProjection, finalInnerProjection⟩

private theorem InnerPrefixFactorization.projectLeft
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    (outerLeft : DDC A₁ B₁) (outerRight : DDC A₂ B₂)
    (innerLeft : DDC B₁ C₁) (innerRight : DDC B₂ C₂)
    {jointOuter jointInner jointResponse finalJointOuter finalJointInner}
    (factorization : InnerPrefixFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      jointOuter jointInner jointResponse finalJointOuter finalJointInner)
    {componentOuter : DDC.History A₁ B₁}
    {componentInner : DDC.History B₁ C₁}
    (outerProjection : LeftProjection jointOuter componentOuter)
    (innerProjection : LeftProjection jointInner componentInner) :
    factorization.LeftResult outerLeft outerRight innerLeft innerRight
      componentOuter componentInner := by
  cases factorization with
  | @innerQuery _ _ jointQuery linked responds =>
      obtain ⟨componentOuterResponse, componentLinked, _outerEqual,
          linkedEqual⟩ :=
        component_mem_of_left outerLeft outerRight outerProjection linked
      cases componentOuterResponse with
      | inr componentReply => simp [tagLeftResponse] at linkedEqual
      | inl componentMiddleQuery =>
          obtain ⟨componentInnerResponse, componentResponds, innerOuterEqual,
              responseEqual⟩ :=
            component_mem_of_left innerLeft innerRight innerProjection responds
          cases componentInnerResponse with
          | inr componentReply => simp [tagLeftResponse] at responseEqual
          | inl componentQuery =>
              have middleQueryEqual : jointInner.lastOuter =
                  Sum.inl componentMiddleQuery := by
                simpa [tagLeftResponse] using linkedEqual.symm
              have componentMiddleEqual : componentMiddleQuery =
                  componentInner.lastOuter :=
                Sum.inl.inj (middleQueryEqual.symm.trans innerOuterEqual)
              subst componentMiddleQuery
              have finalEqual : @tagLeftPacked A₁ C₁ A₂ C₂
                  (Sum.inl componentQuery : PackedResponse A₁ C₁) =
                  (Sum.inl jointQuery : PackedResponse
                    (Interface.parallel A₁ A₂)
                    (Interface.parallel C₁ C₂)) := by
                simpa [tagLeftResponse, tagLeftPacked] using responseEqual
              exact ⟨Sum.inl componentQuery, componentOuter,
                some componentInner,
                .innerQuery componentLinked componentResponds, finalEqual,
                outerProjection, innerProjection.2⟩
  | @innerReply _ _ jointReply _ _ _ linked responds tail =>
      obtain ⟨componentOuterResponse, componentLinked, _outerEqual,
          linkedEqual⟩ :=
        component_mem_of_left outerLeft outerRight outerProjection linked
      cases componentOuterResponse with
      | inr componentReply => simp [tagLeftResponse] at linkedEqual
      | inl componentMiddleQuery =>
          obtain ⟨componentInnerResponse, componentResponds, innerOuterEqual,
              responseEqual⟩ :=
            component_mem_of_left innerLeft innerRight innerProjection responds
          cases componentInnerResponse with
          | inl componentQuery => simp [tagLeftResponse] at responseEqual
          | inr componentReply =>
              have middleQueryEqual : jointInner.lastOuter =
                  Sum.inl componentMiddleQuery := by
                simpa [tagLeftResponse] using linkedEqual.symm
              have componentMiddleEqual : componentMiddleQuery =
                  componentInner.lastOuter :=
                Sum.inl.inj (middleQueryEqual.symm.trans innerOuterEqual)
              subst componentMiddleQuery
              have replyEqual : cast
                  (congrArg (fun selected => Option
                    ((Interface.parallel B₁ B₂).answer selected))
                    innerOuterEqual.symm) componentReply = jointReply := by
                exact Sum.inr.inj responseEqual
              have nextOuter : LeftProjection
                  (jointOuter.snocInner jointInner.lastOuter jointReply)
                  (componentOuter.snocInner componentInner.lastOuter
                    componentReply) :=
                outerProjection.snoc_inner_of_eq innerOuterEqual jointReply
                  componentReply replyEqual
              have projectedInner : LeftHistoryProjection (some jointInner)
                  (some componentInner) := innerProjection.2
              obtain ⟨componentFinal, finalOuter, finalInner,
                  componentTail, finalEqual, finalOuterProjection,
                  finalInnerProjection⟩ :=
                tail.projectLeft outerLeft outerRight innerLeft innerRight
                  nextOuter projectedInner ⟨componentReply, componentResponds⟩
              exact ⟨componentFinal, finalOuter, finalInner,
                .innerReply componentLinked componentResponds componentTail,
                finalEqual, finalOuterProjection, finalInnerProjection⟩

private theorem InnerPrefixFactorization.projectRight

    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    (outerLeft : DDC A₁ B₁) (outerRight : DDC A₂ B₂)
    (innerLeft : DDC B₁ C₁) (innerRight : DDC B₂ C₂)
    {jointOuter jointInner jointResponse finalJointOuter finalJointInner}
    (factorization : InnerPrefixFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      jointOuter jointInner jointResponse finalJointOuter finalJointInner)
    {componentOuter : DDC.History A₂ B₂}
    {componentInner : DDC.History B₂ C₂}
    (outerProjection : RightProjection jointOuter componentOuter)
    (innerProjection : RightProjection jointInner componentInner) :
    factorization.RightResult outerLeft outerRight innerLeft innerRight
      componentOuter componentInner := by
  cases factorization with
  | @innerQuery _ _ jointQuery linked responds =>
      obtain ⟨componentOuterResponse, componentLinked, _outerEqual,
          linkedEqual⟩ :=
        component_mem_of_right outerLeft outerRight outerProjection linked
      cases componentOuterResponse with
      | inr componentReply => simp [tagRightResponse] at linkedEqual
      | inl componentMiddleQuery =>
          obtain ⟨componentInnerResponse, componentResponds, innerOuterEqual,
              responseEqual⟩ :=
            component_mem_of_right innerLeft innerRight innerProjection responds
          cases componentInnerResponse with
          | inr componentReply => simp [tagRightResponse] at responseEqual
          | inl componentQuery =>

              have middleQueryEqual : jointInner.lastOuter =
                  Sum.inr componentMiddleQuery := by
                simpa [tagRightResponse] using linkedEqual.symm
              have componentMiddleEqual : componentMiddleQuery =
                  componentInner.lastOuter :=
                Sum.inr.inj (middleQueryEqual.symm.trans innerOuterEqual)
              subst componentMiddleQuery
              have finalEqual : @tagRightPacked A₁ C₁ A₂ C₂
                  (Sum.inl componentQuery : PackedResponse A₂ C₂) =
                  (Sum.inl jointQuery : PackedResponse
                    (Interface.parallel A₁ A₂)
                    (Interface.parallel C₁ C₂)) := by
                simpa [tagRightResponse, tagRightPacked] using responseEqual
              exact ⟨Sum.inl componentQuery, componentOuter,
                some componentInner,
                .innerQuery componentLinked componentResponds, finalEqual,
                outerProjection, innerProjection.2⟩
  | @innerReply _ _ jointReply _ _ _ linked responds tail =>
      obtain ⟨componentOuterResponse, componentLinked, _outerEqual,
          linkedEqual⟩ :=
        component_mem_of_right outerLeft outerRight outerProjection linked
      cases componentOuterResponse with
      | inr componentReply => simp [tagRightResponse] at linkedEqual
      | inl componentMiddleQuery =>
          obtain ⟨componentInnerResponse, componentResponds, innerOuterEqual,
              responseEqual⟩ :=
            component_mem_of_right innerLeft innerRight innerProjection responds
          cases componentInnerResponse with
          | inl componentQuery => simp [tagRightResponse] at responseEqual
          | inr componentReply =>
              have middleQueryEqual : jointInner.lastOuter =
                  Sum.inr componentMiddleQuery := by
                simpa [tagRightResponse] using linkedEqual.symm
              have componentMiddleEqual : componentMiddleQuery =
                  componentInner.lastOuter :=
                Sum.inr.inj (middleQueryEqual.symm.trans innerOuterEqual)
              subst componentMiddleQuery
              have replyEqual : cast
                  (congrArg (fun selected => Option
                    ((Interface.parallel B₁ B₂).answer selected))
                    innerOuterEqual.symm) componentReply = jointReply := by
                exact Sum.inr.inj responseEqual
              have nextOuter : RightProjection
                  (jointOuter.snocInner jointInner.lastOuter jointReply)
                  (componentOuter.snocInner componentInner.lastOuter
                    componentReply) :=
                outerProjection.snoc_inner_of_eq innerOuterEqual jointReply
                  componentReply replyEqual
              have projectedInner : RightHistoryProjection (some jointInner)
                  (some componentInner) := innerProjection.2
              obtain ⟨componentFinal, finalOuter, finalInner,
                  componentTail, finalEqual, finalOuterProjection,
                  finalInnerProjection⟩ :=
                tail.projectRight outerLeft outerRight innerLeft innerRight
                  nextOuter projectedInner ⟨componentReply, componentResponds⟩
              exact ⟨componentFinal, finalOuter, finalInner,
                .innerReply componentLinked componentResponds componentTail,
                finalEqual, finalOuterProjection, finalInnerProjection⟩

private def optionalLeftHistory
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}} :
    Option (DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)) → Option (DDC.History A₁ B₁)
  | none => none
  | some history => (projectParallel history).left

private def optionalRightHistory
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}} :
    Option (DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)) → Option (DDC.History A₂ B₂)
  | none => none
  | some history => (projectParallel history).right

private theorem active_left_of_query_mem
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)) (query : B₁.query)
    (responds : Sum.inl (Sum.inl query) ∈ parallel left right history) :
    (projectParallel history).active = some .left := by
  have admissible := ((mem_parallel_iff left right history _).mp responds).1
  rcases parallelRaw_admissible_active left right admissible with
    ⟨component, active⟩ | ⟨component, active⟩
  · exact active.1
  · obtain ⟨componentResponse, componentResponds, responseEqual⟩ :=
      (mem_parallel_active_right_iff left right history component active
        admissible _).mp responds
    cases componentResponse with
    | inl componentQuery => cases Sum.inl.inj responseEqual
    | inr componentReply => simp [tagRightResponse] at responseEqual

private theorem active_right_of_query_mem
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)) (query : B₂.query)
    (responds : Sum.inl (Sum.inr query) ∈ parallel left right history) :
    (projectParallel history).active = some .right := by
  have admissible := ((mem_parallel_iff left right history _).mp responds).1
  rcases parallelRaw_admissible_active left right admissible with
    ⟨component, active⟩ | ⟨component, active⟩
  · obtain ⟨componentResponse, componentResponds, responseEqual⟩ :=
      (mem_parallel_active_left_iff left right history component active
        admissible _).mp responds
    cases componentResponse with
    | inl componentQuery => cases Sum.inl.inj responseEqual
    | inr componentReply => simp [tagLeftResponse] at responseEqual
  · exact active.1

private theorem query_eq_left_of_active
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (query : (Interface.parallel B₁ B₂).query)
    (active : (projectParallel history).active = some .left)
    (responds : Sum.inl query ∈ parallel left right history) :
    ∃ componentQuery, query = Sum.inl componentQuery := by
  have admissible := ((mem_parallel_iff left right history _).mp responds).1
  have valid := parallelRaw_admissible_projection left right admissible
  obtain ⟨component, componentActive⟩ := valid.activeLeftPresent active
  obtain ⟨componentResponse, componentResponds, _outerEqual,
      responseEqual⟩ := component_mem_of_left left right
        ⟨active, componentActive.2.1⟩ responds
  cases componentResponse with
  | inl componentQuery =>
      exact ⟨componentQuery, by
        simpa [tagLeftResponse] using responseEqual.symm⟩
  | inr componentReply => simp [tagLeftResponse] at responseEqual

private theorem query_eq_right_of_active
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (query : (Interface.parallel B₁ B₂).query)
    (active : (projectParallel history).active = some .right)
    (responds : Sum.inl query ∈ parallel left right history) :
    ∃ componentQuery, query = Sum.inr componentQuery := by
  have admissible := ((mem_parallel_iff left right history _).mp responds).1
  have valid := parallelRaw_admissible_projection left right admissible
  obtain ⟨component, componentActive⟩ := valid.activeRightPresent active
  obtain ⟨componentResponse, componentResponds, _outerEqual,
      responseEqual⟩ := component_mem_of_right left right
        ⟨active, componentActive.2.1⟩ responds
  cases componentResponse with
  | inl componentQuery =>
      exact ⟨componentQuery, by
        simpa [tagRightResponse] using responseEqual.symm⟩
  | inr componentReply => simp [tagRightResponse] at responseEqual

private theorem projectParallel_snocInner_left_of_eq
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    {jointQuery : (Interface.parallel B₁ B₂).query}
    {componentQuery : B₁.query}
    (queryEqual : jointQuery = Sum.inl componentQuery)
    (reply : Option ((Interface.parallel B₁ B₂).answer jointQuery))
    (active : (projectParallel history).active = some .left) :
    (projectParallel (history.snocInner jointQuery reply)).active =
        some .left ∧
      (projectParallel (history.snocInner jointQuery reply)).right =
        (projectParallel history).right := by
  subst jointQuery
  rw [projectParallel_snocInner_left]
  simp [extendParallelProjection, active]

private theorem projectParallel_snocInner_right_of_eq
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    {jointQuery : (Interface.parallel B₁ B₂).query}
    {componentQuery : B₂.query}
    (queryEqual : jointQuery = Sum.inr componentQuery)
    (reply : Option ((Interface.parallel B₁ B₂).answer jointQuery))
    (active : (projectParallel history).active = some .right) :
    (projectParallel (history.snocInner jointQuery reply)).active =
        some .right ∧
      (projectParallel (history.snocInner jointQuery reply)).left =
        (projectParallel history).left := by
  subst jointQuery
  rw [projectParallel_snocInner_right]
  simp [extendParallelProjection, active]

private theorem packResponse_injective_local
    {A C : Interface.{u, v}} (history : DDC.History A C) :
    Function.Injective (packResponse history) := by
  intro left right equal
  cases left with
  | inl leftQuery =>
      cases right with
      | inl rightQuery => exact congrArg Sum.inl (Sum.inl.inj equal)
      | inr rightReply => cases equal
  | inr leftReply =>
      cases right with
      | inl rightQuery => cases equal
      | inr rightReply =>
          have packedEqual := Sum.inr.inj equal
          cases packedEqual
          rfl

private theorem SerialFactorization.start_left_projection
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    (outerLeft : DDC A₁ B₁) (outerRight : DDC A₂ B₂)
    (innerLeft : DDC B₁ C₁) (innerRight : DDC B₂ C₂)
    (input : A₁.query) {response finalOuter finalInner}
    (middleFactorization : OuterPrefixFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      (DDC.History.singleton (B := Interface.parallel B₁ B₂)
        (Sum.inl input)) none response finalOuter finalInner)
    (valid : PrefixEndpointValid (parallel outerLeft outerRight)
      (parallel innerLeft innerRight) response finalOuter finalInner) :
    ∃ componentResponse componentOuter componentInner,
      OuterPrefixFactorization outerLeft innerLeft
        (DDC.History.singleton (B := B₁) input) none componentResponse
          componentOuter componentInner ∧
      tagLeftPacked componentResponse = response ∧
      LeftProjection finalOuter componentOuter ∧
      LeftHistoryProjection finalInner componentInner ∧
      ∃ actual : DDC.Response
          (DDC.History.singleton

            (B := Interface.parallel C₁ C₂) (Sum.inl input)),
        packResponse
            (DDC.History.singleton
              (B := Interface.parallel C₁ C₂) (Sum.inl input)) actual =
          response ∧
        actual ∈ parallel (serial outerLeft innerLeft)
          (serial outerRight innerRight)
            (DDC.History.singleton
              (B := Interface.parallel C₁ C₂) (Sum.inl input)) := by
  let jointHistory : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel C₁ C₂) :=
    DDC.History.singleton (B := Interface.parallel C₁ C₂) (Sum.inl input)
  let componentHistory : DDC.History A₁ C₁ :=
    DDC.History.singleton (B := C₁) input
  have initialOuter : @LeftProjection A₁ B₁ A₂ B₂
      (DDC.History.singleton (B := Interface.parallel B₁ B₂)
        (Sum.inl input : (Interface.parallel A₁ A₂).query))
      (DDC.History.singleton (B := B₁) input) := ⟨rfl, rfl⟩
  obtain ⟨componentResponse, componentOuter, componentInner,
      componentPrefix, responseEqual, finalOuterProjection,
      finalInnerProjection⟩ :=
    middleFactorization.projectLeft outerLeft outerRight innerLeft innerRight
      (componentInner := none) initialOuter
      (by simp [LeftHistoryProjection]) trivial
  have componentValid := componentPrefix.endpointValid
    (DDC.Raw.Admissible.start input)
    (by intro history impossible; cases impossible) trivial
  let componentWhole : SerialFactorization outerLeft innerLeft
      (.start input) componentResponse componentOuter componentInner :=
    .start componentPrefix componentValid
  obtain ⟨componentActual, componentPacked⟩ := componentWhole.realizeResponse
  let jointWhole : SerialFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      (.start (Sum.inl input)) response finalOuter finalInner :=
    .start middleFactorization valid
  obtain ⟨jointActual, jointPacked⟩ := jointWhole.realizeResponse
  have componentMembership : componentActual ∈
      serial outerLeft innerLeft componentHistory := by
    change componentActual ∈ serial outerLeft innerLeft
      (AttemptedHistory.start input).toReceived
    rw [mem_serial_iff, mem_serialRaw_iff]
    refine ⟨.start input, rfl, componentOuter, componentInner, ?_⟩
    rw [componentPacked]
    exact componentWhole
  have active : ActiveLeft jointHistory componentHistory := ⟨rfl, rfl, rfl⟩
  have admissible : DDC.Raw.Admissible
      (parallelRaw (serial outerLeft innerLeft)
        (serial outerRight innerRight)) jointHistory := .start _
  have taggedEqual : tagLeftResponse jointHistory componentHistory rfl
      componentActual = jointActual := by
    apply packResponse_injective_local jointHistory
    calc
      packResponse jointHistory
          (tagLeftResponse jointHistory componentHistory rfl
            componentActual) =
          tagLeftPacked (packResponse componentHistory componentActual) :=
        packResponse_tagLeft jointHistory componentHistory rfl componentActual
      _ = tagLeftPacked componentResponse :=
        congrArg tagLeftPacked componentPacked
      _ = response := responseEqual
      _ = packResponse jointHistory jointActual := jointPacked.symm
  have jointMembership : jointActual ∈ parallel
      (serial outerLeft innerLeft) (serial outerRight innerRight)
      jointHistory :=
    (mem_parallel_active_left_iff (serial outerLeft innerLeft)
      (serial outerRight innerRight) jointHistory componentHistory active
      admissible jointActual).mpr
        ⟨componentActual, componentMembership, taggedEqual⟩
  exact ⟨componentResponse, componentOuter, componentInner, componentPrefix,
    responseEqual, finalOuterProjection, finalInnerProjection, jointActual,
    jointPacked, jointMembership⟩

private theorem SerialFactorization.start_right_projection
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    (outerLeft : DDC A₁ B₁) (outerRight : DDC A₂ B₂)
    (innerLeft : DDC B₁ C₁) (innerRight : DDC B₂ C₂)
    (input : A₂.query) {response finalOuter finalInner}
    (middleFactorization : OuterPrefixFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      (DDC.History.singleton (B := Interface.parallel B₁ B₂)
        (Sum.inr input)) none response finalOuter finalInner)
    (valid : PrefixEndpointValid (parallel outerLeft outerRight)
      (parallel innerLeft innerRight) response finalOuter finalInner) :
    ∃ componentResponse componentOuter componentInner,
      OuterPrefixFactorization outerRight innerRight
        (DDC.History.singleton (B := B₂) input) none componentResponse
          componentOuter componentInner ∧
      tagRightPacked componentResponse = response ∧
      RightProjection finalOuter componentOuter ∧
      RightHistoryProjection finalInner componentInner ∧
      ∃ actual : DDC.Response
          (DDC.History.singleton
            (B := Interface.parallel C₁ C₂) (Sum.inr input)),
        packResponse
            (DDC.History.singleton
              (B := Interface.parallel C₁ C₂) (Sum.inr input)) actual =
          response ∧
        actual ∈ parallel (serial outerLeft innerLeft)
          (serial outerRight innerRight)
            (DDC.History.singleton
              (B := Interface.parallel C₁ C₂) (Sum.inr input)) := by
  let jointHistory : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel C₁ C₂) :=
    DDC.History.singleton (B := Interface.parallel C₁ C₂) (Sum.inr input)
  let componentHistory : DDC.History A₂ C₂ :=
    DDC.History.singleton (B := C₂) input
  have initialOuter : @RightProjection A₁ B₁ A₂ B₂
      (DDC.History.singleton (B := Interface.parallel B₁ B₂)
        (Sum.inr input : (Interface.parallel A₁ A₂).query))
      (DDC.History.singleton (B := B₂) input) := ⟨rfl, rfl⟩
  obtain ⟨componentResponse, componentOuter, componentInner,
      componentPrefix, responseEqual, finalOuterProjection,
      finalInnerProjection⟩ :=
    middleFactorization.projectRight outerLeft outerRight innerLeft innerRight
      (componentInner := none) initialOuter
      (by simp [RightHistoryProjection]) trivial
  have componentValid := componentPrefix.endpointValid
    (DDC.Raw.Admissible.start input)
    (by intro history impossible; cases impossible) trivial
  let componentWhole : SerialFactorization outerRight innerRight
      (.start input) componentResponse componentOuter componentInner :=
    .start componentPrefix componentValid
  obtain ⟨componentActual, componentPacked⟩ := componentWhole.realizeResponse
  let jointWhole : SerialFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      (.start (Sum.inr input)) response finalOuter finalInner :=
    .start middleFactorization valid
  obtain ⟨jointActual, jointPacked⟩ := jointWhole.realizeResponse
  have componentMembership : componentActual ∈
      serial outerRight innerRight componentHistory := by
    change componentActual ∈ serial outerRight innerRight
      (AttemptedHistory.start input).toReceived
    rw [mem_serial_iff, mem_serialRaw_iff]
    refine ⟨.start input, rfl, componentOuter, componentInner, ?_⟩
    rw [componentPacked]
    exact componentWhole
  have active : ActiveRight jointHistory componentHistory := ⟨rfl, rfl, rfl⟩
  have admissible : DDC.Raw.Admissible
      (parallelRaw (serial outerLeft innerLeft)
        (serial outerRight innerRight)) jointHistory := .start _
  have taggedEqual : tagRightResponse jointHistory componentHistory rfl
      componentActual = jointActual := by
    apply packResponse_injective_local jointHistory
    calc
      packResponse jointHistory
          (tagRightResponse jointHistory componentHistory rfl
            componentActual) =
          tagRightPacked (packResponse componentHistory componentActual) :=
        packResponse_tagRight jointHistory componentHistory rfl componentActual
      _ = tagRightPacked componentResponse :=
        congrArg tagRightPacked componentPacked
      _ = response := responseEqual
      _ = packResponse jointHistory jointActual := jointPacked.symm
  have jointMembership : jointActual ∈ parallel
      (serial outerLeft innerLeft) (serial outerRight innerRight)
      jointHistory :=
    (mem_parallel_active_right_iff (serial outerLeft innerLeft)
      (serial outerRight innerRight) jointHistory componentHistory active
      admissible jointActual).mpr
        ⟨componentActual, componentMembership, taggedEqual⟩
  exact ⟨componentResponse, componentOuter, componentInner, componentPrefix,
    responseEqual, finalOuterProjection, finalInnerProjection, jointActual,
    jointPacked, jointMembership⟩

private theorem OuterPrefixFactorization.preservesRight
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    {outerLeft : DDC A₁ B₁} {outerRight : DDC A₂ B₂}
    {innerLeft : DDC B₁ C₁} {innerRight : DDC B₂ C₂}
    {jointOuter finalJointOuter jointInner finalJointInner jointResponse}
    (factorization : OuterPrefixFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      jointOuter jointInner jointResponse finalJointOuter finalJointInner)
    (outerActive : (projectParallel jointOuter).active = some .left) :
    (projectParallel finalJointOuter).right =
        (projectParallel jointOuter).right ∧
      optionalRightHistory finalJointInner =
        optionalRightHistory jointInner := by
  induction factorization using OuterPrefixFactorization.rec
      (motive_2 := fun currentOuter currentInner currentResponse finalOuter
        finalInner currentFactorization =>
          (projectParallel currentOuter).active = some .left →
          (projectParallel currentInner).active = some .left →
          (projectParallel finalOuter).right =
              (projectParallel currentOuter).right ∧
            optionalRightHistory finalInner =
              (projectParallel currentInner).right) with
  | outerReply responds => exact ⟨rfl, rfl⟩
  | outerQueryFirst responds tail inductionHypothesis =>
      rename_i currentOuter jointQuery currentResponse currentFinalOuter
        currentFinalInner
      obtain ⟨componentQuery, queryEqual⟩ :=
        query_eq_left_of_active outerLeft outerRight currentOuter jointQuery
          outerActive responds
      subst jointQuery
      have result := inductionHypothesis outerActive (by rfl)
      simpa [optionalRightHistory] using result
  | outerQueryNext closed responds tail inductionHypothesis =>
      rename_i currentOuter currentInner jointQuery currentResponse
        currentFinalOuter currentFinalInner
      obtain ⟨componentQuery, queryEqual⟩ :=
        query_eq_left_of_active outerLeft outerRight currentOuter jointQuery
          outerActive responds
      subst jointQuery
      have nextActive :
          (projectParallel
            (currentInner.snocOuter (Sum.inl componentQuery))).active =
              some .left := by
        rw [projectParallel_snocOuter_left]
        simp [extendParallelProjection]
      have result := inductionHypothesis outerActive nextActive
      simpa [optionalRightHistory, projectParallel_snocOuter_left,
        extendParallelProjection] using result
  | innerQuery linked responds => exact ⟨rfl, rfl⟩
  | @innerReply currentOuter currentInner jointReply currentResponse
      currentFinalOuter currentFinalInner linked responds tail
      inductionHypothesis outerActive innerActive =>
      obtain ⟨componentQuery, queryEqual⟩ :=
        query_eq_left_of_active outerLeft outerRight currentOuter
          currentInner.lastOuter outerActive linked
      have nextProjection := projectParallel_snocInner_left_of_eq currentOuter
        queryEqual jointReply outerActive
      have nextActive := nextProjection.1
      have result := inductionHypothesis nextActive
      constructor
      · calc
          (projectParallel currentFinalOuter).right =
              (projectParallel
                (currentOuter.snocInner currentInner.lastOuter
                  jointReply)).right := result.1
          _ = (projectParallel currentOuter).right := nextProjection.2
      · exact result.2

private theorem OuterPrefixFactorization.preservesLeft
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    {outerLeft : DDC A₁ B₁} {outerRight : DDC A₂ B₂}
    {innerLeft : DDC B₁ C₁} {innerRight : DDC B₂ C₂}
    {jointOuter finalJointOuter jointInner finalJointInner jointResponse}
    (factorization : OuterPrefixFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      jointOuter jointInner jointResponse finalJointOuter finalJointInner)
    (outerActive : (projectParallel jointOuter).active = some .right) :
    (projectParallel finalJointOuter).left =
        (projectParallel jointOuter).left ∧
      optionalLeftHistory finalJointInner =
        optionalLeftHistory jointInner := by
  induction factorization using OuterPrefixFactorization.rec
      (motive_2 := fun currentOuter currentInner currentResponse finalOuter
        finalInner currentFactorization =>
          (projectParallel currentOuter).active = some .right →
          (projectParallel currentInner).active = some .right →

          (projectParallel finalOuter).left =
              (projectParallel currentOuter).left ∧
            optionalLeftHistory finalInner =
              (projectParallel currentInner).left) with
  | outerReply responds => exact ⟨rfl, rfl⟩
  | outerQueryFirst responds tail inductionHypothesis =>
      rename_i currentOuter jointQuery currentResponse currentFinalOuter
        currentFinalInner
      obtain ⟨componentQuery, queryEqual⟩ :=
        query_eq_right_of_active outerLeft outerRight currentOuter jointQuery
          outerActive responds
      subst jointQuery
      have result := inductionHypothesis outerActive (by rfl)
      simpa [optionalLeftHistory] using result
  | outerQueryNext closed responds tail inductionHypothesis =>
      rename_i currentOuter currentInner jointQuery currentResponse
        currentFinalOuter currentFinalInner
      obtain ⟨componentQuery, queryEqual⟩ :=
        query_eq_right_of_active outerLeft outerRight currentOuter jointQuery
          outerActive responds
      subst jointQuery
      have nextActive :
          (projectParallel
            (currentInner.snocOuter (Sum.inr componentQuery))).active =
              some .right := by
        rw [projectParallel_snocOuter_right]
        simp [extendParallelProjection]
      have result := inductionHypothesis outerActive nextActive
      simpa [optionalLeftHistory, projectParallel_snocOuter_right,
        extendParallelProjection] using result
  | innerQuery linked responds => exact ⟨rfl, rfl⟩
  | @innerReply currentOuter currentInner jointReply currentResponse
      currentFinalOuter currentFinalInner linked responds tail
      inductionHypothesis outerActive innerActive =>
      obtain ⟨componentQuery, queryEqual⟩ :=
        query_eq_right_of_active outerLeft outerRight currentOuter
          currentInner.lastOuter outerActive linked
      have nextProjection := projectParallel_snocInner_right_of_eq currentOuter
        queryEqual jointReply outerActive
      have nextActive := nextProjection.1
      have result := inductionHypothesis nextActive
      constructor
      · calc
          (projectParallel currentFinalOuter).left =
              (projectParallel
                (currentOuter.snocInner currentInner.lastOuter
                  jointReply)).left := result.1
          _ = (projectParallel currentOuter).left := nextProjection.2
      · exact result.2

private theorem InnerPrefixFactorization.preservesRight
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    {outerLeft : DDC A₁ B₁} {outerRight : DDC A₂ B₂}
    {innerLeft : DDC B₁ C₁} {innerRight : DDC B₂ C₂}
    {jointOuter jointInner jointResponse finalJointOuter finalJointInner}
    (factorization : InnerPrefixFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      jointOuter jointInner jointResponse finalJointOuter finalJointInner)
    (outerActive : (projectParallel jointOuter).active = some .left)
    (_innerActive : (projectParallel jointInner).active = some .left) :
    (projectParallel finalJointOuter).right =
        (projectParallel jointOuter).right ∧
      optionalRightHistory finalJointInner =
        (projectParallel jointInner).right := by
  cases factorization with
  | innerQuery linked responds => exact ⟨rfl, rfl⟩
  | @innerReply _ _ jointReply _ _ _ linked responds tail =>
      obtain ⟨componentQuery, queryEqual⟩ :=
        query_eq_left_of_active outerLeft outerRight jointOuter
          jointInner.lastOuter outerActive linked
      have nextProjection := projectParallel_snocInner_left_of_eq jointOuter
        queryEqual jointReply outerActive
      have result := tail.preservesRight nextProjection.1
      exact ⟨result.1.trans nextProjection.2, result.2⟩

private theorem InnerPrefixFactorization.preservesLeft
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    {outerLeft : DDC A₁ B₁} {outerRight : DDC A₂ B₂}
    {innerLeft : DDC B₁ C₁} {innerRight : DDC B₂ C₂}
    {jointOuter jointInner jointResponse finalJointOuter finalJointInner}
    (factorization : InnerPrefixFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      jointOuter jointInner jointResponse finalJointOuter finalJointInner)
    (outerActive : (projectParallel jointOuter).active = some .right)
    (_innerActive : (projectParallel jointInner).active = some .right) :
    (projectParallel finalJointOuter).left =
        (projectParallel jointOuter).left ∧
      optionalLeftHistory finalJointInner =
        (projectParallel jointInner).left := by
  cases factorization with
  | innerQuery linked responds => exact ⟨rfl, rfl⟩
  | @innerReply _ _ jointReply _ _ _ linked responds tail =>
      obtain ⟨componentQuery, queryEqual⟩ :=
        query_eq_right_of_active outerLeft outerRight jointOuter
          jointInner.lastOuter outerActive linked
      have nextProjection := projectParallel_snocInner_right_of_eq jointOuter
        queryEqual jointReply outerActive
      have result := tail.preservesLeft nextProjection.1
      exact ⟨result.1.trans nextProjection.2, result.2⟩

private theorem OptionalComponentHistories.snoc_outer_left
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    {joint : Option (DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))}
    {left : Option (DDC.History A₁ B₁)}
    {right : Option (DDC.History A₂ B₂)}
    (projection : OptionalComponentHistories joint left right)
    (query : A₁.query) :
    OptionalComponentHistories
      (some (appendOuter joint (Sum.inl query)))
      (some (appendOuter left query)) right := by
  cases joint with
  | none =>
      change left = none ∧ right = none at projection
      rcases projection with ⟨rfl, rfl⟩
      simp [OptionalComponentHistories, appendOuter]
  | some joint =>
      change (projectParallel joint).left = left ∧
        (projectParallel joint).right = right at projection
      change
        (projectParallel (joint.snocOuter (Sum.inl query))).left =
            some (appendOuter left query) ∧
          (projectParallel (joint.snocOuter (Sum.inl query))).right = right
      rw [projectParallel_snocOuter_left]
      simp [extendParallelProjection, projection.1, projection.2, appendOuter]

private theorem OptionalComponentHistories.snoc_outer_right
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    {joint : Option (DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))}
    {left : Option (DDC.History A₁ B₁)}
    {right : Option (DDC.History A₂ B₂)}
    (projection : OptionalComponentHistories joint left right)
    (query : A₂.query) :
    OptionalComponentHistories
      (some (appendOuter joint (Sum.inr query))) left
      (some (appendOuter right query)) := by
  cases joint with
  | none =>
      change left = none ∧ right = none at projection
      rcases projection with ⟨rfl, rfl⟩
      simp [OptionalComponentHistories, appendOuter]
  | some joint =>
      change (projectParallel joint).left = left ∧
        (projectParallel joint).right = right at projection
      change
        (projectParallel (joint.snocOuter (Sum.inr query))).left = left ∧
          (projectParallel (joint.snocOuter (Sum.inr query))).right =
            some (appendOuter right query)
      rw [projectParallel_snocOuter_right]
      simp [extendParallelProjection, projection.1, projection.2, appendOuter]

private theorem OptionalComponentHistories.snoc_inner_left
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    {joint : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {left : DDC.History A₁ B₁}
    {right : Option (DDC.History A₂ B₂)}
    (projection : OptionalComponentHistories (some joint) (some left) right)
    (query : B₁.query) (reply : Option (B₁.answer query)) :
    OptionalComponentHistories
      (some (joint.snocInner (Sum.inl query) reply))
      (some (left.snocInner query reply)) right := by
  change (projectParallel joint).left = some left ∧
    (projectParallel joint).right = right at projection
  change
    (projectParallel (joint.snocInner (Sum.inl query) reply)).left =
        some (left.snocInner query reply) ∧
      (projectParallel (joint.snocInner (Sum.inl query) reply)).right = right
  rw [projectParallel_snocInner_left]
  simp [extendParallelProjection, projection.1, projection.2]

private theorem OptionalComponentHistories.snoc_inner_right
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    {joint : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {left : Option (DDC.History A₁ B₁)}
    {right : DDC.History A₂ B₂}
    (projection : OptionalComponentHistories (some joint) left (some right))
    (query : B₂.query) (reply : Option (B₂.answer query)) :
    OptionalComponentHistories
      (some (joint.snocInner (Sum.inr query) reply)) left
      (some (right.snocInner query reply)) := by
  change (projectParallel joint).left = left ∧
    (projectParallel joint).right = some right at projection
  change
    (projectParallel (joint.snocInner (Sum.inr query) reply)).left = left ∧
      (projectParallel (joint.snocInner (Sum.inr query) reply)).right =
        some (right.snocInner query reply)
  rw [projectParallel_snocInner_right]
  simp [extendParallelProjection, projection.1, projection.2]

private theorem OptionalComponentHistories.left_of_some
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    {joint : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {left : DDC.History A₁ B₁}
    {right : Option (DDC.History A₂ B₂)}
    (projection : OptionalComponentHistories (some joint) (some left) right)
    (active : (projectParallel joint).active = some .left) :
    LeftProjection joint left := ⟨active, projection.1⟩

private theorem OptionalComponentHistories.right_of_some
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    {joint : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {left : Option (DDC.History A₁ B₁)}
    {right : DDC.History A₂ B₂}
    (projection : OptionalComponentHistories (some joint) left (some right))
    (active : (projectParallel joint).active = some .right) :
    RightProjection joint right := ⟨active, projection.2⟩

private theorem OptionalComponentHistories.left_eq
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    {joint : Option (DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))}
    {left : Option (DDC.History A₁ B₁)}
    {right : Option (DDC.History A₂ B₂)}
    (projection : OptionalComponentHistories joint left right) :
    optionalLeftHistory joint = left := by
  cases joint with
  | none => exact projection.1.symm
  | some history => exact projection.1

private theorem OptionalComponentHistories.right_eq
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    {joint : Option (DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))}
    {left : Option (DDC.History A₁ B₁)}
    {right : Option (DDC.History A₂ B₂)}
    (projection : OptionalComponentHistories joint left right) :
    optionalRightHistory joint = right := by
  cases joint with
  | none => exact projection.2.symm
  | some history => exact projection.2

private theorem OptionalComponentHistories.of_left
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    {joint : Option (DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))}
    {left : Option (DDC.History A₁ B₁)}
    {right : Option (DDC.History A₂ B₂)}
    (leftProjection : LeftHistoryProjection joint left)
    (rightEqual : optionalRightHistory joint = right) :
    OptionalComponentHistories joint left right := by
  cases joint <;> cases left <;> cases right <;>
    simp [LeftHistoryProjection, optionalRightHistory,
      OptionalComponentHistories] at leftProjection rightEqual ⊢
  all_goals exact ⟨leftProjection, rightEqual⟩


private theorem OptionalComponentHistories.of_right
    {A₁ : Interface.{u, v}} {B₁ : Interface.{w, z}}
    {A₂ : Interface.{u, v}} {B₂ : Interface.{w, z}}
    {joint : Option (DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))}
    {left : Option (DDC.History A₁ B₁)}
    {right : Option (DDC.History A₂ B₂)}
    (leftEqual : optionalLeftHistory joint = left)
    (rightProjection : RightHistoryProjection joint right) :
    OptionalComponentHistories joint left right := by
  cases joint <;> cases left <;> cases right <;>
    simp [RightHistoryProjection, optionalLeftHistory,
      OptionalComponentHistories] at leftEqual rightProjection ⊢
  all_goals exact ⟨leftEqual, rightProjection⟩

private inductive OptionalSerialFactorization
    {A B C : Interface.{u, v}} (outer : DDC A B) (inner : DDC B C) :
    Option (AttemptedHistory A C) → Option (PackedResponse A C) →
      Option (DDC.History A B) →
      Option (DDC.History B C) → Prop
  | none : OptionalSerialFactorization outer inner none none none none
  | some {history response outerHistory innerHistory}
      (factorization : SerialFactorization outer inner history response
        outerHistory innerHistory) :
      OptionalSerialFactorization outer inner (some history) (some response)
        (some outerHistory) innerHistory

private inductive OptionalOuterResponse {A C : Interface.{u, v}} :
    Option (PackedResponse A C) → Prop
  | none : OptionalOuterResponse none
  | some (reply : DDC.History.InnerReply A) :
      OptionalOuterResponse (some (Sum.inr reply))

private inductive ParallelSerialResponse
    {A₁ C₁ A₂ C₂ : Interface.{u, v}} :
    Option ParallelSide → Option (PackedResponse A₁ C₁) →
      Option (PackedResponse A₂ C₂) →
      PackedResponse (Interface.parallel A₁ A₂)
        (Interface.parallel C₁ C₂) → Prop
  | left (response : PackedResponse A₁ C₁)
      {rightResponse : Option (PackedResponse A₂ C₂)}
      (rightClosed : OptionalOuterResponse rightResponse) :
      ParallelSerialResponse (some .left) (some response) rightResponse
        (tagLeftPacked response)
  | right {leftResponse : Option (PackedResponse A₁ C₁)}
      (response : PackedResponse A₂ C₂)
      (leftClosed : OptionalOuterResponse leftResponse) :
      ParallelSerialResponse (some .right) leftResponse (some response)
        (tagRightPacked response)

private theorem ParallelSerialResponse.left_inner
    {A₁ C₁ A₂ C₂ : Interface.{u, v}}
    {active leftResponse rightResponse} {query : C₁.query}
    (projection : @ParallelSerialResponse A₁ C₁ A₂ C₂ active
      leftResponse rightResponse (Sum.inl (Sum.inl query))) :
    active = some .left ∧ leftResponse = some (Sum.inl query) ∧
      OptionalOuterResponse rightResponse := by
  generalize outputEqual :
      (Sum.inl (Sum.inl query) : PackedResponse
        (Interface.parallel A₁ A₂) (Interface.parallel C₁ C₂)) = output
    at projection
  cases projection with
  | left response closed =>
      cases response with
      | inl componentQuery =>
          have queryEqual := Sum.inl.inj outputEqual
          cases queryEqual
          exact ⟨rfl, rfl, closed⟩
      | inr reply => simp [tagLeftPacked] at outputEqual
  | right response closed =>
      cases response <;> simp [tagRightPacked] at outputEqual

private theorem ParallelSerialResponse.right_inner
    {A₁ C₁ A₂ C₂ : Interface.{u, v}}
    {active leftResponse rightResponse} {query : C₂.query}
    (projection : @ParallelSerialResponse A₁ C₁ A₂ C₂ active
      leftResponse rightResponse (Sum.inl (Sum.inr query))) :
    active = some .right ∧ rightResponse = some (Sum.inl query) ∧
      OptionalOuterResponse leftResponse := by
  generalize outputEqual :
      (Sum.inl (Sum.inr query) : PackedResponse
        (Interface.parallel A₁ A₂) (Interface.parallel C₁ C₂)) = output
    at projection
  cases projection with
  | left response closed =>
      cases response <;> simp [tagLeftPacked] at outputEqual
  | right response closed =>
      cases response with
      | inl componentQuery =>
          have taggedEqual := Sum.inl.inj outputEqual
          have queryEqual := Sum.inr.inj taggedEqual
          cases queryEqual
          exact ⟨rfl, rfl, closed⟩
      | inr reply => simp [tagRightPacked] at outputEqual

private theorem ParallelSerialResponse.outer
    {A₁ C₁ A₂ C₂ : Interface.{u, v}}
    {active leftResponse rightResponse} {reply : DDC.History.InnerReply
      (Interface.parallel A₁ A₂)}
    (projection : @ParallelSerialResponse A₁ C₁ A₂ C₂ active
      leftResponse rightResponse (Sum.inr reply)) :
    OptionalOuterResponse leftResponse ∧
      OptionalOuterResponse rightResponse := by
  generalize outputEqual :
      (Sum.inr reply : PackedResponse (Interface.parallel A₁ A₂)
        (Interface.parallel C₁ C₂)) = output at projection
  cases projection with
  | left response closed =>
      cases response with
      | inl query => simp [tagLeftPacked] at outputEqual
      | inr componentReply => exact ⟨.some componentReply, closed⟩
  | right response closed =>
      cases response with
      | inl query => simp [tagRightPacked] at outputEqual
      | inr componentReply => exact ⟨closed, .some componentReply⟩

private theorem SerialFactorization.realize_mem_serial
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {history : AttemptedHistory A C} {response outerHistory innerHistory}
    (factorization : SerialFactorization outer inner history response
      outerHistory innerHistory) :
    ∃ actual : DDC.Response history.toReceived,
      packResponse history.toReceived actual = response ∧
        actual ∈ serial outer inner history.toReceived := by
  obtain ⟨actual, packedEqual⟩ := factorization.realizeResponse
  refine ⟨actual, packedEqual, ?_⟩
  rw [mem_serial_iff, mem_serialRaw_iff]
  refine ⟨history, rfl, outerHistory, innerHistory, ?_⟩
  rw [packedEqual]
  exact factorization

private theorem ParallelSerialResponse.mem_parallel
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    (outerLeft : DDC A₁ B₁) (outerRight : DDC A₂ B₂)
    (innerLeft : DDC B₁ C₁) (innerRight : DDC B₂ C₂)
    {history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel C₁ C₂)}
    {leftHistory rightHistory leftResponse rightResponse response
      leftOuter rightOuter leftInner rightInner}
    (inputProjection : OptionalComponentHistories (some history)
      (leftHistory.map AttemptedHistory.toReceived)
      (rightHistory.map AttemptedHistory.toReceived))
    (leftFactorization : OptionalSerialFactorization outerLeft innerLeft
      leftHistory leftResponse leftOuter leftInner)
    (rightFactorization : OptionalSerialFactorization outerRight innerRight
      rightHistory rightResponse rightOuter rightInner)
    (responseProjection : ParallelSerialResponse
      (projectParallel history).active leftResponse rightResponse response)
    (actual : DDC.Response history)
    (packedEqual : packResponse history actual = response)
    (admissible : DDC.Raw.Admissible
      (parallelRaw (serial outerLeft innerLeft)
        (serial outerRight innerRight)) history) :
    actual ∈ parallel (serial outerLeft innerLeft)
      (serial outerRight innerRight) history := by
  generalize activeEqual : (projectParallel history).active = active
    at responseProjection
  cases responseProjection with
  | left componentResponse rightClosed =>
      cases leftFactorization with
      | @some componentAttempted _ componentOuter componentInner
          componentFactorization =>
          obtain ⟨componentActual, componentPacked, componentMembership⟩ :=
            componentFactorization.realize_mem_serial
          have valid := parallelRaw_admissible_projection
            (serial outerLeft innerLeft) (serial outerRight innerRight)
              admissible
          obtain ⟨componentHistory, componentActive⟩ :=
            valid.activeLeftPresent activeEqual
          have componentHistoryEqual : componentHistory =
              componentAttempted.toReceived :=
            Option.some.inj
              (componentActive.2.1.symm.trans inputProjection.1)
          subst componentHistory
          have taggedEqual : tagLeftResponse history
              componentAttempted.toReceived componentActive.2.2
                componentActual = actual := by
            apply packResponse_injective_local history
            calc

              packResponse history
                  (tagLeftResponse history componentAttempted.toReceived
                    componentActive.2.2 componentActual) =
                  tagLeftPacked
                    (packResponse componentAttempted.toReceived
                      componentActual) :=
                packResponse_tagLeft history componentAttempted.toReceived
                  componentActive.2.2 componentActual
              _ = tagLeftPacked componentResponse :=
                congrArg tagLeftPacked componentPacked
              _ = packResponse history actual := packedEqual.symm
          exact (mem_parallel_active_left_iff
            (serial outerLeft innerLeft) (serial outerRight innerRight)
            history componentAttempted.toReceived componentActive admissible
              actual).mpr
            ⟨componentActual, componentMembership, taggedEqual⟩
  | right componentResponse leftClosed =>
      cases rightFactorization with
      | @some componentAttempted _ componentOuter componentInner
          componentFactorization =>
          obtain ⟨componentActual, componentPacked, componentMembership⟩ :=
            componentFactorization.realize_mem_serial
          have valid := parallelRaw_admissible_projection
            (serial outerLeft innerLeft) (serial outerRight innerRight)
              admissible
          obtain ⟨componentHistory, componentActive⟩ :=
            valid.activeRightPresent activeEqual
          have componentHistoryEqual : componentHistory =
              componentAttempted.toReceived :=
            Option.some.inj
              (componentActive.2.1.symm.trans inputProjection.2)
          subst componentHistory
          have taggedEqual : tagRightResponse history
              componentAttempted.toReceived componentActive.2.2
                componentActual = actual := by
            apply packResponse_injective_local history
            calc
              packResponse history
                  (tagRightResponse history componentAttempted.toReceived
                    componentActive.2.2 componentActual) =
                  tagRightPacked
                    (packResponse componentAttempted.toReceived
                      componentActual) :=
                packResponse_tagRight history componentAttempted.toReceived
                  componentActive.2.2 componentActual
              _ = tagRightPacked componentResponse :=
                congrArg tagRightPacked componentPacked
              _ = packResponse history actual := packedEqual.symm
          exact (mem_parallel_active_right_iff
            (serial outerLeft innerLeft) (serial outerRight innerRight)
            history componentAttempted.toReceived componentActive admissible
              actual).mpr
            ⟨componentActual, componentMembership, taggedEqual⟩

private def SerialFactorization.ParallelResult
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    (outerLeft : DDC A₁ B₁) (outerRight : DDC A₂ B₂)
    (innerLeft : DDC B₁ C₁) (innerRight : DDC B₂ C₂)
    {history response finalOuter finalInner}
    (_factorization : SerialFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      history response finalOuter finalInner) : Prop :=
  ∃ leftHistory rightHistory leftResponse rightResponse leftOuter rightOuter
      leftInner rightInner,
    OptionalComponentHistories (some history.toReceived)
        (leftHistory.map AttemptedHistory.toReceived)
        (rightHistory.map AttemptedHistory.toReceived) ∧
      OptionalComponentHistories (some finalOuter) leftOuter rightOuter ∧
      (projectParallel finalOuter).active =
        (projectParallel history.toReceived).active ∧
      OptionalComponentHistories finalInner leftInner rightInner ∧

      OptionalSerialFactorization outerLeft innerLeft leftHistory leftResponse
        leftOuter leftInner ∧
      OptionalSerialFactorization outerRight innerRight rightHistory
        rightResponse rightOuter rightInner ∧
      ParallelSerialResponse (projectParallel history.toReceived).active
        leftResponse rightResponse response ∧
      ∃ actual : DDC.Response history.toReceived,
        packResponse history.toReceived actual = response ∧
          actual ∈ parallel (serial outerLeft innerLeft)
            (serial outerRight innerRight) history.toReceived

private theorem SerialFactorization.start_left_parallelResult
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    (outerLeft : DDC A₁ B₁) (outerRight : DDC A₂ B₂)
    (innerLeft : DDC B₁ C₁) (innerRight : DDC B₂ C₂)
    (input : A₁.query) {response finalOuter finalInner}
    (middleFactorization : OuterPrefixFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      (DDC.History.singleton (B := Interface.parallel B₁ B₂)
        (Sum.inl input)) none response finalOuter finalInner)
    (valid : PrefixEndpointValid (parallel outerLeft outerRight)
      (parallel innerLeft innerRight) response finalOuter finalInner) :
    (SerialFactorization.start middleFactorization valid).ParallelResult
      outerLeft outerRight innerLeft innerRight := by
  obtain ⟨componentResponse, componentOuter, componentInner,
      componentPrefix, responseEqual, finalOuterProjection,
      finalInnerProjection, actual, packedEqual, membership⟩ :=
    SerialFactorization.start_left_projection outerLeft outerRight innerLeft
      innerRight input middleFactorization valid
  have initialOuter : @LeftProjection A₁ B₁ A₂ B₂
      (DDC.History.singleton (B := Interface.parallel B₁ B₂)
        (Sum.inl input : (Interface.parallel A₁ A₂).query))
      (DDC.History.singleton (B := B₁) input) := ⟨rfl, rfl⟩
  have preserved := middleFactorization.preservesRight initialOuter.1
  have componentValid := componentPrefix.endpointValid
    (DDC.Raw.Admissible.start input)
    (by intro history impossible; cases impossible) trivial
  let componentWhole : SerialFactorization outerLeft innerLeft
      (.start input) componentResponse componentOuter componentInner :=
    .start componentPrefix componentValid
  refine ⟨some (.start input), none, some componentResponse, none,
    some componentOuter, none, componentInner, none, ?_, ?_, ?_, ?_,
    .some componentWhole, .none, ?_, actual, packedEqual, membership⟩
  · simp [OptionalComponentHistories, AttemptedHistory.toReceived]
  · exact ⟨finalOuterProjection.2, by simpa using preserved.1⟩
  · simpa [AttemptedHistory.toReceived] using finalOuterProjection.1
  · apply OptionalComponentHistories.of_left finalInnerProjection
    simpa [optionalRightHistory] using preserved.2
  · cases responseEqual
    exact .left componentResponse .none

private theorem SerialFactorization.start_right_parallelResult
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    (outerLeft : DDC A₁ B₁) (outerRight : DDC A₂ B₂)
    (innerLeft : DDC B₁ C₁) (innerRight : DDC B₂ C₂)
    (input : A₂.query) {response finalOuter finalInner}
    (middleFactorization : OuterPrefixFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      (DDC.History.singleton (B := Interface.parallel B₁ B₂)
        (Sum.inr input)) none response finalOuter finalInner)
    (valid : PrefixEndpointValid (parallel outerLeft outerRight)
      (parallel innerLeft innerRight) response finalOuter finalInner) :
    (SerialFactorization.start middleFactorization valid).ParallelResult
      outerLeft outerRight innerLeft innerRight := by
  obtain ⟨componentResponse, componentOuter, componentInner,
      componentPrefix, responseEqual, finalOuterProjection,
      finalInnerProjection, actual, packedEqual, membership⟩ :=
    SerialFactorization.start_right_projection outerLeft outerRight innerLeft
      innerRight input middleFactorization valid
  have initialOuter : @RightProjection A₁ B₁ A₂ B₂
      (DDC.History.singleton (B := Interface.parallel B₁ B₂)
        (Sum.inr input : (Interface.parallel A₁ A₂).query))
      (DDC.History.singleton (B := B₂) input) := ⟨rfl, rfl⟩
  have preserved := middleFactorization.preservesLeft initialOuter.1
  have componentValid := componentPrefix.endpointValid
    (DDC.Raw.Admissible.start input)
    (by intro history impossible; cases impossible) trivial
  let componentWhole : SerialFactorization outerRight innerRight
      (.start input) componentResponse componentOuter componentInner :=
    .start componentPrefix componentValid
  refine ⟨none, some (.start input), none, some componentResponse,
    none, some componentOuter, none, componentInner, ?_, ?_, ?_, ?_,
    .none, .some componentWhole, ?_, actual, packedEqual, membership⟩
  · simp [OptionalComponentHistories, AttemptedHistory.toReceived]
  · exact ⟨by simpa using preserved.1, finalOuterProjection.2⟩
  · simpa [AttemptedHistory.toReceived] using finalOuterProjection.1
  · apply OptionalComponentHistories.of_right
      (by simpa [optionalLeftHistory] using preserved.2)
      finalInnerProjection
  · cases responseEqual
    exact .right componentResponse .none

private theorem SerialFactorization.afterInner_left_parallelResult
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    (outerLeft : DDC A₁ B₁) (outerRight : DDC A₂ B₂)
    (innerLeft : DDC B₁ C₁) (innerRight : DDC B₂ C₂)
    {history currentOuter currentInner query reply response finalOuter
      finalInner}
    (previous : SerialFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      history (Sum.inl (Sum.inl query)) currentOuter (some currentInner))
    (tail : InnerPrefixFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      currentOuter (currentInner.snocInner (Sum.inl query) reply)
        response finalOuter finalInner)
    (valid : PrefixEndpointValid (parallel outerLeft outerRight)
      (parallel innerLeft innerRight) response finalOuter finalInner)
    (inductionHypothesis : previous.ParallelResult
      outerLeft outerRight innerLeft innerRight) :
    (SerialFactorization.afterInner previous tail valid).ParallelResult
      outerLeft outerRight innerLeft innerRight := by
  obtain ⟨leftHistory, rightHistory, leftResponse, rightResponse,
      leftOuter, rightOuter, leftInner, rightInner, inputProjection,
      outerProjection, outerActiveEqual, innerProjection,
      leftFactorization, rightFactorization, responseProjection,
      previousActual, previousPacked, previousMembership⟩ :=
    inductionHypothesis
  obtain ⟨externalActive, leftResponseEqual, rightClosed⟩ :=
    responseProjection.left_inner
  subst leftResponse
  cases leftFactorization with
  | @some componentAttempted _ componentOuter componentInner
      componentPrevious =>
      obtain ⟨componentCurrentInner, componentInnerEqual, innerResponds,
          componentLinked⟩ :=
        componentPrevious.endpointValid.exposedInner query rfl
      subst leftInner
      have jointInnerResponds : Sum.inl (Sum.inl query) ∈
          parallel innerLeft innerRight currentInner := by
        obtain ⟨otherInner, otherEqual, responds, linked⟩ :=
          previous.endpointValid.exposedInner (Sum.inl query) rfl
        cases Option.some.inj otherEqual.symm
        exact responds
      have innerActive := active_left_of_query_mem innerLeft innerRight
        currentInner query jointInnerResponds
      have jointOuterActive := outerActiveEqual.trans externalActive
      have componentOuterProjection :=
        outerProjection.left_of_some jointOuterActive
      have componentInnerProjection :=
        innerProjection.left_of_some innerActive
      have nextComponentInnerProjection :=
        innerProjection.snoc_inner_left query reply
      have nextInnerProjection :=
        componentInnerProjection.snoc_inner query reply
      obtain ⟨componentResponse, componentFinalOuter, componentFinalInner,
          componentTail, responseEqual, finalOuterProjection,
          finalInnerProjection⟩ :=
        tail.projectLeft outerLeft outerRight innerLeft innerRight
          componentOuterProjection nextInnerProjection
      have componentInnerAdmissible : DDC.Raw.Admissible innerLeft.toFun
          (componentCurrentInner.snocInner query reply) :=
        .afterInner
          (componentPrevious.endpointValid.innerAdmissible
            componentCurrentInner rfl)
          innerResponds reply
      have componentValid := componentTail.endpointValid
        componentPrevious.endpointValid.outerAdmissible
        componentInnerAdmissible
      let componentFactorization : SerialFactorization outerLeft innerLeft
          (.afterInner componentAttempted query reply) componentResponse
            componentFinalOuter componentFinalInner :=
        .afterInner componentPrevious componentTail componentValid
      have nextInputProjection : OptionalComponentHistories
          (some (AttemptedHistory.afterInner history (Sum.inl query) reply).toReceived)
          (some (AttemptedHistory.afterInner componentAttempted query reply).toReceived)
          (rightHistory.map AttemptedHistory.toReceived) := by
        simpa [AttemptedHistory.toReceived] using
          inputProjection.snoc_inner_left query reply
      have nextInnerActive :
          (projectParallel
            (currentInner.snocInner (Sum.inl query) reply)).active =
              some .left := by
        rw [projectParallel_snocInner_left]
        simp [extendParallelProjection, innerActive]
      have preserved := tail.preservesRight jointOuterActive nextInnerActive
      have nextOuterProjection : OptionalComponentHistories
          (some finalOuter) (some componentFinalOuter) rightOuter :=
        ⟨finalOuterProjection.2,
          preserved.1.trans outerProjection.2⟩
      have nextFinalInnerProjection : OptionalComponentHistories finalInner
          componentFinalInner rightInner :=
        OptionalComponentHistories.of_left finalInnerProjection
          (preserved.2.trans nextComponentInnerProjection.2)
      have nextExternalActive :
          (projectParallel
            (AttemptedHistory.afterInner history (Sum.inl query) reply).toReceived).active =
              some .left := by
        rw [AttemptedHistory.toReceived, projectParallel_snocInner_left]
        simp [extendParallelProjection, externalActive]
      have previousActualEqual : previousActual = Sum.inl (Sum.inl query) := by
        cases previousActual with
        | inl previousQuery =>
            exact congrArg Sum.inl (Sum.inl.inj previousPacked)
        | inr previousReply => cases previousPacked
      subst previousActual
      have nextAdmissible : DDC.Raw.Admissible
          (parallelRaw (serial outerLeft innerLeft)
            (serial outerRight innerRight))
          (AttemptedHistory.afterInner history (Sum.inl query) reply).toReceived :=
        by
          have previousRaw := (mem_parallel_iff
            (serial outerLeft innerLeft) (serial outerRight innerRight)
            history.toReceived (Sum.inl (Sum.inl query))).mp
              previousMembership
          simpa [AttemptedHistory.toReceived] using
            DDC.Raw.Admissible.afterInner previousRaw.1 previousRaw.2 reply
      let whole : SerialFactorization
          (parallel outerLeft outerRight) (parallel innerLeft innerRight)
          (.afterInner history (Sum.inl query) reply) response finalOuter
            finalInner := .afterInner previous tail valid
      obtain ⟨actual, packedEqual⟩ := whole.realizeResponse
      cases responseEqual
      let nextResponseProjection : ParallelSerialResponse
          (projectParallel
            (AttemptedHistory.afterInner history (Sum.inl query) reply).toReceived).active
          (some componentResponse) rightResponse
          (tagLeftPacked componentResponse) := by
        rw [nextExternalActive]
        exact .left componentResponse rightClosed
      have nextMembership := nextResponseProjection.mem_parallel
        outerLeft outerRight innerLeft innerRight nextInputProjection
        (.some componentFactorization) rightFactorization actual packedEqual
          nextAdmissible
      refine ⟨some (.afterInner componentAttempted query reply), rightHistory,
        some componentResponse, rightResponse, some componentFinalOuter,
        rightOuter, componentFinalInner, rightInner, nextInputProjection,
        nextOuterProjection, ?_, nextFinalInnerProjection,
        .some componentFactorization, rightFactorization,
        nextResponseProjection, actual, packedEqual, nextMembership⟩
      exact finalOuterProjection.1.trans nextExternalActive.symm

private theorem SerialFactorization.afterInner_right_parallelResult
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    (outerLeft : DDC A₁ B₁) (outerRight : DDC A₂ B₂)
    (innerLeft : DDC B₁ C₁) (innerRight : DDC B₂ C₂)
    {history currentOuter currentInner query reply response finalOuter
      finalInner}
    (previous : SerialFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      history (Sum.inl (Sum.inr query)) currentOuter (some currentInner))
    (tail : InnerPrefixFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      currentOuter (currentInner.snocInner (Sum.inr query) reply)
        response finalOuter finalInner)
    (valid : PrefixEndpointValid (parallel outerLeft outerRight)
      (parallel innerLeft innerRight) response finalOuter finalInner)
    (inductionHypothesis : previous.ParallelResult
      outerLeft outerRight innerLeft innerRight) :
    (SerialFactorization.afterInner previous tail valid).ParallelResult
      outerLeft outerRight innerLeft innerRight := by

  obtain ⟨leftHistory, rightHistory, leftResponse, rightResponse,
      leftOuter, rightOuter, leftInner, rightInner, inputProjection,
      outerProjection, outerActiveEqual, innerProjection,
      leftFactorization, rightFactorization, responseProjection,
      previousActual, previousPacked, previousMembership⟩ :=
    inductionHypothesis
  obtain ⟨externalActive, rightResponseEqual, leftClosed⟩ :=
    responseProjection.right_inner
  subst rightResponse
  cases rightFactorization with
  | @some componentAttempted _ componentOuter componentInner
      componentPrevious =>
      obtain ⟨componentCurrentInner, componentInnerEqual, innerResponds,
          componentLinked⟩ :=
        componentPrevious.endpointValid.exposedInner query rfl
      subst rightInner
      have jointInnerResponds : Sum.inl (Sum.inr query) ∈
          parallel innerLeft innerRight currentInner := by
        obtain ⟨otherInner, otherEqual, responds, linked⟩ :=
          previous.endpointValid.exposedInner (Sum.inr query) rfl
        cases Option.some.inj otherEqual.symm
        exact responds
      have innerActive := active_right_of_query_mem innerLeft innerRight
        currentInner query jointInnerResponds
      have jointOuterActive := outerActiveEqual.trans externalActive
      have componentOuterProjection :=
        outerProjection.right_of_some jointOuterActive
      have componentInnerProjection :=
        innerProjection.right_of_some innerActive
      have nextComponentInnerProjection :=
        innerProjection.snoc_inner_right query reply
      have nextInnerProjection :=
        componentInnerProjection.snoc_inner query reply
      obtain ⟨componentResponse, componentFinalOuter, componentFinalInner,
          componentTail, responseEqual, finalOuterProjection,
          finalInnerProjection⟩ :=
        tail.projectRight outerLeft outerRight innerLeft innerRight
          componentOuterProjection nextInnerProjection
      have componentInnerAdmissible : DDC.Raw.Admissible innerRight.toFun
          (componentCurrentInner.snocInner query reply) :=
        .afterInner
          (componentPrevious.endpointValid.innerAdmissible
            componentCurrentInner rfl)
          innerResponds reply
      have componentValid := componentTail.endpointValid
        componentPrevious.endpointValid.outerAdmissible
        componentInnerAdmissible
      let componentFactorization : SerialFactorization outerRight innerRight
          (.afterInner componentAttempted query reply) componentResponse
            componentFinalOuter componentFinalInner :=
        .afterInner componentPrevious componentTail componentValid
      have nextInputProjection : OptionalComponentHistories
          (some (AttemptedHistory.afterInner history (Sum.inr query) reply).toReceived)
          (leftHistory.map AttemptedHistory.toReceived)
          (some (AttemptedHistory.afterInner componentAttempted query reply).toReceived) := by
        simpa [AttemptedHistory.toReceived] using
          inputProjection.snoc_inner_right query reply
      have nextInnerActive :
          (projectParallel
            (currentInner.snocInner (Sum.inr query) reply)).active =
              some .right := by
        rw [projectParallel_snocInner_right]
        simp [extendParallelProjection, innerActive]
      have preserved := tail.preservesLeft jointOuterActive nextInnerActive
      have nextOuterProjection : OptionalComponentHistories
          (some finalOuter) leftOuter (some componentFinalOuter) :=
        ⟨preserved.1.trans outerProjection.1,
          finalOuterProjection.2⟩
      have nextFinalInnerProjection : OptionalComponentHistories finalInner
          leftInner componentFinalInner :=
        OptionalComponentHistories.of_right
          (preserved.2.trans nextComponentInnerProjection.1)
          finalInnerProjection
      have nextExternalActive :
          (projectParallel
            (AttemptedHistory.afterInner history (Sum.inr query) reply).toReceived).active =
              some .right := by
        rw [AttemptedHistory.toReceived, projectParallel_snocInner_right]
        simp [extendParallelProjection, externalActive]
      have previousActualEqual : previousActual = Sum.inl (Sum.inr query) := by
        cases previousActual with
        | inl previousQuery =>
            exact congrArg Sum.inl (Sum.inl.inj previousPacked)
        | inr previousReply => cases previousPacked
      subst previousActual
      have nextAdmissible : DDC.Raw.Admissible
          (parallelRaw (serial outerLeft innerLeft)
            (serial outerRight innerRight))
          (AttemptedHistory.afterInner history (Sum.inr query) reply).toReceived :=
        by
          have previousRaw := (mem_parallel_iff
            (serial outerLeft innerLeft) (serial outerRight innerRight)
            history.toReceived (Sum.inl (Sum.inr query))).mp
              previousMembership
          simpa [AttemptedHistory.toReceived] using
            DDC.Raw.Admissible.afterInner previousRaw.1 previousRaw.2 reply
      let whole : SerialFactorization
          (parallel outerLeft outerRight) (parallel innerLeft innerRight)
          (.afterInner history (Sum.inr query) reply) response finalOuter
            finalInner := .afterInner previous tail valid
      obtain ⟨actual, packedEqual⟩ := whole.realizeResponse
      cases responseEqual
      let nextResponseProjection : ParallelSerialResponse
          (projectParallel
            (AttemptedHistory.afterInner history (Sum.inr query) reply).toReceived).active
          leftResponse (some componentResponse)
          (tagRightPacked componentResponse) := by
        rw [nextExternalActive]
        exact .right componentResponse leftClosed
      have nextMembership := nextResponseProjection.mem_parallel
        outerLeft outerRight innerLeft innerRight nextInputProjection
        leftFactorization (.some componentFactorization) actual packedEqual
          nextAdmissible
      refine ⟨leftHistory, some (.afterInner componentAttempted query reply),
        leftResponse, some componentResponse, leftOuter,
        some componentFinalOuter, leftInner, componentFinalInner,
        nextInputProjection, nextOuterProjection, ?_,
        nextFinalInnerProjection, leftFactorization,
        .some componentFactorization, nextResponseProjection, actual,
        packedEqual, nextMembership⟩
      exact finalOuterProjection.1.trans nextExternalActive.symm

private theorem SerialFactorization.afterOuter_left_parallelResult
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    (outerLeft : DDC A₁ B₁) (outerRight : DDC A₂ B₂)
    (innerLeft : DDC B₁ C₁) (innerRight : DDC B₂ C₂)
    {history previousReply currentOuter currentInner input response finalOuter
      finalInner}
    (previous : SerialFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      history (Sum.inr ⟨history.toReceived.lastOuter, previousReply⟩)
        currentOuter currentInner)
    (tail : OuterPrefixFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      (currentOuter.snocOuter (Sum.inl input)) currentInner response
        finalOuter finalInner)
    (valid : PrefixEndpointValid (parallel outerLeft outerRight)
      (parallel innerLeft innerRight) response finalOuter finalInner)
    (inductionHypothesis : previous.ParallelResult
      outerLeft outerRight innerLeft innerRight) :
    (SerialFactorization.afterOuter previous tail valid).ParallelResult
      outerLeft outerRight innerLeft innerRight := by
  obtain ⟨leftHistory, rightHistory, leftResponse, rightResponse,
      leftOuter, rightOuter, leftInner, rightInner, inputProjection,
      outerProjection, outerActiveEqual, innerProjection,
      leftFactorization, rightFactorization, responseProjection,
      previousActual, previousPacked, previousMembership⟩ :=
    inductionHypothesis
  obtain ⟨leftClosed, rightClosed⟩ := responseProjection.outer
  have jointOuterStartProjection := outerProjection.snoc_outer_left input
  have jointOuterStartActive :
      (projectParallel (currentOuter.snocOuter (Sum.inl input))).active =
        some .left := by
    rw [projectParallel_snocOuter_left]
    simp [extendParallelProjection]
  have nextInputProjection := inputProjection.snoc_outer_left input
  have nextExternalActive :
      (projectParallel
        (AttemptedHistory.afterOuter history (Sum.inl input)).toReceived).active =
          some .left := by
    rw [AttemptedHistory.toReceived, projectParallel_snocOuter_left]
    simp [extendParallelProjection]
  have previousActualEqual : previousActual = Sum.inr previousReply := by
    apply packResponse_injective_local history.toReceived
    exact previousPacked.trans rfl.symm
  subst previousActual
  have nextAdmissible : DDC.Raw.Admissible
      (parallelRaw (serial outerLeft innerLeft)
        (serial outerRight innerRight))
      (AttemptedHistory.afterOuter history (Sum.inl input)).toReceived := by
    have previousRaw := (mem_parallel_iff
      (serial outerLeft innerLeft) (serial outerRight innerRight)
      history.toReceived (Sum.inr previousReply)).mp previousMembership
    simpa [AttemptedHistory.toReceived] using
      DDC.Raw.Admissible.afterOuter previousRaw.1 previousRaw.2 (Sum.inl input)
  cases leftClosed with
  | none =>
      cases leftFactorization with
      | none =>
          have componentOuterProjection :=
            jointOuterStartProjection.left_of_some jointOuterStartActive
          have componentInnerProjection : LeftHistoryProjection currentInner none := by
            cases currentInner with
            | none => trivial
            | some history => exact innerProjection.1
          obtain ⟨componentResponse, componentFinalOuter,
              componentFinalInner, componentTail, responseEqual,
              finalOuterProjection, finalInnerProjection⟩ :=
            tail.projectLeft outerLeft outerRight innerLeft innerRight
              componentOuterProjection componentInnerProjection trivial
          have componentValid := componentTail.endpointValid
            (DDC.Raw.Admissible.start input)
            (by intro history impossible; cases impossible) trivial
          let componentFactorization : SerialFactorization outerLeft innerLeft
              (.start input) componentResponse componentFinalOuter
                componentFinalInner := .start componentTail componentValid
          have preserved := tail.preservesRight jointOuterStartActive
          have nextOuterProjection : OptionalComponentHistories
              (some finalOuter) (some componentFinalOuter) rightOuter :=
            ⟨finalOuterProjection.2,
              preserved.1.trans jointOuterStartProjection.2⟩
          have nextFinalInnerProjection : OptionalComponentHistories
              finalInner componentFinalInner rightInner :=
            OptionalComponentHistories.of_left finalInnerProjection
              (preserved.2.trans innerProjection.right_eq)
          let whole : SerialFactorization
              (parallel outerLeft outerRight) (parallel innerLeft innerRight)
              (.afterOuter history (Sum.inl input)) response finalOuter
                finalInner := .afterOuter previous tail valid
          obtain ⟨actual, packedEqual⟩ := whole.realizeResponse
          cases responseEqual
          let nextResponseProjection : ParallelSerialResponse
              (projectParallel
                (AttemptedHistory.afterOuter history
                  (Sum.inl input)).toReceived).active
              (some componentResponse) rightResponse
              (tagLeftPacked componentResponse) := by
            rw [nextExternalActive]
            exact .left componentResponse rightClosed
          have nextMembership := nextResponseProjection.mem_parallel
            outerLeft outerRight innerLeft innerRight nextInputProjection
            (.some componentFactorization) rightFactorization actual
              packedEqual nextAdmissible
          refine ⟨some (.start input), rightHistory, some componentResponse,
            rightResponse, some componentFinalOuter, rightOuter,
            componentFinalInner, rightInner, nextInputProjection,
            nextOuterProjection, ?_, nextFinalInnerProjection,
            .some componentFactorization, rightFactorization,
            nextResponseProjection, actual, packedEqual, nextMembership⟩
          exact finalOuterProjection.1.trans nextExternalActive.symm
  | some componentPreviousReply =>
      cases leftFactorization with
      | @some componentAttempted _ componentOuter componentInner
          componentPrevious =>
          have selectedEqual : componentPreviousReply.1 =
              componentOuter.lastOuter :=
            componentPrevious.endpointValid.selectedOuter
              componentPreviousReply rfl
          rcases componentPreviousReply with ⟨selected, componentPreviousReply⟩
          cases selectedEqual
          obtain ⟨componentOuterResponds, componentInnerClosed⟩ :=
            componentPrevious.endpointValid.closedOuter componentPreviousReply rfl
          have componentOuterLastEqual := componentPrevious.outerLast_eq
          let replyAtAttempt : Option
              (A₁.answer componentAttempted.toReceived.lastOuter) :=
            cast (congrArg (fun query => Option (A₁.answer query))
              componentOuterLastEqual) componentPreviousReply
          have packedReplyEqual :
              (⟨componentOuter.lastOuter, componentPreviousReply⟩ :
                DDC.History.InnerReply A₁) =

              ⟨componentAttempted.toReceived.lastOuter,
                replyAtAttempt⟩ := by
            apply Sigma.ext componentOuterLastEqual
            exact (cast_heq
              (congrArg (fun query => Option (A₁.answer query))
                componentOuterLastEqual) componentPreviousReply).symm
          let adjustedPrevious : SerialFactorization outerLeft innerLeft
              componentAttempted
              (Sum.inr ⟨componentAttempted.toReceived.lastOuter,
                replyAtAttempt⟩) componentOuter leftInner :=
            congrArg Sum.inr packedReplyEqual ▸ componentPrevious
          have componentOuterProjection :=
            jointOuterStartProjection.left_of_some jointOuterStartActive
          have componentInnerProjection : LeftHistoryProjection currentInner
              leftInner := by
            cases currentInner with
            | none =>
                have equal := innerProjection.1
                subst leftInner
                trivial
            | some history => exact innerProjection.1
          obtain ⟨componentResponse, componentFinalOuter,
              componentFinalInner, componentTail, responseEqual,
              finalOuterProjection, finalInnerProjection⟩ :=
            tail.projectLeft outerLeft outerRight innerLeft innerRight
              componentOuterProjection componentInnerProjection
                componentInnerClosed
          have componentValid := componentTail.endpointValid
            (DDC.Raw.Admissible.afterOuter
              componentPrevious.endpointValid.outerAdmissible
              componentOuterResponds input)
            componentPrevious.endpointValid.innerAdmissible
            componentInnerClosed
          let componentFactorization : SerialFactorization outerLeft innerLeft
              (.afterOuter componentAttempted input) componentResponse
                componentFinalOuter componentFinalInner :=
            .afterOuter adjustedPrevious componentTail componentValid
          have preserved := tail.preservesRight jointOuterStartActive
          have nextOuterProjection : OptionalComponentHistories
              (some finalOuter) (some componentFinalOuter) rightOuter :=
            ⟨finalOuterProjection.2,
              preserved.1.trans jointOuterStartProjection.2⟩
          have nextFinalInnerProjection : OptionalComponentHistories
              finalInner componentFinalInner rightInner :=
            OptionalComponentHistories.of_left finalInnerProjection
              (preserved.2.trans innerProjection.right_eq)
          let whole : SerialFactorization
              (parallel outerLeft outerRight) (parallel innerLeft innerRight)
              (.afterOuter history (Sum.inl input)) response finalOuter
                finalInner := .afterOuter previous tail valid
          obtain ⟨actual, packedEqual⟩ := whole.realizeResponse
          cases responseEqual
          let nextResponseProjection : ParallelSerialResponse
              (projectParallel
                (AttemptedHistory.afterOuter history
                  (Sum.inl input)).toReceived).active
              (some componentResponse) rightResponse
              (tagLeftPacked componentResponse) := by
            rw [nextExternalActive]
            exact .left componentResponse rightClosed
          have nextMembership := nextResponseProjection.mem_parallel
            outerLeft outerRight innerLeft innerRight nextInputProjection
            (.some componentFactorization) rightFactorization actual
              packedEqual nextAdmissible
          refine ⟨some (.afterOuter componentAttempted input), rightHistory,
            some componentResponse, rightResponse, some componentFinalOuter,
            rightOuter, componentFinalInner, rightInner, nextInputProjection,
            nextOuterProjection, ?_, nextFinalInnerProjection,
            .some componentFactorization, rightFactorization,
            nextResponseProjection, actual, packedEqual, nextMembership⟩
          exact finalOuterProjection.1.trans nextExternalActive.symm

private theorem SerialFactorization.afterOuter_right_parallelResult
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    (outerLeft : DDC A₁ B₁) (outerRight : DDC A₂ B₂)
    (innerLeft : DDC B₁ C₁) (innerRight : DDC B₂ C₂)
    {history previousReply currentOuter currentInner input response finalOuter
      finalInner}
    (previous : SerialFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      history (Sum.inr ⟨history.toReceived.lastOuter, previousReply⟩)
        currentOuter currentInner)
    (tail : OuterPrefixFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      (currentOuter.snocOuter (Sum.inr input)) currentInner response
        finalOuter finalInner)
    (valid : PrefixEndpointValid (parallel outerLeft outerRight)
      (parallel innerLeft innerRight) response finalOuter finalInner)
    (inductionHypothesis : previous.ParallelResult
      outerLeft outerRight innerLeft innerRight) :
    (SerialFactorization.afterOuter previous tail valid).ParallelResult
      outerLeft outerRight innerLeft innerRight := by
  obtain ⟨leftHistory, rightHistory, leftResponse, rightResponse,
      leftOuter, rightOuter, leftInner, rightInner, inputProjection,
      outerProjection, outerActiveEqual, innerProjection,
      leftFactorization, rightFactorization, responseProjection,
      previousActual, previousPacked, previousMembership⟩ :=
    inductionHypothesis
  obtain ⟨leftClosed, rightClosed⟩ := responseProjection.outer
  have jointOuterStartProjection := outerProjection.snoc_outer_right input
  have jointOuterStartActive :
      (projectParallel (currentOuter.snocOuter (Sum.inr input))).active =
        some .right := by
    rw [projectParallel_snocOuter_right]
    simp [extendParallelProjection]
  have nextInputProjection := inputProjection.snoc_outer_right input
  have nextExternalActive :
      (projectParallel
        (AttemptedHistory.afterOuter history (Sum.inr input)).toReceived).active =
          some .right := by
    rw [AttemptedHistory.toReceived, projectParallel_snocOuter_right]
    simp [extendParallelProjection]
  have previousActualEqual : previousActual = Sum.inr previousReply := by
    apply packResponse_injective_local history.toReceived
    exact previousPacked.trans rfl.symm
  subst previousActual
  have nextAdmissible : DDC.Raw.Admissible
      (parallelRaw (serial outerLeft innerLeft)
        (serial outerRight innerRight))
      (AttemptedHistory.afterOuter history (Sum.inr input)).toReceived := by
    have previousRaw := (mem_parallel_iff
      (serial outerLeft innerLeft) (serial outerRight innerRight)
      history.toReceived (Sum.inr previousReply)).mp previousMembership
    simpa [AttemptedHistory.toReceived] using
      DDC.Raw.Admissible.afterOuter previousRaw.1 previousRaw.2 (Sum.inr input)
  cases rightClosed with
  | none =>
      cases rightFactorization with
      | none =>
          have componentOuterProjection :=
            jointOuterStartProjection.right_of_some jointOuterStartActive
          have componentInnerProjection : RightHistoryProjection currentInner none := by
            cases currentInner with
            | none => trivial
            | some history => exact innerProjection.2
          obtain ⟨componentResponse, componentFinalOuter,
              componentFinalInner, componentTail, responseEqual,
              finalOuterProjection, finalInnerProjection⟩ :=
            tail.projectRight outerLeft outerRight innerLeft innerRight
              componentOuterProjection componentInnerProjection trivial
          have componentValid := componentTail.endpointValid
            (DDC.Raw.Admissible.start input)
            (by intro history impossible; cases impossible) trivial
          let componentFactorization : SerialFactorization outerRight innerRight
              (.start input) componentResponse componentFinalOuter
                componentFinalInner := .start componentTail componentValid
          have preserved := tail.preservesLeft jointOuterStartActive
          have nextOuterProjection : OptionalComponentHistories
              (some finalOuter) leftOuter (some componentFinalOuter) :=
            ⟨preserved.1.trans jointOuterStartProjection.1,
              finalOuterProjection.2⟩
          have nextFinalInnerProjection : OptionalComponentHistories
              finalInner leftInner componentFinalInner :=
            OptionalComponentHistories.of_right
              (preserved.2.trans innerProjection.left_eq)
              finalInnerProjection
          let whole : SerialFactorization
              (parallel outerLeft outerRight) (parallel innerLeft innerRight)
              (.afterOuter history (Sum.inr input)) response finalOuter
                finalInner := .afterOuter previous tail valid
          obtain ⟨actual, packedEqual⟩ := whole.realizeResponse
          cases responseEqual
          let nextResponseProjection : ParallelSerialResponse
              (projectParallel
                (AttemptedHistory.afterOuter history
                  (Sum.inr input)).toReceived).active
              leftResponse (some componentResponse)
              (tagRightPacked componentResponse) := by
            rw [nextExternalActive]
            exact .right componentResponse leftClosed
          have nextMembership := nextResponseProjection.mem_parallel
            outerLeft outerRight innerLeft innerRight nextInputProjection
            leftFactorization (.some componentFactorization) actual
              packedEqual nextAdmissible
          refine ⟨leftHistory, some (.start input), leftResponse,
            some componentResponse, leftOuter, some componentFinalOuter,
            leftInner, componentFinalInner, nextInputProjection,
            nextOuterProjection, ?_, nextFinalInnerProjection,
            leftFactorization, .some componentFactorization,
            nextResponseProjection, actual, packedEqual, nextMembership⟩
          exact finalOuterProjection.1.trans nextExternalActive.symm
  | some componentPreviousReply =>
      cases rightFactorization with
      | @some componentAttempted _ componentOuter componentInner
          componentPrevious =>
          have selectedEqual : componentPreviousReply.1 =
              componentOuter.lastOuter :=
            componentPrevious.endpointValid.selectedOuter
              componentPreviousReply rfl
          rcases componentPreviousReply with ⟨selected, componentPreviousReply⟩
          cases selectedEqual
          obtain ⟨componentOuterResponds, componentInnerClosed⟩ :=
            componentPrevious.endpointValid.closedOuter componentPreviousReply rfl
          have componentOuterLastEqual := componentPrevious.outerLast_eq
          let replyAtAttempt : Option
              (A₂.answer componentAttempted.toReceived.lastOuter) :=
            cast (congrArg (fun query => Option (A₂.answer query))
              componentOuterLastEqual) componentPreviousReply
          have packedReplyEqual :
              (⟨componentOuter.lastOuter, componentPreviousReply⟩ :
                DDC.History.InnerReply A₂) =
              ⟨componentAttempted.toReceived.lastOuter,
                replyAtAttempt⟩ := by
            apply Sigma.ext componentOuterLastEqual
            exact (cast_heq
              (congrArg (fun query => Option (A₂.answer query))
                componentOuterLastEqual) componentPreviousReply).symm
          let adjustedPrevious : SerialFactorization outerRight innerRight
              componentAttempted
              (Sum.inr ⟨componentAttempted.toReceived.lastOuter,
                replyAtAttempt⟩) componentOuter rightInner :=
            congrArg Sum.inr packedReplyEqual ▸ componentPrevious
          have componentOuterProjection :=
            jointOuterStartProjection.right_of_some jointOuterStartActive
          have componentInnerProjection : RightHistoryProjection currentInner
              rightInner := by
            cases currentInner with
            | none =>
                have equal := innerProjection.2
                subst rightInner
                trivial
            | some history => exact innerProjection.2
          obtain ⟨componentResponse, componentFinalOuter,
              componentFinalInner, componentTail, responseEqual,
              finalOuterProjection, finalInnerProjection⟩ :=
            tail.projectRight outerLeft outerRight innerLeft innerRight
              componentOuterProjection componentInnerProjection
                componentInnerClosed
          have componentValid := componentTail.endpointValid
            (DDC.Raw.Admissible.afterOuter
              componentPrevious.endpointValid.outerAdmissible
              componentOuterResponds input)
            componentPrevious.endpointValid.innerAdmissible
            componentInnerClosed
          let componentFactorization : SerialFactorization outerRight innerRight
              (.afterOuter componentAttempted input) componentResponse
                componentFinalOuter componentFinalInner :=
            .afterOuter adjustedPrevious componentTail componentValid
          have preserved := tail.preservesLeft jointOuterStartActive
          have nextOuterProjection : OptionalComponentHistories
              (some finalOuter) leftOuter (some componentFinalOuter) :=
            ⟨preserved.1.trans jointOuterStartProjection.1,
              finalOuterProjection.2⟩
          have nextFinalInnerProjection : OptionalComponentHistories
              finalInner leftInner componentFinalInner :=
            OptionalComponentHistories.of_right
              (preserved.2.trans innerProjection.left_eq)
              finalInnerProjection
          let whole : SerialFactorization
              (parallel outerLeft outerRight) (parallel innerLeft innerRight)

              (.afterOuter history (Sum.inr input)) response finalOuter
                finalInner := .afterOuter previous tail valid
          obtain ⟨actual, packedEqual⟩ := whole.realizeResponse
          cases responseEqual
          let nextResponseProjection : ParallelSerialResponse
              (projectParallel
                (AttemptedHistory.afterOuter history
                  (Sum.inr input)).toReceived).active
              leftResponse (some componentResponse)
              (tagRightPacked componentResponse) := by
            rw [nextExternalActive]
            exact .right componentResponse leftClosed
          have nextMembership := nextResponseProjection.mem_parallel
            outerLeft outerRight innerLeft innerRight nextInputProjection
            leftFactorization (.some componentFactorization) actual
              packedEqual nextAdmissible
          refine ⟨leftHistory, some (.afterOuter componentAttempted input),
            leftResponse, some componentResponse, leftOuter,
            some componentFinalOuter, leftInner, componentFinalInner,
            nextInputProjection, nextOuterProjection, ?_,
            nextFinalInnerProjection, leftFactorization,
            .some componentFactorization, nextResponseProjection, actual,
            packedEqual, nextMembership⟩
          exact finalOuterProjection.1.trans nextExternalActive.symm

private theorem SerialFactorization.parallelResult
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    (outerLeft : DDC A₁ B₁) (outerRight : DDC A₂ B₂)
    (innerLeft : DDC B₁ C₁) (innerRight : DDC B₂ C₂)
    {history response finalOuter finalInner}
    (factorization : SerialFactorization
      (parallel outerLeft outerRight) (parallel innerLeft innerRight)
      history response finalOuter finalInner) :
    factorization.ParallelResult outerLeft outerRight innerLeft innerRight := by
  induction factorization with
  | @start outerQuery response finalOuter finalInner middle valid =>
      cases outerQuery with
      | inl input =>
          exact SerialFactorization.start_left_parallelResult
            outerLeft outerRight innerLeft innerRight input middle valid
      | inr input =>
          exact SerialFactorization.start_right_parallelResult
            outerLeft outerRight innerLeft innerRight input middle valid
  | @afterInner history query currentOuter currentInner reply response
      finalOuter finalInner previous tail valid inductionHypothesis =>
      cases query with
      | inl componentQuery =>
          exact SerialFactorization.afterInner_left_parallelResult
            outerLeft outerRight innerLeft innerRight previous tail valid
              inductionHypothesis
      | inr componentQuery =>
          exact SerialFactorization.afterInner_right_parallelResult
            outerLeft outerRight innerLeft innerRight previous tail valid
              inductionHypothesis
  | @afterOuter history previousReply currentOuter currentInner outerQuery
      response finalOuter finalInner previous tail valid inductionHypothesis =>
      cases outerQuery with
      | inl input =>
          exact SerialFactorization.afterOuter_left_parallelResult
            outerLeft outerRight innerLeft innerRight previous tail valid
              inductionHypothesis
      | inr input =>
          exact SerialFactorization.afterOuter_right_parallelResult
            outerLeft outerRight innerLeft innerRight previous tail valid
              inductionHypothesis

end Internal

/--
Ordered parallel preserves serial composition componentwise. This combines
Maurer--Renner 2016 converter composition (Section 3.3, printed p. 7) with Jost's
disjoint-interface parallel resources (printed p. 17).
-/
theorem parallel_serial_eq
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    (outerLeft : DDC A₁ B₁) (outerRight : DDC A₂ B₂)
    (innerLeft : DDC B₁ C₁) (innerRight : DDC B₂ C₂) :
    parallel (serial outerLeft innerLeft) (serial outerRight innerRight) =
      serial (parallel outerLeft outerRight)
        (parallel innerLeft innerRight) := by
  -- It suffices to include the right-hand canonical graph in the left-hand graph.
  apply eq_of_graph_subset_parallel
  intro history response responds
  rw [mem_serial_iff, mem_serialRaw_iff] at responds
  -- Decompose the joint serial witness into its two component factorizations.
  obtain ⟨attempted, historyEqual, finalOuter, finalInner, factorization⟩ :=
    responds
  subst history
  obtain ⟨leftHistory, rightHistory, leftResponse, rightResponse,
      leftOuter, rightOuter, leftInner, rightInner, inputProjection,
      outerProjection, outerActiveEqual, innerProjection,
      leftFactorization, rightFactorization, responseProjection,
      actual, packedEqual, membership⟩ :=
    factorization.parallelResult outerLeft outerRight innerLeft innerRight
  -- Determinism identifies the packed response with the requested response.
  have responseEqual : actual = response := by
    exact packResponse_injective_local attempted.toReceived
      (packedEqual.trans rfl.symm)
  subst actual
  -- The component memberships assemble the parallel-of-serial response.
  exact membership


end DDC




namespace DDC

private inductive TripleSide where
  | first
  | second
  | third
  deriving DecidableEq

private structure TripleProjection
    (A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}) where
  active : Option TripleSide
  first : Option (DDC.History A₁ B₁)
  second : Option (DDC.History A₂ B₂)
  third : Option (DDC.History A₃ B₃)

private def extendTripleLeftProjection
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    (projection : TripleProjection A₁ B₁ A₂ B₂ A₃ B₃)
    (input : DDC.History.Input
      (Interface.parallel (Interface.parallel A₁ A₂) A₃)
      (Interface.parallel (Interface.parallel B₁ B₂) B₃)) :
    TripleProjection A₁ B₁ A₂ B₂ A₃ B₃ :=
  match input with
  | Sum.inl (Sum.inl (Sum.inl query)) =>
      { projection with
        active := some .first
        first := some (appendOuter projection.first query) }
  | Sum.inl (Sum.inl (Sum.inr query)) =>
      { projection with
        active := some .second
        second := some (appendOuter projection.second query) }
  | Sum.inl (Sum.inr query) =>
      { projection with
        active := some .third
        third := some (appendOuter projection.third query) }
  | Sum.inr ⟨Sum.inl (Sum.inl query), reply⟩ =>
      { projection with first := projection.first.map fun history =>
          history.snocInner query reply }
  | Sum.inr ⟨Sum.inl (Sum.inr query), reply⟩ =>
      { projection with second := projection.second.map fun history =>
          history.snocInner query reply }
  | Sum.inr ⟨Sum.inr query, reply⟩ =>
      { projection with third := projection.third.map fun history =>
          history.snocInner query reply }

private def extendTripleRightProjection
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    (projection : TripleProjection A₁ B₁ A₂ B₂ A₃ B₃)
    (input : DDC.History.Input
      (Interface.parallel A₁ (Interface.parallel A₂ A₃))
      (Interface.parallel B₁ (Interface.parallel B₂ B₃))) :
    TripleProjection A₁ B₁ A₂ B₂ A₃ B₃ :=
  match input with
  | Sum.inl (Sum.inl query) =>
      { projection with
        active := some .first
        first := some (appendOuter projection.first query) }
  | Sum.inl (Sum.inr (Sum.inl query)) =>
      { projection with
        active := some .second
        second := some (appendOuter projection.second query) }
  | Sum.inl (Sum.inr (Sum.inr query)) =>
      { projection with
        active := some .third
        third := some (appendOuter projection.third query) }
  | Sum.inr ⟨Sum.inl query, reply⟩ =>
      { projection with first := projection.first.map fun history =>
          history.snocInner query reply }
  | Sum.inr ⟨Sum.inr (Sum.inl query), reply⟩ =>
      { projection with second := projection.second.map fun history =>
          history.snocInner query reply }
  | Sum.inr ⟨Sum.inr (Sum.inr query), reply⟩ =>
      { projection with third := projection.third.map fun history =>
          history.snocInner query reply }

private def flattenLeftProjection
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    (projection : ParallelProjection
      (Interface.parallel A₁ A₂) (Interface.parallel B₁ B₂) A₃ B₃) :
    TripleProjection A₁ B₁ A₂ B₂ A₃ B₃ :=
  let nested := projection.left.map projectParallel
  { active := match projection.active with
      | none => none
      | some .right => some .third
      | some .left => nested.bind fun p => p.active.map fun
          | .left => .first
          | .right => .second
    first := nested.bind fun p => p.left
    second := nested.bind fun p => p.right
    third := projection.right }

private def flattenRightProjection
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    (projection : ParallelProjection
      A₁ B₁ (Interface.parallel A₂ A₃) (Interface.parallel B₂ B₃)) :
    TripleProjection A₁ B₁ A₂ B₂ A₃ B₃ :=
  let nested := projection.right.map projectParallel
  { active := match projection.active with
      | none => none
      | some .left => some .first
      | some .right => nested.bind fun p => p.active.map fun
          | .left => .second
          | .right => .third
    first := projection.left
    second := nested.bind fun p => p.left
    third := nested.bind fun p => p.right }

private theorem flattenLeft_extend
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    (projection : ParallelProjection
      (Interface.parallel A₁ A₂) (Interface.parallel B₁ B₂) A₃ B₃)
    (input : DDC.History.Input
      (Interface.parallel (Interface.parallel A₁ A₂) A₃)
      (Interface.parallel (Interface.parallel B₁ B₂) B₃)) :
    flattenLeftProjection (extendParallelProjection projection input) =
      extendTripleLeftProjection (flattenLeftProjection projection) input := by
  rcases projection with ⟨active, left, right⟩
  cases input with
  | inl outer =>
      rcases outer with (inner | third)
      · rcases inner with (first | second) <;>
          cases left <;> simp [flattenLeftProjection, extendParallelProjection,
            extendTripleLeftProjection, appendOuter]
      · cases right <;>
          simp [flattenLeftProjection, extendParallelProjection, extendTripleLeftProjection,
            appendOuter]
  | inr inner =>
      rcases inner with ⟨query, reply⟩
      rcases query with (nested | third)
      · rcases nested with (first | second) <;>
          cases left <;> simp [flattenLeftProjection, extendParallelProjection,
            extendTripleLeftProjection]
      · cases right <;>
          simp [flattenLeftProjection, extendParallelProjection, extendTripleLeftProjection]

private theorem flattenRight_extend
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    (projection : ParallelProjection
      A₁ B₁ (Interface.parallel A₂ A₃) (Interface.parallel B₂ B₃))
    (input : DDC.History.Input
      (Interface.parallel A₁ (Interface.parallel A₂ A₃))
      (Interface.parallel B₁ (Interface.parallel B₂ B₃))) :
    flattenRightProjection (extendParallelProjection projection input) =
      extendTripleRightProjection (flattenRightProjection projection) input := by
  rcases projection with ⟨active, left, right⟩
  cases input with
  | inl outer =>
      rcases outer with (first | nested)
      · cases left <;>
          simp [flattenRightProjection, extendParallelProjection, extendTripleRightProjection,
            appendOuter]
      · rcases nested with (second | third) <;>
          cases right <;> simp [flattenRightProjection, extendParallelProjection,
            extendTripleRightProjection, appendOuter]
  | inr inner =>
      rcases inner with ⟨query, reply⟩
      rcases query with (first | nested)
      · cases left <;>
          simp [flattenRightProjection, extendParallelProjection, extendTripleRightProjection]
      · rcases nested with (second | third) <;>
          cases right <;> simp [flattenRightProjection, extendParallelProjection,
            extendTripleRightProjection]

private theorem tripleExtension_relabel_assoc
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    (projection : TripleProjection A₁ B₁ A₂ B₂ A₃ B₃)
    (input : DDC.History.Input
      (Interface.parallel (Interface.parallel A₁ A₂) A₃)
      (Interface.parallel (Interface.parallel B₁ B₂) B₃)) :
    extendTripleRightProjection projection
        (DDC.History.relabelInput
          (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
          (Interface.Equiv.parallelAssoc B₁ B₂ B₃) input) =
      extendTripleLeftProjection projection input := by
  cases input with
  | inl outer =>
      rcases outer with (nested | third)
      · rcases nested with (first | second) <;> rfl
      · rfl
  | inr inner =>
      rcases inner with ⟨query, reply⟩
      rcases query with (nested | third)
      · rcases nested with (first | second) <;> cases reply <;> rfl
      · cases reply <;> rfl

private theorem flattenLeft_foldl
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    (projection : ParallelProjection
      (Interface.parallel A₁ A₂) (Interface.parallel B₁ B₂) A₃ B₃)
    (inputs : List (DDC.History.Input
      (Interface.parallel (Interface.parallel A₁ A₂) A₃)
      (Interface.parallel (Interface.parallel B₁ B₂) B₃))) :
    flattenLeftProjection
        (inputs.foldl extendParallelProjection projection) =
      inputs.foldl extendTripleLeftProjection (flattenLeftProjection projection) := by
  induction inputs generalizing projection with
  | nil => rfl
  | cons input tail inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis]
      exact congrArg (fun initial => tail.foldl extendTripleLeftProjection initial)
        (flattenLeft_extend projection input)

private theorem flattenRight_foldl
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    (projection : ParallelProjection
      A₁ B₁ (Interface.parallel A₂ A₃) (Interface.parallel B₂ B₃))
    (inputs : List (DDC.History.Input
      (Interface.parallel A₁ (Interface.parallel A₂ A₃))
      (Interface.parallel B₁ (Interface.parallel B₂ B₃)))) :
    flattenRightProjection
        (inputs.foldl extendParallelProjection projection) =
      inputs.foldl extendTripleRightProjection (flattenRightProjection projection) := by
  induction inputs generalizing projection with
  | nil => rfl
  | cons input tail inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis]
      exact congrArg (fun initial => tail.foldl extendTripleRightProjection initial)
        (flattenRight_extend projection input)

private theorem foldl_relabel_assoc
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    (projection : TripleProjection A₁ B₁ A₂ B₂ A₃ B₃)
    (inputs : List (DDC.History.Input
      (Interface.parallel (Interface.parallel A₁ A₂) A₃)
      (Interface.parallel (Interface.parallel B₁ B₂) B₃))) :
    (inputs.map (DDC.History.relabelInput
        (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
        (Interface.Equiv.parallelAssoc B₁ B₂ B₃))).foldl
        extendTripleRightProjection projection =
      inputs.foldl extendTripleLeftProjection projection := by
  induction inputs generalizing projection with
  | nil => rfl
  | cons input tail inductionHypothesis =>
      simp only [List.map_cons, List.foldl_cons]
      rw [tripleExtension_relabel_assoc]
      exact inductionHypothesis _

/-- Reassociation relabeling preserves the exact active component and all
three component histories of a complete received history. -/
private theorem flattenProjection_relabel_assoc
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    (history : DDC.History
      (Interface.parallel (Interface.parallel A₁ A₂) A₃)
      (Interface.parallel (Interface.parallel B₁ B₂) B₃)) :
    flattenRightProjection
        (projectParallel (DDC.History.relabel
          (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
          (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history)) =
      flattenLeftProjection (projectParallel history) := by
  unfold projectParallel
  rw [show (DDC.History.relabel
      (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
      (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history).inputs.1 =
      history.inputs.1.map (DDC.History.relabelInput
        (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
        (Interface.Equiv.parallelAssoc B₁ B₂ B₃)) by rfl]
  rw [flattenRight_foldl, flattenLeft_foldl]
  exact foldl_relabel_assoc _ history.inputs.1


end DDC

/-! ## Parallel projection under relabeling -/





namespace DDC

@[simp]
private theorem parallelQueries_left
    {A₁ A₂ C₁ C₂ : Interface.{u, v}}
    (left : A₁.Equiv C₁) (right : A₂.Equiv C₂)
    (query : A₁.query) :
    (Interface.Equiv.parallel left right).queries (Sum.inl query) =
      Sum.inl (left.queries query) := by
  rfl

@[simp]
private theorem parallelQueries_right
    {A₁ A₂ C₁ C₂ : Interface.{u, v}}
    (left : A₁.Equiv C₁) (right : A₂.Equiv C₂)
    (query : A₂.query) :
    (Interface.Equiv.parallel left right).queries (Sum.inr query) =
      Sum.inr (right.queries query) := by
  rfl

@[simp]
private theorem parallelAnswers_left
    {A₁ A₂ C₁ C₂ : Interface.{u, v}}
    (left : A₁.Equiv C₁) (right : A₂.Equiv C₂)
    (query : A₁.query) :
    (Interface.Equiv.parallel left right).answers (Sum.inl query) =
      left.answers query := by
  rfl

@[simp]
private theorem parallelAnswers_right
    {A₁ A₂ C₁ C₂ : Interface.{u, v}}
    (left : A₁.Equiv C₁) (right : A₂.Equiv C₂)
    (query : A₂.query) :
    (Interface.Equiv.parallel left right).answers (Sum.inr query) =
      right.answers query := by
  rfl

@[simp]
private theorem parallelInnerReply_left
    {A₁ A₂ C₁ C₂ : Interface.{u, v}}
    (left : A₁.Equiv C₁) (right : A₂.Equiv C₂)
    (query : A₁.query) (reply : Option (A₁.answer query)) :
    (Interface.Equiv.parallel left right).innerReply ⟨Sum.inl query, reply⟩ =
      ⟨Sum.inl (left.queries query), reply.map (left.answers query)⟩ := by
  rfl

@[simp]
private theorem parallelInnerReply_right
    {A₁ A₂ C₁ C₂ : Interface.{u, v}}
    (left : A₁.Equiv C₁) (right : A₂.Equiv C₂)
    (query : A₂.query) (reply : Option (A₂.answer query)) :
    (Interface.Equiv.parallel left right).innerReply ⟨Sum.inr query, reply⟩ =
      ⟨Sum.inr (right.queries query), reply.map (right.answers query)⟩ := by
  rfl

@[simp]
private theorem relabelInput_parallel_outer_left
    {A₁ B₁ A₂ B₂ C₁ D₁ C₂ D₂ : Interface.{u, v}}
    (outerLeft : A₁.Equiv C₁) (innerLeft : B₁.Equiv D₁)
    (outerRight : A₂.Equiv C₂) (innerRight : B₂.Equiv D₂)
    (query : A₁.query) :
    DDC.History.relabelInput
        (Interface.Equiv.parallel outerLeft outerRight)
        (Interface.Equiv.parallel innerLeft innerRight)
        (Sum.inl (Sum.inl query)) =
      Sum.inl (Sum.inl (outerLeft.queries query)) := by
  rfl

@[simp]
private theorem relabelInput_parallel_outer_right
    {A₁ B₁ A₂ B₂ C₁ D₁ C₂ D₂ : Interface.{u, v}}
    (outerLeft : A₁.Equiv C₁) (innerLeft : B₁.Equiv D₁)
    (outerRight : A₂.Equiv C₂) (innerRight : B₂.Equiv D₂)
    (query : A₂.query) :
    DDC.History.relabelInput
        (Interface.Equiv.parallel outerLeft outerRight)
        (Interface.Equiv.parallel innerLeft innerRight)
        (Sum.inl (Sum.inr query)) =
      Sum.inl (Sum.inr (outerRight.queries query)) := by
  rfl

@[simp]
private theorem relabelInput_parallel_inner_left
    {A₁ B₁ A₂ B₂ C₁ D₁ C₂ D₂ : Interface.{u, v}}
    (outerLeft : A₁.Equiv C₁) (innerLeft : B₁.Equiv D₁)
    (outerRight : A₂.Equiv C₂) (innerRight : B₂.Equiv D₂)
    (query : B₁.query) (reply : Option (B₁.answer query)) :
    DDC.History.relabelInput
        (Interface.Equiv.parallel outerLeft outerRight)
        (Interface.Equiv.parallel innerLeft innerRight)
        (Sum.inr ⟨Sum.inl query, reply⟩) =
      Sum.inr ⟨Sum.inl (innerLeft.queries query),
        reply.map (innerLeft.answers query)⟩ := by
  rfl

@[simp]
private theorem relabelInput_parallel_inner_right
    {A₁ B₁ A₂ B₂ C₁ D₁ C₂ D₂ : Interface.{u, v}}
    (outerLeft : A₁.Equiv C₁) (innerLeft : B₁.Equiv D₁)
    (outerRight : A₂.Equiv C₂) (innerRight : B₂.Equiv D₂)
    (query : B₂.query) (reply : Option (B₂.answer query)) :
    DDC.History.relabelInput
        (Interface.Equiv.parallel outerLeft outerRight)
        (Interface.Equiv.parallel innerLeft innerRight)
        (Sum.inr ⟨Sum.inr query, reply⟩) =
      Sum.inr ⟨Sum.inr (innerRight.queries query),
        reply.map (innerRight.answers query)⟩ := by
  rfl

private def ParallelProjection.relabel
    {A₁ B₁ A₂ B₂ C₁ D₁ C₂ D₂ : Interface.{u, v}}
    (outerLeft : A₁.Equiv C₁) (innerLeft : B₁.Equiv D₁)
    (outerRight : A₂.Equiv C₂) (innerRight : B₂.Equiv D₂)
    (projection : ParallelProjection A₁ B₁ A₂ B₂) :
    ParallelProjection C₁ D₁ C₂ D₂ :=
  { active := projection.active
    left := projection.left.map
      (DDC.History.relabel outerLeft innerLeft)
    right := projection.right.map
      (DDC.History.relabel outerRight innerRight) }

private theorem extendParallelProjection_relabel
    {A₁ B₁ A₂ B₂ C₁ D₁ C₂ D₂ : Interface.{u, v}}
    (outerLeft : A₁.Equiv C₁) (innerLeft : B₁.Equiv D₁)
    (outerRight : A₂.Equiv C₂) (innerRight : B₂.Equiv D₂)
    (projection : ParallelProjection A₁ B₁ A₂ B₂)
    (input : DDC.History.Input (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)) :
    extendParallelProjection
        (projection.relabel outerLeft innerLeft outerRight innerRight)
        (DDC.History.relabelInput
          (Interface.Equiv.parallel outerLeft outerRight)
          (Interface.Equiv.parallel innerLeft innerRight) input) =
      (extendParallelProjection projection input).relabel
        outerLeft innerLeft outerRight innerRight := by
  rcases projection with ⟨active, left, right⟩
  cases input with
  | inl outer =>
      rcases outer with (query | query)
      · cases left <;>
          simp [ParallelProjection.relabel, extendParallelProjection,
            appendOuter,
            DDC.History.relabel_singleton,
            DDC.History.relabel_snocOuter]
      · cases right <;>
          simp [ParallelProjection.relabel, extendParallelProjection,
            appendOuter,
            DDC.History.relabel_singleton,
            DDC.History.relabel_snocOuter]
  | inr inner =>
      rcases inner with ⟨query, reply⟩
      rcases query with (query | query)
      · cases left <;> cases reply <;>
          simp [ParallelProjection.relabel, extendParallelProjection,
            relabelInput_parallel_inner_left,
            DDC.History.relabel_snocInner] <;> rfl
      · cases right <;> cases reply <;>
          simp [ParallelProjection.relabel, extendParallelProjection,
            relabelInput_parallel_inner_right,
            DDC.History.relabel_snocInner] <;> rfl

private theorem projectParallel_foldl_relabel
    {A₁ B₁ A₂ B₂ C₁ D₁ C₂ D₂ : Interface.{u, v}}
    (outerLeft : A₁.Equiv C₁) (innerLeft : B₁.Equiv D₁)
    (outerRight : A₂.Equiv C₂) (innerRight : B₂.Equiv D₂)
    (projection : ParallelProjection A₁ B₁ A₂ B₂)
    (inputs : List (DDC.History.Input (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))) :
    (inputs.map (DDC.History.relabelInput
        (Interface.Equiv.parallel outerLeft outerRight)
        (Interface.Equiv.parallel innerLeft innerRight))).foldl
        extendParallelProjection
        (projection.relabel outerLeft innerLeft outerRight innerRight) =
      (inputs.foldl extendParallelProjection projection).relabel
        outerLeft innerLeft outerRight innerRight := by
  induction inputs generalizing projection with
  | nil => rfl
  | cons input tail inductionHypothesis =>
      simp only [List.map_cons, List.foldl_cons]
      rw [extendParallelProjection_relabel]
      exact inductionHypothesis _

/-- Ordered binary projection commutes exactly with componentwise dependent
interface relabeling. -/
private theorem projectParallel_relabel
    {A₁ B₁ A₂ B₂ C₁ D₁ C₂ D₂ : Interface.{u, v}}
    (outerLeft : A₁.Equiv C₁) (innerLeft : B₁.Equiv D₁)
    (outerRight : A₂.Equiv C₂) (innerRight : B₂.Equiv D₂)
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)) :
    projectParallel (DDC.History.relabel
        (Interface.Equiv.parallel outerLeft outerRight)
        (Interface.Equiv.parallel innerLeft innerRight) history) =
      (projectParallel history).relabel
        outerLeft innerLeft outerRight innerRight := by
  unfold projectParallel
  rw [show (DDC.History.relabel
      (Interface.Equiv.parallel outerLeft outerRight)
      (Interface.Equiv.parallel innerLeft innerRight) history).inputs.1 =
      history.inputs.1.map (DDC.History.relabelInput
        (Interface.Equiv.parallel outerLeft outerRight)
        (Interface.Equiv.parallel innerLeft innerRight)) by rfl]
  simpa [ParallelProjection.relabel] using
    (projectParallel_foldl_relabel outerLeft innerLeft outerRight
      innerRight
      ({ active := none, left := none, right := none } :
        ParallelProjection A₁ B₁ A₂ B₂)
      history.inputs.1)


end DDC

/-! ## Parallel graph under relabeling -/





namespace DDC

private theorem targetOuterLeft
    {A₁ B₁ A₂ B₂ C₁ D₁ C₂ D₂ : Interface.{u, v}}
    (outerLeft : A₁.Equiv C₁) (innerLeft : B₁.Equiv D₁)
    (outerRight : A₂.Equiv C₂) (innerRight : B₂.Equiv D₂)
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₁ B₁)
    (outerEqual : history.lastOuter = Sum.inl component.lastOuter) :
    (DDC.History.relabel
      (Interface.Equiv.parallel outerLeft outerRight)
      (Interface.Equiv.parallel innerLeft innerRight) history).lastOuter =
      Sum.inl (DDC.History.relabel outerLeft innerLeft component).lastOuter := by
  rw [DDC.History.lastOuter_relabel,
    DDC.History.lastOuter_relabel, outerEqual]
  rfl

private theorem targetOuterRight
    {A₁ B₁ A₂ B₂ C₁ D₁ C₂ D₂ : Interface.{u, v}}
    (outerLeft : A₁.Equiv C₁) (innerLeft : B₁.Equiv D₁)
    (outerRight : A₂.Equiv C₂) (innerRight : B₂.Equiv D₂)
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₂ B₂)
    (outerEqual : history.lastOuter = Sum.inr component.lastOuter) :
    (DDC.History.relabel
      (Interface.Equiv.parallel outerLeft outerRight)
      (Interface.Equiv.parallel innerLeft innerRight) history).lastOuter =
      Sum.inr (DDC.History.relabel outerRight innerRight component).lastOuter := by
  rw [DDC.History.lastOuter_relabel,
    DDC.History.lastOuter_relabel, outerEqual]
  rfl

private theorem packed_tagLeft
    {A₁ A₂ : Interface.{u, v}}
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel A₁ A₂))
    (component : DDC.History A₁ A₁)
    (outerEqual : history.lastOuter = Sum.inl component.lastOuter)
    (reply : Option (A₁.answer component.lastOuter)) :
    (⟨history.lastOuter,
      cast (congrArg (fun selected =>
        Option ((Interface.parallel A₁ A₂).answer selected))
        outerEqual.symm) reply⟩ : DDC.History.InnerReply (Interface.parallel A₁ A₂)) =
      ⟨Sum.inl component.lastOuter, reply⟩ := by
  apply Sigma.ext outerEqual
  exact cast_heq _ _

private theorem packed_tagLeft_general
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₁ B₁)
    (outerEqual : history.lastOuter = Sum.inl component.lastOuter)
    (reply : Option (A₁.answer component.lastOuter)) :
    (⟨history.lastOuter,
      cast (congrArg (fun selected =>
        Option ((Interface.parallel A₁ A₂).answer selected))
        outerEqual.symm) reply⟩ : DDC.History.InnerReply (Interface.parallel A₁ A₂)) =
      ⟨Sum.inl component.lastOuter, reply⟩ := by
  apply Sigma.ext outerEqual
  exact cast_heq _ _

private theorem packed_tagRight_general
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₂ B₂)
    (outerEqual : history.lastOuter = Sum.inr component.lastOuter)
    (reply : Option (A₂.answer component.lastOuter)) :
    (⟨history.lastOuter,
      cast (congrArg (fun selected =>
        Option ((Interface.parallel A₁ A₂).answer selected))
        outerEqual.symm) reply⟩ : DDC.History.InnerReply (Interface.parallel A₁ A₂)) =
      ⟨Sum.inr component.lastOuter, reply⟩ := by
  apply Sigma.ext outerEqual
  exact cast_heq _ _

private theorem relabelResponse_tagLeft
    {A₁ B₁ A₂ B₂ C₁ D₁ C₂ D₂ : Interface.{u, v}}
    (outerLeft : A₁.Equiv C₁) (innerLeft : B₁.Equiv D₁)
    (outerRight : A₂.Equiv C₂) (innerRight : B₂.Equiv D₂)
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₁ B₁)
    (outerEqual : history.lastOuter = Sum.inl component.lastOuter)
    (response : DDC.Response component) :
    relabelResponse
        (Interface.Equiv.parallel outerLeft outerRight)
        (Interface.Equiv.parallel innerLeft innerRight) history
        (tagLeftResponse history component outerEqual response) =
      tagLeftResponse
        (DDC.History.relabel
          (Interface.Equiv.parallel outerLeft outerRight)
          (Interface.Equiv.parallel innerLeft innerRight) history)
        (DDC.History.relabel outerLeft innerLeft component)
        (targetOuterLeft outerLeft innerLeft outerRight innerRight
          history component outerEqual)
        (relabelResponse outerLeft innerLeft component response) := by
  cases response with
  | inl query => rfl
  | inr reply =>
      let targetHistory := DDC.History.relabel
        (Interface.Equiv.parallel outerLeft outerRight)
        (Interface.Equiv.parallel innerLeft innerRight) history
      let targetComponent := DDC.History.relabel outerLeft innerLeft component
      let sourceTagged := cast
        (congrArg (fun selected =>
          Option ((Interface.parallel A₁ A₂).answer selected))
          outerEqual.symm) reply
      let componentReply := relabelOuterReply outerLeft innerLeft component reply
      let targetEqual := targetOuterLeft outerLeft innerLeft outerRight innerRight
        history component outerEqual
      let targetTagged := cast
        (congrArg (fun selected =>
          Option ((Interface.parallel C₁ C₂).answer selected))
          targetEqual.symm) componentReply
      simp only [tagLeftResponse, relabelResponse_outer]
      have componentPacked := packed_outer_relabel outerLeft innerLeft
        component reply
      let leftPacked : DDC.History.InnerReply C₁ →
          DDC.History.InnerReply (Interface.parallel C₁ C₂) :=
        fun packed => ⟨Sum.inl packed.1, packed.2⟩
      have embeddedComponentPacked := congrArg leftPacked componentPacked
      have packedEqual :
          (⟨targetHistory.lastOuter,
            relabelOuterReply
              (Interface.Equiv.parallel outerLeft outerRight)
              (Interface.Equiv.parallel innerLeft innerRight)
              history sourceTagged⟩ :
              DDC.History.InnerReply (Interface.parallel C₁ C₂)) =
            ⟨targetHistory.lastOuter, targetTagged⟩ := by
        calc
          _ = (Interface.Equiv.parallel outerLeft outerRight).innerReply
                ⟨history.lastOuter, sourceTagged⟩ :=
            packed_outer_relabel
              (Interface.Equiv.parallel outerLeft outerRight)
              (Interface.Equiv.parallel innerLeft innerRight)
              history sourceTagged
          _ = (Interface.Equiv.parallel outerLeft outerRight).innerReply
                ⟨Sum.inl component.lastOuter, reply⟩ := by
            exact congrArg
              (Interface.Equiv.parallel outerLeft outerRight).innerReply
              (packed_tagLeft_general history component outerEqual reply)
          _ = leftPacked
                (outerLeft.innerReply ⟨component.lastOuter, reply⟩) := by
            rfl
          _ = leftPacked ⟨targetComponent.lastOuter, componentReply⟩ :=
            embeddedComponentPacked.symm
          _ = ⟨Sum.inl targetComponent.lastOuter, componentReply⟩ := rfl
          _ = ⟨targetHistory.lastOuter, targetTagged⟩ :=
            (packed_tagLeft_general targetHistory targetComponent
              targetEqual componentReply).symm
      exact congrArg Sum.inr
        (eq_of_heq (Sigma.mk.inj_iff.mp packedEqual).2)

private theorem relabelResponse_tagRight
    {A₁ B₁ A₂ B₂ C₁ D₁ C₂ D₂ : Interface.{u, v}}
    (outerLeft : A₁.Equiv C₁) (innerLeft : B₁.Equiv D₁)
    (outerRight : A₂.Equiv C₂) (innerRight : B₂.Equiv D₂)
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₂ B₂)
    (outerEqual : history.lastOuter = Sum.inr component.lastOuter)
    (response : DDC.Response component) :
    relabelResponse
        (Interface.Equiv.parallel outerLeft outerRight)
        (Interface.Equiv.parallel innerLeft innerRight) history
        (tagRightResponse history component outerEqual response) =
      tagRightResponse
        (DDC.History.relabel
          (Interface.Equiv.parallel outerLeft outerRight)
          (Interface.Equiv.parallel innerLeft innerRight) history)
        (DDC.History.relabel outerRight innerRight component)
        (targetOuterRight outerLeft innerLeft outerRight innerRight
          history component outerEqual)
        (relabelResponse outerRight innerRight component response) := by
  cases response with
  | inl query => rfl
  | inr reply =>
      let targetHistory := DDC.History.relabel
        (Interface.Equiv.parallel outerLeft outerRight)
        (Interface.Equiv.parallel innerLeft innerRight) history
      let targetComponent := DDC.History.relabel outerRight innerRight component
      let sourceTagged := cast
        (congrArg (fun selected =>
          Option ((Interface.parallel A₁ A₂).answer selected))
          outerEqual.symm) reply
      let componentReply := relabelOuterReply outerRight innerRight component reply
      let targetEqual := targetOuterRight outerLeft innerLeft outerRight innerRight
        history component outerEqual
      let targetTagged := cast
        (congrArg (fun selected =>
          Option ((Interface.parallel C₁ C₂).answer selected))
          targetEqual.symm) componentReply
      simp only [tagRightResponse, relabelResponse_outer]
      have componentPacked := packed_outer_relabel outerRight innerRight
        component reply
      let rightPacked : DDC.History.InnerReply C₂ →
          DDC.History.InnerReply (Interface.parallel C₁ C₂) :=
        fun packed => ⟨Sum.inr packed.1, packed.2⟩
      have embeddedComponentPacked := congrArg rightPacked componentPacked
      have packedEqual :
          (⟨targetHistory.lastOuter,
            relabelOuterReply
              (Interface.Equiv.parallel outerLeft outerRight)
              (Interface.Equiv.parallel innerLeft innerRight)
              history sourceTagged⟩ :
              DDC.History.InnerReply (Interface.parallel C₁ C₂)) =
            ⟨targetHistory.lastOuter, targetTagged⟩ := by
        calc
          _ = (Interface.Equiv.parallel outerLeft outerRight).innerReply
                ⟨history.lastOuter, sourceTagged⟩ :=
            packed_outer_relabel
              (Interface.Equiv.parallel outerLeft outerRight)
              (Interface.Equiv.parallel innerLeft innerRight)
              history sourceTagged
          _ = (Interface.Equiv.parallel outerLeft outerRight).innerReply
                ⟨Sum.inr component.lastOuter, reply⟩ := by
            exact congrArg
              (Interface.Equiv.parallel outerLeft outerRight).innerReply
              (packed_tagRight_general history component outerEqual reply)
          _ = rightPacked
                (outerRight.innerReply ⟨component.lastOuter, reply⟩) := by
            rfl
          _ = rightPacked ⟨targetComponent.lastOuter, componentReply⟩ :=
            embeddedComponentPacked.symm
          _ = ⟨Sum.inr targetComponent.lastOuter, componentReply⟩ := rfl
          _ = ⟨targetHistory.lastOuter, targetTagged⟩ :=
            (packed_tagRight_general targetHistory targetComponent
              targetEqual componentReply).symm
      exact congrArg Sum.inr
        (eq_of_heq (Sigma.mk.inj_iff.mp packedEqual).2)

/-- Componentwise dependent relabeling carries every admissible raw parallel
graph row to the correspondingly relabeled raw parallel graph row. -/
private theorem parallelRaw_relabel_mem
    {A₁ B₁ A₂ B₂ C₁ D₁ C₂ D₂ : Interface.{u, v}}
    (outerLeft : A₁.Equiv C₁) (innerLeft : B₁.Equiv D₁)
    (outerRight : A₂.Equiv C₂) (innerRight : B₂.Equiv D₂)
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (admissible : DDC.Raw.Admissible (parallelRaw left right) history)
    (response : DDC.Response history)
    (responds : response ∈ parallelRaw left right history) :
    relabelResponse
        (Interface.Equiv.parallel outerLeft outerRight)
        (Interface.Equiv.parallel innerLeft innerRight) history response ∈
      parallelRaw (relabel outerLeft innerLeft left)
        (relabel outerRight innerRight right)
        (DDC.History.relabel
          (Interface.Equiv.parallel outerLeft outerRight)
          (Interface.Equiv.parallel innerLeft innerRight) history) := by
  let targetHistory := DDC.History.relabel
    (Interface.Equiv.parallel outerLeft outerRight)
    (Interface.Equiv.parallel innerLeft innerRight) history
  have projectionEqual := projectParallel_relabel outerLeft innerLeft
    outerRight innerRight history
  rcases parallelRaw_admissible_active left right admissible with
      ⟨component, active⟩ | ⟨component, active⟩
  · obtain ⟨componentResponse, componentResponds, tagged⟩ :=
      (mem_parallelRaw_left_iff left right history component active
        response).mp responds
    have targetActive : ActiveLeft targetHistory
        (DDC.History.relabel outerLeft innerLeft component) := by
      refine ⟨?_, ?_, targetOuterLeft outerLeft innerLeft outerRight
        innerRight history component active.2.2⟩
      · rw [projectionEqual]
        exact active.1
      · rw [projectionEqual]
        change (projectParallel history).left.map
            (DDC.History.relabel outerLeft innerLeft) = _
        rw [active.2.1]
        rfl
    apply (mem_parallelRaw_left_iff
      (relabel outerLeft innerLeft left)
      (relabel outerRight innerRight right)
      targetHistory (DDC.History.relabel outerLeft innerLeft component)
      targetActive _).mpr
    refine ⟨relabelResponse outerLeft innerLeft component componentResponse,
      mem_relabel_of_mem outerLeft innerLeft left component componentResponse
        componentResponds, ?_⟩
    rw [← tagged]
    exact (relabelResponse_tagLeft outerLeft innerLeft outerRight innerRight
      history component active.2.2 componentResponse).symm
  · obtain ⟨componentResponse, componentResponds, tagged⟩ :=
      (mem_parallelRaw_right_iff left right history component active
        response).mp responds
    have targetActive : ActiveRight targetHistory
        (DDC.History.relabel outerRight innerRight component) := by
      refine ⟨?_, ?_, targetOuterRight outerLeft innerLeft outerRight
        innerRight history component active.2.2⟩
      · rw [projectionEqual]
        exact active.1
      · rw [projectionEqual]
        change (projectParallel history).right.map
            (DDC.History.relabel outerRight innerRight) = _
        rw [active.2.1]
        rfl
    apply (mem_parallelRaw_right_iff
      (relabel outerLeft innerLeft left)
      (relabel outerRight innerRight right)
      targetHistory (DDC.History.relabel outerRight innerRight component)
      targetActive _).mpr
    refine ⟨relabelResponse outerRight innerRight component componentResponse,
      mem_relabel_of_mem outerRight innerRight right component componentResponse
        componentResponds, ?_⟩
    rw [← tagged]
    exact (relabelResponse_tagRight outerLeft innerLeft outerRight innerRight
      history component active.2.2 componentResponse).symm

/-- Componentwise dependent relabeling preserves the exact raw parallel
history tree. -/
private theorem parallelRaw_admissible_relabel
    {A₁ B₁ A₂ B₂ C₁ D₁ C₂ D₂ : Interface.{u, v}}
    (outerLeft : A₁.Equiv C₁) (innerLeft : B₁.Equiv D₁)
    (outerRight : A₂.Equiv C₂) (innerRight : B₂.Equiv D₂)
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    {history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    (admissible : DDC.Raw.Admissible (parallelRaw left right) history) :
    DDC.Raw.Admissible
      (parallelRaw (relabel outerLeft innerLeft left)
        (relabel outerRight innerRight right))
      (DDC.History.relabel
        (Interface.Equiv.parallel outerLeft outerRight)
        (Interface.Equiv.parallel innerLeft innerRight) history) := by
  induction admissible with
  | start query =>
      exact @DDC.Raw.Admissible.start _ _ _
        ((Interface.Equiv.parallel outerLeft outerRight).queries query)
  | @afterInner prior query priorAdmissible responds reply
      inductionHypothesis =>
      have mappedResponds := parallelRaw_relabel_mem outerLeft innerLeft
        outerRight innerRight left right prior priorAdmissible
        (Sum.inl query) responds
      have target := @DDC.Raw.Admissible.afterInner _ _ _ _
        ((Interface.Equiv.parallel innerLeft innerRight).queries query)
        inductionHypothesis mappedResponds
        (reply.map ((Interface.Equiv.parallel innerLeft innerRight).answers query))
      exact (DDC.History.relabel_snocInner
        (Interface.Equiv.parallel outerLeft outerRight)
        (Interface.Equiv.parallel innerLeft innerRight)
        prior query reply) ▸ target
  | @afterOuter prior priorAdmissible reply responds query
      inductionHypothesis =>
      have mappedResponds := parallelRaw_relabel_mem outerLeft innerLeft
        outerRight innerRight left right prior priorAdmissible
        (Sum.inr reply) responds
      have target := @DDC.Raw.Admissible.afterOuter _ _ _ _
        inductionHypothesis _ mappedResponds
        ((Interface.Equiv.parallel outerLeft outerRight).queries query)
      exact (DDC.History.relabel_snocOuter
        (Interface.Equiv.parallel outerLeft outerRight)
        (Interface.Equiv.parallel innerLeft innerRight)
        prior query) ▸ target

/-- Componentwise dependent relabeling carries each canonical ordered-parallel
graph row to the corresponding row of the relabeled ordered parallel. -/
private theorem parallel_relabel_mem
    {A₁ B₁ A₂ B₂ C₁ D₁ C₂ D₂ : Interface.{u, v}}
    (outerLeft : A₁.Equiv C₁) (innerLeft : B₁.Equiv D₁)
    (outerRight : A₂.Equiv C₂) (innerRight : B₂.Equiv D₂)
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (response : DDC.Response history)
    (responds : response ∈ parallel left right history) :
    relabelResponse
        (Interface.Equiv.parallel outerLeft outerRight)
        (Interface.Equiv.parallel innerLeft innerRight) history response ∈
      parallel (relabel outerLeft innerLeft left)
        (relabel outerRight innerRight right)
        (DDC.History.relabel
          (Interface.Equiv.parallel outerLeft outerRight)
          (Interface.Equiv.parallel innerLeft innerRight) history) := by
  obtain ⟨admissible, rawResponds⟩ :=
    (mem_parallel_iff left right history response).mp responds
  apply (mem_parallel_iff
    (relabel outerLeft innerLeft left)
    (relabel outerRight innerRight right)
    (DDC.History.relabel
      (Interface.Equiv.parallel outerLeft outerRight)
      (Interface.Equiv.parallel innerLeft innerRight) history) _).mpr
  exact ⟨parallelRaw_admissible_relabel outerLeft innerLeft outerRight
      innerRight left right admissible,
    parallelRaw_relabel_mem outerLeft innerLeft outerRight innerRight left
      right history admissible response rawResponds⟩

private theorem eq_of_graph_subset_local
    {A B : Interface.{u, v}} (left right : DDC A B)
    (subset : ∀ history response,
      response ∈ right history → response ∈ left history) :
    left = right := by
  have admissible : ∀ {history},
      DDC.Raw.Admissible left.toFun history →
        DDC.Raw.Admissible right.toFun history := by
    intro history valid
    induction valid with
    | start query => exact .start query
    | @afterInner previous query prior leftResponds reply ih =>
        have rightResponds := right.response_mem previous ih
        have responseEqual : right.response previous ih = Sum.inl query :=
          Part.mem_unique (subset previous _ rightResponds) leftResponds
        exact .afterInner ih (responseEqual ▸ rightResponds) reply
    | @afterOuter previous prior reply leftResponds query ih =>
        have rightResponds := right.response_mem previous ih
        have responseEqual : right.response previous ih = Sum.inr reply :=
          Part.mem_unique (subset previous _ rightResponds) leftResponds
        exact .afterOuter ih (responseEqual ▸ rightResponds) query
  apply DDC.ext
  intro history response
  constructor
  · intro leftResponds
    have rightAdmissible := admissible
      ((left.exactDomain history).mp leftResponds.1)
    have rightResponds := right.response_mem history rightAdmissible
    have responseEqual : right.response history rightAdmissible = response :=
      Part.mem_unique (subset history _ rightResponds) leftResponds
    exact responseEqual ▸ rightResponds
  · exact subset history response

private def responseRelabelLocal
    {A B C D : Interface.{u, v}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (targetHistory : DDC.History C D) :
    DDC.Response
        ((DDC.History.relabelEquiv outer inner).symm targetHistory) ≃
      DDC.Response targetHistory :=
  let histories := DDC.History.relabelEquiv outer inner
  let sourceHistory := histories.symm targetHistory
  (relabelResponse outer inner sourceHistory).trans
    (_root_.Equiv.cast (congrArg (fun history => DDC.Response history)
      (histories.apply_symm_apply targetHistory)))

private theorem transport_mem_local
    {A B : Interface.{u, v}} (converter : DDC A B)
    {left right : DDC.History A B} (equal : left = right)
    (response : DDC.Response left)
    (responds : response ∈ converter left) :
    cast (congrArg (fun history => DDC.Response history) equal) response ∈
      converter right := by
  cases equal
  exact responds

/-- Ordered parallel commutes with simultaneous dependent relabeling of both
components. -/
private theorem parallel_relabel_eq
    {A₁ B₁ A₂ B₂ C₁ D₁ C₂ D₂ : Interface.{u, v}}
    (outerLeft : A₁.Equiv C₁) (innerLeft : B₁.Equiv D₁)
    (outerRight : A₂.Equiv C₂) (innerRight : B₂.Equiv D₂)
    (left : DDC A₁ B₁) (right : DDC A₂ B₂) :
    parallel (relabel outerLeft innerLeft left)
        (relabel outerRight innerRight right) =
      relabel (Interface.Equiv.parallel outerLeft outerRight)
        (Interface.Equiv.parallel innerLeft innerRight)
        (parallel left right) := by
  let jointOuter := Interface.Equiv.parallel outerLeft outerRight
  let jointInner := Interface.Equiv.parallel innerLeft innerRight
  apply eq_of_graph_subset_local
  intro targetHistory targetResponse responds
  have sourceResponds :=
    (mem_relabel_iff_symm jointOuter jointInner (parallel left right)
      targetHistory targetResponse).mp responds
  let histories := DDC.History.relabelEquiv jointOuter jointInner
  let sourceHistory := histories.symm targetHistory
  let responses := responseRelabelLocal jointOuter jointInner targetHistory
  let sourceResponse := responses.symm targetResponse
  have mapped := parallel_relabel_mem outerLeft innerLeft outerRight innerRight
    left right sourceHistory sourceResponse sourceResponds
  have historyEqual : DDC.History.relabel jointOuter jointInner
      sourceHistory = targetHistory := histories.apply_symm_apply targetHistory
  have responseEqual :
      cast (congrArg (fun selected => DDC.Response selected) historyEqual)
          (relabelResponse jointOuter jointInner sourceHistory sourceResponse) =
        targetResponse := responses.apply_symm_apply targetResponse
  have transported := transport_mem_local
    (parallel (relabel outerLeft innerLeft left)
      (relabel outerRight innerRight right)) historyEqual _ mapped
  exact responseEqual ▸ transported


end DDC
namespace DDC

private def outerReceivedInput?
    {A B : Interface.{u, v}} : DDC.History.Input A B → Option A.query
  | Sum.inl query => some query
  | Sum.inr _ => none

private def ParallelProjection.selectedLast
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    (projection : ParallelProjection A₁ B₁ A₂ B₂) :
    Option (A₁.query ⊕ A₂.query) :=
  match projection.active with
  | none => none
  | some .left => projection.left.map fun history => Sum.inl history.lastOuter
  | some .right => projection.right.map fun history => Sum.inr history.lastOuter

private theorem projectParallel_selectedLast
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    (inputs : List (DDC.History.Input (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))) :
    (inputs.filterMap outerReceivedInput?).getLast? =
      (inputs.foldl extendParallelProjection
        ({ active := none, left := none, right := none } :
          ParallelProjection A₁ B₁ A₂ B₂)).selectedLast := by
  induction inputs using List.reverseRecOn with
  | nil => rfl
  | append_singleton inputs input inductionHypothesis =>
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, List.filterMap_append]
    let projection := inputs.foldl extendParallelProjection
      ({ active := none, left := none, right := none } :
        ParallelProjection A₁ B₁ A₂ B₂)
    change _ = (extendParallelProjection projection input).selectedLast
    have previous :
        (inputs.filterMap outerReceivedInput?).getLast? =
          projection.selectedLast :=
      inductionHypothesis
    rcases projection with ⟨active, left, right⟩
    cases input with
    | inl outer =>
        rcases outer with (query | query) <;>
          cases left <;> cases right <;>
          simp [ParallelProjection.selectedLast, extendParallelProjection,
            appendOuter] <;> rfl
    | inr inner =>
        rcases inner with ⟨query, reply⟩
        rcases query with (query | query) <;>
          cases active <;> cases left <;> cases right <;>
          simpa [ParallelProjection.selectedLast, extendParallelProjection]
            using previous

private theorem activeLeft_of_projection
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    {history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {component : DDC.History A₁ B₁}
    (active : (projectParallel history).active = some .left)
    (componentEqual : (projectParallel history).left = some component) :
    ActiveLeft history component := by
  refine ⟨active, componentEqual, ?_⟩
  have selected := projectParallel_selectedLast history.inputs.1
  change _ = (projectParallel history).selectedLast at selected
  change (history.inputs.1.filterMap outerReceivedInput?).getLast? =
    (projectParallel history).selectedLast at selected
  have projects : history.inputs.1.filterMap outerReceivedInput? =
      history.outer.1 := by
    simpa [outerReceivedInput?] using history.projects
  have outerLast : history.outer.1.getLast? = some history.lastOuter :=
    List.getLast?_eq_some_getLast history.outer.2
  rw [← projects] at outerLast
  have projectedLast :
      (projectParallel history).selectedLast =
        some (Sum.inl component.lastOuter) := by
    simp [ParallelProjection.selectedLast, active, componentEqual]
  have equal : some history.lastOuter =
      (projectParallel history).selectedLast := outerLast.symm.trans selected
  rw [projectedLast] at equal
  exact Option.some.inj equal

private theorem activeRight_of_projection
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    {history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {component : DDC.History A₂ B₂}
    (active : (projectParallel history).active = some .right)
    (componentEqual : (projectParallel history).right = some component) :
    ActiveRight history component := by
  refine ⟨active, componentEqual, ?_⟩
  have selected := projectParallel_selectedLast history.inputs.1
  change _ = (projectParallel history).selectedLast at selected
  change (history.inputs.1.filterMap outerReceivedInput?).getLast? =
    (projectParallel history).selectedLast at selected
  have projects : history.inputs.1.filterMap outerReceivedInput? =
      history.outer.1 := by
    simpa [outerReceivedInput?] using history.projects
  have outerLast : history.outer.1.getLast? = some history.lastOuter :=
    List.getLast?_eq_some_getLast history.outer.2
  rw [← projects] at outerLast
  have projectedLast :
      (projectParallel history).selectedLast =
        some (Sum.inr component.lastOuter) := by
    simp [ParallelProjection.selectedLast, active, componentEqual]
  have equal : some history.lastOuter =
      (projectParallel history).selectedLast := outerLast.symm.trans selected
  rw [projectedLast] at equal
  exact Option.some.inj equal

private theorem activeFirst_relabel_assoc
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    {history : DDC.History
      (Interface.parallel (Interface.parallel A₁ A₂) A₃)
      (Interface.parallel (Interface.parallel B₁ B₂) B₃)}
    {pairHistory : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {component : DDC.History A₁ B₁}
    (outerActive : ActiveLeft history pairHistory)
    (innerActive : ActiveLeft pairHistory component) :
    ActiveLeft
      (DDC.History.relabel
        (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
        (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history)
      component := by
  let target := DDC.History.relabel
    (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
    (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history
  let targetProjection := projectParallel target
  have flattened := flattenProjection_relabel_assoc history
  have targetLeft : targetProjection.left = some component := by
    have firstEqual := congrArg TripleProjection.first flattened
    simpa only [target, targetProjection, flattenRightProjection,
      flattenLeftProjection, outerActive.2.1, innerActive.2.1,
      Option.map_some, Option.bind_some] using firstEqual
  have targetActive : targetProjection.active = some .left := by
    have activeEqual := congrArg TripleProjection.active flattened
    simp only [flattenRightProjection,
      flattenLeftProjection, outerActive.1, outerActive.2.1,
      innerActive.1, Option.map_some, Option.bind_some] at activeEqual
    change (flattenRightProjection targetProjection).active =
      some .first at activeEqual
    cases active : targetProjection.active with
    | none => simp [flattenRightProjection, active] at activeEqual
    | some side =>
        cases side with
        | left => rfl
        | right =>
            cases rightEqual : targetProjection.right with
            | none =>
                simp [flattenRightProjection, active, rightEqual] at activeEqual
            | some targetPair =>
                cases nestedActive : (projectParallel targetPair).active with
                | none =>
                    simp [flattenRightProjection, active, rightEqual,
                      nestedActive] at activeEqual
                | some nestedSide =>
                    cases nestedSide <;>
                      simp [flattenRightProjection, active, rightEqual,
                        nestedActive] at activeEqual
  have targetOuter : target.lastOuter = Sum.inl component.lastOuter := by
    calc
      target.lastOuter =
          (Interface.Equiv.parallelAssoc A₁ A₂ A₃).queries
            history.lastOuter :=
        DDC.History.lastOuter_relabel _ _ _
      _ = Sum.inl component.lastOuter := by
        rw [outerActive.2.2, innerActive.2.2]
        exact Equiv.sumAssoc_apply_inl_inl component.lastOuter
  exact ⟨targetActive, targetLeft, targetOuter⟩

private theorem activeSecond_relabel_assoc
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    {history : DDC.History
      (Interface.parallel (Interface.parallel A₁ A₂) A₃)
      (Interface.parallel (Interface.parallel B₁ B₂) B₃)}
    {pairHistory : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {component : DDC.History A₂ B₂}
    (outerActive : ActiveLeft history pairHistory)
    (innerActive : ActiveRight pairHistory component) :
    ∃ targetPair : DDC.History (Interface.parallel A₂ A₃)
        (Interface.parallel B₂ B₃),
      ActiveRight
          (DDC.History.relabel
            (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
            (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history)
          targetPair ∧
        ActiveLeft targetPair component := by
  let target := DDC.History.relabel
    (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
    (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history
  let targetProjection := projectParallel target
  have flattened := flattenProjection_relabel_assoc history
  have secondEqual := congrArg TripleProjection.second flattened
  have activeEqual := congrArg TripleProjection.active flattened
  simp only [flattenLeftProjection, outerActive.1, outerActive.2.1,
    innerActive.1, innerActive.2.1, Option.map_some, Option.bind_some]
      at secondEqual activeEqual
  change (flattenRightProjection targetProjection).second =
    some component at secondEqual
  change (flattenRightProjection targetProjection).active =
    some .second at activeEqual
  cases rightEqual : targetProjection.right with
  | none => simp [flattenRightProjection, rightEqual] at secondEqual
  | some targetPair =>
      have nestedLeft : (projectParallel targetPair).left =
          some component := by
        simpa [flattenRightProjection, rightEqual] using secondEqual
      have targetActive : targetProjection.active = some .right := by
        cases active : targetProjection.active with
        | none => simp [flattenRightProjection, active] at activeEqual
        | some side =>
            cases side with
            | left => simp [flattenRightProjection, active] at activeEqual
            | right => rfl
      have nestedActive : (projectParallel targetPair).active =
          some .left := by
        cases active : (projectParallel targetPair).active with
        | none =>
            simp [flattenRightProjection, targetActive, rightEqual, active]
              at activeEqual
        | some side =>
            cases side with
            | left => rfl
            | right =>
                simp [flattenRightProjection, targetActive, rightEqual,
                  active] at activeEqual
      exact ⟨targetPair,
        activeRight_of_projection targetActive rightEqual,
        activeLeft_of_projection nestedActive nestedLeft⟩

private theorem activeThird_relabel_assoc
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    {history : DDC.History
      (Interface.parallel (Interface.parallel A₁ A₂) A₃)
      (Interface.parallel (Interface.parallel B₁ B₂) B₃)}
    {component : DDC.History A₃ B₃}
    (outerActive : ActiveRight history component) :
    ∃ targetPair : DDC.History (Interface.parallel A₂ A₃)
        (Interface.parallel B₂ B₃),
      ActiveRight
          (DDC.History.relabel
            (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
            (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history)
          targetPair ∧
        ActiveRight targetPair component := by
  let target := DDC.History.relabel
    (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
    (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history
  let targetProjection := projectParallel target
  have flattened := flattenProjection_relabel_assoc history
  have thirdEqual := congrArg TripleProjection.third flattened
  have activeEqual := congrArg TripleProjection.active flattened
  simp only [flattenLeftProjection, outerActive.1, outerActive.2.1]
      at thirdEqual activeEqual
  change (flattenRightProjection targetProjection).third =
    some component at thirdEqual
  change (flattenRightProjection targetProjection).active =
    some .third at activeEqual
  cases rightEqual : targetProjection.right with
  | none => simp [flattenRightProjection, rightEqual] at thirdEqual
  | some targetPair =>
      have nestedRight : (projectParallel targetPair).right =
          some component := by
        simpa [flattenRightProjection, rightEqual] using thirdEqual
      have targetActive : targetProjection.active = some .right := by
        cases active : targetProjection.active with
        | none => simp [flattenRightProjection, active] at activeEqual
        | some side =>
            cases side with
            | left => simp [flattenRightProjection, active] at activeEqual
            | right => rfl
      have nestedActive : (projectParallel targetPair).active =
          some .right := by
        cases active : (projectParallel targetPair).active with
        | none =>
            simp [flattenRightProjection, targetActive, rightEqual, active]
              at activeEqual
        | some side =>
            cases side with
            | left =>
                simp [flattenRightProjection, targetActive, rightEqual,
                  active] at activeEqual
            | right => rfl
      exact ⟨targetPair,
        activeRight_of_projection targetActive rightEqual,
        activeRight_of_projection nestedActive nestedRight⟩

private theorem relabelResponse_tagFirst_assoc
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    {history : DDC.History
      (Interface.parallel (Interface.parallel A₁ A₂) A₃)
      (Interface.parallel (Interface.parallel B₁ B₂) B₃)}
    {pairHistory : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {component : DDC.History A₁ B₁}
    (outerActive : ActiveLeft history pairHistory)
    (innerActive : ActiveLeft pairHistory component)
    (response : DDC.Response component) :
    relabelResponse
        (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
        (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history
        (tagLeftResponse history pairHistory outerActive.2.2
          (tagLeftResponse pairHistory component innerActive.2.2 response)) =
      tagLeftResponse
        (DDC.History.relabel
          (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
          (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history)
        component
        (activeFirst_relabel_assoc outerActive innerActive).2.2 response := by
  cases response with
  | inl query => rfl
  | inr reply =>
      let targetHistory := DDC.History.relabel
        (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
        (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history
      let innerTagged := cast
        (congrArg (fun selected =>
          Option ((Interface.parallel A₁ A₂).answer selected))
          innerActive.2.2.symm) reply
      let sourceTagged := cast
        (congrArg (fun selected => Option
          ((Interface.parallel (Interface.parallel A₁ A₂) A₃).answer
            selected)) outerActive.2.2.symm) innerTagged
      let targetEqual :=
        (activeFirst_relabel_assoc outerActive innerActive).2.2
      let targetTagged := cast
        (congrArg (fun selected => Option
          ((Interface.parallel A₁ (Interface.parallel A₂ A₃)).answer
            selected)) targetEqual.symm) reply
      simp only [tagLeftResponse, relabelResponse_outer]
      have innerPacked := packed_tagLeft_general pairHistory component
        innerActive.2.2 reply
      let embedFirst : DDC.History.InnerReply (Interface.parallel A₁ A₂) →
          DDC.History.InnerReply
            (Interface.parallel (Interface.parallel A₁ A₂) A₃) :=
        fun packed => ⟨Sum.inl packed.1, packed.2⟩
      have embeddedInner := congrArg embedFirst innerPacked
      have packedEqual :
          (⟨targetHistory.lastOuter,
            relabelOuterReply
              (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
              (Interface.Equiv.parallelAssoc B₁ B₂ B₃)
              history sourceTagged⟩ :
            DDC.History.InnerReply
              (Interface.parallel A₁ (Interface.parallel A₂ A₃))) =
          ⟨targetHistory.lastOuter, targetTagged⟩ := by
        calc
          _ = (Interface.Equiv.parallelAssoc A₁ A₂ A₃).innerReply
                ⟨history.lastOuter, sourceTagged⟩ :=
            packed_outer_relabel
              (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
              (Interface.Equiv.parallelAssoc B₁ B₂ B₃)
              history sourceTagged
          _ = (Interface.Equiv.parallelAssoc A₁ A₂ A₃).innerReply
                ⟨Sum.inl pairHistory.lastOuter, innerTagged⟩ := by
            exact congrArg
              (Interface.Equiv.parallelAssoc A₁ A₂ A₃).innerReply
              (packed_tagLeft_general history pairHistory outerActive.2.2
                innerTagged)
          _ = (Interface.Equiv.parallelAssoc A₁ A₂ A₃).innerReply
                (embedFirst ⟨Sum.inl component.lastOuter, reply⟩) := by
            exact congrArg
              (Interface.Equiv.parallelAssoc A₁ A₂ A₃).innerReply
              embeddedInner
          _ = ⟨Sum.inl component.lastOuter, reply⟩ := by
            cases reply <;> rfl
          _ = ⟨targetHistory.lastOuter, targetTagged⟩ :=
            (packed_tagLeft_general targetHistory component targetEqual
              reply).symm
      exact congrArg Sum.inr
        (eq_of_heq (Sigma.mk.inj_iff.mp packedEqual).2)

private theorem relabelResponse_tagSecond_assoc
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    {history : DDC.History
      (Interface.parallel (Interface.parallel A₁ A₂) A₃)
      (Interface.parallel (Interface.parallel B₁ B₂) B₃)}
    {pairHistory : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    {component : DDC.History A₂ B₂}
    (outerActive : ActiveLeft history pairHistory)
    (innerActive : ActiveRight pairHistory component)
    (response : DDC.Response component) :
    let targetWitness := activeSecond_relabel_assoc outerActive innerActive
    let targetPair := targetWitness.choose
    let targetOuter := targetWitness.choose_spec.1
    let targetInner := targetWitness.choose_spec.2
    relabelResponse
        (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
        (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history
        (tagLeftResponse history pairHistory outerActive.2.2
          (tagRightResponse pairHistory component innerActive.2.2 response)) =
      tagRightResponse
        (DDC.History.relabel
          (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
          (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history)
        targetPair targetOuter.2.2
        (tagLeftResponse targetPair component targetInner.2.2 response) := by
  dsimp only
  let targetWitness := activeSecond_relabel_assoc outerActive innerActive
  let targetPair := targetWitness.choose
  let targetOuter := targetWitness.choose_spec.1
  let targetInner := targetWitness.choose_spec.2
  change relabelResponse _ _ history
      (tagLeftResponse history pairHistory outerActive.2.2
        (tagRightResponse pairHistory component innerActive.2.2 response)) =
    tagRightResponse _ targetPair targetOuter.2.2
      (tagLeftResponse targetPair component targetInner.2.2 response)
  cases response with
  | inl query => rfl
  | inr reply =>
      let targetHistory := DDC.History.relabel
        (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
        (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history
      let innerTagged := cast
        (congrArg (fun selected =>
          Option ((Interface.parallel A₁ A₂).answer selected))
          innerActive.2.2.symm) reply
      let sourceTagged := cast
        (congrArg (fun selected => Option
          ((Interface.parallel (Interface.parallel A₁ A₂) A₃).answer
            selected)) outerActive.2.2.symm) innerTagged
      let targetInnerTagged := cast
        (congrArg (fun selected => Option
          ((Interface.parallel A₂ A₃).answer selected))
          targetInner.2.2.symm) reply
      let targetTagged := cast
        (congrArg (fun selected => Option
          ((Interface.parallel A₁ (Interface.parallel A₂ A₃)).answer
            selected)) targetOuter.2.2.symm) targetInnerTagged
      simp only [tagLeftResponse, tagRightResponse, relabelResponse_outer]
      let embedSource : DDC.History.InnerReply (Interface.parallel A₁ A₂) →
          DDC.History.InnerReply
            (Interface.parallel (Interface.parallel A₁ A₂) A₃) :=
        fun packed => ⟨Sum.inl packed.1, packed.2⟩
      have sourceInnerPacked := packed_tagRight_general pairHistory component
        innerActive.2.2 reply
      have embeddedSource := congrArg embedSource sourceInnerPacked
      let embedTarget : DDC.History.InnerReply (Interface.parallel A₂ A₃) →
          DDC.History.InnerReply
            (Interface.parallel A₁ (Interface.parallel A₂ A₃)) :=
        fun packed => ⟨Sum.inr packed.1, packed.2⟩
      have targetInnerPacked := packed_tagLeft_general targetPair component
        targetInner.2.2 reply
      have embeddedTarget := congrArg embedTarget targetInnerPacked
      have packedEqual :
          (⟨targetHistory.lastOuter,
            relabelOuterReply
              (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
              (Interface.Equiv.parallelAssoc B₁ B₂ B₃)
              history sourceTagged⟩ :
            DDC.History.InnerReply
              (Interface.parallel A₁ (Interface.parallel A₂ A₃))) =
          ⟨targetHistory.lastOuter, targetTagged⟩ := by
        calc
          _ = (Interface.Equiv.parallelAssoc A₁ A₂ A₃).innerReply
                ⟨history.lastOuter, sourceTagged⟩ :=
            packed_outer_relabel
              (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
              (Interface.Equiv.parallelAssoc B₁ B₂ B₃)
              history sourceTagged
          _ = (Interface.Equiv.parallelAssoc A₁ A₂ A₃).innerReply
                ⟨Sum.inl pairHistory.lastOuter, innerTagged⟩ := by
            exact congrArg
              (Interface.Equiv.parallelAssoc A₁ A₂ A₃).innerReply
              (packed_tagLeft_general history pairHistory outerActive.2.2
                innerTagged)
          _ = (Interface.Equiv.parallelAssoc A₁ A₂ A₃).innerReply
                (embedSource ⟨Sum.inr component.lastOuter, reply⟩) := by
            exact congrArg
              (Interface.Equiv.parallelAssoc A₁ A₂ A₃).innerReply
              embeddedSource
          _ = ⟨Sum.inr (Sum.inl component.lastOuter), reply⟩ := by
            cases reply <;> rfl
          _ = embedTarget ⟨Sum.inl component.lastOuter, reply⟩ := rfl
          _ = embedTarget ⟨targetPair.lastOuter, targetInnerTagged⟩ :=
            embeddedTarget.symm
          _ = ⟨Sum.inr targetPair.lastOuter, targetInnerTagged⟩ := rfl
          _ = ⟨targetHistory.lastOuter, targetTagged⟩ :=
            (packed_tagRight_general targetHistory targetPair targetOuter.2.2
              targetInnerTagged).symm
      exact congrArg Sum.inr
        (eq_of_heq (Sigma.mk.inj_iff.mp packedEqual).2)

private theorem relabelResponse_tagThird_assoc
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    {history : DDC.History
      (Interface.parallel (Interface.parallel A₁ A₂) A₃)
      (Interface.parallel (Interface.parallel B₁ B₂) B₃)}
    {component : DDC.History A₃ B₃}
    (outerActive : ActiveRight history component)

    (response : DDC.Response component) :
    let targetWitness := activeThird_relabel_assoc outerActive
    let targetPair := targetWitness.choose
    let targetOuter := targetWitness.choose_spec.1
    let targetInner := targetWitness.choose_spec.2
    relabelResponse
        (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
        (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history
        (tagRightResponse history component outerActive.2.2 response) =
      tagRightResponse
        (DDC.History.relabel
          (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
          (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history)
        targetPair targetOuter.2.2
        (tagRightResponse targetPair component targetInner.2.2 response) := by
  dsimp only
  let targetWitness := activeThird_relabel_assoc outerActive
  let targetPair := targetWitness.choose
  let targetOuter := targetWitness.choose_spec.1
  let targetInner := targetWitness.choose_spec.2
  change relabelResponse _ _ history
      (tagRightResponse history component outerActive.2.2 response) =
    tagRightResponse _ targetPair targetOuter.2.2
      (tagRightResponse targetPair component targetInner.2.2 response)
  cases response with
  | inl query => rfl
  | inr reply =>
      let targetHistory := DDC.History.relabel
        (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
        (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history
      let sourceTagged := cast
        (congrArg (fun selected => Option
          ((Interface.parallel (Interface.parallel A₁ A₂) A₃).answer
            selected)) outerActive.2.2.symm) reply
      let targetInnerTagged := cast
        (congrArg (fun selected => Option
          ((Interface.parallel A₂ A₃).answer selected))
          targetInner.2.2.symm) reply
      let targetTagged := cast
        (congrArg (fun selected => Option
          ((Interface.parallel A₁ (Interface.parallel A₂ A₃)).answer
            selected)) targetOuter.2.2.symm) targetInnerTagged
      simp only [tagRightResponse, relabelResponse_outer]
      let embedTarget : DDC.History.InnerReply (Interface.parallel A₂ A₃) →
          DDC.History.InnerReply
            (Interface.parallel A₁ (Interface.parallel A₂ A₃)) :=
        fun packed => ⟨Sum.inr packed.1, packed.2⟩
      have targetInnerPacked := packed_tagRight_general targetPair component
        targetInner.2.2 reply
      have embeddedTarget := congrArg embedTarget targetInnerPacked
      have packedEqual :
          (⟨targetHistory.lastOuter,
            relabelOuterReply
              (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
              (Interface.Equiv.parallelAssoc B₁ B₂ B₃)
              history sourceTagged⟩ :
            DDC.History.InnerReply
              (Interface.parallel A₁ (Interface.parallel A₂ A₃))) =
          ⟨targetHistory.lastOuter, targetTagged⟩ := by
        calc
          _ = (Interface.Equiv.parallelAssoc A₁ A₂ A₃).innerReply
                ⟨history.lastOuter, sourceTagged⟩ :=
            packed_outer_relabel
              (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
              (Interface.Equiv.parallelAssoc B₁ B₂ B₃)
              history sourceTagged
          _ = (Interface.Equiv.parallelAssoc A₁ A₂ A₃).innerReply
                ⟨Sum.inr component.lastOuter, reply⟩ := by
            exact congrArg
              (Interface.Equiv.parallelAssoc A₁ A₂ A₃).innerReply
              (packed_tagRight_general history component outerActive.2.2
                reply)
          _ = ⟨Sum.inr (Sum.inr component.lastOuter), reply⟩ := by
            cases reply <;> rfl
          _ = embedTarget ⟨Sum.inr component.lastOuter, reply⟩ := rfl
          _ = embedTarget ⟨targetPair.lastOuter, targetInnerTagged⟩ :=
            embeddedTarget.symm
          _ = ⟨Sum.inr targetPair.lastOuter, targetInnerTagged⟩ := rfl
          _ = ⟨targetHistory.lastOuter, targetTagged⟩ :=
            (packed_tagRight_general targetHistory targetPair targetOuter.2.2
              targetInnerTagged).symm
      exact congrArg Sum.inr
        (eq_of_heq (Sigma.mk.inj_iff.mp packedEqual).2)

private theorem parallelRaw_assoc_mem
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    (first : DDC A₁ B₁) (second : DDC A₂ B₂)
    (third : DDC A₃ B₃)
    (history : DDC.History
      (Interface.parallel (Interface.parallel A₁ A₂) A₃)
      (Interface.parallel (Interface.parallel B₁ B₂) B₃))
    (sourceAdmissible : DDC.Raw.Admissible
      (parallelRaw (parallel first second) third) history)
    (targetAdmissible : DDC.Raw.Admissible
      (parallelRaw first (parallel second third))
      (DDC.History.relabel
        (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
        (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history))
    (response : DDC.Response history)
    (responds : response ∈
      parallelRaw (parallel first second) third history) :
    relabelResponse
        (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
        (Interface.Equiv.parallelAssoc B₁ B₂ B₃)
        history response ∈
      parallelRaw first (parallel second third)
        (DDC.History.relabel
          (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
          (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history) := by
  have sourceValid := parallelRaw_admissible_projection
    (parallel first second) third sourceAdmissible
  rcases parallelRaw_admissible_active (parallel first second) third
      sourceAdmissible with
    ⟨pairHistory, outerActive⟩ | ⟨component, outerActive⟩
  · rcases (mem_parallelRaw_left_iff (parallel first second) third history
        pairHistory outerActive response).mp responds with
      ⟨pairResponse, pairResponds, pairTagged⟩
    have pairCanonicalAdmissible :=
      sourceValid.leftAdmissible pairHistory outerActive.2.1
    have pairRawAdmissible : DDC.Raw.Admissible
        (parallelRaw first second) pairHistory := by
      exact (DDC.Raw.admissible_canonicalize_iff
        (parallelRaw first second) pairHistory).mp pairCanonicalAdmissible
    have pairRawResponds :=
      (mem_parallel_iff first second pairHistory pairResponse).mp
        pairResponds |>.2
    rcases parallelRaw_admissible_active first second pairRawAdmissible with
      ⟨component, innerActive⟩ | ⟨component, innerActive⟩
    · rcases (mem_parallelRaw_left_iff first second pairHistory component
          innerActive pairResponse).mp pairRawResponds with
        ⟨componentResponse, componentResponds, componentTagged⟩
      subst pairResponse
      subst response
      have targetActive := activeFirst_relabel_assoc outerActive innerActive
      apply (mem_parallelRaw_left_iff first (parallel second third)
        _ component targetActive _).mpr
      exact ⟨componentResponse, componentResponds,
        (relabelResponse_tagFirst_assoc outerActive innerActive
          componentResponse).symm⟩
    · rcases (mem_parallelRaw_right_iff first second pairHistory component
          innerActive pairResponse).mp pairRawResponds with
        ⟨componentResponse, componentResponds, componentTagged⟩
      subst pairResponse
      subst response
      let targetWitness := activeSecond_relabel_assoc outerActive innerActive
      let targetPair := targetWitness.choose
      let targetOuter := targetWitness.choose_spec.1
      let targetInner := targetWitness.choose_spec.2
      have targetValid := parallelRaw_admissible_projection
        first (parallel second third) targetAdmissible
      have targetPairCanonicalAdmissible :=
        targetValid.rightAdmissible targetPair targetOuter.2.1
      have targetPairRawAdmissible : DDC.Raw.Admissible
          (parallelRaw second third) targetPair := by
        exact (DDC.Raw.admissible_canonicalize_iff
          (parallelRaw second third) targetPair).mp
            targetPairCanonicalAdmissible
      have targetPairRawResponds :
          tagLeftResponse targetPair component targetInner.2.2
              componentResponse ∈
            parallelRaw second third targetPair := by
        apply (mem_parallelRaw_left_iff second third targetPair component
          targetInner _).mpr
        exact ⟨componentResponse, componentResponds, rfl⟩
      have targetPairResponds :
          tagLeftResponse targetPair component targetInner.2.2
              componentResponse ∈
            parallel second third targetPair :=
        (mem_parallel_iff second third targetPair _).mpr
          ⟨targetPairRawAdmissible, targetPairRawResponds⟩
      apply (mem_parallelRaw_right_iff first (parallel second third)
        _ targetPair targetOuter _).mpr
      exact ⟨_, targetPairResponds,
        (relabelResponse_tagSecond_assoc outerActive innerActive
          componentResponse).symm⟩
  · rcases (mem_parallelRaw_right_iff (parallel first second) third history
        component outerActive response).mp responds with
      ⟨componentResponse, componentResponds, componentTagged⟩
    subst response
    let targetWitness := activeThird_relabel_assoc outerActive
    let targetPair := targetWitness.choose
    let targetOuter := targetWitness.choose_spec.1
    let targetInner := targetWitness.choose_spec.2
    have targetValid := parallelRaw_admissible_projection
      first (parallel second third) targetAdmissible
    have targetPairCanonicalAdmissible :=
      targetValid.rightAdmissible targetPair targetOuter.2.1
    have targetPairRawAdmissible : DDC.Raw.Admissible
        (parallelRaw second third) targetPair := by
      exact (DDC.Raw.admissible_canonicalize_iff
        (parallelRaw second third) targetPair).mp
          targetPairCanonicalAdmissible
    have targetPairRawResponds :
        tagRightResponse targetPair component targetInner.2.2
            componentResponse ∈
          parallelRaw second third targetPair := by
      apply (mem_parallelRaw_right_iff second third targetPair component
        targetInner _).mpr
      exact ⟨componentResponse, componentResponds, rfl⟩
    have targetPairResponds :
        tagRightResponse targetPair component targetInner.2.2
            componentResponse ∈
          parallel second third targetPair :=
      (mem_parallel_iff second third targetPair _).mpr
        ⟨targetPairRawAdmissible, targetPairRawResponds⟩
    apply (mem_parallelRaw_right_iff first (parallel second third)
      _ targetPair targetOuter _).mpr
    exact ⟨_, targetPairResponds,
      (relabelResponse_tagThird_assoc outerActive componentResponse).symm⟩

private theorem parallelRaw_assoc_admissible
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    (first : DDC A₁ B₁) (second : DDC A₂ B₂)
    (third : DDC A₃ B₃)
    {history : DDC.History
      (Interface.parallel (Interface.parallel A₁ A₂) A₃)
      (Interface.parallel (Interface.parallel B₁ B₂) B₃)}
    (admissible : DDC.Raw.Admissible
      (parallelRaw (parallel first second) third) history) :
    DDC.Raw.Admissible (parallelRaw first (parallel second third))
      (DDC.History.relabel
        (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
        (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history) := by
  induction admissible with
  | start query =>
      exact @DDC.Raw.Admissible.start
        (Interface.parallel A₁ (Interface.parallel A₂ A₃))
        (Interface.parallel B₁ (Interface.parallel B₂ B₃))
        (parallelRaw first (parallel second third))
        ((Interface.Equiv.parallelAssoc A₁ A₂ A₃).queries query)
  | @afterInner previous query prior responds reply inductionHypothesis =>
      have mapped := parallelRaw_assoc_mem first second third previous prior
        inductionHypothesis (Sum.inl query) responds
      have next := @DDC.Raw.Admissible.afterInner
        (Interface.parallel A₁ (Interface.parallel A₂ A₃))
        (Interface.parallel B₁ (Interface.parallel B₂ B₃))
        (parallelRaw first (parallel second third))
        (DDC.History.relabel
          (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
          (Interface.Equiv.parallelAssoc B₁ B₂ B₃) previous)
        ((Interface.Equiv.parallelAssoc B₁ B₂ B₃).queries query)
        inductionHypothesis mapped
        (reply.map
          ((Interface.Equiv.parallelAssoc B₁ B₂ B₃).answers query))
      simpa only [DDC.History.relabel_snocInner] using next
  | @afterOuter previous prior reply responds query inductionHypothesis =>
      have mapped := parallelRaw_assoc_mem first second third previous prior
        inductionHypothesis (Sum.inr reply) responds
      have next := @DDC.Raw.Admissible.afterOuter
        (Interface.parallel A₁ (Interface.parallel A₂ A₃))
        (Interface.parallel B₁ (Interface.parallel B₂ B₃))
        (parallelRaw first (parallel second third))
        (DDC.History.relabel
          (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
          (Interface.Equiv.parallelAssoc B₁ B₂ B₃) previous)
        inductionHypothesis
        (relabelOuterReply
          (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
          (Interface.Equiv.parallelAssoc B₁ B₂ B₃)
          previous reply)
        mapped
        ((Interface.Equiv.parallelAssoc A₁ A₂ A₃).queries query)
      simpa only [DDC.History.relabel_snocOuter] using next

private theorem parallel_assoc_mem
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    (first : DDC A₁ B₁) (second : DDC A₂ B₂)
    (third : DDC A₃ B₃)
    (history : DDC.History
      (Interface.parallel (Interface.parallel A₁ A₂) A₃)
      (Interface.parallel (Interface.parallel B₁ B₂) B₃))
    (response : DDC.Response history)
    (responds : response ∈ parallel (parallel first second) third history) :
    relabelResponse
        (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
        (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history response ∈
      parallel first (parallel second third)
        (DDC.History.relabel
          (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
          (Interface.Equiv.parallelAssoc B₁ B₂ B₃) history) := by
  obtain ⟨admissible, rawResponds⟩ :=
    (mem_parallel_iff (parallel first second) third history response).mp
      responds
  have mappedAdmissible := parallelRaw_assoc_admissible first second third
    admissible
  apply (mem_parallel_iff first (parallel second third) _ _).mpr
  exact ⟨mappedAdmissible,
    parallelRaw_assoc_mem first second third history admissible
      mappedAdmissible response rawResponds⟩

private theorem eq_of_graph_subset_assoc
    {A B : Interface.{u, v}} (left right : DDC A B)
    (subset : ∀ history response,
      response ∈ right history → response ∈ left history) :
    left = right := by
  have admissible : ∀ {history},
      DDC.Raw.Admissible left.toFun history →
        DDC.Raw.Admissible right.toFun history := by
    intro history valid
    induction valid with
    | start query => exact .start query
    | @afterInner previous query prior leftResponds reply ih =>
        have rightResponds := right.response_mem previous ih
        have responseEqual : right.response previous ih = Sum.inl query :=
          Part.mem_unique (subset previous _ rightResponds) leftResponds
        exact .afterInner ih (responseEqual ▸ rightResponds) reply
    | @afterOuter previous prior reply leftResponds query ih =>
        have rightResponds := right.response_mem previous ih
        have responseEqual : right.response previous ih = Sum.inr reply :=
          Part.mem_unique (subset previous _ rightResponds) leftResponds
        exact .afterOuter ih (responseEqual ▸ rightResponds) query
  apply DDC.ext
  intro history response
  constructor
  · intro leftResponds
    have rightAdmissible := admissible
      ((left.exactDomain history).mp leftResponds.1)
    have rightResponds := right.response_mem history rightAdmissible
    have responseEqual : right.response history rightAdmissible = response :=
      Part.mem_unique (subset history _ rightResponds) leftResponds
    exact responseEqual ▸ rightResponds
  · exact subset history response

private def responseRelabelAssoc
    {A B C D : Interface.{u, v}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (targetHistory : DDC.History C D) :
    DDC.Response
        ((DDC.History.relabelEquiv outer inner).symm targetHistory) ≃
      DDC.Response targetHistory :=
  let histories := DDC.History.relabelEquiv outer inner
  let sourceHistory := histories.symm targetHistory
  (relabelResponse outer inner sourceHistory).trans
    (_root_.Equiv.cast (congrArg (fun history => DDC.Response history)
      (histories.apply_symm_apply targetHistory)))

private theorem transport_mem_assoc
    {A B : Interface.{u, v}} (converter : DDC A B)
    {left right : DDC.History A B} (equal : left = right)
    (response : DDC.Response left)
    (responds : response ∈ converter left) :
    cast (congrArg (fun history => DDC.Response history) equal) response ∈
      converter right := by
  cases equal
  exact responds

/-- Reassociation of ordered interfaces carries the left-nested parallel
converter graph to the right-nested parallel converter graph. -/
theorem relabel_parallel_assoc_eq
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    (first : DDC A₁ B₁) (second : DDC A₂ B₂)
    (third : DDC A₃ B₃) :
    relabel
        (Interface.Equiv.parallelAssoc A₁ A₂ A₃)
        (Interface.Equiv.parallelAssoc B₁ B₂ B₃)
        (parallel (parallel first second) third) =
      parallel first (parallel second third) := by
  symm
  apply eq_of_graph_subset_assoc
  intro targetHistory targetResponse responds
  let outer := Interface.Equiv.parallelAssoc A₁ A₂ A₃
  let inner := Interface.Equiv.parallelAssoc B₁ B₂ B₃
  have sourceResponds :=
    (mem_relabel_iff_symm outer inner
      (parallel (parallel first second) third)
      targetHistory targetResponse).mp responds
  let histories := DDC.History.relabelEquiv outer inner
  let sourceHistory := histories.symm targetHistory
  let responses := responseRelabelAssoc outer inner targetHistory
  let sourceResponse := responses.symm targetResponse
  have mapped := parallel_assoc_mem first second third sourceHistory
    sourceResponse sourceResponds
  have historyEqual : DDC.History.relabel outer inner sourceHistory =
      targetHistory := histories.apply_symm_apply targetHistory
  have responseEqual :
      cast (congrArg (fun selected => DDC.Response selected) historyEqual)
          (relabelResponse outer inner sourceHistory sourceResponse) =
        targetResponse := responses.apply_symm_apply targetResponse
  have transported := transport_mem_assoc
    (parallel first (parallel second third)) historyEqual _ mapped
  exact responseEqual ▸ transported


end DDC

/-! ## DDC empty-interface routers -/





namespace DDC

@[simp]
private theorem parallelEmptyLeft_symm_queries
    (A : Interface.{u, v}) (query : A.query) :
    (Interface.Equiv.parallelEmptyLeft A).symm.queries query = Sum.inr query :=
  rfl

@[simp]
private theorem parallelEmptyLeft_symm_answers
    (A : Interface.{u, v}) (query : A.query) (answer : A.answer query) :
    (Interface.Equiv.parallelEmptyLeft A).symm.answers query answer = answer := by
  change (_root_.Equiv.refl (A.answer query)).symm answer = answer
  rfl

private theorem parallelRaw_empty_left_admissible
    {A B : Interface.{u, v}} (converter : DDC A B)
    {history : DDC.History A B}
    (admissible : DDC.Raw.Admissible converter.toFun history) :
    let outer := Interface.Equiv.parallelEmptyLeft A
    let inner := Interface.Equiv.parallelEmptyLeft B
    let embedded := DDC.History.relabel outer.symm inner.symm history
    DDC.Raw.Admissible
        (parallelRaw (forwarding Interface.empty) converter) embedded ∧
      ActiveRight embedded history := by
  induction admissible with
  | start query =>
      refine ⟨?_, ?_⟩
      · exact @DDC.Raw.Admissible.start
          (Interface.parallel Interface.empty A)
          (Interface.parallel Interface.empty B)
          (parallelRaw (forwarding Interface.empty) converter)
          (Sum.inr query)
      · exact ⟨rfl, rfl, rfl⟩
  | @afterInner previous query prior responds reply inductionHypothesis =>
      let outer := Interface.Equiv.parallelEmptyLeft A
      let inner := Interface.Equiv.parallelEmptyLeft B
      let embedded := DDC.History.relabel outer.symm inner.symm previous
      have tagged : Sum.inl (Sum.inr query) ∈
          parallelRaw (forwarding Interface.empty) converter embedded := by
        apply (mem_parallelRaw_right_iff (forwarding Interface.empty) converter
          embedded previous inductionHypothesis.2 _).mpr
        exact ⟨Sum.inl query, responds, rfl⟩
      let embeddedAnswer :=
        (Interface.Equiv.parallelEmptyLeft B).symm.answers query
      let embeddedReply := reply.map embeddedAnswer
      have next : DDC.Raw.Admissible
          (parallelRaw (forwarding Interface.empty) converter)
          (embedded.snocInner (Sum.inr query) embeddedReply) :=
        .afterInner inductionHypothesis.1 tagged embeddedReply
      have embeddedReply_eq : embeddedReply = reply := by
        cases reply with
        | none => rfl
        | some answer =>
            change some (embeddedAnswer answer) = some answer
            rw [parallelEmptyLeft_symm_answers]
            rfl
      refine ⟨?_, ?_⟩
      · have relabelAfter :
            DDC.History.relabel outer.symm inner.symm
                (previous.snocInner query reply) =
              embedded.snocInner (Sum.inr query) embeddedReply := by
          rw [DDC.History.relabel_snocInner]
          rfl
        exact relabelAfter.symm ▸ next
      · refine ⟨?_, ?_, ?_⟩
        · simp only [DDC.History.relabel_snocInner,
            parallelEmptyLeft_symm_queries]
          rw [
            projectParallel_snocInner_right]
          simpa [extendParallelProjection] using inductionHypothesis.2.1
        · simp only [DDC.History.relabel_snocInner,
            parallelEmptyLeft_symm_queries]
          rw [
            projectParallel_snocInner_right]
          simp only [extendParallelProjection, inductionHypothesis.2.1,
            inductionHypothesis.2.2.1, Option.map_some]
          exact congrArg (fun selected => some (previous.snocInner query selected))
            embeddedReply_eq
        · simp only [DDC.History.relabel_snocInner,
            parallelEmptyLeft_symm_queries]
          rw [DDC.History.lastOuter_snocInner,
            DDC.History.lastOuter_snocInner]
          exact inductionHypothesis.2.2.2
  | @afterOuter previous prior reply responds query inductionHypothesis =>
      let outer := Interface.Equiv.parallelEmptyLeft A
      let inner := Interface.Equiv.parallelEmptyLeft B
      let embedded := DDC.History.relabel outer.symm inner.symm previous
      let embeddedReply : Option
          ((Interface.parallel Interface.empty A).answer embedded.lastOuter) :=
        cast (congrArg (fun selected => Option
          ((Interface.parallel Interface.empty A).answer selected))
          inductionHypothesis.2.2.2.symm) reply
      have tagged : Sum.inr embeddedReply ∈
          parallelRaw (forwarding Interface.empty) converter embedded := by
        apply (mem_parallelRaw_right_iff (forwarding Interface.empty) converter
          embedded previous inductionHypothesis.2 _).mpr
        exact ⟨Sum.inr reply, responds, rfl⟩
      have next : DDC.Raw.Admissible
          (parallelRaw (forwarding Interface.empty) converter)
          (embedded.snocOuter (Sum.inr query)) :=
        .afterOuter inductionHypothesis.1 tagged (Sum.inr query)
      refine ⟨?_, ?_⟩
      · simpa only [outer, inner, embedded,
          DDC.History.relabel_snocOuter,
          parallelEmptyLeft_symm_queries] using next
      · refine ⟨?_, ?_, ?_⟩
        · simp only [DDC.History.relabel_snocOuter,
            parallelEmptyLeft_symm_queries]
          rw [
            projectParallel_snocOuter_right]
          rfl
        · simp only [DDC.History.relabel_snocOuter,
            parallelEmptyLeft_symm_queries]
          rw [
            projectParallel_snocOuter_right]
          simp only [extendParallelProjection, inductionHypothesis.2.2.1,
            appendOuter]
        · rw [DDC.History.relabel_snocOuter,
            DDC.History.lastOuter_snocOuter,
            DDC.History.lastOuter_snocOuter]
          exact parallelEmptyLeft_symm_queries A query

private theorem transport_mem_empty
    {A B : Interface.{u, v}} (converter : DDC A B)
    {left right : DDC.History A B} (equal : left = right)
    (response : DDC.Response left)
    (responds : response ∈ converter left) :
    cast (congrArg (fun history => DDC.Response history) equal) response ∈
      converter right := by
  cases equal
  exact responds

private theorem cast_converterResponse_inner_empty
    {A B : Interface.{u, v}}
    {left right : DDC.History A B} (equal : left = right)
    (query : B.query) :
    cast (congrArg (fun history => DDC.Response history) equal)
        (Sum.inl query) =
      (Sum.inl query : DDC.Response right) := by
  cases equal
  rfl

private theorem cast_converterResponse_outer_empty
    {A B : Interface.{u, v}}
    {left right : DDC.History A B} (equal : left = right)
    (reply : Option (A.answer left.lastOuter)) :
    cast (congrArg (fun history => DDC.Response history) equal)
        (Sum.inr reply) =
      Sum.inr (cast (congrArg
        (fun history => Option (A.answer history.lastOuter)) equal) reply) := by
  cases equal
  rfl

private theorem pack_cast_outerReply_empty
    {A B : Interface.{u, v}}
    {left right : DDC.History A B} (equal : left = right)
    (reply : Option (A.answer left.lastOuter)) :
    (⟨right.lastOuter,
        cast (congrArg
          (fun history => Option (A.answer history.lastOuter)) equal) reply⟩ :
        DDC.History.InnerReply A) =
      ⟨left.lastOuter, reply⟩ := by
  cases equal
  rfl

private theorem eq_of_graph_subset_empty
    {A B : Interface.{u, v}} (left right : DDC A B)
    (subset : ∀ history response,
      response ∈ right history → response ∈ left history) :
    left = right := by
  have admissible : ∀ {history},
      DDC.Raw.Admissible left.toFun history →
        DDC.Raw.Admissible right.toFun history := by
    intro history valid
    induction valid with
    | start query => exact .start query
    | @afterInner previous query prior leftResponds reply ih =>
        have rightResponds := right.response_mem previous ih
        have responseEqual : right.response previous ih = Sum.inl query :=
          Part.mem_unique (subset previous _ rightResponds) leftResponds
        exact .afterInner ih (responseEqual ▸ rightResponds) reply
    | @afterOuter previous prior reply leftResponds query ih =>
        have rightResponds := right.response_mem previous ih
        have responseEqual : right.response previous ih = Sum.inr reply :=
          Part.mem_unique (subset previous _ rightResponds) leftResponds
        exact .afterOuter ih (responseEqual ▸ rightResponds) query
  apply DDC.ext
  intro history response
  constructor
  · intro leftResponds
    have rightAdmissible := admissible
      ((left.exactDomain history).mp leftResponds.1)
    have rightResponds := right.response_mem history rightAdmissible
    have responseEqual : right.response history rightAdmissible = response :=
      Part.mem_unique (subset history _ rightResponds) leftResponds
    exact responseEqual ▸ rightResponds
  · exact subset history response

private theorem parallel_empty_left_mem
    {A B : Interface.{u, v}} (converter : DDC A B)
    (history : DDC.History A B) (response : DDC.Response history)
    (responds : response ∈ converter history) :
    response ∈
      relabel (Interface.Equiv.parallelEmptyLeft A)
        (Interface.Equiv.parallelEmptyLeft B)
        (parallel (forwarding Interface.empty) converter) history := by
  let outer := Interface.Equiv.parallelEmptyLeft A
  let inner := Interface.Equiv.parallelEmptyLeft B
  let embedded := DDC.History.relabel outer.symm inner.symm history
  have valid := parallelRaw_empty_left_admissible converter
    ((converter.exactDomain history).mp responds.1)
  let sourceResponse := tagRightResponse embedded history valid.2.2.2 response
  have rawResponds : sourceResponse ∈
      parallelRaw (forwarding Interface.empty) converter embedded := by
    apply (mem_parallelRaw_right_iff (forwarding Interface.empty) converter
      embedded history valid.2 sourceResponse).mpr
    exact ⟨response, responds, rfl⟩
  have sourceResponds : sourceResponse ∈
      parallel (forwarding Interface.empty) converter embedded :=
    (mem_parallel_iff (forwarding Interface.empty) converter embedded
      sourceResponse).mpr ⟨valid.1, rawResponds⟩
  have mapped := mem_relabel_of_mem outer inner
    (parallel (forwarding Interface.empty) converter)
    embedded sourceResponse sourceResponds
  have historyEqual : DDC.History.relabel outer inner embedded = history := by
    calc
      DDC.History.relabel outer inner embedded =
          DDC.History.relabel (outer.symm.trans outer)
            (inner.symm.trans inner) history :=
        DDC.History.relabel_trans outer.symm inner.symm outer inner history
      _ = history := by
        rw [Interface.Equiv.symm_trans, Interface.Equiv.symm_trans]
        exact DDC.History.relabel_refl history
  have mappedResponseEqual :
      cast (congrArg (fun selected => DDC.Response selected) historyEqual)
          (relabelResponse outer inner embedded sourceResponse) = response := by
    cases response with
    | inl query =>
        simp only [sourceResponse, tagRightResponse, relabelResponse_inner]
        change cast
            (congrArg (fun selected => DDC.Response selected) historyEqual)
              (Sum.inl query) = Sum.inl query
        exact cast_converterResponse_inner_empty historyEqual query
    | inr reply =>
        simp only [sourceResponse, tagRightResponse, relabelResponse_outer]
        let sourceReply := cast
          (congrArg (fun selected => Option
            ((Interface.parallel Interface.empty A).answer selected))
            valid.2.2.2.symm) reply
        let mappedReply := relabelOuterReply outer inner embedded sourceReply
        change cast
            (congrArg (fun selected => DDC.Response selected) historyEqual)
              (Sum.inr mappedReply) = Sum.inr reply
        rw [cast_converterResponse_outer_empty historyEqual mappedReply]
        apply congrArg Sum.inr
        have taggedPacked :
            (⟨embedded.lastOuter, sourceReply⟩ :
                DDC.History.InnerReply (Interface.parallel Interface.empty A)) =
              ⟨Sum.inr history.lastOuter, reply⟩ :=
          packed_tagRight_general embedded history valid.2.2.2 reply
        have mappedPacked :
            (⟨(DDC.History.relabel outer inner embedded).lastOuter,
                mappedReply⟩ : DDC.History.InnerReply A) =
              ⟨history.lastOuter, reply⟩ := by
          calc
            _ = outer.innerReply ⟨embedded.lastOuter, sourceReply⟩ :=
              packed_outer_relabel outer inner embedded sourceReply
            _ = outer.innerReply ⟨Sum.inr history.lastOuter, reply⟩ :=
              congrArg outer.innerReply taggedPacked
            _ = ⟨history.lastOuter, reply⟩ := by
              cases reply <;> rfl
        have castPacked :
            (⟨history.lastOuter,
                cast (congrArg
                  (fun selected => Option (A.answer selected.lastOuter))
                  historyEqual) mappedReply⟩ : DDC.History.InnerReply A) =
              ⟨(DDC.History.relabel outer inner embedded).lastOuter,
                mappedReply⟩ :=
          pack_cast_outerReply_empty historyEqual mappedReply
        exact eq_of_heq (Sigma.mk.inj_iff.mp (castPacked.trans mappedPacked)).2
  have transported := transport_mem_empty
    (relabel outer inner (parallel (forwarding Interface.empty) converter))
    historyEqual _ mapped
  exact mappedResponseEqual ▸ transported

/-- Ordered parallel with the empty converter on the left is the left unit,
after the canonical query-indexed interface relabeling. -/
theorem relabel_parallel_empty_left_eq
    {A B : Interface.{u, v}} (converter : DDC A B) :
    relabel (Interface.Equiv.parallelEmptyLeft A)
        (Interface.Equiv.parallelEmptyLeft B)

        (parallel (forwarding Interface.empty) converter) = converter := by
  apply eq_of_graph_subset_empty
  exact parallel_empty_left_mem converter

@[simp]
private theorem parallelEmptyRight_symm_queries
    (A : Interface.{u, v}) (query : A.query) :
    (Interface.Equiv.parallelEmptyRight A).symm.queries query = Sum.inl query :=
  rfl

@[simp]
private theorem parallelEmptyRight_symm_answers
    (A : Interface.{u, v}) (query : A.query) (answer : A.answer query) :
    (Interface.Equiv.parallelEmptyRight A).symm.answers query answer = answer := by
  change (_root_.Equiv.refl (A.answer query)).symm answer = answer
  rfl

private theorem parallelRaw_empty_right_admissible
    {A B : Interface.{u, v}} (converter : DDC A B)
    {history : DDC.History A B}
    (admissible : DDC.Raw.Admissible converter.toFun history) :
    let outer := Interface.Equiv.parallelEmptyRight A
    let inner := Interface.Equiv.parallelEmptyRight B
    let embedded := DDC.History.relabel outer.symm inner.symm history
    DDC.Raw.Admissible
        (parallelRaw converter (forwarding Interface.empty)) embedded ∧
      ActiveLeft embedded history := by
  induction admissible with
  | start query =>
      refine ⟨?_, ?_⟩
      · exact @DDC.Raw.Admissible.start
          (Interface.parallel A Interface.empty)
          (Interface.parallel B Interface.empty)
          (parallelRaw converter (forwarding Interface.empty))
          (Sum.inl query)
      · exact ⟨rfl, rfl, rfl⟩
  | @afterInner previous query prior responds reply inductionHypothesis =>
      let outer := Interface.Equiv.parallelEmptyRight A
      let inner := Interface.Equiv.parallelEmptyRight B
      let embedded := DDC.History.relabel outer.symm inner.symm previous
      have tagged : Sum.inl (Sum.inl query) ∈
          parallelRaw converter (forwarding Interface.empty) embedded := by
        apply (mem_parallelRaw_left_iff converter (forwarding Interface.empty)
          embedded previous inductionHypothesis.2 _).mpr
        exact ⟨Sum.inl query, responds, rfl⟩
      let embeddedAnswer :=
        (Interface.Equiv.parallelEmptyRight B).symm.answers query
      let embeddedReply := reply.map embeddedAnswer
      have next : DDC.Raw.Admissible
          (parallelRaw converter (forwarding Interface.empty))
          (embedded.snocInner (Sum.inl query) embeddedReply) :=
        .afterInner inductionHypothesis.1 tagged embeddedReply
      have embeddedReply_eq : embeddedReply = reply := by
        cases reply with
        | none => rfl
        | some answer =>
            change some (embeddedAnswer answer) = some answer
            rw [parallelEmptyRight_symm_answers]
            rfl
      refine ⟨?_, ?_⟩
      · have relabelAfter :
            DDC.History.relabel outer.symm inner.symm
                (previous.snocInner query reply) =
              embedded.snocInner (Sum.inl query) embeddedReply := by
          rw [DDC.History.relabel_snocInner]
          rfl
        exact relabelAfter.symm ▸ next
      · refine ⟨?_, ?_, ?_⟩
        · simp only [DDC.History.relabel_snocInner,
            parallelEmptyRight_symm_queries]
          rw [projectParallel_snocInner_left]
          simpa [extendParallelProjection] using inductionHypothesis.2.1
        · simp only [DDC.History.relabel_snocInner,
            parallelEmptyRight_symm_queries]
          rw [projectParallel_snocInner_left]
          simp only [extendParallelProjection, inductionHypothesis.2.1,
            inductionHypothesis.2.2.1, Option.map_some]
          exact congrArg (fun selected => some (previous.snocInner query selected))
            embeddedReply_eq
        · simp only [DDC.History.relabel_snocInner,
            parallelEmptyRight_symm_queries]
          rw [DDC.History.lastOuter_snocInner,
            DDC.History.lastOuter_snocInner]
          exact inductionHypothesis.2.2.2
  | @afterOuter previous prior reply responds query inductionHypothesis =>
      let outer := Interface.Equiv.parallelEmptyRight A
      let inner := Interface.Equiv.parallelEmptyRight B
      let embedded := DDC.History.relabel outer.symm inner.symm previous
      let embeddedReply : Option
          ((Interface.parallel A Interface.empty).answer embedded.lastOuter) :=
        cast (congrArg (fun selected => Option
          ((Interface.parallel A Interface.empty).answer selected))
          inductionHypothesis.2.2.2.symm) reply
      have tagged : Sum.inr embeddedReply ∈
          parallelRaw converter (forwarding Interface.empty) embedded := by
        apply (mem_parallelRaw_left_iff converter (forwarding Interface.empty)
          embedded previous inductionHypothesis.2 _).mpr
        exact ⟨Sum.inr reply, responds, rfl⟩
      have next : DDC.Raw.Admissible
          (parallelRaw converter (forwarding Interface.empty))
          (embedded.snocOuter (Sum.inl query)) :=
        .afterOuter inductionHypothesis.1 tagged (Sum.inl query)
      refine ⟨?_, ?_⟩
      · simpa only [outer, inner, embedded,
          DDC.History.relabel_snocOuter,
          parallelEmptyRight_symm_queries] using next
      · refine ⟨?_, ?_, ?_⟩
        · simp only [DDC.History.relabel_snocOuter,
            parallelEmptyRight_symm_queries]
          rw [projectParallel_snocOuter_left]
          rfl
        · simp only [DDC.History.relabel_snocOuter,
            parallelEmptyRight_symm_queries]
          rw [projectParallel_snocOuter_left]
          simp only [extendParallelProjection, inductionHypothesis.2.2.1,
            appendOuter]
        · rw [DDC.History.relabel_snocOuter,
            DDC.History.lastOuter_snocOuter,
            DDC.History.lastOuter_snocOuter]
          exact parallelEmptyRight_symm_queries A query

private theorem parallel_empty_right_mem
    {A B : Interface.{u, v}} (converter : DDC A B)
    (history : DDC.History A B) (response : DDC.Response history)
    (responds : response ∈ converter history) :
    response ∈
      relabel (Interface.Equiv.parallelEmptyRight A)
        (Interface.Equiv.parallelEmptyRight B)
        (parallel converter (forwarding Interface.empty)) history := by
  let outer := Interface.Equiv.parallelEmptyRight A
  let inner := Interface.Equiv.parallelEmptyRight B
  let embedded := DDC.History.relabel outer.symm inner.symm history
  have valid := parallelRaw_empty_right_admissible converter
    ((converter.exactDomain history).mp responds.1)
  let sourceResponse := tagLeftResponse embedded history valid.2.2.2 response
  have rawResponds : sourceResponse ∈
      parallelRaw converter (forwarding Interface.empty) embedded := by
    apply (mem_parallelRaw_left_iff converter (forwarding Interface.empty)
      embedded history valid.2 sourceResponse).mpr
    exact ⟨response, responds, rfl⟩
  have sourceResponds : sourceResponse ∈
      parallel converter (forwarding Interface.empty) embedded :=
    (mem_parallel_iff converter (forwarding Interface.empty) embedded
      sourceResponse).mpr ⟨valid.1, rawResponds⟩
  have mapped := mem_relabel_of_mem outer inner
    (parallel converter (forwarding Interface.empty))
    embedded sourceResponse sourceResponds
  have historyEqual : DDC.History.relabel outer inner embedded = history := by
    calc
      DDC.History.relabel outer inner embedded =
          DDC.History.relabel (outer.symm.trans outer)
            (inner.symm.trans inner) history :=
        DDC.History.relabel_trans outer.symm inner.symm outer inner history
      _ = history := by
        rw [Interface.Equiv.symm_trans, Interface.Equiv.symm_trans]
        exact DDC.History.relabel_refl history
  have mappedResponseEqual :
      cast (congrArg (fun selected => DDC.Response selected) historyEqual)
          (relabelResponse outer inner embedded sourceResponse) = response := by
    cases response with
    | inl query =>
        simp only [sourceResponse, tagLeftResponse, relabelResponse_inner]
        change cast
            (congrArg (fun selected => DDC.Response selected) historyEqual)
              (Sum.inl query) = Sum.inl query
        exact cast_converterResponse_inner_empty historyEqual query
    | inr reply =>
        simp only [sourceResponse, tagLeftResponse, relabelResponse_outer]
        let sourceReply := cast
          (congrArg (fun selected => Option
            ((Interface.parallel A Interface.empty).answer selected))
            valid.2.2.2.symm) reply
        let mappedReply := relabelOuterReply outer inner embedded sourceReply
        change cast
            (congrArg (fun selected => DDC.Response selected) historyEqual)
              (Sum.inr mappedReply) = Sum.inr reply
        rw [cast_converterResponse_outer_empty historyEqual mappedReply]
        apply congrArg Sum.inr
        have taggedPacked :
            (⟨embedded.lastOuter, sourceReply⟩ :
                DDC.History.InnerReply (Interface.parallel A Interface.empty)) =
              ⟨Sum.inl history.lastOuter, reply⟩ :=
          packed_tagLeft_general embedded history valid.2.2.2 reply
        have mappedPacked :
            (⟨(DDC.History.relabel outer inner embedded).lastOuter,
                mappedReply⟩ : DDC.History.InnerReply A) =
              ⟨history.lastOuter, reply⟩ := by
          calc
            _ = outer.innerReply ⟨embedded.lastOuter, sourceReply⟩ :=
              packed_outer_relabel outer inner embedded sourceReply
            _ = outer.innerReply ⟨Sum.inl history.lastOuter, reply⟩ :=
              congrArg outer.innerReply taggedPacked
            _ = ⟨history.lastOuter, reply⟩ := by
              cases reply <;> rfl
        have castPacked :
            (⟨history.lastOuter,
                cast (congrArg
                  (fun selected => Option (A.answer selected.lastOuter))
                  historyEqual) mappedReply⟩ : DDC.History.InnerReply A) =
              ⟨(DDC.History.relabel outer inner embedded).lastOuter,
                mappedReply⟩ :=
          pack_cast_outerReply_empty historyEqual mappedReply
        exact eq_of_heq (Sigma.mk.inj_iff.mp (castPacked.trans mappedPacked)).2
  have transported := transport_mem_empty
    (relabel outer inner (parallel converter (forwarding Interface.empty)))
    historyEqual _ mapped
  exact mappedResponseEqual ▸ transported

/-- Ordered parallel with the empty converter on the right is the right unit,
after the canonical query-indexed interface relabeling. -/
theorem relabel_parallel_empty_right_eq
    {A B : Interface.{u, v}} (converter : DDC A B) :
    relabel (Interface.Equiv.parallelEmptyRight A)
        (Interface.Equiv.parallelEmptyRight B)
        (parallel converter (forwarding Interface.empty)) = converter := by
  apply eq_of_graph_subset_empty
  exact parallel_empty_right_mem converter


end DDC

open CategoryTheory


namespace DDC

/--
Ordered parallel commutes with simultaneous relabeling of both components.
This is the routed form of Jost's disjoint-interface attachment law
(Proposition 2.2.3, printed p. 18).
-/
theorem relabel_parallel_eq
    {A₁ B₁ A₂ B₂ C₁ D₁ C₂ D₂ : Interface.{u, v}}
    (outerLeft : A₁.Equiv C₁) (innerLeft : B₁.Equiv D₁)
    (outerRight : A₂.Equiv C₂) (innerRight : B₂.Equiv D₂)
    (left : DDC A₁ B₁) (right : DDC A₂ B₂) :
    relabel (Interface.Equiv.parallel outerLeft outerRight)
        (Interface.Equiv.parallel innerLeft innerRight)
        (parallel left right) =
      parallel (relabel outerLeft innerLeft left)
        (relabel outerRight innerRight right) :=
  (parallel_relabel_eq outerLeft innerLeft outerRight innerRight
    left right).symm

private def ParallelSide.swap : ParallelSide → ParallelSide
  | .left => .right
  | .right => .left

private def ParallelProjection.swap
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    (projection : ParallelProjection A₁ B₁ A₂ B₂) :
    ParallelProjection A₂ B₂ A₁ B₁ where
  active := projection.active.map ParallelSide.swap
  left := projection.right
  right := projection.left

@[simp]
private theorem relabelInput_parallelSwap_outer_left
    {A₁ B₁ A₂ B₂ : Interface.{u, v}} (query : A₁.query) :
    DDC.History.relabelInput
        (Interface.Equiv.parallelSwap A₁ A₂)
        (Interface.Equiv.parallelSwap B₁ B₂)
        (Sum.inl (Sum.inl query)) =
      (Sum.inl (Sum.inr query) : DDC.History.Input
        (Interface.parallel A₂ A₁) (Interface.parallel B₂ B₁)) := by
  rfl

@[simp]
private theorem relabelInput_parallelSwap_outer_right
    {A₁ B₁ A₂ B₂ : Interface.{u, v}} (query : A₂.query) :
    DDC.History.relabelInput
        (Interface.Equiv.parallelSwap A₁ A₂)
        (Interface.Equiv.parallelSwap B₁ B₂)
        (Sum.inl (Sum.inr query)) =
      (Sum.inl (Sum.inl query) : DDC.History.Input
        (Interface.parallel A₂ A₁) (Interface.parallel B₂ B₁)) := by
  rfl

@[simp]
private theorem relabelInput_parallelSwap_inner_left
    {A₁ B₁ A₂ B₂ : Interface.{u, v}} (query : B₁.query)
    (reply : Option (B₁.answer query)) :
    DDC.History.relabelInput
        (Interface.Equiv.parallelSwap A₁ A₂)
        (Interface.Equiv.parallelSwap B₁ B₂)
        (Sum.inr ⟨Sum.inl query, reply⟩) =
      (Sum.inr ⟨Sum.inr query, reply⟩ : DDC.History.Input
        (Interface.parallel A₂ A₁) (Interface.parallel B₂ B₁)) := by
  cases reply <;> rfl

@[simp]
private theorem relabelInput_parallelSwap_inner_right
    {A₁ B₁ A₂ B₂ : Interface.{u, v}} (query : B₂.query)
    (reply : Option (B₂.answer query)) :
    DDC.History.relabelInput
        (Interface.Equiv.parallelSwap A₁ A₂)
        (Interface.Equiv.parallelSwap B₁ B₂)
        (Sum.inr ⟨Sum.inr query, reply⟩) =
      (Sum.inr ⟨Sum.inl query, reply⟩ : DDC.History.Input
        (Interface.parallel A₂ A₁) (Interface.parallel B₂ B₁)) := by
  cases reply <;> rfl

private theorem swap_extendParallelProjection
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    (projection : ParallelProjection A₁ B₁ A₂ B₂)
    (input : DDC.History.Input (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)) :
    (extendParallelProjection projection input).swap =
      extendParallelProjection projection.swap
        (DDC.History.relabelInput
          (Interface.Equiv.parallelSwap A₁ A₂)
          (Interface.Equiv.parallelSwap B₁ B₂) input) := by
  -- Each explicit left tag becomes a right tag and conversely.
  rcases projection with ⟨active, left, right⟩
  cases input with
  | inl query =>
      rcases query with query | query <;>
        simp [ParallelProjection.swap, ParallelSide.swap,
          extendParallelProjection, appendOuter]
  | inr reply =>
      rcases reply with ⟨query, reply⟩
      rcases query with query | query <;> cases reply <;>
        simp [ParallelProjection.swap, extendParallelProjection]

private theorem swap_foldl_extendParallelProjection
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    (projection : ParallelProjection A₁ B₁ A₂ B₂)
    (inputs : List (DDC.History.Input (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))) :
    (inputs.foldl extendParallelProjection projection).swap =
      (inputs.map (DDC.History.relabelInput
        (Interface.Equiv.parallelSwap A₁ A₂)
        (Interface.Equiv.parallelSwap B₁ B₂))).foldl
          extendParallelProjection projection.swap := by
  induction inputs generalizing projection with
  | nil => rfl
  | cons input remaining inductionHypothesis =>
      -- Exchange the first tag, then apply the same statement to the tail.
      simp only [List.foldl_cons, List.map_cons]
      rw [inductionHypothesis]
      exact congrArg
        (fun initial => remaining.map (DDC.History.relabelInput
          (Interface.Equiv.parallelSwap A₁ A₂)
          (Interface.Equiv.parallelSwap B₁ B₂)) |>.foldl
            extendParallelProjection initial)
        (swap_extendParallelProjection projection input)

private theorem projectParallel_relabel_swap
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)) :
    projectParallel (DDC.History.relabel
        (Interface.Equiv.parallelSwap A₁ A₂)
        (Interface.Equiv.parallelSwap B₁ B₂) history) =
      (projectParallel history).swap := by
  -- Projection is a fold over received inputs, so the pointwise tag exchange
  -- exchanges the two accumulated component histories.
  unfold projectParallel
  rw [show (DDC.History.relabel
      (Interface.Equiv.parallelSwap A₁ A₂)
      (Interface.Equiv.parallelSwap B₁ B₂) history).inputs.1 =
      history.inputs.1.map (DDC.History.relabelInput
        (Interface.Equiv.parallelSwap A₁ A₂)
        (Interface.Equiv.parallelSwap B₁ B₂)) by rfl]
  simpa [ParallelProjection.swap] using
    (swap_foldl_extendParallelProjection
      (A₁ := A₁) (B₁ := B₁) (A₂ := A₂) (B₂ := B₂)
      { active := none, left := none, right := none } history.inputs.1).symm

private theorem targetOuterSwapLeft
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₁ B₁)
    (outerEqual : history.lastOuter = Sum.inl component.lastOuter) :
    (DDC.History.relabel
      (Interface.Equiv.parallelSwap A₁ A₂)
      (Interface.Equiv.parallelSwap B₁ B₂) history).lastOuter =
        Sum.inr component.lastOuter := by
  -- The outer query keeps its value and exchanges its routing tag.
  rw [DDC.History.lastOuter_relabel, outerEqual]
  rfl

private theorem targetOuterSwapRight
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₂ B₂)
    (outerEqual : history.lastOuter = Sum.inr component.lastOuter) :
    (DDC.History.relabel
      (Interface.Equiv.parallelSwap A₁ A₂)
      (Interface.Equiv.parallelSwap B₁ B₂) history).lastOuter =
        Sum.inl component.lastOuter := by
  -- The outer query keeps its value and exchanges its routing tag.
  rw [DDC.History.lastOuter_relabel, outerEqual]
  rfl

private theorem relabelResponse_swap_tagLeft
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₁ B₁)
    (outerEqual : history.lastOuter = Sum.inl component.lastOuter)
    (response : DDC.Response component) :
    relabelResponse
        (Interface.Equiv.parallelSwap A₁ A₂)
        (Interface.Equiv.parallelSwap B₁ B₂) history
        (tagLeftResponse history component outerEqual response) =
      tagRightResponse
        (DDC.History.relabel
          (Interface.Equiv.parallelSwap A₁ A₂)
          (Interface.Equiv.parallelSwap B₁ B₂) history)
        component (targetOuterSwapLeft history component outerEqual) response := by
  cases response with
  | inl query => rfl
  | inr reply =>
      -- For an outer reply, compare the two dependent answer fibres as packed
      -- query/reply pairs before removing the common query component.
      let outer := Interface.Equiv.parallelSwap A₁ A₂
      let inner := Interface.Equiv.parallelSwap B₁ B₂
      let targetHistory := DDC.History.relabel outer inner history
      let sourceTagged := cast
        (congrArg (fun selected =>
          Option ((Interface.parallel A₁ A₂).answer selected))
          outerEqual.symm) reply
      let targetEqual := targetOuterSwapLeft history component outerEqual
      let targetTagged := cast
        (congrArg (fun selected =>
          Option ((Interface.parallel A₂ A₁).answer selected))
          targetEqual.symm) reply
      simp only [tagLeftResponse, tagRightResponse, relabelResponse_outer]
      have packedEqual :
          (⟨targetHistory.lastOuter,
            relabelOuterReply outer inner history sourceTagged⟩ :
              DDC.History.InnerReply (Interface.parallel A₂ A₁)) =
            ⟨targetHistory.lastOuter, targetTagged⟩ := by
        calc
          _ = outer.innerReply ⟨history.lastOuter, sourceTagged⟩ :=
            packed_outer_relabel outer inner history sourceTagged
          _ = outer.innerReply ⟨Sum.inl component.lastOuter, reply⟩ := by
            exact congrArg outer.innerReply
              (packed_tagLeft_general history component outerEqual reply)
          _ = ⟨Sum.inr component.lastOuter, reply⟩ := by
            cases reply <;> rfl
          _ = ⟨targetHistory.lastOuter, targetTagged⟩ :=
            (packed_tagRight_general targetHistory component targetEqual reply).symm
      exact congrArg Sum.inr
        (eq_of_heq (Sigma.mk.inj_iff.mp packedEqual).2)

private theorem relabelResponse_swap_tagRight
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (component : DDC.History A₂ B₂)
    (outerEqual : history.lastOuter = Sum.inr component.lastOuter)
    (response : DDC.Response component) :
    relabelResponse
        (Interface.Equiv.parallelSwap A₁ A₂)
        (Interface.Equiv.parallelSwap B₁ B₂) history
        (tagRightResponse history component outerEqual response) =
      tagLeftResponse
        (DDC.History.relabel
          (Interface.Equiv.parallelSwap A₁ A₂)
          (Interface.Equiv.parallelSwap B₁ B₂) history)
        component (targetOuterSwapRight history component outerEqual) response := by
  cases response with
  | inl query => rfl
  | inr reply =>
      -- The right-to-left case is the same dependent fibre calculation with
      -- the two explicit routing tags exchanged.
      let outer := Interface.Equiv.parallelSwap A₁ A₂
      let inner := Interface.Equiv.parallelSwap B₁ B₂
      let targetHistory := DDC.History.relabel outer inner history
      let sourceTagged := cast
        (congrArg (fun selected =>
          Option ((Interface.parallel A₁ A₂).answer selected))
          outerEqual.symm) reply
      let targetEqual := targetOuterSwapRight history component outerEqual
      let targetTagged := cast
        (congrArg (fun selected =>
          Option ((Interface.parallel A₂ A₁).answer selected))
          targetEqual.symm) reply
      simp only [tagLeftResponse, tagRightResponse, relabelResponse_outer]
      have packedEqual :
          (⟨targetHistory.lastOuter,
            relabelOuterReply outer inner history sourceTagged⟩ :
              DDC.History.InnerReply (Interface.parallel A₂ A₁)) =
            ⟨targetHistory.lastOuter, targetTagged⟩ := by
        calc
          _ = outer.innerReply ⟨history.lastOuter, sourceTagged⟩ :=
            packed_outer_relabel outer inner history sourceTagged
          _ = outer.innerReply ⟨Sum.inr component.lastOuter, reply⟩ := by
            exact congrArg outer.innerReply
              (packed_tagRight_general history component outerEqual reply)
          _ = ⟨Sum.inl component.lastOuter, reply⟩ := by
            cases reply <;> rfl
          _ = ⟨targetHistory.lastOuter, targetTagged⟩ :=
            (packed_tagLeft_general targetHistory component targetEqual reply).symm
      exact congrArg Sum.inr
        (eq_of_heq (Sigma.mk.inj_iff.mp packedEqual).2)

private theorem parallelRaw_swap_mem
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (admissible : DDC.Raw.Admissible (parallelRaw left right) history)
    (response : DDC.Response history)
    (responds : response ∈ parallelRaw left right history) :
    relabelResponse
        (Interface.Equiv.parallelSwap A₁ A₂)
        (Interface.Equiv.parallelSwap B₁ B₂) history response ∈
      parallelRaw right left
        (DDC.History.relabel
          (Interface.Equiv.parallelSwap A₁ A₂)
          (Interface.Equiv.parallelSwap B₁ B₂) history) := by
  let targetHistory := DDC.History.relabel
    (Interface.Equiv.parallelSwap A₁ A₂)
    (Interface.Equiv.parallelSwap B₁ B₂) history
  have projectionEqual := projectParallel_relabel_swap history
  rcases parallelRaw_admissible_active left right admissible with
      ⟨component, active⟩ | ⟨component, active⟩
  · -- An active left component becomes the active right component.
    obtain ⟨componentResponse, componentResponds, tagged⟩ :=
      (mem_parallelRaw_left_iff left right history component active
        response).mp responds
    have targetActive : ActiveRight targetHistory component := by
      refine ⟨?_, ?_, targetOuterSwapLeft history component active.2.2⟩
      · rw [projectionEqual]
        simp [ParallelProjection.swap, ParallelSide.swap, active.1]
      · rw [projectionEqual]
        simpa [ParallelProjection.swap] using active.2.1
    apply (mem_parallelRaw_right_iff right left targetHistory component
      targetActive _).mpr
    refine ⟨componentResponse, componentResponds, ?_⟩
    rw [← tagged]
    exact (relabelResponse_swap_tagLeft history component active.2.2
      componentResponse).symm
  · -- An active right component becomes the active left component.
    obtain ⟨componentResponse, componentResponds, tagged⟩ :=
      (mem_parallelRaw_right_iff left right history component active
        response).mp responds
    have targetActive : ActiveLeft targetHistory component := by
      refine ⟨?_, ?_, targetOuterSwapRight history component active.2.2⟩
      · rw [projectionEqual]
        simp [ParallelProjection.swap, ParallelSide.swap, active.1]
      · rw [projectionEqual]
        simpa [ParallelProjection.swap] using active.2.1
    apply (mem_parallelRaw_left_iff right left targetHistory component
      targetActive _).mpr
    refine ⟨componentResponse, componentResponds, ?_⟩
    rw [← tagged]
    exact (relabelResponse_swap_tagRight history component active.2.2
      componentResponse).symm

private theorem parallelRaw_admissible_swap
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    {history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂)}
    (admissible : DDC.Raw.Admissible (parallelRaw left right) history) :
    DDC.Raw.Admissible (parallelRaw right left)
      (DDC.History.relabel
        (Interface.Equiv.parallelSwap A₁ A₂)
        (Interface.Equiv.parallelSwap B₁ B₂) history) := by
  induction admissible with
  | start query =>
      -- The initial routed outer query is exchanged pointwise.
      exact @DDC.Raw.Admissible.start _ _ _
        ((Interface.Equiv.parallelSwap A₁ A₂).queries query)
  | @afterInner prior query priorAdmissible responds reply
      inductionHypothesis =>
      -- Exchange the inner query and its answer, then extend the target tree.
      have mappedResponds := parallelRaw_swap_mem left right prior
        priorAdmissible (Sum.inl query) responds
      have target := @DDC.Raw.Admissible.afterInner _ _ _ _
        ((Interface.Equiv.parallelSwap B₁ B₂).queries query)
        inductionHypothesis mappedResponds
        (reply.map ((Interface.Equiv.parallelSwap B₁ B₂).answers query))
      exact (DDC.History.relabel_snocInner
        (Interface.Equiv.parallelSwap A₁ A₂)
        (Interface.Equiv.parallelSwap B₁ B₂)
        prior query reply) ▸ target
  | @afterOuter prior priorAdmissible reply responds query
      inductionHypothesis =>
      -- Exchange the completed outer reply before the next outer query.
      have mappedResponds := parallelRaw_swap_mem left right prior
        priorAdmissible (Sum.inr reply) responds
      have target := @DDC.Raw.Admissible.afterOuter _ _ _ _
        inductionHypothesis _ mappedResponds
        ((Interface.Equiv.parallelSwap A₁ A₂).queries query)
      exact (DDC.History.relabel_snocOuter
        (Interface.Equiv.parallelSwap A₁ A₂)
        (Interface.Equiv.parallelSwap B₁ B₂)
        prior query) ▸ target

private theorem parallel_swap_mem
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂)
    (history : DDC.History (Interface.parallel A₁ A₂)
      (Interface.parallel B₁ B₂))
    (response : DDC.Response history)
    (responds : response ∈ parallel left right history) :
    relabelResponse
        (Interface.Equiv.parallelSwap A₁ A₂)
        (Interface.Equiv.parallelSwap B₁ B₂) history response ∈
      parallel right left
        (DDC.History.relabel
          (Interface.Equiv.parallelSwap A₁ A₂)
          (Interface.Equiv.parallelSwap B₁ B₂) history) := by
  -- Canonical membership consists of admissibility and raw graph membership.
  obtain ⟨admissible, rawResponds⟩ :=
    (mem_parallel_iff left right history response).mp responds
  apply (mem_parallel_iff right left
    (DDC.History.relabel
      (Interface.Equiv.parallelSwap A₁ A₂)
      (Interface.Equiv.parallelSwap B₁ B₂) history) _).mpr
  exact ⟨parallelRaw_admissible_swap left right admissible,
    parallelRaw_swap_mem left right history admissible response rawResponds⟩

private theorem parallel_swap_relabel_eq
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂) :
    parallel right left =
      relabel (Interface.Equiv.parallelSwap A₁ A₂)
        (Interface.Equiv.parallelSwap B₁ B₂) (parallel left right) := by
  let outer := Interface.Equiv.parallelSwap A₁ A₂
  let inner := Interface.Equiv.parallelSwap B₁ B₂
  apply eq_of_graph_subset_local
  intro targetHistory targetResponse responds
  -- Pull the relabeled graph row back to the original routed interface.
  have sourceResponds :=
    (mem_relabel_iff_symm outer inner (parallel left right)
      targetHistory targetResponse).mp responds
  let histories := DDC.History.relabelEquiv outer inner
  let sourceHistory := histories.symm targetHistory
  let responses := responseRelabelLocal outer inner targetHistory
  let sourceResponse := responses.symm targetResponse
  -- Exchange the two component tags in that source row.
  have mapped := parallel_swap_mem left right sourceHistory sourceResponse
    sourceResponds
  have historyEqual : DDC.History.relabel outer inner sourceHistory =
      targetHistory := histories.apply_symm_apply targetHistory
  have responseEqual :
      cast (congrArg (fun selected => DDC.Response selected) historyEqual)
          (relabelResponse outer inner sourceHistory sourceResponse) =
        targetResponse := responses.apply_symm_apply targetResponse
  -- Transport the mapped row along the inverse-image equality.
  have transported := transport_mem_local (parallel right left)
    historyEqual _ mapped
  exact responseEqual ▸ transported

/-- Relabeling both explicit routing tags exchanges the two components of
ordered DDC parallel composition.  This is a theorem about the concrete
query-sum routing equivalence; it does not add symmetry to the abstract
ordered tensor. -/
theorem relabel_parallel_swap_eq
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    (left : DDC A₁ B₁) (right : DDC A₂ B₂) :
    relabel (Interface.Equiv.parallelSwap A₁ A₂)
        (Interface.Equiv.parallelSwap B₁ B₂) (parallel left right) =
      parallel right left :=
  (parallel_swap_relabel_eq left right).symm

end DDC

end RandomSystems.Ambient
