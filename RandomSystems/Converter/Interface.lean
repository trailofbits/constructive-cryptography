/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Logic.Equiv.Sum

set_option autoImplicit false

/-!
# Query-indexed interfaces

This file owns the interface objects of the query-indexed DDC extension.  It
is intentionally Mathlib-only.

Jost, immediately before Definition 2.2.1 (printed p. 16), states that “the
interface address is encoded as part of the inputs” and that a query obtains
“the corresponding response y at the same interface.”
Liu--Maurer instead use fixed tuple coordinates for the interfaces of a
resource (Definitions 4--7, printed pp. 9--11).  The family
`answer : query → Type` below is our common type-safe refinement of these
representations: an answer belonging to a different query cannot be formed.
It is not claimed to be the literal syntax of either source.

Ordered parallel uses a tagged sum of queries.  The tag selects the answer
family of the corresponding component.  No commutativity or symmetry is
postulated here.  The concrete reassociation and empty-unit equivalences are
proved to satisfy the object-level pentagon and triangle equations needed by
later categorical packaging.
-/

namespace RandomSystems.Ambient

universe u v

/--
An addressed interface: a query type together with the answer type selected
by each query.

The query-selected family is a type-safe refinement of the source convention
that an addressed query receives an answer at the same interface; it is not a
literal primary-source definition.
-/
structure Interface where
  query : Type u
  answer : query → Type v

namespace Interface

/--
The dependent sum of a query and an answer in the fibre selected by that
query.
-/
abbrev Reply (A : Interface.{u, v}) := Σ query : A.query, A.answer query

/-- The interface with no possible query. -/
def empty : Interface.{u, v} where
  query := PEmpty
  answer := PEmpty.elim

/--
Ordered parallel of interfaces.  The query tag selects both the component and
its answer family.
-/
@[reducible]
def parallel (left right : Interface.{u, v}) : Interface.{u, v} where
  query := left.query ⊕ right.query
  answer
    | Sum.inl query => left.answer query
    | Sum.inr query => right.answer query

/--
The reducible constant-answer-family specialization.  This is the interface
used to bridge the established fixed-interface Random Systems
presentation; it is not a separately named primary-source primitive.
-/
abbrev single (X : Type u) (Y : Type v) : Interface.{u, v} where
  query := X
  answer := fun _ => Y

/-- Replies of ordered parallel are exactly tagged component replies. -/
def replyParallelEquiv (left right : Interface.{u, v}) :
    Reply (parallel left right) ≃ Reply left ⊕ Reply right where
  toFun
    | ⟨Sum.inl query, answer⟩ => Sum.inl ⟨query, answer⟩
    | ⟨Sum.inr query, answer⟩ => Sum.inr ⟨query, answer⟩
  invFun
    | Sum.inl ⟨query, answer⟩ => ⟨Sum.inl query, answer⟩
    | Sum.inr ⟨query, answer⟩ => ⟨Sum.inr query, answer⟩
  left_inv reply := by
    rcases reply with ⟨query, answer⟩
    cases query <;> rfl
  right_inv reply := by
    cases reply with
    | inl reply => rcases reply with ⟨query, answer⟩; rfl
    | inr reply => rcases reply with ⟨query, answer⟩; rfl

/--
Replies of the constant-answer-family specialization are pairs of queries and
answers.
-/
def replySingleEquiv (X : Type u) (Y : Type v) :
    Reply (single X Y) ≃ X × Y where
  toFun reply := (reply.1, reply.2)
  invFun reply := ⟨reply.1, reply.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
An equivalence of addressed interfaces: an equivalence of queries together
with an answer equivalence in every selected fibre.
-/
structure Equiv (left right : Interface.{u, v}) where
  queries : left.query ≃ right.query
  answers : ∀ query, left.answer query ≃ right.answer (queries query)

namespace Equiv

/-- Reflexive interface equivalence. -/
def refl (A : Interface.{u, v}) : A.Equiv A where
  queries := _root_.Equiv.refl A.query
  answers := fun _ => _root_.Equiv.refl _

/-- Symmetry of interface equivalence. -/
def symm {A B : Interface.{u, v}} (equivalence : A.Equiv B) : B.Equiv A where
  queries := equivalence.queries.symm
  answers := fun query =>
    (_root_.Equiv.cast (congrArg B.answer
      (equivalence.queries.apply_symm_apply query).symm)).trans
      (equivalence.answers (equivalence.queries.symm query)).symm

/-- Transitivity of interface equivalence. -/
def trans {A B C : Interface.{u, v}}
    (first : A.Equiv B) (second : B.Equiv C) : A.Equiv C where
  queries := first.queries.trans second.queries
  answers := fun query =>
    (first.answers query).trans (second.answers (first.queries query))

/-- An interface equivalence induces an equivalence of dependent replies. -/
def replies {A B : Interface.{u, v}} (equivalence : A.Equiv B) :
    A.Reply ≃ B.Reply :=
  _root_.Equiv.sigmaCongr equivalence.queries equivalence.answers

/-- Ordered parallel preserves interface equivalences. -/
def parallel {A B C D : Interface.{u, v}}
    (left : A.Equiv C) (right : B.Equiv D) :
    (Interface.parallel A B).Equiv (Interface.parallel C D) where
  queries := _root_.Equiv.sumCongr left.queries right.queries
  answers
    | Sum.inl query => left.answers query
    | Sum.inr query => right.answers query

/-- Reassociation of ordered parallel interfaces. -/
def parallelAssoc (A B C : Interface.{u, v}) :
    (Interface.parallel (Interface.parallel A B) C).Equiv
      (Interface.parallel A (Interface.parallel B C)) where
  queries := _root_.Equiv.sumAssoc A.query B.query C.query
  answers
    | Sum.inl (Sum.inl _) => _root_.Equiv.refl _
    | Sum.inl (Sum.inr _) => _root_.Equiv.refl _
    | Sum.inr _ => _root_.Equiv.refl _

/-- Exchange the two explicit query tags of an ordered parallel interface.

This is a concrete equivalence of routed interfaces.  It is not installed as
a symmetry law for the abstract ordered tensor. -/
def parallelSwap (A B : Interface.{u, v}) :
    (Interface.parallel A B).Equiv (Interface.parallel B A) where
  queries := _root_.Equiv.sumComm A.query B.query
  answers
    | Sum.inl _ => _root_.Equiv.refl _
    | Sum.inr _ => _root_.Equiv.refl _

/-- Left empty-unit equivalence for ordered parallel interfaces. -/
def parallelEmptyLeft (A : Interface.{u, v}) :
    (Interface.parallel Interface.empty A).Equiv A where
  queries :=
    { toFun := fun query => match query with
        | Sum.inl impossible => PEmpty.elim impossible
        | Sum.inr query => query
      invFun := Sum.inr
      left_inv := fun query => by
        cases query with
        | inl impossible => exact PEmpty.elim impossible
        | inr query => rfl
      right_inv := fun _ => rfl }
  answers := fun query => match query with
    | Sum.inl impossible => PEmpty.elim impossible
    | Sum.inr _ => _root_.Equiv.refl _

/-- Right empty-unit equivalence for ordered parallel interfaces. -/
def parallelEmptyRight (A : Interface.{u, v}) :
    (Interface.parallel A Interface.empty).Equiv A where
  queries :=
    { toFun := fun query => match query with
        | Sum.inl query => query
        | Sum.inr impossible => PEmpty.elim impossible
      invFun := Sum.inl
      left_inv := fun query => by
        cases query with
        | inl query => rfl
        | inr impossible => exact PEmpty.elim impossible
      right_inv := fun _ => rfl }
  answers := fun query => match query with
    | Sum.inl _ => _root_.Equiv.refl _
    | Sum.inr impossible => PEmpty.elim impossible

/--
Interface equivalences are determined by their query equivalence and their
dependent family of answer equivalences.
-/
theorem ext
    {A B : Interface.{u, v}} {left right : A.Equiv B}
    (queries : left.queries = right.queries)
    (answers : HEq left.answers right.answers) :
    left = right := by
  cases left
  cases right
  cases queries
  cases answers
  rfl

/--
Pointwise equality on queries and heterogeneous pointwise equality on answer
fibres determine an interface equivalence.
-/
theorem ext_apply
    {A B : Interface.{u, v}} {left right : A.Equiv B}
    (queries : ∀ query, left.queries query = right.queries query)
    (answers : ∀ query, HEq (left.answers query) (right.answers query)) :
    left = right := by
  have queryEqual : left.queries = right.queries := by
    apply _root_.Equiv.ext
    exact queries
  apply ext queryEqual
  apply Function.hfunext rfl
  intro query other equal
  cases equal
  exact answers query

/-- Relabeling dependent replies respects composition. -/
theorem replies_trans
    {A B C : Interface.{u, v}}
    (first : A.Equiv B) (second : B.Equiv C) :
    (first.trans second).replies = first.replies.trans second.replies := by
  apply _root_.Equiv.ext
  rintro ⟨query, answer⟩
  rfl

theorem answers_inverse_transport
    {A B : Interface.{u, v}} (equivalence : A.Equiv B)
    {left right : A.query} (queryEqual : left = right)
    (mappedEqual : equivalence.queries left = equivalence.queries right)
    (answer : A.answer right) :
    (equivalence.answers left).symm
        (cast (congrArg B.answer mappedEqual.symm)
          (equivalence.answers right answer)) ≍ answer := by
  cases queryEqual
  have mappedEqual_refl : mappedEqual = rfl := Subsingleton.elim _ _
  cases mappedEqual_refl
  exact heq_of_eq ((equivalence.answers left).symm_apply_apply answer)

/-- Relabeling dependent replies respects inverse interface equivalences. -/
theorem replies_symm
    {A B : Interface.{u, v}} (equivalence : A.Equiv B) :
    equivalence.symm.replies = equivalence.replies.symm := by
  symm
  apply _root_.Equiv.trans_eq_refl_iff_symm_eq.mp
  apply _root_.Equiv.ext
  rintro ⟨query, answer⟩
  let queryEqual := equivalence.queries.symm_apply_apply query
  apply Sigma.ext queryEqual
  simp [Interface.Equiv.replies, Interface.Equiv.symm,
    _root_.Equiv.sigmaCongr, _root_.Equiv.sigmaCongrRight,
    _root_.Equiv.sigmaCongrLeft]
  exact answers_inverse_transport equivalence queryEqual
    (equivalence.queries.apply_symm_apply
      (equivalence.queries query)) answer

/--
An interface equivalence is determined by its query equivalence and its
equivalence on dependent replies.
-/
theorem ext_queries_replies
    {A B : Interface.{u, v}} {left right : A.Equiv B}
    (queries : left.queries = right.queries)
    (replies : left.replies = right.replies) : left = right := by
  apply Interface.Equiv.ext queries
  cases left with
  | mk leftQueries leftAnswers =>
    cases right with
    | mk rightQueries rightAnswers =>
      dsimp only at queries replies ⊢
      cases queries
      apply heq_of_eq
      funext query
      apply _root_.Equiv.ext
      intro answer
      have applied := congrFun (congrArg _root_.Equiv.toFun replies)
        ⟨query, answer⟩
      exact eq_of_heq (Sigma.mk.inj_iff.mp applied).2

@[simp]
theorem trans_symm
    {A B : Interface.{u, v}} (equivalence : A.Equiv B) :
    equivalence.trans equivalence.symm = .refl A := by
  apply ext_queries_replies
  · exact _root_.Equiv.self_trans_symm equivalence.queries
  · rw [replies_trans, replies_symm]
    exact _root_.Equiv.self_trans_symm equivalence.replies

@[simp]
theorem symm_trans
    {A B : Interface.{u, v}} (equivalence : A.Equiv B) :
    equivalence.symm.trans equivalence = .refl B := by
  apply ext_queries_replies
  · exact _root_.Equiv.symm_trans_self equivalence.queries
  · rw [replies_trans, replies_symm]
    exact _root_.Equiv.symm_trans_self equivalence.replies

@[simp]
theorem trans_refl
    {A B : Interface.{u, v}} (equivalence : A.Equiv B) :
    equivalence.trans (.refl B) = equivalence := by
  apply ext_apply
  · intro query
    rfl
  · intro query
    rfl

@[simp]
theorem refl_trans
    {A B : Interface.{u, v}} (equivalence : A.Equiv B) :
    (Interface.Equiv.refl A).trans equivalence = equivalence := by
  apply ext_apply
  · intro query
    rfl
  · intro query
    rfl

/-- Symmetry preserves the reflexive interface equivalence. -/
theorem symm_refl_eq (A : Interface.{u, v}) :
    (Interface.Equiv.refl A).symm = .refl A := by
  apply Interface.Equiv.ext_queries_replies
  · rfl
  · rw [Interface.Equiv.replies_symm]
    rfl

/-- Applying symmetry twice recovers the original interface equivalence. -/
theorem symm_symm_eq
    {A B : Interface.{u, v}} (equivalence : A.Equiv B) :
    equivalence.symm.symm = equivalence := by
  apply Interface.Equiv.ext_queries_replies
  · exact _root_.Equiv.symm_symm _
  · rw [Interface.Equiv.replies_symm, Interface.Equiv.replies_symm]
    exact _root_.Equiv.symm_symm _

/-- Symmetry reverses transitivity of interface equivalences. -/
theorem trans_symm_reverse_eq
    {A B C : Interface.{u, v}}
    (first : A.Equiv B) (second : B.Equiv C) :
    (first.trans second).symm = second.symm.trans first.symm := by
  apply Interface.Equiv.ext_queries_replies
  · rfl
  · rw [Interface.Equiv.replies_symm, Interface.Equiv.replies_trans,
      Interface.Equiv.replies_trans, Interface.Equiv.replies_symm,
      Interface.Equiv.replies_symm]
    rfl

/-- Transitivity of interface equivalences is associative. -/
theorem trans_assoc_eq
    {A B C D : Interface.{u, v}}
    (first : A.Equiv B) (second : B.Equiv C) (third : C.Equiv D) :
    (first.trans second).trans third = first.trans (second.trans third) := by
  apply Interface.Equiv.ext_queries_replies
  · rfl
  · rw [Interface.Equiv.replies_trans, Interface.Equiv.replies_trans,
      Interface.Equiv.replies_trans, Interface.Equiv.replies_trans]
    rfl

/-- Ordered parallel preserves reflexive interface equivalences. -/
theorem parallel_refl_eq (left right : Interface.{u, v}) :
    Interface.Equiv.parallel (.refl left) (.refl right) =
      .refl (Interface.parallel left right) := by
  apply Interface.Equiv.ext_apply
  · intro query
    cases query <;> rfl
  · intro query
    cases query <;> rfl

/-- Symmetry acts componentwise on ordered parallel interface equivalences. -/
theorem parallel_symm_eq
    {A B C D : Interface.{u, v}}
    (left : A.Equiv C) (right : B.Equiv D) :
    (Interface.Equiv.parallel left right).symm =
      Interface.Equiv.parallel left.symm right.symm := by
  apply Interface.Equiv.ext_apply
  · intro query
    cases query <;> rfl
  · intro query
    cases query <;> rfl

/-- The concrete ordered-parallel associator satisfies the object-level pentagon. -/
theorem parallelAssoc_pentagon (A B C D : Interface.{u, v}) :
    (parallel (parallelAssoc A B C) (.refl D)).trans
        ((parallelAssoc A (Interface.parallel B C) D).trans
          (parallel (.refl A) (parallelAssoc B C D))) =
      (parallelAssoc (Interface.parallel A B) C D).trans
        (parallelAssoc A B (Interface.parallel C D)) := by
  apply ext_apply
  · intro query
    rcases query with (((query | query) | query) | query) <;> rfl
  · intro query
    rcases query with (((query | query) | query) | query) <;> rfl

/--
The concrete ordered-parallel associator and empty-unit equivalences satisfy
the object-level triangle.
-/
theorem parallel_triangle (A B : Interface.{u, v}) :
    (parallelAssoc A Interface.empty B).trans
        (parallel (.refl A) (parallelEmptyLeft B)) =
      parallel (parallelEmptyRight A) (.refl B) := by
  apply ext_apply
  · intro query
    cases query with
    | inl leftOrEmpty =>
        cases leftOrEmpty with
        | inl query => rfl
        | inr impossible => exact PEmpty.elim impossible
    | inr query => rfl
  · intro query
    cases query with
    | inl leftOrEmpty =>
        cases leftOrEmpty with
        | inl query => rfl
        | inr impossible => exact PEmpty.elim impossible
    | inr query => rfl

end Equiv

end Interface

end RandomSystems.Ambient
