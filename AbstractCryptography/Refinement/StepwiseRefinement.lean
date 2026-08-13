/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import AbstractCryptography.Refinement.Basic

/-!
# Soundness of step-wise refinement (MauRen11 App. A)

"Here we formalize the claim that general composability (cf. Definition 7) is
sufficient for the step-wise refinement paradigm to work."

"For this, we think of a construction represented by a tree as follows.  Any
node `v` of the tree labels a component, called `S_v`, as well as, if `v` is
not a leaf, a constructor, called `α_v`.  Furthermore, for any non-leaf node
`v` we define the constructor `α*_v` of the underlying tree inductively as

  `α*_v = id`                                if `v` is a leaf
  `α*_v = α_v ∘ (α*_{v₁} | ⋯ | α*_{v_d})`    otherwise."

"It is intuitively clear that general composability is sufficient (and
necessary) for the step-wise refinement paradigm to work in the following
sense.  Given a tree representing a construction as described above where the
relation `R₁‖R₂ —α→ S` holds for any node `S` and its children `R₁` and `R₂`,
the relation also holds between the root and the leaves." (§3)

Reading the paper's notation here:

* Inner nodes have one or two children; `d ≥ 3` is nesting of binary nodes,
  and the tree fixes the parenthesization fn. 10 asks for: "If there are `d`
  children `R₁, …, R_d`, one can write `R₁‖⋯‖R_d —α→ S`.  If `‖` is not
  associative, appropriate parentheses are required in the expression
  `R₁‖⋯‖R_d`."  Unary nodes are the `d = 1` case, encoding a *serial*
  refinement chain as a tree.
* Fn. 11: "One could naturally postulate that `(α|id)(id|α′) = α|α′`, but
  this is not necessary."  The `|` in `α*_v` is therefore rendered twice:
  literally, by `childParallelStar`, and as the derived chain
  `(1 ∥ α*_{v₂}) * (α*_{v₁} ∥ 1)` of `red_par_left_first`, by
  `derivedChainStar`.
* App. A's `α_v ∘ (α*_{v₁} | ⋯ | α*_{v_d})` applies the children's
  constructors first and `α_v` last, so `∘` here is §6.2's juxtaposition and
  not Definition 7 (i)'s diagrammatic `∘`.

**Theorem 3** — "A reduction `{—α→}_{α∈Γ}` (for component set `Ω` and
constructor set `Γ`) is sound for step-wise refinement if and only if it is
generally composable" — is the theorem "which ultimately justifies our
definition of general composability (Definition 7)".

Its "only if" direction needs equations on `Γ` that this file otherwise does
not postulate: a leaf inside a larger tree contributes `α* = id` factors, so
axioms (i)–(iii) come back only up to neutral-element dressing.  They are
taken from Definition 5's "special (neutral) element `id`": `1 * α = α`,
`α * 1 = α`, `1 ∥ 1 = 1`.  The "if" direction is law-free.
-/

namespace AbstractCryptography
variable {Ω Γ : Type*}

/-- "A construction represented by a tree as follows.  Any node `v` of the
tree labels a component, called `S_v`, as well as, if `v` is not a leaf, a
constructor, called `α_v`."

"One can describe the overall construction as a tree where each inner
(non-leaf) node is labeled by a component `S` and a constructor `α`
describing how component `S` is obtained from components, say `R₁` and `R₂`,
at the children nodes.  Then we write `R₁‖R₂ —α→ S`.  This can be generalized
to nodes with more than two children." (§3) -/
inductive ConstructionTree (Ω : Type*) (Γ : Type*) where
  /-- A leaf, labeling a component. -/
  | leaf (R : Ω)
  /-- An inner node with a single child, the `d = 1` case. -/
  | node₁ (α : Γ) (S : Ω) (child : ConstructionTree Ω Γ)
  /-- An inner node with two children: "`S` is obtained from components, say
  `R₁` and `R₂`, at the children nodes."  `d ≥ 3` is nesting of these. -/
  | node₂ (α : Γ) (S : Ω) (left right : ConstructionTree Ω Γ)

namespace ConstructionTree

/-- `S_r`, the component labeled by "the root `r`". -/
def root : ConstructionTree Ω Γ → Ω
  | leaf R => R
  | node₁ _ S _ => S
  | node₂ _ S _ _ => S

/-- `S_{ℓ₁}‖⋯‖S_{ℓ_k}`, the components labeled by "the leaves `ℓ₁, …, ℓ_k`",
parenthesized as in the tree — fn. 10: "If `‖` is not associative,
appropriate parentheses are required." -/
def leavesPar [Par Ω] : ConstructionTree Ω Γ → Ω
  | leaf R => R
  | node₁ _ _ t => t.leavesPar
  | node₂ _ _ l r => l.leavesPar ∥ r.leavesPar

/-- Appendix A's tree constructor `α*_v`, with the binary child constructor
read as Definition 7's left-first derived chain
`(1 ∥ α*_{v₂}) * (α*_{v₁} ∥ 1)` rather than the literal `α*_{v₁} ∥ α*_{v₂}`
printed there.  Footnote 11 does not identify the two. -/
def derivedChainStar [Mul Γ] [One Γ] [Par Γ] : ConstructionTree Ω Γ → Γ
  | leaf _ => 1
  | node₁ α _ t => α * t.derivedChainStar
  | node₂ α _ l r =>
      α * ((1 ∥ r.derivedChainStar) * (l.derivedChainStar ∥ 1))

/-- Appendix A's tree constructor `α*_v`, with the binary child constructor
kept under the literal parallel operation printed in the paper.  The children
act first and the node constructor last, hence `α * (leftStar ∥ rightStar)`.
No equation with `derivedChainStar` is assumed. -/
def childParallelStar [Mul Γ] [One Γ] [Par Γ] : ConstructionTree Ω Γ → Γ
  | leaf _ => 1
  | node₁ α _ t => α * t.childParallelStar
  | node₂ α _ l r => α * (l.childParallelStar ∥ r.childParallelStar)

/-- Definition 19's hypothesis: "at every node `v` of the tree we have
`S_{v₁}‖⋯‖S_{v_d} —α_v→ S_v` (a local property in the tree)." -/
def LocallyValid [Par Ω] [HasReduction Ω Γ] : ConstructionTree Ω Γ → Prop
  | leaf _ => True
  | node₁ α S t => (t.root —[α]→ S) ∧ t.LocallyValid
  | node₂ α S l r => (l.root ∥ r.root —[α]→ S) ∧ l.LocallyValid ∧ r.LocallyValid

end ConstructionTree

variable (Ω Γ) in
/-- MauRen11 Definition 19 with the global constructor read as
`ConstructionTree.derivedChainStar`: local validity and the leaf/root
condition are the paper's, the binary child constructor is Definition 7's
left-first derived serial chain. -/
def SoundForDerivedChainStepwiseRefinement
    [Par Ω] [Mul Γ] [One Γ] [Par Γ] [HasReduction Ω Γ] : Prop :=
  ∀ t : ConstructionTree Ω Γ,
    t.LocallyValid → t.leavesPar —[t.derivedChainStar]→ t.root

variable (Ω Γ) in
/-- MauRen11 Definition 19 with the global constructor read as
`ConstructionTree.childParallelStar`, whose binary clause keeps the literal
child parallel printed in Appendix A. -/
def SoundForChildParallelStepwiseRefinement
    [Par Ω] [Mul Γ] [One Γ] [Par Γ] [HasReduction Ω Γ] : Prop :=
  ∀ t : ConstructionTree Ω Γ,
    t.LocallyValid → t.leavesPar —[t.childParallelStar]→ t.root

section Thm3

variable [Par Ω] [Mul Γ] [One Γ] [Par Γ] [HasReduction Ω Γ]

/-- MauRen11 Theorem 3, "if", for Appendix A's child-parallel constructor,
under an extra premise.

`red_par_par` combines two labelled reductions under the undressed constructor
parallel `α ∥ α'`.  Definition 7 derives only a serial-chain label, which
footnote 11 does not identify with `α ∥ α'`; footnote 23 is why a concrete
converter model can satisfy `red_par_par` without equating constructor
labels. -/
theorem soundForChildParallelStepwiseRefinement_of_isSeriallyComposable_of_red_par_par
    [IsSeriallyComposable Ω Γ]
    (red_par_par : ∀ {R R' S S' : Ω} {α α' : Γ},
      R —[α]→ S → R' —[α']→ S' →
        R ∥ R' —[α ∥ α']→ S ∥ S') :
    SoundForChildParallelStepwiseRefinement Ω Γ := by
  intro t
  induction t with
  | leaf R =>
    exact fun _ => red_one R
  | node₁ α S t ih =>
    rintro ⟨hα, ht⟩
    exact red_mul (ih ht) hα
  | node₂ α S l r ihl ihr =>
    rintro ⟨hα, hl, hr⟩
    exact red_mul (red_par_par (ihl hl) (ihr hr)) hα

/-- Child-parallel step-wise-refinement soundness implies MauRen11 Definition
7's general composability.

Leaf, nested-unary, and identity-root binary trees recover `red_one`,
`red_mul`, `red_par_one`, and `red_one_par`.  Unlike the derived-chain
converse, this needs neither `1 ∥ 1 = 1` nor a `red_par_par` premise. -/
theorem isGenerallyComposable_of_soundForChildParallelStepwiseRefinement
    (one_mul : ∀ α : Γ, 1 * α = α)
    (mul_one : ∀ α : Γ, α * 1 = α)
    (h : SoundForChildParallelStepwiseRefinement Ω Γ) :
    IsGenerallyComposable Ω Γ where
  red_one R := h (.leaf R) trivial
  red_mul {R S T α β} hRS hST := by
    have htree := h (.node₁ β T (.node₁ α S (.leaf R)))
      ⟨hST, hRS, trivial⟩
    simpa only [ConstructionTree.leavesPar,
      ConstructionTree.childParallelStar, ConstructionTree.root, mul_one]
      using htree
  red_par_one {R S α} T hRS := by
    have htree := h (.node₂ 1 (S ∥ T) (.node₁ α S (.leaf R)) (.leaf T))
      ⟨h (.leaf (S ∥ T)) trivial, ⟨hRS, trivial⟩, trivial⟩
    simpa only [ConstructionTree.leavesPar,
      ConstructionTree.childParallelStar, ConstructionTree.root, one_mul,
      mul_one] using htree
  red_one_par {R S α} T hRS := by
    have htree := h (.node₂ 1 (T ∥ S) (.leaf T) (.node₁ α S (.leaf R)))
      ⟨h (.leaf (T ∥ S)) trivial, trivial, hRS, trivial⟩
    simpa only [ConstructionTree.leavesPar,
      ConstructionTree.childParallelStar, ConstructionTree.root, one_mul,
      mul_one] using htree

/-- Child-parallel step-wise-refinement soundness entails reduction-level
parallel closure with the undressed constructor-parallel label.

The witness is an identity-root binary tree with two active unary children,
whose global label `1 * ((α * 1) ∥ (α' * 1))` normalizes by the two serial
neutrality equations alone.  No constructor-label equality is used. -/
theorem red_par_par_of_soundForChildParallelStepwiseRefinement
    (one_mul : ∀ α : Γ, 1 * α = α)
    (mul_one : ∀ α : Γ, α * 1 = α)
    (h : SoundForChildParallelStepwiseRefinement Ω Γ) :
    ∀ {R R' S S' : Ω} {α α' : Γ},
      R —[α]→ S → R' —[α']→ S' →
        R ∥ R' —[α ∥ α']→ S ∥ S' := by
  intro R R' S S' α α' hRS hR'S'
  have htree := h
    (.node₂ 1 (S ∥ S') (.node₁ α S (.leaf R)) (.node₁ α' S' (.leaf R')))
    ⟨h (.leaf (S ∥ S')) trivial, ⟨hRS, trivial⟩, hR'S', trivial⟩
  simpa only [ConstructionTree.leavesPar,
    ConstructionTree.childParallelStar, ConstructionTree.root, one_mul,
    mul_one] using htree

/-- MauRen11 Theorem 3 for Appendix A's child-parallel constructor.

Definition 7 yields only chain-labelled parallel reductions, so general
composability alone does not give soundness with the undressed label
`α ∥ α'`; the left side carries that closure rule explicitly.  The reverse
direction uses only the two serial neutrality equations. -/
theorem isGenerallyComposable_and_red_par_par_iff_soundForChildParallelStepwiseRefinement
    (one_mul : ∀ α : Γ, 1 * α = α)
    (mul_one : ∀ α : Γ, α * 1 = α) :
    (IsGenerallyComposable Ω Γ ∧
      ∀ {R R' S S' : Ω} {α α' : Γ},
        R —[α]→ S → R' —[α']→ S' →
          R ∥ R' —[α ∥ α']→ S ∥ S') ↔
      SoundForChildParallelStepwiseRefinement Ω Γ := by
  constructor
  · rintro ⟨hgc, red_par_par⟩
    letI : IsGenerallyComposable Ω Γ := hgc
    exact
      soundForChildParallelStepwiseRefinement_of_isSeriallyComposable_of_red_par_par
        red_par_par
  · intro h
    exact
      ⟨isGenerallyComposable_of_soundForChildParallelStepwiseRefinement
          one_mul mul_one h,
        red_par_par_of_soundForChildParallelStepwiseRefinement
          one_mul mul_one h⟩

/-- MauRen11 Theorem 3, "if", for the derived-chain constructor: general
composability implies `SoundForDerivedChainStepwiseRefinement`.

The paper's tree induction.  No equational law on `Γ` is needed:
`derivedChainStar` is exactly the constructor generated by Definition 7
(i)–(iii). -/
theorem soundForDerivedChainStepwiseRefinement_of_isGenerallyComposable
    [IsGenerallyComposable Ω Γ] :
    SoundForDerivedChainStepwiseRefinement Ω Γ := by
  intro t
  induction t with
  | leaf R => exact fun _ => red_one R
  | node₁ α S t ih =>
    rintro ⟨hα, ht⟩
    exact red_mul (ih ht) hα
  | node₂ α S l r ihl ihr =>
    rintro ⟨hα, hl, hr⟩
    exact red_mul (red_par_left_first (ihl hl) (ihr hr)) hα

/-- MauRen11 Theorem 3, "only if", for the derived-chain constructor:
`SoundForDerivedChainStepwiseRefinement` implies general composability.

Recovering Definition 7 (i)–(iii) needs the two serial neutrality equations
for `id` and, additionally, `1 ∥ 1 = 1`. -/
theorem isGenerallyComposable_of_soundForDerivedChainStepwiseRefinement
    (one_mul : ∀ α : Γ, 1 * α = α)
    (mul_one : ∀ α : Γ, α * 1 = α)
    (one_par_one : (1 : Γ) ∥ 1 = 1)
    (h : SoundForDerivedChainStepwiseRefinement Ω Γ) : IsGenerallyComposable Ω Γ where
  red_one R := h (.leaf R) trivial
  red_mul {R S T α β} hRS hST := by
    have := h (.node₁ β T (.node₁ α S (.leaf R))) ⟨hST, hRS, trivial⟩
    simp only [ConstructionTree.leavesPar, ConstructionTree.derivedChainStar,
      ConstructionTree.root,
      mul_one] at this
    exact this
  red_par_one {R S α} T hRS := by
    have := h (.node₂ 1 (S ∥ T) (.node₁ α S (.leaf R)) (.leaf T))
      ⟨h (.leaf (S ∥ T)) trivial, ⟨hRS, trivial⟩, trivial⟩
    simp only [ConstructionTree.leavesPar, ConstructionTree.derivedChainStar,
      ConstructionTree.root,
      one_mul, mul_one, one_par_one] at this
    exact this
  red_one_par {R S α} T hRS := by
    have := h (.node₂ 1 (T ∥ S) (.leaf T) (.node₁ α S (.leaf R)))
      ⟨h (.leaf (T ∥ S)) trivial, trivial, hRS, trivial⟩
    simp only [ConstructionTree.leavesPar, ConstructionTree.derivedChainStar,
      ConstructionTree.root,
      one_mul, mul_one, one_par_one] at this
    exact this

/-- MauRen11 Theorem 3 for the derived-chain constructor: general
composability is equivalent to `SoundForDerivedChainStepwiseRefinement`.

The reverse implication requires the two serial neutrality equations and
`1 ∥ 1 = 1`. -/
theorem isGenerallyComposable_iff_soundForDerivedChainStepwiseRefinement
    (one_mul : ∀ α : Γ, 1 * α = α)
    (mul_one : ∀ α : Γ, α * 1 = α)
    (one_par_one : (1 : Γ) ∥ 1 = 1) :
    IsGenerallyComposable Ω Γ ↔
      SoundForDerivedChainStepwiseRefinement Ω Γ :=
  ⟨fun _ => soundForDerivedChainStepwiseRefinement_of_isGenerallyComposable,
    isGenerallyComposable_of_soundForDerivedChainStepwiseRefinement
      one_mul mul_one one_par_one⟩

end Thm3

end AbstractCryptography
