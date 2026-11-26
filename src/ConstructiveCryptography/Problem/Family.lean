module

public import ConstructiveCryptography.Problem
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Uniform reductions between problem families

`Problem.Easier` chooses one solver transformation before the instances being compared.
`Easier.lowerBounds_subset` transports lower bounds in any preorder;
`Easier.isGLB_le` specializes this to greatest lower bounds, and
`Easier.worstCase_le` applies it to infima in a conditionally complete lattice.
Games instantiate these laws by taking solvers to be their admitted winning evaluations.

```text
infimum of source scores ≤ p G s ≤ q H (ρ s), for each target instance H
```

## References

1. U. Maurer, C. Portmann and J. Zhu. *Unifying Generic Group Models*.
   Cryptology ePrint Archive, Paper 2020/996, 2020.
-/

@[expose] public section

set_option autoImplicit false

namespace ConstructiveCryptography.Problem

universe u v w x y

/-- A uniform family reduction: [1, Definition 4, p. 6], "there exists a function α"
with `∀g₂ ∈ G₂, ∃g₁ ∈ G₁, g₂ ⟶ g₁`. The solver map is chosen before either instance. -/
def Easier
    -- `Instance` and `OtherInstance` index the source and target problems.
    {Instance : Type u} {OtherInstance : Type v}
    -- `Solver` and `OtherSolver` carry their solvers, including any admission restriction.
    {Solver : Type w} {OtherSolver : Type x}
    -- Ω carries performance values; `≤` compares their quality.
    {Ω : Type y} [LE Ω]
    -- `p G s` and `q H t` evaluate solvers on source instance `G` and target instance `H`.
    (p : Instance → Solver → Ω) (q : OtherInstance → OtherSolver → Ω)
    -- Each `H ∈ target` must have a comparison instance `G ∈ source` for every solver.
    (target : Set OtherInstance) (source : Set Instance) : Prop :=
  ∃ ρ : Solver → OtherSolver,
    ∀ H ∈ target, ∃ G ∈ source, ∀ s, p G s ≤ q H (ρ s)

/-- Worst-case performance is the infimum over a family of instances.
[1, Definition 2, p. 5]: "the worst-case game" has performance `inf_{g ∈ G} w_g(s)`. -/
noncomputable def worstCase
    -- `Instance` indexes the family and Ω contains its performance values.
    {Instance : Type u} {Ω : Type v} [InfSet Ω]
    (family : Set Instance) (performance : Instance → Ω) : Ω :=
  sInf (performance '' family)

/-- Every lower bound on source performances is a lower bound on the reduced target scores.
The same solver transformation witnesses all these inclusions. -/
lemma Easier.lowerBounds_subset
    -- `Instance`, `OtherInstance` index problems; `Solver`, `OtherSolver` carry solvers.
    {Instance : Type u} {OtherInstance : Type v}
    {Solver : Type w} {OtherSolver : Type x}
    -- Ω needs only the performance preorder; this law makes no choice of infimum.
    {Ω : Type y} [Preorder Ω]
    {p : Instance → Solver → Ω} {q : OtherInstance → OtherSolver → Ω}
    {target : Set OtherInstance} {source : Set Instance}
    (reduction : Easier p q target source) :
    ∃ ρ : Solver → OtherSolver, ∀ s,
      lowerBounds ((p · s) '' source) ⊆ lowerBounds ((q · (ρ s)) '' target) := by
  obtain ⟨ρ, reduces⟩ := reduction
  refine ⟨ρ, fun s => lowerBounds_mono_of_isCoinitialFor ?_⟩
  rintro _ ⟨H, member, rfl⟩
  obtain ⟨G, sourceMember, comparison⟩ := reduces H member
  exact ⟨p G s, ⟨G, sourceMember, rfl⟩, comparison s⟩

/-- A uniform family reduction compares greatest lower bounds of the performances.
This is [1, Lemma 3, p. 22], "G₂ ⊵ G₁ implies Ĝ₂ ⊵ Ĝ₁", stated with explicit infima. -/
theorem Easier.isGLB_le
    -- `Instance`, `OtherInstance` index problems; `Solver`, `OtherSolver` carry solvers.
    {Instance : Type u} {OtherInstance : Type v}
    {Solver : Type w} {OtherSolver : Type x}
    -- Ω needs only its performance preorder; the required infima are supplied below.
    {Ω : Type y} [Preorder Ω]
    {p : Instance → Solver → Ω} {q : OtherInstance → OtherSolver → Ω}
    {target : Set OtherInstance} {source : Set Instance}
    (reduction : Easier p q target source)
    -- `sourceInf s` and `targetInf t` are the respective solvers' worst-case performances.
    {sourceInf : Solver → Ω} {targetInf : OtherSolver → Ω}
    (sourceGLB : ∀ s, IsGLB ((p · s) '' source) (sourceInf s))
    (targetGLB : ∀ t, IsGLB ((q · t) '' target) (targetInf t)) :
    ∃ ρ : Solver → OtherSolver, ∀ s, sourceInf s ≤ targetInf (ρ s) := by
  obtain ⟨ρ, lowerBounds⟩ := reduction.lowerBounds_subset
  exact ⟨ρ, fun s => (targetGLB (ρ s)).2 (lowerBounds s (sourceGLB s).1)⟩

/-- A family reduction transports worst-case performance using the same solver map.
[1, Lemma 3, p. 22]: "G₂ ⊵ G₁ implies Ĝ₂ ⊵ Ĝ₁". -/
theorem Easier.worstCase_le
    -- `Instance`, `OtherInstance` index problems; `Solver`, `OtherSolver` carry solvers.
    {Instance : Type u} {OtherInstance : Type v}
    {Solver : Type w} {OtherSolver : Type x}
    -- Ω supplies the infimum of every nonempty family bounded below.
    {Ω : Type y} [ConditionallyCompleteLattice Ω]
    {p : Instance → Solver → Ω} {q : OtherInstance → OtherSolver → Ω}
    {target : Set OtherInstance} {source : Set Instance}
    (reduction : Easier p q target source)
    -- `inhabited` makes the target infimum meaningful; reduction supplies a source member.
    (inhabited : target.Nonempty)
    -- `bounded s` bounds all source scores for solver `s` from below.
    (bounded : ∀ s, BddBelow ((p · s) '' source)) :
    ∃ ρ : Solver → OtherSolver,
      ∀ s, worstCase source (p · s) ≤ worstCase target (q · (ρ s)) := by
  have sourceNonempty : source.Nonempty := by
    obtain ⟨H, member⟩ := inhabited
    obtain ⟨_, reduces⟩ := reduction
    obtain ⟨G, sourceMember, _⟩ := reduces H member
    exact ⟨G, sourceMember⟩
  obtain ⟨ρ, lowerBounds⟩ := reduction.lowerBounds_subset
  refine ⟨ρ, fun s => le_csInf (inhabited.image (q · (ρ s))) ?_⟩
  -- The source infimum is a lower bound; the reduction transports that lower bound.
  exact lowerBounds s (isGLB_csInf (sourceNonempty.image (p · s)) (bounded s)).1

end ConstructiveCryptography.Problem
