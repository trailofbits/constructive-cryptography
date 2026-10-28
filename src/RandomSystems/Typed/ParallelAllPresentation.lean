import RandomSystems.Typed.ParallelAll
import RandomSystems.Cumulative.ParallelAllPresentation

/-!
# Deterministic presentations of typed finite parallel systems

The component DDS presentations combine by the tagged `parAll` rule, trim to canonical
reachable behavior, and regroup into the combined interface. Their independent probability
product presents `TypedSystem.parallelAll`.

Jost, Thesis, printed p. 17: “A finite set of resources with disjoint interface sets can be
viewed as a single one.” This construction keeps the component domains and chosen
independence law explicit.
-/

namespace SystemAlgebra.TypedSystem

open Probability Interface

variable {K : Type} [Fintype K] {A : K → Interface}

/-- A family of deterministic component resources combines into a deterministic resource
on the n-ary interface. Jost, Thesis, printed p. 17, treats finite disjoint-interface
families as one resource; this proof preserves each component's input domain. -/
lemma parallelAll_system_valid
    (s : ∀ k, {t : InterfaceSystem (A k).I (A k).X (A k).Y //
      IsDDS t ∧ RepliesAtQueriedInterface t ∧ ∀ h, (t h).Dom ↔ (A k).domain h}) :
    let r := relabel (trim (parAll (fun k => (s k).1)))
      (Equiv.sigmaAssoc fun k i => (A k).X i)
      (Equiv.sigmaAssoc fun k i => (A k).Y i).symm
    IsDDS r ∧ RepliesAtQueriedInterface r ∧
      ∀ h, (r h).Dom ↔ (tensorAll A).domain h := by
  let xAssoc := Equiv.sigmaAssoc fun k i => (A k).X i
  let yAssoc := (Equiv.sigmaAssoc fun k i => (A k).Y i).symm
  let S := parAll fun k => (s k).1
  change IsDDS (relabel (trim S) xAssoc yAssoc) ∧
    RepliesAtQueriedInterface (relabel (trim S) xAssoc yAssoc) ∧ _
  refine ⟨?_, ?_, ?_⟩
  · -- Trim canonicalizes reachability before the interface regrouping.
    rw [← trim_relabel]
    exact SilentAtEmpty.isDDS_trim (by simp [SilentAtEmpty, relabel, S])
  · -- A component reply retains both its family tag and local port label.
    intro h x y hy
    change y ∈ (trim S ((h ++ [x]).map xAssoc)).map yAssoc at hy
    obtain ⟨z, hz, hzy⟩ := (Part.mem_map_iff _).mp hy
    simp only [List.map_append, List.map_singleton] at hz
    rw [trim] at hz
    split_ifs at hz with hr
    · obtain ⟨⟨k, i⟩, a⟩ := x
      change z ∈ parAll (fun k => (s k).1)
        (h.map xAssoc ++ [⟨k, ⟨i, a⟩⟩]) at hz
      rw [parAll_snoc] at hz
      obtain ⟨w, hw, hzw⟩ := (Part.mem_map_iff _).mp hz
      subst z
      subst y
      have hi := (s k).2.2.1 (restrict k (h.map xAssoc)) ⟨i, a⟩ w hw
      exact congrArg (Sigma.mk k) hi
    · simp at hz
  · -- The trimmed joint domain is exactly the componentwise input domain.
    intro h
    change (trim S (h.map xAssoc)).Dom ↔ (tensorAll A).domain h
    rw [trim_parAll_dom (fun k => (s k).2.1)]
    change (h.map xAssoc ≠ [] ∧
        ∀ k, restrict k (h.map xAssoc) = [] ∨
          ((s k).1 (restrict k (h.map xAssoc))).Dom) ↔
      h ≠ [] ∧ ∀ k, restrict k (h.map xAssoc) = [] ∨
        (A k).domain (restrict k (h.map xAssoc))
    have hnonempty : h.map xAssoc ≠ [] ↔ h ≠ [] := by
      cases h <;> simp
    rw [hnonempty]
    exact and_congr_right fun _ => forall_congr' fun k =>
      or_congr Iff.rfl ((s k).2.2.2 _)

open Classical in
/-- Independent component PDSs present a PDS on the tagged n-ary interface.
Jost, Thesis, printed p. 17: “A finite set of resources with disjoint interface sets can be
viewed as a single one.” The product distribution records the additional independence choice. -/
noncomputable def parallelAllPDS [DecidableEq K]
    (P : ∀ k, Distribution.ProbDist {s : InterfaceSystem (A k).I (A k).X (A k).Y //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ (A k).domain h}) :
    Distribution.ProbDist {r : InterfaceSystem (tensorAll A).I (tensorAll A).X
        (tensorAll A).Y //
      IsDDS r ∧ RepliesAtQueriedInterface r ∧
        ∀ h, (r h).Dom ↔ (tensorAll A).domain h} :=
  ⟨Distribution.fTransform (fun s =>
      ⟨relabel (trim (parAll (fun k => (s k).1)))
        (Equiv.sigmaAssoc fun k i => (A k).X i)
        (Equiv.sigmaAssoc fun k i => (A k).Y i).symm,
       parallelAll_system_valid s⟩)
      (Distribution.piDep (fun k => (P k).1)),
    Distribution.fTransform_isProbDist _
      (Distribution.piDep_isProbDist (fun k => (P k).2))⟩

open Classical in
/-- The independent parallel behavior has the transcript law of `parallelAllPDS`.
Jost, Thesis, printed p. 17: “A finite set of resources with disjoint interface sets can be
viewed as a single one.” Here the component laws are independently sampled. -/
lemma parallelAll_ofPDS [DecidableEq K]
    (P : ∀ k, Distribution.ProbDist {s : InterfaceSystem (A k).I (A k).X (A k).Y //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ (A k).domain h}) :
    parallelAll (fun k => ofPDS (P k)) = ofPDS (parallelAllPDS P) := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [parallelAll_mass, RandomSystem.parallelAll_mass_of_presentations
    (fun k => (ofPDS (P k)).1) (fun k => (P k).1)
    (fun k i => (i : {s : InterfaceSystem (A k).I (A k).X (A k).Y //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧
        ∀ h, (s h).Dom ↔ (A k).domain h}).1) (fun _ _ => rfl)]
  change _ = behaviorMass _ _ _
  simp only [behaviorMass, parallelAllPDS, Distribution.mass_fTransform]
  symm
  apply Distribution.mass_congr
  intro s
  rw [replies_relabel_iff, replies_trim_iff]
  simp only [Equiv.symm_symm]

end SystemAlgebra.TypedSystem
