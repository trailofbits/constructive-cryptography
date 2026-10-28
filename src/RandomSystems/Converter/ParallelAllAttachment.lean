import RandomSystems.Converter.ParallelAll
import RandomSystems.System.ParallelWiring

/-!
# Locality of finite parallel attachment

Each converter interacts only with its corresponding resource. Explicit alphabet
regrouping identifies the parallel family of attachments with attachment of the two
parallel families. Jost, Thesis, printed p. 17: “A finite set of resources with disjoint
interface sets can be viewed as a single one.” The deterministic wiring proof needs only
component convergence; the stochastic specialization additionally chooses independence.
-/

namespace SystemAlgebra


variable {K : Type} {O J : K → Type} {U V : ∀ k, O k → Type} {X Y : ∀ k, J k → Type}
  {α : ∀ k, InsideOutsideSystem (O k) (J k) (U k) (V k) (X k) (Y k)} {b : K → ℕ}

open Classical in
/-- Componentwise attachment, before canonicalization, after explicit alphabet regrouping.
Jost's disjoint-interface view (Thesis, printed p. 17) gives the intended locality law;
convergence follows from each DDC's bounded internal interaction. -/
lemma apply_tensorAllRaw_parAll (hα : ∀ k, IsDDC (b k) (α k))
    (R : ∀ k, InterfaceSystem (J k) (X k) (Y k)) :
    apply (tensorAllRaw α)
      (relabel (parAll R) (Equiv.sigmaAssoc fun k j => X k j)
        (Equiv.sigmaAssoc fun k j => Y k j).symm) =
      relabel (parAll fun k => apply (α k) (R k))
        (Equiv.sigmaAssoc fun k o => U k o)
        (Equiv.sigmaAssoc fun k o => V k o).symm := by
  -- Regroup the converter and resource families into corresponding pairs.
  simp only [apply_eq, tensorAllRaw, pair_relabel, pair_parAll, interconnect_relabel]
  -- Each pair performs its own feedback exchange without changing the component tag.
  rw [parAll_interconnect_all (fun k => (hα k).converges_resource (R k)),
    relabel_interconnect]
  congr 1
  · funext z
    rcases z with ⟨k, ⟨(_ | ⟨⟨⟩⟩), z⟩⟩
    · rcases z with ⟨⟨(_ | ⟨⟨⟩⟩), i⟩, z⟩ <;> rfl
    · rcases z with ⟨i, z⟩; rfl

open Classical in
/-- Component tags and interface labels are both preserved by parallel replies. -/
lemma RepliesAtQueriedInterface.parallelAll
    {R : ∀ k, InterfaceSystem (J k) (X k) (Y k)}
    (hR : ∀ k, RepliesAtQueriedInterface (R k)) :
    RepliesAtQueriedInterface (SystemAlgebra.relabel (parAll R)
      (Equiv.sigmaAssoc fun k j => X k j)
      (Equiv.sigmaAssoc fun k j => Y k j).symm) := by
  -- The last query selects a component; its reply retains the local interface.
  intro h x y hy
  obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).mp hy
  obtain ⟨⟨k, j⟩, x⟩ := x
  simp only [List.map_append, List.map_singleton] at hv
  change v ∈ parAll R
    (h.map (Equiv.sigmaAssoc fun k j => X k j) ++ [⟨k, ⟨j, x⟩⟩]) at hv
  rw [parAll_snoc] at hv
  obtain ⟨z, hz, rfl⟩ := (Part.mem_map_iff _).mp hv
  exact congrArg (Sigma.mk k)
    (hR k (restrict k (h.map (Equiv.sigmaAssoc fun k j => X k j))) ⟨j, x⟩ z hz)

open Classical in
/-- Canonical n-ary attachment preserves the componentwise completed partial behavior. -/
lemma trim_apply_tensorAllL_parAll [_root_.Finite K]
    (hα : ∀ k, IsDDC (b k) (α k))
    {R : ∀ k, InterfaceSystem (J k) (X k) (Y k)}
    (hR : ∀ k, RepliesAtQueriedInterface (R k)) :
    trim (apply (tensorAllL α)
      (relabel (trim (parAll R)) (Equiv.sigmaAssoc fun k j => X k j)
        (Equiv.sigmaAssoc fun k j => Y k j).symm)) =
      relabel (trim (parAll fun k => trim (apply (α k) (R k))))
        (Equiv.sigmaAssoc fun k o => U k o)
        (Equiv.sigmaAssoc fun k o => V k o).symm := by
  let _ := Fintype.ofFinite K
  -- Remove the resource trim using behavioral congruence of attachment.
  have he := (EqOnReachable.rfl' (tensorAllL α)).apply
    ((trim_behEq (parAll R)).relabel (Equiv.sigmaAssoc fun k j => X k j)
      (Equiv.sigmaAssoc fun k j => Y k j).symm)
  have ht := he.trim_eq (by simp [SilentAtEmpty, apply_eq])
    (by simp [SilentAtEmpty, apply_eq])
  -- Canonicalization preserves valid exchanges; the raw locality law now applies.
  rw [ht, tensorAllL, trim_apply_canon (IsDDC.tensorAllL hα)
    (RepliesAtQueriedInterface.parallelAll hR), apply_tensorAllRaw_parAll hα,
    trim_relabel, trim_parAll_trim]

end SystemAlgebra
