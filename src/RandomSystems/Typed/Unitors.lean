module

public import RandomSystems.Typed.Relabel
public import RandomSystems.Typed.InterfaceCoherence

/-!
# Unit converters

The unit interface has no ports. `leftUnitorHom A` forwards `(inr i, x)` to `(i, x)`;
`rightUnitorHom A` forwards `(inl i, x)` to `(i, x)`. Their inverses insert these tags.
All four are `TypedConverter.rename` with the existing domain equivalences.

Cancellation and naturality are in `RandomSystems.Typed.ConverterCoherence`.
`RandomSystems.Typed.Context` uses the inverses to project a parallel system, and
`ConstructiveCryptography.Instances.Monoidal` packages the same converters as isomorphisms.
-/

@[expose] public section

namespace SystemAlgebra.TypedConverter

open Interface

/-- Forward the `A` ports of `unit ⊗ A` to `A`, leaving each query and reply unchanged. -/
noncomputable def leftUnitorHom
    -- `A` carries the ports, message types and admitted histories retained by the renaming.
    (A : Interface) : TypedConverter (tensor unit A) A :=
  rename (Equiv.emptySum Empty A.I) (leftUnitAlphabet A.X) (leftUnitAlphabet A.Y)
    (leftUnitAlphabet_fst A.X) (leftUnitAlphabet_fst A.Y) (parallelDomain_unit_left A)

/-- Forward `(i, x)` on `A` to `(inr i, x)` on `unit ⊗ A`; remove `inr` from each reply. -/
noncomputable def leftUnitorInv (A : Interface) : TypedConverter A (tensor unit A) :=
  rename (Equiv.emptySum Empty A.I).symm (leftUnitAlphabet A.X).symm
    (leftUnitAlphabet A.Y).symm
    (alphabet_symm_label _ _ (leftUnitAlphabet_fst A.X))
    (alphabet_symm_label _ _ (leftUnitAlphabet_fst A.Y))
    (fun h => by
      have he := (parallelDomain_unit_left A (h.map (leftUnitAlphabet A.X).symm)).symm
      simpa only [List.map_map, Equiv.self_comp_symm, List.map_id] using he)

/-- Forward the `A` ports of `A ⊗ unit` to `A`, leaving each query and reply unchanged. -/
noncomputable def rightUnitorHom (A : Interface) : TypedConverter (tensor A unit) A :=
  rename (Equiv.sumEmpty A.I Empty) (rightUnitAlphabet A.X) (rightUnitAlphabet A.Y)
    (rightUnitAlphabet_fst A.X) (rightUnitAlphabet_fst A.Y) (parallelDomain_unit_right A)

/-- Forward `(i, x)` on `A` to `(inl i, x)` on `A ⊗ unit`; remove `inl` from each reply. -/
noncomputable def rightUnitorInv (A : Interface) : TypedConverter A (tensor A unit) :=
  rename (Equiv.sumEmpty A.I Empty).symm (rightUnitAlphabet A.X).symm
    (rightUnitAlphabet A.Y).symm
    (alphabet_symm_label _ _ (rightUnitAlphabet_fst A.X))
    (alphabet_symm_label _ _ (rightUnitAlphabet_fst A.Y))
    (fun h => by
      have he := (parallelDomain_unit_right A (h.map (rightUnitAlphabet A.X).symm)).symm
      simpa only [List.map_map, Equiv.self_comp_symm, List.map_id] using he)

end SystemAlgebra.TypedConverter
