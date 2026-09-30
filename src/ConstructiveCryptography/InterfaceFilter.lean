import ConstructiveCryptography.Interface

/-!
# Domain filters

A filter forwards the queries of an admitted history and stops on the others. The filter
admitting `D` on `A` is a converter from `A` restricted to `D` to `A`: the forwarding DDC of
the restricted domain, a DDC from `A`'s domain.
Source: CR18, §3.4.3 (printed p. 62).

## Main definitions

* `Interface.restrict A D`: the histories of `A`'s domain admitted by `D`
* `Interface.filter A D`: the filter admitting `D` on `A`
-/

namespace SystemAlgebra.Interface

/-- The histories of `A`'s domain admitted by `D`. -/
abbrev restrict (A : Interface) (D : List (Σ i, A.X i) → Prop)
    (hD : ∀ p h, p <+: h → D h → D p) : Interface where
  I := A.I
  X := A.X
  Y := A.Y
  domain h := A.domain h ∧ D h
  nonempty_prefix := ⟨fun hd => A.nonempty_prefix.1 hd.1,
    fun hp hne hd => ⟨A.nonempty_prefix.2 hp hne hd.1, hD _ _ hp hd.2⟩⟩
  bound := A.bound
  length_le h hd := A.length_le h hd.1

/-- **The filter** admitting `D` on `A`: it forwards the queries of an admitted history and
stops on the others. -/
noncomputable def filter (A : Interface) (D : List (Σ i, A.X i) → Prop)
    (hD : ∀ p h, p <+: h → D h → D p) : A.restrict D hD ⟶ A :=
  ofDDC
    (DDC.filter (Y := A.Y) (fun h => h = [] ∨ (A.restrict D hD).domain h)
      (prefix_or_nil (A.restrict D hD).nonempty_prefix.2)).1
    ((isDDCFrom_filter (A.restrict D hD).nonempty_prefix).inside_mono fun _ hd => hd.1)

end SystemAlgebra.Interface
