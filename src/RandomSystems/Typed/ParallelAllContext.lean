module

public import RandomSystems.Typed.Context
public import RandomSystems.Typed.ParallelAllAttachment

/-!
# Isolating one component of a finite parallel family

`TypedConverter.parallelAllContext R k` supplies the fixed systems `R j` at every component
except `k`, where it forwards queries to its inside system `S`. Its exact attachment law is

  `parallelAllContext R k • S = ∥ j, Function.update R k S j`.

Each fixed component retains its state through `ofSystem`; the parallel converter family
supplies the independence.
The component at `k` remains the same inside system throughout the interaction. This is the
finite-family context needed to transport a bound on the changed component through an assembly.
A selected feasible class must explicitly admit this domain-preserving converter.

```text
outside family                   converter                           inside
j ≠ k : query ──────────► ofSystem (R j), retained own state
            reply ◄─────
k : query     ──────────► id (A k) ── explicit renaming ──────────► S
            reply ◄───────────────────────────────────────────────
```

`Interface.singleFamily A k` puts `A` at `k` and the existing unit interface everywhere else.
`Interface.singleFamilyAlphabet` removes the sole active tag, preserving local ports and values;
`Interface.singleFamily_domain` proves the corresponding domain equation, including the empty
history. Thus `TypedConverter.singleFamily` is an explicit renaming to this family.
`TypedSystem.parallelAll_singleFamily_mass` reduces its product mass to the active factor,
which proves `TypedConverter.singleFamily_smul`. Finally, `parallelAll_attach` from
`Typed.ParallelAllAttachment` attaches the family of identity and fixed-system converters;
`identity_attach` and `attach_ofSystem` give `TypedConverter.parallelAllContext_smul`.

[1, p. 17] views a “finite set of resources with disjoint interface sets” as one system and
introduces the dummy resource with empty interfaces. The renaming here makes that unit wiring
explicit on tagged, typed interfaces. The “composition order independence” of
[1, Proposition 2.2.3, p. 18] gives attachment locality. Here its finite-family form is the
existing law `(⨂ₘ j, c j) • (∥ j, T j) = ∥ j, c j • T j`, `TypedConverter.parallelAll_attach`.

## References

1. D. Jost. *On Generalizations of Composable Security*. Doctoral thesis,
   Diss. ETH No. 26723, ETH Zurich, 2020.
-/

@[expose] public section

namespace SystemAlgebra

open scoped SystemAlgebra

-- `K` names the family components; equality selects its single active component.
variable {K : Type} [DecidableEq K]

section SingleFamily

-- `A` is the active interface; `k` selects its tag in the family.
variable (A : Interface) (k : K)

/-- The family with interface `A` at index `k` and no ports at every other index. -/
abbrev Interface.singleFamily
    -- `j` selects the member: it is active exactly when `j = k`.
    (j : K) : Interface :=
  if j = k then A else Interface.unit

/-- The selected component has the original interface `A`. -/
lemma Interface.singleFamily_self : Interface.singleFamily A k k = A := ite_eq_left rfl

/-- Every other component has the empty unit interface. -/
lemma Interface.singleFamily_of_ne
    -- `j` selects an inactive component, as certified by `hj`.
    (j : K) (hj : j ≠ k) : Interface.singleFamily A k j = Interface.unit := ite_eq_right hj

/-- Remove the active tag from a field of the single-active-component family. Inactive components
carry no values of that field. -/
def Interface.singleFamilyEquiv
    -- `F` selects a field of an interface; the unit interface has no values of this field.
    (F : Interface → Type)
    [IsEmpty (F Interface.unit)] : (Σ j, F (Interface.singleFamily A k j)) ≃ F A where
  toFun p := by
    rcases p with ⟨j, x⟩
    by_cases h : j = k
    · simpa only [Interface.singleFamily, h, ite_true] using x
    · exact isEmptyElim (show F Interface.unit from by
        simpa only [Interface.singleFamily, h, ite_false] using x)
  invFun x := ⟨k, by simpa only [Interface.singleFamily, ite_true] using x⟩
  left_inv := by
    rintro ⟨j, x⟩
    by_cases h : j = k
    · subst j
      simp only [↓reduceDIte, eq_mpr_eq_cast, eq_mp_eq_cast, cast_cast, cast_eq]
    · exact isEmptyElim (show F Interface.unit from by
        simpa only [Interface.singleFamily, h, ite_false] using x)
  right_inv x := by simp only [↓reduceDIte, eq_mpr_eq_cast, eq_mp_eq_cast, cast_cast, cast_eq]

/-- Remove the active component tag, keeping the local port and its value. -/
def Interface.singleFamilyAlphabet
    -- `F B i` selects the value type at port `i` of `B`, for queries or for replies.
    (F : (B : Interface) → B.I → Type) :
    (Σ l : (Σ j, (Interface.singleFamily A k j).I), F (Interface.singleFamily A k l.1) l.2) ≃
      (Σ i, F A i) :=
  (Equiv.sigmaAssoc fun j i => F (Interface.singleFamily A k j) i).trans
    (Interface.singleFamilyEquiv A k (fun B => Σ i, F B i))

/-- Removing the component tag preserves the local port selected by the alphabet equivalence. -/
lemma Interface.singleFamilyAlphabet_fst
    -- `F B i` selects the value type at port `i` of `B`, for queries or for replies.
    (F : (B : Interface) → B.I → Type)
    -- `x` is a value at a tagged family port; its label must follow the same renaming.
    (x : Σ l : (Σ j, (Interface.singleFamily A k j).I), F (Interface.singleFamily A k l.1) l.2) :
    (Interface.singleFamilyAlphabet A k F x).1 =
      Interface.singleFamilyEquiv A k Interface.I x.1 := by
  rcases x with ⟨⟨j, i⟩, x⟩
  by_cases h : j = k
  · subst j
    simp only [Interface.singleFamilyAlphabet, Equiv.trans_apply, Interface.singleFamilyEquiv,
      Equiv.coe_fn_mk, Equiv.sigmaAssoc, ↓reduceDIte, eq_mp_eq_cast]
    -- Transporting an interface transports both its local port and its complete alphabet.
    have cast_fst {B C : Interface} (e : B = C) (z : Σ i, F B i) :
        (cast (congrArg (fun B => Σ i, F B i) e) z).1 =
          cast (congrArg Interface.I e) z.1 := by
      cases e
      rfl
    exact cast_fst (Interface.singleFamily_self A k) ⟨i, x⟩
  · exact isEmptyElim (show Empty from by
      simpa only [Interface.singleFamily, h, ite_false] using i)

/-- Projecting an embedded history to the active component retains every value. -/
lemma Interface.restrict_map_singleFamilyEquiv_symm
    -- `F` selects a field of an interface; the unit interface has no values of this field.
    (F : Interface → Type)
    [IsEmpty (F Interface.unit)]
    -- `h` is the original history on `A`, before adding the active tag.
    (h : List (F A)) :
    restrict k (h.map (Interface.singleFamilyEquiv A k F).symm) =
      h.map (cast (congrArg F
        (show A = Interface.singleFamily A k k from (Interface.singleFamily_self A k).symm))) := by
  induction h with
  | nil => rfl
  | cons x h ih =>
    change restrict k (⟨k, _⟩ :: h.map (Interface.singleFamilyEquiv A k F).symm) = _
    rw [restrict_cons_self, ih]
    rfl

/-- An embedded history has no values at an inactive component. -/
lemma Interface.restrict_map_singleFamilyEquiv_symm_of_ne
    -- `j` is inactive by `hj`; projection to it must be empty.
    (j : K) (hj : j ≠ k)
    -- `F` selects a field of an interface; the unit interface has no values of this field.
    (F : Interface → Type) [IsEmpty (F Interface.unit)]
    -- `h` is the original history on `A`, before adding the active tag.
    (h : List (F A)) :
    restrict j (h.map (Interface.singleFamilyEquiv A k F).symm) = [] := by
  induction h with
  | nil => rfl
  | cons x h ih =>
    change restrict j (⟨k, _⟩ :: h.map (Interface.singleFamilyEquiv A k F).symm) = _
    rw [restrict_cons_ne hj.symm, ih]

-- Finite `K` supplies the interface product and its independent product law.
variable [Fintype K]

/-- The single-active-component family admits exactly the histories embedded from `A`'s domain. -/
lemma Interface.singleFamily_domain
    -- `h` is the query history on the active interface before adding its component tag.
    (h : List (Σ i, A.X i)) :
    (⨂ j, Interface.singleFamily A k j).domain
      (h.map (Interface.singleFamilyAlphabet A k Interface.X).symm) ↔ A.domain h := by
  -- Undo the alphabet flattening: the regrouped history consists only of active tags.
  have hregroup : (h.map (Interface.singleFamilyAlphabet A k Interface.X).symm).map
      (Equiv.sigmaAssoc fun j i => (Interface.singleFamily A k j).X i) =
      h.map (Interface.singleFamilyEquiv A k (fun B => Σ i, B.X i)).symm := by
    rw [List.map_map]
    rfl
  -- The active projection is the original history, transported through the interface equality.
  have hk : (Interface.singleFamily A k k).domain
      (restrict k (h.map (Interface.singleFamilyEquiv A k (fun B => Σ i, B.X i)).symm)) ↔
        A.domain h := by
    rw [Interface.restrict_map_singleFamilyEquiv_symm]
    have cast_domain {B C : Interface} (e : B = C) (xs : List (Σ i, B.X i)) :
        C.domain (xs.map (cast (congrArg (fun B => Σ i, B.X i) e))) ↔ B.domain xs := by
      cases e
      exact (congrArg B.domain (List.map_id xs)).to_iff
    exact cast_domain (Interface.singleFamily_self A k).symm h
  change parallelAllInputs (fun j => (Interface.singleFamily A k j).domain)
    (h.map (Interface.singleFamilyAlphabet A k Interface.X).symm) ↔ _
  simp only [parallelAllInputs, hregroup, ne_eq, List.map_eq_nil_iff]
  constructor
  · -- A nonempty admitted family history has an admitted active projection.
    rintro ⟨hne, hd⟩
    apply hk.mp
    exact (hd k).resolve_left (by
      rw [Interface.restrict_map_singleFamilyEquiv_symm, List.map_eq_nil_iff]
      exact hne)
  · -- An admitted active history gives the active domain; every other projection is empty.
    intro hd
    refine ⟨fun he => A.nonempty_prefix.1 (he ▸ hd), fun j => ?_⟩
    by_cases hj : j = k
    · subst j
      exact Or.inr (hk.mpr hd)
    · exact Or.inl (Interface.restrict_map_singleFamilyEquiv_symm_of_ne A k j hj
        (fun B => Σ i, B.X i) h)

/-- Put `S` at component `k` and `TypedSystem.dummy` at every other component. -/
noncomputable def TypedSystem.singleFamily
    -- `S` supplies the active component; `j` selects the returned member of the family.
    (S : TypedSystem A) (j : K) :
    TypedSystem (Interface.singleFamily A k j) := by
  by_cases h : j = k
  · simpa only [Interface.singleFamily, h, ite_true] using S
  · simpa only [Interface.singleFamily, h, ite_false] using TypedSystem.dummy

/-- The single-active-component family has `S`'s mass on an embedded transcript.
Every inactive component sees the empty transcript and contributes the factor one. -/
lemma TypedSystem.parallelAll_singleFamily_mass
    -- `S` is the active system; `h` is its original transcript before adding the tag.
    (S : TypedSystem A)
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i))) :
    (∥ j, TypedSystem.singleFamily A k S j).1
      (h.map ((Interface.singleFamilyAlphabet A k Interface.X).symm.prodCongr
        (Interface.singleFamilyAlphabet A k Interface.Y).symm)) = S.1 h := by
  classical
  let eX := Interface.singleFamilyEquiv A k (fun B => Σ i, B.X i)
  let eY := Interface.singleFamilyEquiv A k (fun B => Σ i, B.Y i)
  let h' := h.map (eX.symm.prodCongr eY.symm)
  rw [TypedSystem.parallelAll_mass]
  change RandomSystem.parallelAll (fun j => (TypedSystem.singleFamily A k S j).1)
    (h.map ((Interface.singleFamilyAlphabet A k Interface.X).symm.prodCongr
      (Interface.singleFamilyAlphabet A k Interface.Y).symm) |>.map
        ((Equiv.sigmaAssoc fun j i => (Interface.singleFamily A k j).X i).prodCongr
          (Equiv.sigmaAssoc fun j i => (Interface.singleFamily A k j).Y i))) = _
  rw [List.map_map]
  change RandomSystem.parallelAll (fun j => (TypedSystem.singleFamily A k S j).1) h' = _
  -- Every embedded exchange carries the active component tag on both query and reply.
  have hc : RandomSystem.parallelAllConsistent h' := by
    intro z hz
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
    rfl
  rw [RandomSystem.parallelAll_mass, ite_eq_left hc]
  -- Inactive components see no exchanges and therefore contribute unit mass.
  have hother (j : K) (hj : j ≠ k) : RandomSystem.restrictExchanges j h' = [] := by
    clear hc
    induction h with
    | nil => rfl
    | cons z h ih =>
      change RandomSystem.restrictExchanges j ((⟨k, _⟩, ⟨k, _⟩) :: _) = []
      rw [RandomSystem.restrictExchanges_cons_of_ne hj.symm]
      exact ih
  rw [Finset.prod_eq_single k (fun j _ hj => by rw [hother j hj, RandomSystem.mass_nil])
    (fun hn => False.elim (hn (Finset.mem_univ k)))]
  -- The active projection retains every exchange; transport back to the original interface.
  let e : A = Interface.singleFamily A k k := (Interface.singleFamily_self A k).symm
  have hselected : RandomSystem.restrictExchanges k h' = h.map
      ((Equiv.cast (congrArg (fun B => Σ i, B.X i) e)).prodCongr
        (Equiv.cast (congrArg (fun B => Σ i, B.Y i) e))) := by
    clear hc hother
    induction h with
    | nil => rfl
    | cons z h ih =>
      change RandomSystem.restrictExchanges k ((⟨k, _⟩, ⟨k, _⟩) :: _) = _
      rw [RandomSystem.restrictExchanges_cons_self, ih]
      rfl
  rw [hselected]
  -- Casting the system and its transcript along the same interface equality preserves mass.
  have cast_mass {B C : Interface} (e : B = C) (R : TypedSystem B)
      (xs : List ((Σ i, B.X i) × (Σ i, B.Y i))) :
      (cast (congrArg TypedSystem e) R).1 (xs.map
        ((Equiv.cast (congrArg (fun B => Σ i, B.X i) e)).prodCongr
          (Equiv.cast (congrArg (fun B => Σ i, B.Y i) e)))) = R.1 xs := by
    cases e
    exact congrArg R.1 (List.map_id xs)
  simpa only [TypedSystem.singleFamily, ↓reduceDIte, eq_mpr_eq_cast] using cast_mass e S h

/-- Expose `A` as the family with one active component at `k`, using explicit port/alphabet
bijections and their domain equation. Each outside query makes one inside call at its local port;
the reply is retagged at `k`. The renaming retains no state. -/
noncomputable def TypedConverter.singleFamily :
    TypedConverter (⨂ j, Interface.singleFamily A k j) A :=
  TypedConverter.rename (Interface.singleFamilyEquiv A k Interface.I)
    (Interface.singleFamilyAlphabet A k Interface.X)
    (Interface.singleFamilyAlphabet A k Interface.Y)
    (Interface.singleFamilyAlphabet_fst A k Interface.X)
    (Interface.singleFamilyAlphabet_fst A k Interface.Y)
    (fun h => by
      -- Inactive tags have no ports, so inverse renaming embeds every family history.
      have hd := Interface.singleFamily_domain A k
        (h.map (Interface.singleFamilyAlphabet A k Interface.X))
      rw [List.map_map] at hd
      simpa only [Equiv.symm_comp_self, List.map_id] using hd.symm)

/-- The single-active-component family renaming exposes `S` at `k` and empty systems elsewhere. -/
lemma TypedConverter.singleFamily_smul
    -- `S` is the original inside system, retained throughout the interaction.
    (S : TypedSystem A) :
    TypedConverter.singleFamily A k • S = ∥ j, TypedSystem.singleFamily A k S j := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [TypedConverter.singleFamily, TypedConverter.rename_mass]
  -- The renaming uses the component-tag bijection on queries and replies.
  let e := (Interface.singleFamilyAlphabet A k Interface.X).prodCongr
    (Interface.singleFamilyAlphabet A k Interface.Y)
  -- The inverse alphabet maps cancel, leaving the active system's transcript probability.
  have hm := TypedSystem.parallelAll_singleFamily_mass A k S (h.map e)
  change (∥ j, TypedSystem.singleFamily A k S j).1 ((h.map e).map e.symm) = S.1 (h.map e) at hm
  rw [List.map_map] at hm
  simpa only [Equiv.symm_comp_self, List.map_id] using hm.symm

end SingleFamily

-- Finite `K` supplies the interface product and its independent product law.
variable [Fintype K]

/-- At `k`, use identity; at `j ≠ k`, supply `R j` through `ofSystem`. The latter retains
`R j`'s state and makes no inside calls. Parallel composition keeps the components independent. -/
noncomputable def TypedConverter.parallelAllContextFamily
    -- `A j` fixes each component's interface; `R j` supplies the fixed system when `j ≠ k`.
    {A : K → Interface} (R : ∀ j, TypedSystem (A j)) (k : K)
    -- `j` selects the returned converter, whose inside interface is active only at `k`.
    (j : K) : TypedConverter (A j) (Interface.singleFamily (A k) k j) := by
  by_cases h : j = k
  · subst j
    simpa only [Interface.singleFamily, ite_true] using TypedConverter.id (A k)
  · simpa only [Interface.singleFamily, h, ite_false] using TypedConverter.ofSystem (R j)

/-- A query at `j ≠ k` is answered by the retained fixed system `R j`, with no inside call.
A query at `k` makes one inside call and returns its reply. The domain is the original family
of component domains, and the fixed components have independent randomness. -/
noncomputable def TypedConverter.parallelAllContext
    -- `A j` fixes the ports, alphabets and domain of each component.
    {A : K → Interface}
    -- `R j` supplies the fixed components for `j ≠ k`; the value `R k` is unused.
    -- `k` selects the component left open for the inside system.
    (R : ∀ j, TypedSystem (A j)) (k : K) : TypedConverter (⨂ j, A j) (A k) :=
  TypedConverter.comp (⨂ₘ j, TypedConverter.parallelAllContextFamily R k j)
    (TypedConverter.singleFamily (A k) k)

/-- Isolating `k` and attaching `S` gives exactly the family with that component replaced. -/
theorem TypedConverter.parallelAllContext_smul
    -- `A j` fixes the ports, alphabets and domain of each component.
    {A : K → Interface}
    -- `R j` is the fixed component on `A j`; `k` selects the component left open.
    (R : ∀ j, TypedSystem (A j)) (k : K)
    -- `S` is the replacement system connected at the selected component.
    (S : TypedSystem (A k)) :
    TypedConverter.parallelAllContext R k • S = ∥ j, Function.update R k S j := by
  -- Distribute the family converters over the independent single-active-component family system.
  rw [TypedConverter.parallelAllContext, TypedConverter.comp_smul, TypedConverter.singleFamily_smul,
    TypedConverter.parallelAll_attach]
  congr 1
  funext j
  -- The explicit interface transports in both factors cancel under attachment.
  have cast_attach {B C D : Interface} (e : C = D) (α : TypedConverter B C)
      (T : TypedSystem C) :
      cast (congrArg (TypedConverter B) e) α • cast (congrArg TypedSystem e) T = α • T := by
    cases e
    rfl
  by_cases hj : j = k
  · -- At the selected component, identity leaves `S` unchanged.
    subst j
    simp only [TypedConverter.parallelAllContextFamily, ↓reduceDIte, TypedSystem.singleFamily,
      Function.update_self, eq_mpr_eq_cast]
    rw [cast_attach (show A k = Interface.singleFamily (A k) k k from
      (Interface.singleFamily_self (A k) k).symm),
      TypedConverter.identity_attach]
  · -- At every other component, `ofSystem` supplies its fixed retained system `R j`.
    simp only [TypedConverter.parallelAllContextFamily, hj, ↓reduceDIte, TypedSystem.singleFamily,
      Function.update_of_ne hj, eq_mpr_eq_cast]
    rw [cast_attach (show Interface.unit = Interface.singleFamily (A k) k j from
      (Interface.singleFamily_of_ne (A k) k j hj).symm), TypedConverter.attach_ofSystem]

end SystemAlgebra
