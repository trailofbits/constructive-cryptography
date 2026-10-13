import RandomSystems.Typed.SystemParallel

/-!
# Regrouping parallel typed systems

Regrouping three parallel typed systems leaves each component history unchanged, so by
independence the probabilities agree. The dummy system, on the unit interface, has only its
empty transcript, so beside a typed system it leaves the probabilities unchanged. Exchanging the
two components of a parallel composition exchanges the labels of its transcripts.

## Main definitions

* `TypedSystem.dummy`: the typed system on the unit interface

## Main results

* `TypedSystem.parallel_assoc_mass`: regrouping three parallel typed systems keeps the
  probabilities of the regrouped transcripts
* `TypedSystem.parallel_unit_left_mass`, `TypedSystem.parallel_unit_right_mass`: the dummy
  system beside a typed system keeps its probabilities
* `TypedSystem.parallel_swap_mass`: exchanging the two components exchanges the labels
-/

namespace SystemAlgebra

open Classical Probability Interface

lemma Interface.parallel_system_assoc {A B C : Interface}
    (a : InterfaceSystem A.I A.X A.Y) (b : InterfaceSystem B.I B.X B.Y) (c : InterfaceSystem C.I C.X C.Y) :
    relabel (pair (relabel (pair a b) (sumAlphabet (Sum.rec A.X B.X)).symm
      (sumAlphabet (Sum.rec A.Y B.Y))) c)
      (sumAlphabet (Sum.rec (Sum.rec A.X B.X) C.X)).symm
      (sumAlphabet (Sum.rec (Sum.rec A.Y B.Y) C.Y)) =
    relabel (relabel (pair a (relabel (pair b c) (sumAlphabet (Sum.rec B.X C.X)).symm
      (sumAlphabet (Sum.rec B.Y C.Y))))
      (sumAlphabet (Sum.rec A.X (Sum.rec B.X C.X))).symm
      (sumAlphabet (Sum.rec A.Y (Sum.rec B.Y C.Y))))
      (assocAlphabet A.X B.X C.X) (assocAlphabet A.Y B.Y C.Y).symm := by
  simp only [pair_relabel_left, pair_relabel_right, relabel_relabel]
  rw [pair_assoc, relabel_relabel]
  congr 1
  · funext z
    rcases z with ⟨((i | j) | k), z⟩ <;> rfl
  · funext z
    rcases z with ⟨(_ | ⟨⟨⟩⟩), z⟩
    · rfl
    · rcases z with ⟨(_ | ⟨⟨⟩⟩), z⟩ <;> rfl

namespace TypedSystem

lemma parallel_mass_of_presentations_raw {A B : Interface} {ι κ : Type}
    (R : TypedSystem A) (S : TypedSystem B) (P : Distribution ι) (Q : Distribution κ)
    (s : ι → InterfaceSystem A.I A.X A.Y) (t : κ → InterfaceSystem B.I B.X B.Y)
    (hR : ∀ h, R.1 h = P.mass (fun i => Replies (s i) (h.map Prod.fst) (h.map Prod.snd)))
    (hS : ∀ h, S.1 h = Q.mass (fun i => Replies (t i) (h.map Prod.fst) (h.map Prod.snd)))
    (h : List ((Σ i, (tensor A B).X i) × (Σ i, (tensor A B).Y i))) :
    (parallel R S).1 h = (Distribution.prod P Q).mass (fun st =>
      Replies (relabel (pair (s st.1) (t st.2))
        (sumAlphabet (Sum.rec A.X B.X)).symm (sumAlphabet (Sum.rec A.Y B.Y)))
        (h.map Prod.fst) (h.map Prod.snd)) := by
  rw [parallel_mass_of_presentations R S P Q s t hR hS]
  exact Distribution.mass_congr _
    (fun _ => by rw [replies_relabel_iff, replies_relabel_iff, replies_trim_iff])

lemma parallel_assoc_mass_of_presentations {A B C : Interface} {ι κ ν : Type}
    (R : TypedSystem A) (S : TypedSystem B) (T : TypedSystem C)
    (P : Distribution ι) (Q : Distribution κ) (U : Distribution ν)
    (s : ι → InterfaceSystem A.I A.X A.Y) (t : κ → InterfaceSystem B.I B.X B.Y) (u : ν → InterfaceSystem C.I C.X C.Y)
    (hR : ∀ h, R.1 h = P.mass (fun i => Replies (s i) (h.map Prod.fst) (h.map Prod.snd)))
    (hS : ∀ h, S.1 h = Q.mass (fun i => Replies (t i) (h.map Prod.fst) (h.map Prod.snd)))
    (hT : ∀ h, T.1 h = U.mass (fun i => Replies (u i) (h.map Prod.fst) (h.map Prod.snd)))
    (h : List ((Σ i, (tensor (tensor A B) C).X i) × (Σ i, (tensor (tensor A B) C).Y i))) :
    (parallel (parallel R S) T).1 h = (parallel R (parallel S T)).1
      (h.map ((assocAlphabet A.X B.X C.X).prodCongr (assocAlphabet A.Y B.Y C.Y))) := by
  rw [parallel_mass_of_presentations_raw (parallel R S) T _ _ _ _
    (parallel_mass_of_presentations_raw R S P Q s t hR hS) hT,
    parallel_mass_of_presentations_raw R (parallel S T) _ _ _ _ hR
      (parallel_mass_of_presentations_raw S T Q U t u hS hT)]
  rw [← Distribution.fTransform_assoc_prod P Q U, Distribution.mass_fTransform]
  apply Distribution.mass_congr
  intro p
  rw [parallel_system_assoc, replies_relabel_iff]
  rfl

lemma parallel_assoc_mass {A B C : Interface} (R : TypedSystem A) (S : TypedSystem B)
    (T : TypedSystem C)
    (h : List ((Σ i, (tensor (tensor A B) C).X i) × (Σ i, (tensor (tensor A B) C).Y i))) :
    (parallel (parallel R S) T).1 h = (parallel R (parallel S T)).1
      (h.map ((assocAlphabet A.X B.X C.X).prodCongr (assocAlphabet A.Y B.Y C.Y))) := by
  obtain ⟨P, rfl⟩ := R.exists_ofPDS
  obtain ⟨Q, rfl⟩ := S.exists_ofPDS
  obtain ⟨U, rfl⟩ := T.exists_ofPDS
  exact parallel_assoc_mass_of_presentations _ _ _ P.1 Q.1 U.1 Subtype.val Subtype.val Subtype.val
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) h

/-- The empty interface family has no possible input or output. -/
noncomputable def dummy : TypedSystem unit :=
  ofDeterministic (fun _ => Part.none) ⟨⟨Part.not_none_dom,
    fun _ _ _ _ h => (Part.not_none_dom h).elim⟩,
    fun _ _ _ h => (Part.not_none_dom h.1).elim,
    fun _ => iff_of_false Part.not_none_dom id⟩

lemma parallel_unit_left_mass {A : Interface} (R : TypedSystem A)
    (h : List ((Σ i, (tensor unit A).X i) × (Σ i, (tensor unit A).Y i))) :
    (parallel dummy R).1 h = R.1
      (h.map ((leftUnitAlphabet A.X).prodCongr (leftUnitAlphabet A.Y))) := by
  let k := h.map ((sumAlphabet (Sum.rec unit.X A.X)).symm.prodCongr
    (sumAlphabet (Sum.rec unit.Y A.Y)).symm)
  have hp : RandomSystem.parallelConsistent k ∧ RandomSystem.parallelLeft k = [] ∧
      RandomSystem.parallelRight k =
        h.map ((leftUnitAlphabet A.X).prodCongr (leftUnitAlphabet A.Y)) := by
    dsimp only [k]
    induction h with
    | nil => exact ⟨by simp [RandomSystem.parallelConsistent], rfl, rfl⟩
    | cons z h ih =>
      rcases z with ⟨⟨(e | i), x⟩, ⟨(e' | j), y⟩⟩
      · exact e.elim
      · exact e.elim
      · exact e'.elim
      · simpa only [List.map_cons, RandomSystem.parallelConsistent, List.mem_cons,
          forall_eq_or_imp, RandomSystem.parallelLeft, RandomSystem.parallelRight,
          List.filterMap_cons, sumAlphabet, leftUnitAlphabet, Equiv.prodCongr_apply,
          Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Prod.map_apply,
          Option.some.injEq, List.cons.injEq, true_and] using ih
  change RandomSystem.parallel dummy.1 R.1 k = _
  rw [RandomSystem.parallel_mass, if_pos hp.1, hp.2.1, hp.2.2, dummy.1.mass_nil, one_mul]

lemma parallel_unit_right_mass {A : Interface} (R : TypedSystem A)
    (h : List ((Σ i, (tensor A unit).X i) × (Σ i, (tensor A unit).Y i))) :
    (parallel R dummy).1 h = R.1
      (h.map ((rightUnitAlphabet A.X).prodCongr (rightUnitAlphabet A.Y))) := by
  let k := h.map ((sumAlphabet (Sum.rec A.X unit.X)).symm.prodCongr
    (sumAlphabet (Sum.rec A.Y unit.Y)).symm)
  have hp : RandomSystem.parallelConsistent k ∧ RandomSystem.parallelRight k = [] ∧
      RandomSystem.parallelLeft k =
        h.map ((rightUnitAlphabet A.X).prodCongr (rightUnitAlphabet A.Y)) := by
    dsimp only [k]
    induction h with
    | nil => exact ⟨by simp [RandomSystem.parallelConsistent], rfl, rfl⟩
    | cons z h ih =>
      rcases z with ⟨⟨(i | e), x⟩, ⟨(j | e'), y⟩⟩
      · simpa only [List.map_cons, RandomSystem.parallelConsistent, List.mem_cons,
          forall_eq_or_imp, RandomSystem.parallelLeft, RandomSystem.parallelRight,
          List.filterMap_cons, sumAlphabet, rightUnitAlphabet, Equiv.prodCongr_apply,
          Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Prod.map_apply,
          List.cons.injEq, true_and] using ih
      · exact e'.elim
      · exact e.elim
      · exact e.elim
  change RandomSystem.parallel R.1 dummy.1 k = _
  rw [RandomSystem.parallel_mass, if_pos hp.1, hp.2.1, hp.2.2, dummy.1.mass_nil, mul_one]

lemma parallel_swap_mass {A B : Interface} (R : TypedSystem A) (S : TypedSystem B)
    (h : List ((Σ i, (tensor A B).X i) × (Σ i, (tensor A B).Y i))) :
    (parallel S R).1 (h.map ((swapAlphabet A.X B.X).prodCongr (swapAlphabet A.Y B.Y))) =
      (parallel R S).1 h := by
  let k := h.map ((sumAlphabet (Sum.rec A.X B.X)).symm.prodCongr
    (sumAlphabet (Sum.rec A.Y B.Y)).symm)
  let k' := (h.map ((swapAlphabet A.X B.X).prodCongr (swapAlphabet A.Y B.Y))).map
    ((sumAlphabet (Sum.rec B.X A.X)).symm.prodCongr (sumAlphabet (Sum.rec B.Y A.Y)).symm)
  have hp : (RandomSystem.parallelConsistent k' ↔ RandomSystem.parallelConsistent k) ∧
      RandomSystem.parallelLeft k' = RandomSystem.parallelRight k ∧
      RandomSystem.parallelRight k' = RandomSystem.parallelLeft k := by
    dsimp only [k, k']
    induction h with
    | nil => exact ⟨by simp [RandomSystem.parallelConsistent], rfl, rfl⟩
    | cons z h ih =>
      rcases z with ⟨⟨(i | j), x⟩, ⟨(k | l), y⟩⟩
      all_goals
        simp only [List.map_cons, Equiv.prodCongr_apply, Prod.map_apply,
          swapAlphabet, sumAlphabet, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
          RandomSystem.parallelConsistent, List.mem_cons, forall_eq_or_imp,
          RandomSystem.parallelLeft, RandomSystem.parallelRight, List.filterMap_cons,
          List.cons.injEq, reduceCtorEq, true_and, false_and, iff_self] at ih ⊢
        first | exact ih | exact ih.2
  change RandomSystem.parallel S.1 R.1 k' = RandomSystem.parallel R.1 S.1 k
  rw [RandomSystem.parallel_mass, RandomSystem.parallel_mass, hp.1, hp.2.1, hp.2.2]
  split_ifs
  · exact mul_comm _ _
  · rfl

end TypedSystem

end SystemAlgebra
