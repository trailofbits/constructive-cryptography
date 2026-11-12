module

public import RandomSystems.Cumulative.PDSSequence

/-! Certified Boolean echo samples form a normalized sequence consumed by cumulative gluing. -/

@[expose] public section

namespace Tests.PDSSequence

open SystemAlgebra Probability Probability.Distribution

/-- The deterministic evaluator returns each Boolean query on every nonempty input history. -/
noncomputable def echo : DDS Bool Bool :=
  DDS.ofFunction (fun xs => xs ≠ [])
    ⟨fun hn => hn rfl, fun _ hn _ => hn⟩ id

/-- The finite echo sample answers exactly the first `n` queries. -/
noncomputable def echoAt (n : ℕ) :
    {s : System Bool Bool // IsDDS s ∧ HasDomain (cutDomain (fun _ _ => True) n) s} :=
  ⟨cutSystem echo.1 n, echo.2.cutSystem n, by
    intro h x _
    change (filterDom (fun xs => xs.length ≤ n) echo.1 (h.map Prod.fst ++ [x])).Dom ↔ _
    rw [filterDom_dom, echo, DDS.ofFunction_dom]
    have nonempty : h.map Prod.fst ++ [x] ≠ [] :=
      List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
    simp only [cutDomain, true_and, List.length_append, List.length_map,
      List.length_singleton, Nat.add_one_le_iff]
    exact ⟨fun hh => hh.1, fun hh => ⟨hh, nonempty⟩⟩⟩

/-- Each level concentrates its entire mass on the corresponding certified echo sample. -/
noncomputable def echoSequence : SystemAlgebra.PDSSequence Bool Bool (fun _ _ => True) where
  level n := ProbDist.single (echoAt n)
  compatible n := by
    apply Subtype.ext
    change fTransform (PDS.cutSample _ (Nat.le_succ n)) (Finsupp.single (echoAt (n + 1)) 1) = _
    rw [fTransform_single]
    congr 1
    apply Subtype.ext
    exact (cutSystem_cutSystem echo.1 n (n + 1)).trans
      (congrArg (cutSystem echo.1) (min_eq_left (Nat.le_succ n)))

/-- Certified same-horizon restriction preserves an actual deterministic sample. -/
example : PDS.cutSample (fun _ _ => True) (Nat.le_refl 3) (echoAt 3) = echoAt 3 :=
  PDS.cutSample_refl _ _ _

/-- Two sample restrictions compose on the actual echo sample. -/
example :
    PDS.cutSample (fun _ _ => True) (show 1 ≤ 2 from Nat.le_succ 1)
      (PDS.cutSample (fun _ _ => True) (show 2 ≤ 3 from Nat.le_succ 2) (echoAt 3)) =
    PDS.cutSample (fun _ _ => True) (show 1 ≤ 3 from (Nat.le_succ 1).trans (Nat.le_succ 2))
      (echoAt 3) :=
  PDS.cutSample_comp _ _ _ _

/-- Gluing the normalized echo levels gives a behavior admitting every query. -/
lemma echo_normalized : IsRandomSystem (fun _ _ => True) echoSequence.behavior :=
  echoSequence.behavior_isRandomSystem

/-- A finite observation recovers the existing PDS behavior at that level. -/
lemma echo_cut (n : ℕ) :
    IsRandomSystem.cut (fun _ _ => True) echoSequence.behavior echo_normalized n =
      PDS.behavior (echoSequence.level n).1 (echoSequence.level n).2 :=
  echoSequence.cut_behavior n

/-- A negative sample weight is retained when its echo transcript lies within the cut. -/
lemma signed_cut_mass :
    behaviorMass (fTransform (PDS.cutSample (fun _ _ => True)
      (show 1 ≤ 3 from (Nat.le_succ 1).trans (Nat.le_succ 2)))
      (Finsupp.single (echoAt 3) (-2))) [false] [false] = -2 := by
  have within : ([false] : List Bool).length ≤ 1 := Nat.le_refl 1
  rw [PDS.behaviorMass_fTransform_cutSystem _ _ 1 (fun _ => rfl), ite_eq_left within]
  have replies : Replies (echoAt 3).1 [false] [false] := by
    change Replies (cutSystem echo.1 3) [false] [false]
    rw [replies_cutSystem_iff _ _ ((Nat.le_succ 1).trans (Nat.le_succ 2)),
      echo, DDS.replies_ofFunction_iff]
    exact ⟨Or.inr (List.cons_ne_nil _ _), rfl⟩
  rw [behaviorMass, mass_single, ite_eq_left replies]

/-- Later signed mass vanishes even when the target sample keeps only the trivial certificate. -/
lemma signed_cut_later_mass :
    behaviorMass (fTransform
      (fun s : {s : System Bool Bool //
        IsDDS s ∧ HasDomain (cutDomain (fun _ _ => True) 3) s} =>
        (⟨cutSystem s.1 1, trivial⟩ : {_s : System Bool Bool // True}))
      (Finsupp.single (echoAt 3) (-2))) [false, true] [false, true] = 0 := by
  have beyond : ¬ ([false, true] : List Bool).length ≤ 1 := Nat.not_succ_le_self 1
  rw [PDS.behaviorMass_fTransform_cutSystem _ _ 1 (fun _ => rfl), ite_eq_right beyond]

#print axioms SystemAlgebra.PDS.behaviorMass_fTransform_cutSystem
#print axioms signed_cut_mass
#print axioms signed_cut_later_mass

#print axioms SystemAlgebra.PDS.cutSample_refl
#print axioms SystemAlgebra.PDS.cutSample_comp
#print axioms SystemAlgebra.PDS.behaviorMass_cutSample
#print axioms SystemAlgebra.PDSSequence.behavior_isRandomSystem
#print axioms SystemAlgebra.PDSSequence.cut_behavior
#print axioms SystemAlgebra.PDSSequence.behavior_eq_iff
#print axioms echo_normalized
#print axioms echo_cut

end Tests.PDSSequence
