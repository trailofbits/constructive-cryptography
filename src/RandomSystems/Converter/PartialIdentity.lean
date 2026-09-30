import RandomSystems.Converter.ResourceAttachment

/-!
# The identity on partial converters

Along the transcripts of a partial DDC, the identity's history alternates a forwarded
query and its reply, so it stays within its admissible histories. Composing a partial
DDC with the identity on either side changes no transcript; the DDC need not answer
every legal input.

## Main results

* `IsDDC.replies_serialM_id`, `IsDDC.replies_id_serialM`: composition with the identity
  keeps the transcripts
* `IsDDC.trim_serialM_id`, `IsDDC.trim_id_serialM`: the identity laws for partial DDCs
-/

namespace SystemAlgebra

open Classical

variable {O J : Type} {U V : O → Type} {X Y : J → Type}

/-- The last reply of a completed history fixes the reply label. -/
theorem Replies.replyLabel_eq {α : InsideOutsideSystem O J U V X Y} (hα : SilentAtEmpty α) {us ys}
    (hr : Replies α us ys) : SystemAlgebra.replyLabel α us = ys.getLast?.map (·.1) := by
  rcases List.eq_nil_or_concat us with rfl | ⟨us, a, rfl⟩
  · have hy : ys = [] := List.length_eq_zero_iff.mp hr.length
    subst ys
    rw [SystemAlgebra.replyLabel, dif_neg hα]
    rfl
  · have hn : ys ≠ [] := by intro hz; simpa [hz] using hr.length
    obtain ⟨ys, w, rfl⟩ := List.eq_nil_or_concat ys |>.resolve_left hn
    simp only [List.concat_eq_append] at hr ⊢
    rw [replyLabel_of_mem _ (Part.eq_some_iff.mp (replies_snoc.mp hr).2)]
    simp

/-- A completed history restricted to its first `k + 1` exchanges is completed. -/
theorem Replies.take {A B : Type} {s : System A B} {xs : List A} {ys : List B}
    (hr : Replies s xs ys) (k : ℕ) : Replies s (xs.take (k + 1)) (ys.take (k + 1)) := by
  refine ⟨by simp [hr.length], fun i hi hi' => ?_⟩
  simp only [List.length_take] at hi hi'
  have hik : i + 1 ≤ k + 1 := by omega
  simpa only [List.take_take, Nat.min_eq_left hik, List.getElem_take] using
    hr.2 i (by omega) (by omega)

/-- Completed histories are those whose every prefix has the corresponding
exposed run. -/
theorem replies_interconnect_of_runs {A B X' Y' : Type} {s : System X' Y'}
    {route : Y' → B ⊕ X'} {inj : A → X'} {us : List A} {ys : List B}
    (hl : ys.length = us.length)
    (hrun : ∀ k (hk : k < us.length) (hj : k < ys.length),
      ∃ H, Induces s route inj (us.take (k + 1)) (some ys[k]) H) :
    Replies (interconnect s route inj) us ys := by
  refine ⟨hl, fun k hk hj => ?_⟩
  obtain ⟨H, hi⟩ := hrun k hk hj
  exact Part.eq_some_iff.mpr (mem_interconnect.mpr ⟨H, hi⟩)

theorem getLast?_take_succ {A : Type} {ys : List A} {k : ℕ} (hk : k < ys.length) :
    (ys.take (k + 1)).getLast? = some ys[k] := by
  have he : ys.take (k + 1) = ys.take k ++ [ys[k]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
  rw [he, List.getLast?_append]
  rfl

/-- The identity forwards an outside query of an idle history. -/
theorem idConverter_query {h : List (Σ l, twoFam X Y l)}
    (hi : Idle (idConverter J X Y) h) (j : J) (x : X j) :
    idConverter J X Y (h ++ [⟨⟨none, j⟩, x⟩]) = Part.some ⟨⟨some (), j⟩, x⟩ := by
  have ha : Admissible (idConverter J X Y) (h ++ [⟨⟨none, j⟩, x⟩]) :=
    admissible_snoc.mpr ⟨hi.1, hi.2.1, (admitAfter_of_ne hi.2.2).mpr rfl⟩
  rw [idConverter, canon_of_admissible ((admissible_canon_iff _).mp ha)]
  exact forwardAll_snoc_outer h j x

theorem admitAfter_none_iff {P Q : Type} {r : Option (Two P Q)} {l : P} :
    admitAfter r ⟨none, l⟩ ↔ ∀ j, r ≠ some ⟨some (), j⟩ := by
  rcases r with _ | ⟨_ | ⟨⟨⟩⟩, l'⟩ <;> simp [admitAfter]

theorem admitAfter_some_iff {P Q : Type} {r : Option (Two P Q)} {j : Q} :
    admitAfter r ⟨some (), j⟩ ↔ r = some ⟨some (), j⟩ := by
  rcases r with _ | ⟨_ | ⟨⟨⟩⟩, l'⟩ <;> simp [admitAfter, eq_comm]

/-- Composing on the inside with the identity reproduces every completed
history of a partial converter. -/
theorem IsDDC.replies_serialM_id {b : ℕ} {α : InsideOutsideSystem O J U V X Y} (hα : IsDDC b α)
    {us ys} (hr : Replies α us ys) : Replies (serialM α (idConverter J X Y)) us ys := by
  have key : ∀ us ys, Replies α us ys → ∃ H,
      Induces (pair α (idConverter J X Y)) serialRouteM serialInjM us ys.getLast? H ∧
      restrict none H = us ∧
      ((∀ j x, ys.getLast? ≠ some ⟨⟨some (), j⟩, x⟩) →
        Idle (idConverter J X Y) (restrict (some ()) H)) ∧
      (∀ j x, ys.getLast? = some ⟨⟨some (), j⟩, x⟩ → ∃ G,
        restrict (some ()) H = G ++ [⟨⟨none, j⟩, x⟩] ∧ Idle (idConverter J X Y) G) := by
    intro us
    induction us using List.reverseRecOn with
    | nil =>
      intro ys hr
      have hy : ys = [] := List.length_eq_zero_iff.mp hr.length
      subst ys
      refine ⟨[], Induces.nil, rfl, fun _ => ?_, fun j x h => by simp at h⟩
      exact ⟨admissible_nil, by simp, fun j => by simp [replyLabel, idConverter, canon, forwardAll]⟩
    | append_singleton us a ih =>
      intro ys hr
      have hn : ys ≠ [] := by intro hz; simpa [hz] using hr.length
      obtain ⟨ys, w, rfl⟩ := List.eq_nil_or_concat ys |>.resolve_left hn
      rw [List.concat_eq_append] at hr ⊢
      obtain ⟨hp, hw⟩ := replies_snoc.mp hr
      obtain ⟨H, hi, hH, hidle, hwait⟩ := ih ys hp
      have hw' : w ∈ α (us ++ [a]) := Part.eq_some_iff.mp hw
      have hadm : Admits α us a := hα.admits us a hw'.1
      rw [Admits, hp.replyLabel_eq hα.dds.1] at hadm
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
      rcases a with ⟨⟨_ | ⟨⟨⟩⟩, o₁⟩, v⟩
      · -- an outside input reaches the converter directly
        have hI : Idle (idConverter J X Y) (restrict (some ()) H) := by
          apply hidle
          intro j x he
          rw [he] at hadm
          simp [admitAfter] at hadm
        let H₁ := H ++ [serialInjM (⟨⟨none, o₁⟩, v⟩ : Σ l : Two O J, twoFam U Y l)]
        have hq : (⟨none, w⟩ : Two _ _) ∈ pair α (idConverter J X Y) H₁ := by
          change _ ∈ pair α (idConverter J X Y) (H ++ [⟨none, ⟨⟨none, o₁⟩, v⟩⟩])
          rw [pair_left, hH]
          exact Part.mem_map _ hw'
        rcases w with ⟨⟨_ | ⟨⟨⟩⟩, o'⟩, v'⟩
        · refine ⟨H₁, Induces.snoc _ _ _ _ _ _ hi (Exchange.out _ _ _ hq rfl), ?_,
            fun _ => ?_, fun j x h => by simp at h⟩
          · simp [H₁, serialInjM, hH]
          · simpa [H₁, serialInjM] using hI
        · let H₂ := H₁ ++ [⟨some (), ⟨⟨none, o'⟩, v'⟩⟩]
          have hq₂ : (⟨some (), ⟨⟨some (), o'⟩, v'⟩⟩ : Two (Σ l, twoFam V X l) _) ∈
              pair α (idConverter J X Y) H₂ := by
            change _ ∈ pair α (idConverter J X Y) (H₁ ++ [⟨some (), ⟨⟨none, o'⟩, v'⟩⟩])
            rw [pair_right]
            simp only [H₁, serialInjM, restrict_some_snoc_left, idConverter_query hI]
            exact Part.mem_map _ (Part.mem_some _)
          refine ⟨H₂, Induces.snoc _ _ _ _ _ _ hi
            (Exchange.feed _ _ _ _ _ hq rfl (Exchange.out _ _ _ hq₂ rfl)), ?_,
            fun h => absurd rfl (h o' v'), fun j x h => ?_⟩
          · simp [H₂, H₁, serialInjM, hH]
          · have h' : (⟨⟨some (), o'⟩, v'⟩ : Σ l : Two O J, twoFam V X l) =
                ⟨⟨some (), j⟩, x⟩ := by simpa using h
            cases h'
            exact ⟨restrict (some ()) H, by simp [H₂, H₁, serialInjM], hI⟩
      · -- an inside reply reaches the identity, which forwards it
        obtain ⟨x, hx⟩ : ∃ x, ys.getLast? = some ⟨⟨some (), o₁⟩, x⟩ := by
          rcases hl : ys.getLast? with _ | ⟨⟨⟨_ | ⟨⟨⟩⟩, j⟩, x⟩⟩
          · rw [hl] at hadm; simp [admitAfter] at hadm
          · rw [hl] at hadm; simp [admitAfter] at hadm
          · rw [hl] at hadm
            have hj : o₁ = j := by simpa [admitAfter] using hadm
            subst hj
            exact ⟨x, rfl⟩
        obtain ⟨G, hG, hIG⟩ := hwait o₁ x hx
        obtain ⟨-, hy, hIG'⟩ := idConverter_call hIG o₁ x v
        let H₁ := H ++ [serialInjM (⟨⟨some (), o₁⟩, v⟩ : Σ l : Two O J, twoFam U Y l)]
        have hq₁ : (⟨some (), ⟨⟨none, o₁⟩, v⟩⟩ : Two (Σ l, twoFam V X l) _) ∈
            pair α (idConverter J X Y) H₁ := by
          change _ ∈ pair α (idConverter J X Y) (H ++ [⟨some (), ⟨⟨some (), o₁⟩, v⟩⟩])
          rw [pair_right, hG, List.append_assoc, List.singleton_append, hy]
          exact Part.mem_map _ (Part.mem_some _)
        let H₂ := H₁ ++ [⟨none, ⟨⟨some (), o₁⟩, v⟩⟩]
        have hq₂ : (⟨none, w⟩ : Two _ _) ∈ pair α (idConverter J X Y) H₂ := by
          change _ ∈ pair α (idConverter J X Y) (H₁ ++ [⟨none, ⟨⟨some (), o₁⟩, v⟩⟩])
          rw [pair_left]
          simp only [H₁, serialInjM, restrict_none_snoc_right, hH]
          exact Part.mem_map _ hw'
        have hS₂ : restrict (some ()) H₂ = G ++ [⟨⟨none, o₁⟩, x⟩, ⟨⟨some (), o₁⟩, v⟩] := by
          simp [H₂, H₁, serialInjM, hG]
        rcases w with ⟨⟨_ | ⟨⟨⟩⟩, o'⟩, v'⟩
        · refine ⟨H₂, Induces.snoc _ _ _ _ _ _ hi
            (Exchange.feed _ _ _ _ _ hq₁ rfl (Exchange.out _ _ _ hq₂ rfl)), ?_,
            fun _ => by rw [hS₂]; exact hIG', fun j x h => by simp at h⟩
          simp [H₂, H₁, serialInjM, hH]
        · let H₃ := H₂ ++ [⟨some (), ⟨⟨none, o'⟩, v'⟩⟩]
          have hq₃ : (⟨some (), ⟨⟨some (), o'⟩, v'⟩⟩ : Two (Σ l, twoFam V X l) _) ∈
              pair α (idConverter J X Y) H₃ := by
            change _ ∈ pair α (idConverter J X Y) (H₂ ++ [⟨some (), ⟨⟨none, o'⟩, v'⟩⟩])
            rw [pair_right, hS₂, idConverter_query hIG']
            exact Part.mem_map _ (Part.mem_some _)
          refine ⟨H₃, Induces.snoc _ _ _ _ _ _ hi
            (Exchange.feed _ _ _ _ _ hq₁ rfl (Exchange.feed _ _ _ _ _ hq₂ rfl
              (Exchange.out _ _ _ hq₃ rfl))), ?_,
            fun h => absurd rfl (h o' v'), fun j x' h => ?_⟩
          · simp [H₃, H₂, H₁, serialInjM, hH]
          · have h' : (⟨⟨some (), o'⟩, v'⟩ : Σ l : Two O J, twoFam V X l) =
                ⟨⟨some (), j⟩, x'⟩ := by simpa using h
            cases h'
            exact ⟨G ++ [⟨⟨none, o₁⟩, x⟩, ⟨⟨some (), o₁⟩, v⟩], by
              simp only [H₃, restrict_some_snoc_right, hS₂], hIG'⟩
  apply replies_interconnect_of_runs hr.length
  intro k hk hj
  obtain ⟨H, hi, -⟩ := key _ _ (hr.take k)
  rw [getLast?_take_succ hj] at hi
  exact ⟨H, hi⟩

/-- Composing on the outside with the identity reproduces every completed
history of a partial converter. The identity's history alternates each outside
call and the reply returned for it. -/
theorem IsDDC.replies_id_serialM {b : ℕ} {α : InsideOutsideSystem O J U V X Y} (hα : IsDDC b α)
    {us ys} (hr : Replies α us ys) : Replies (serialM (idConverter O U V) α) us ys := by
  have key : ∀ us ys, Replies α us ys → ∃ H,
      Induces (pair (idConverter O U V) α) serialRouteM serialInjM us ys.getLast? H ∧
      restrict (some ()) H = us ∧
      ((∀ j x, ys.getLast? ≠ some ⟨⟨some (), j⟩, x⟩) →
        Idle (idConverter O U V) (restrict none H)) ∧
      (∀ j x, ys.getLast? = some ⟨⟨some (), j⟩, x⟩ → ∃ G o u,
        restrict none H = G ++ [⟨⟨none, o⟩, u⟩] ∧ Idle (idConverter O U V) G ∧
          lastOuter us = some o) := by
    intro us
    induction us using List.reverseRecOn with
    | nil =>
      intro ys hr
      have hy : ys = [] := List.length_eq_zero_iff.mp hr.length
      subst ys
      refine ⟨[], Induces.nil, rfl, fun _ => ?_, fun j x h => by simp at h⟩
      exact ⟨admissible_nil, by simp, fun j => by simp [replyLabel, idConverter, canon, forwardAll]⟩
    | append_singleton us a ih =>
      intro ys hr
      have hn : ys ≠ [] := by intro hz; simpa [hz] using hr.length
      obtain ⟨ys, w, rfl⟩ := List.eq_nil_or_concat ys |>.resolve_left hn
      rw [List.concat_eq_append] at hr ⊢
      obtain ⟨hp, hw⟩ := replies_snoc.mp hr
      obtain ⟨H, hi, hH, hidle, hwait⟩ := ih ys hp
      have hw' : w ∈ α (us ++ [a]) := Part.eq_some_iff.mp hw
      have hadm : Admits α us a := hα.admits us a hw'.1
      rw [Admits, hp.replyLabel_eq hα.dds.1] at hadm
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
      rcases a with ⟨⟨_ | ⟨⟨⟩⟩, o₁⟩, v⟩
      · -- an outside call is forwarded by the identity to the converter
        have hI : Idle (idConverter O U V) (restrict none H) := by
          apply hidle
          intro j x he
          rw [he] at hadm
          simp [admitAfter] at hadm
        let H₁ := H ++ [serialInjM (⟨⟨none, o₁⟩, v⟩ : Σ l : Two O J, twoFam U Y l)]
        have hq₁ : (⟨none, ⟨⟨some (), o₁⟩, v⟩⟩ : Two (Σ l, twoFam V U l) _) ∈
            pair (idConverter O U V) α H₁ := by
          change _ ∈ pair (idConverter O U V) α (H ++ [⟨none, ⟨⟨none, o₁⟩, v⟩⟩])
          rw [pair_left, idConverter_query hI]
          exact Part.mem_map _ (Part.mem_some _)
        let H₂ := H₁ ++ [⟨some (), ⟨⟨none, o₁⟩, v⟩⟩]
        have hq₂ : (⟨some (), w⟩ : Two _ (Σ l, twoFam V X l)) ∈
            pair (idConverter O U V) α H₂ := by
          change _ ∈ pair (idConverter O U V) α (H₁ ++ [⟨some (), ⟨⟨none, o₁⟩, v⟩⟩])
          rw [pair_right]
          simp only [H₁, serialInjM, restrict_some_snoc_left, hH]
          exact Part.mem_map _ hw'
        have hlo : lastOuter (us ++ [(⟨⟨none, o₁⟩, v⟩ : Σ l : Two O J, twoFam U Y l)]) =
            some o₁ := by
          rw [lastOuter_snoc]; rfl
        rcases w with ⟨⟨_ | ⟨⟨⟩⟩, o'⟩, v'⟩
        · have ho : o' = o₁ := by
            have := hα.replies _ _ o' hw' rfl
            rw [hlo] at this
            exact (Option.some_injective _ this).symm
          subst ho
          obtain ⟨-, hy, hI'⟩ := idConverter_call hI o' v v'
          let H₃ := H₂ ++ [⟨none, ⟨⟨some (), o'⟩, v'⟩⟩]
          have hq₃ : (⟨none, ⟨⟨none, o'⟩, v'⟩⟩ : Two (Σ l, twoFam V U l) _) ∈
              pair (idConverter O U V) α H₃ := by
            change _ ∈ pair (idConverter O U V) α (H₂ ++ [⟨none, ⟨⟨some (), o'⟩, v'⟩⟩])
            have hS : restrict none H₂ = restrict none H ++ [⟨⟨none, o'⟩, v⟩] := by
              simp [H₂, H₁, serialInjM]
            rw [pair_left, hS, List.append_assoc, List.singleton_append, hy]
            exact Part.mem_map _ (Part.mem_some _)
          refine ⟨H₃, Induces.snoc _ _ _ _ _ _ hi
            (Exchange.feed _ _ _ _ _ hq₁ rfl (Exchange.feed _ _ _ _ _ hq₂ rfl
              (Exchange.out _ _ _ hq₃ rfl))), ?_, fun _ => ?_, fun j x h => by simp at h⟩
          · simp [H₃, H₂, H₁, serialInjM, hH]
          · simpa [H₃, H₂, H₁, serialInjM] using hI'
        · refine ⟨H₂, Induces.snoc _ _ _ _ _ _ hi
            (Exchange.feed _ _ _ _ _ hq₁ rfl (Exchange.out _ _ _ hq₂ rfl)), ?_,
            fun h => absurd rfl (h o' v'), fun j x h => ?_⟩
          · simp [H₂, H₁, serialInjM, hH]
          · exact ⟨restrict none H, o₁, v, by simp [H₂, H₁, serialInjM], hI, hlo⟩
      · -- an inside reply reaches the converter directly
        obtain ⟨x, hx⟩ : ∃ x, ys.getLast? = some ⟨⟨some (), o₁⟩, x⟩ := by
          rcases hl : ys.getLast? with _ | ⟨⟨⟨_ | ⟨⟨⟩⟩, j⟩, x⟩⟩
          · rw [hl] at hadm; simp [admitAfter] at hadm
          · rw [hl] at hadm; simp [admitAfter] at hadm
          · rw [hl] at hadm
            have hj : o₁ = j := by simpa [admitAfter] using hadm
            subst hj
            exact ⟨x, rfl⟩
        obtain ⟨G, o, u, hG, hIG, hlo⟩ := hwait o₁ x hx
        have hlo' : lastOuter (us ++ [(⟨⟨some (), o₁⟩, v⟩ : Σ l : Two O J, twoFam U Y l)]) =
            some o := by
          rw [lastOuter_snoc]; exact hlo
        let H₁ := H ++ [serialInjM (⟨⟨some (), o₁⟩, v⟩ : Σ l : Two O J, twoFam U Y l)]
        have hq₁ : (⟨some (), w⟩ : Two _ (Σ l, twoFam V X l)) ∈
            pair (idConverter O U V) α H₁ := by
          change _ ∈ pair (idConverter O U V) α (H ++ [⟨some (), ⟨⟨some (), o₁⟩, v⟩⟩])
          rw [pair_right, hH]
          exact Part.mem_map _ hw'
        rcases w with ⟨⟨_ | ⟨⟨⟩⟩, o'⟩, v'⟩
        · have ho : o' = o := by
            have := hα.replies _ _ o' hw' rfl
            rw [hlo'] at this
            exact (Option.some_injective _ this).symm
          subst ho
          obtain ⟨-, hy, hI'⟩ := idConverter_call hIG o' u v'
          let H₂ := H₁ ++ [⟨none, ⟨⟨some (), o'⟩, v'⟩⟩]
          have hq₂ : (⟨none, ⟨⟨none, o'⟩, v'⟩⟩ : Two (Σ l, twoFam V U l) _) ∈
              pair (idConverter O U V) α H₂ := by
            change _ ∈ pair (idConverter O U V) α (H₁ ++ [⟨none, ⟨⟨some (), o'⟩, v'⟩⟩])
            rw [pair_left]
            simp only [H₁, serialInjM, restrict_none_snoc_right, hG, List.append_assoc,
              List.singleton_append, hy]
            exact Part.mem_map _ (Part.mem_some _)
          refine ⟨H₂, Induces.snoc _ _ _ _ _ _ hi
            (Exchange.feed _ _ _ _ _ hq₁ rfl (Exchange.out _ _ _ hq₂ rfl)), ?_,
            fun _ => ?_, fun j x h => by simp at h⟩
          · simp [H₂, H₁, serialInjM, hH]
          · have hS : restrict none H₂ = G ++ [⟨⟨none, o'⟩, u⟩, ⟨⟨some (), o'⟩, v'⟩] := by
              simp [H₂, H₁, serialInjM, hG]
            rw [hS]; exact hI'
        · refine ⟨H₁, Induces.snoc _ _ _ _ _ _ hi (Exchange.out _ _ _ hq₁ rfl), ?_,
            fun h => absurd rfl (h o' v'), fun j x h => ?_⟩
          · simp [H₁, serialInjM, hH]
          · exact ⟨G, o, u, by simp [H₁, serialInjM, hG], hIG, hlo'⟩
  apply replies_interconnect_of_runs hr.length
  intro k hk hj
  obtain ⟨H, hi, -⟩ := key _ _ (hr.take k)
  rw [getLast?_take_succ hj] at hi
  exact ⟨H, hi⟩

/-- The identity is a right unit for partial converters. -/
theorem IsDDC.trim_serialM_id {b : ℕ} {α : InsideOutsideSystem O J U V X Y} (hα : IsDDC b α) :
    trim (serialM α (idConverter J X Y)) = α := by
  apply IsDDS.eq_of_replies_iff (SilentAtEmpty.isDDS_trim (by simp [SilentAtEmpty, serialM])) hα.dds
  intro xs ys
  rw [replies_trim_iff]
  constructor
  · intro hr
    have hr' := hr.interconnect_mono (pair_mono (fun _ _ h => h) (fun _ _ h => canon_mem h))
    change Replies (serialM α (forwardAll J X Y)) xs ys at hr'
    rwa [serialM_forwardAll hα.dds.1] at hr'
  · exact hα.replies_serialM_id

/-- The identity is a left unit for partial converters. -/
theorem IsDDC.trim_id_serialM {b : ℕ} {α : InsideOutsideSystem O J U V X Y} (hα : IsDDC b α) :
    trim (serialM (idConverter O U V) α) = α := by
  apply IsDDS.eq_of_replies_iff (SilentAtEmpty.isDDS_trim (by simp [SilentAtEmpty, serialM])) hα.dds
  intro xs ys
  rw [replies_trim_iff]
  constructor
  · intro hr
    have hr' := hr.interconnect_mono (pair_mono (fun _ _ h => canon_mem h) (fun _ _ h => h))
    change Replies (serialM (forwardAll O U V) α) xs ys at hr'
    rwa [forwardAll_serialM hα.dds.1] at hr'
  · exact hα.replies_id_serialM

end SystemAlgebra
