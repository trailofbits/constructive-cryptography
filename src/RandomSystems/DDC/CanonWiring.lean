import RandomSystems.Converter.ConverterDomain
import RandomSystems.Converter.PartialIdentity

/-!
# Canonical converters in serial wiring

Along an admitted external history, the serial composition of two canonical
restrictions consults only admissible component histories. It therefore has
exactly the completed histories of the unrestricted composition.

## Main results

* `pair_canon_eq_of_admissible`: canonical restriction does not change the
  values at admissible component histories
* `SerialState.admissible`: a reached serial state has admissible component
  histories
* `replies_serialM_canon_iff`: canonical restriction commutes with serial
  composition on admitted histories
-/

namespace SystemAlgebra

open Classical

variable {O M J : Type} {U V : O → Type} {Xm Ym : M → Type} {X Y : J → Type}

/-- Canonical restriction changes no value at a prefix of admissible
component histories. -/
theorem pair_canon_eq_of_admissible {β : InsideOutsideSystem O M U V Xm Ym} {α : InsideOutsideSystem M J Xm Ym X Y}
    {H : List (Two (Σ l, twoFam U Ym l) (Σ l, twoFam Xm Y l))}
    (hβ : Admissible β (restrict none H)) (hα : Admissible α (restrict (some ()) H)) :
    ∀ p, p <+: H → pair (canon β) (canon α) p = pair β α p := by
  intro p hp
  rcases List.eq_nil_or_concat p with rfl | ⟨p, ⟨_ | ⟨⟨⟩⟩, x⟩, rfl⟩
  · simp [pair, parAll]
  · simp only [List.concat_eq_append] at hp ⊢
    rw [pair_left, pair_left]
    obtain ⟨e, he⟩ := restrict_prefix none hp
    rw [restrict_none_snoc_left] at he
    rw [← he] at hβ
    rw [canon_of_admissible hβ.of_append]
  · simp only [List.concat_eq_append] at hp ⊢
    rw [pair_right, pair_right]
    obtain ⟨e, he⟩ := restrict_prefix (some ()) hp
    rw [restrict_some_snoc_right] at he
    rw [← he] at hα
    rw [canon_of_admissible hα.of_append]

/-- A reached serial state has admissible component histories. -/
theorem SerialState.admissible {bα : ℕ} {β : InsideOutsideSystem O M U V Xm Ym} {α : InsideOutsideSystem M J Xm Ym X Y}
    {u : List (Σ l : Two O J, twoFam U Y l)} {w} {H}
    (hs : SerialState β α bα u (some w) H) :
    Admissible β (restrict none H) ∧ Admissible α (restrict (some ()) H) := by
  rcases hs with ⟨-, ⟨-, h, -⟩ | ⟨w', -, -, hib, hia⟩ | ⟨w', j, m, o', -, -, -, hwa, hwb, -, -⟩⟩
  · cases h
  · exact ⟨hib.1, hia.1⟩
  · exact ⟨hwb.1, hwa.1⟩

/-- **Canonical restriction commutes with serial wiring** on admitted histories. -/
theorem replies_serialM_canon_iff {bβ bα : ℕ} {β : InsideOutsideSystem O M U V Xm Ym}
    {α : InsideOutsideSystem M J Xm Ym X Y} (hβ : IsDDC bβ (canon β)) (hα : IsDDC bα (canon α)) :
    ∀ h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l)), Admitted converterAdmits h →
      (Replies (serialM (canon β) (canon α)) (h.map Prod.fst) (h.map Prod.snd) ↔
        Replies (serialM β α) (h.map Prod.fst) (h.map Prod.snd)) := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intro _; simp [Replies]
  | append_singleton h z ih =>
    intro hh
    obtain ⟨hh₀, hz⟩ := admitted_snoc.mp hh
    rcases z with ⟨x, y⟩
    simp only [List.map_append, List.map_singleton]
    constructor
    · intro hr
      exact Replies.interconnect_mono (pair_mono (fun _ _ h => canon_mem h)
        (fun _ _ h => canon_mem h)) hr
    · intro hr
      obtain ⟨hr₀, hy⟩ := replies_snoc.mp hr
      have hc₀ := (ih hh₀).mpr hr₀
      obtain ⟨o, H, r, hs, -⟩ := serialM_reach_partial hβ hα _ hc₀.reach
      have hlab := hc₀.replyLabel_eq (by simp [SilentAtEmpty, serialM])
      rw [replyLabel_serialM r, List.getLast?_map] at hlab
      have had : admitAfter (o.map (·.1)) x.1 := by
        rw [hlab]
        simpa [converterAdmits, Option.map_map, Function.comp_def] using hz
      rcases (serialM_next_partial hβ hα r hs x).1 had with
        ⟨-, -, H', r', hB', hA'⟩ | ⟨w, H', r', hs', -⟩
      · have rr := r'.congr_of_prefix_eq (pair_canon_eq_of_admissible
          ((admissible_canon_iff _).mp hB') ((admissible_canon_iff _).mp hA'))
        have hn := interconnect_eq_none rr
        change serialM β α _ = Part.none at hn
        rw [hn] at hy
        exact absurd hy (Part.none_ne_some _)
      · obtain ⟨hB', hA'⟩ := hs'.admissible
        have rr := r'.congr_of_prefix_eq (pair_canon_eq_of_admissible
          ((admissible_canon_iff _).mp hB') ((admissible_canon_iff _).mp hA'))
        have hw := interconnect_eq_some rr
        change serialM β α _ = Part.some w at hw
        rw [hw] at hy
        obtain rfl := Part.some_injective hy
        exact replies_snoc.mpr ⟨hc₀, interconnect_eq_some r'⟩

end SystemAlgebra
