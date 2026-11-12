module

public import RandomSystems.Converter.QueryBound
public import RandomSystems.PDS.FiniteCuts

/-!
# Attachment through a sufficient inside horizon

`IsDDCFrom.replies_apply_cutSystem_iff` preserves completed outside replies through horizon
`q` when the resource is cut at the total inside-query bound `k q`.
`IsDDCFrom.cutSystem_trim_apply_cutSystem` packages this agreement as equality of canonical
outside cuts. The completed attachment history supplies the resource prefixes used by the
converter.
-/

@[expose] public section

namespace SystemAlgebra

-- Outside ports `O` expose `U`/`V`; inside ports `J` expose `X`/`Y`.
variable {O J : Type} {U V : O → Type} {X Y : J → Type}
-- `E` and `F` admit inside and outside input histories, respectively.
variable {E : List (Σ j, X j) → Prop} {F : List (Σ o, U o) → Prop}
variable {b : ℕ} {α : InsideOutsideSystem O J U V X Y} {R : InterfaceSystem J X Y}

/-- An inside cut at the total-query bound preserves every completed outside transcript. -/
lemma IsDDCFrom.replies_apply_cutSystem_iff
    (ha : IsDDCFrom E F b α)
    -- `hk` counts all inside queries; `mono` permits increasing the outside horizon.
    {k : ℕ → ℕ} (hk : InsideQueriesBounded α k) (mono : Monotone k)
    -- `hR` preserves reply ports, and `hRE` specifies the resource's exact input domain.
    (hR : RepliesAtQueriedInterface R) (hRE : ∀ xs, (R xs).Dom ↔ E xs)
    {q : ℕ} {xs : List (Σ o, U o)} {ys : List (Σ o, V o)} (hq : xs.length ≤ q) :
    Replies (apply α (cutSystem R (k q))) xs ys ↔ Replies (apply α R) xs ys := by
  constructor
  · intro hr
    rw [apply_eq] at hr ⊢
    exact hr.interconnect_mono (pair_mono (fun _ _ hy => hy)
      (fun xs y hy => (filterDom_mem_iff _ R xs y).mp hy |>.2))
  · intro hr
    obtain ⟨H, hi, T, hT, replies, hQ, _⟩ := ha.attach_idle hR hRE xs ys hr
    -- The converter's outside inputs are exactly the observed input history.
    have outside : outsideInputs (T.map Prod.fst) = xs := by
      rw [← hT]
      exact hi.outsideInputs_resource
    -- Its retained resource history is bounded by the same completed transcript.
    have length : (restrict (some ()) H).length ≤ k q := by
      rw [hQ]
      exact (hk T replies).trans (by rw [outside]; exact mono hq)
    have same : ∀ p, p <+: restrict (some ()) H → R p = cutSystem R (k q) p := by
      intro p hp
      exact (cutSystem_apply_of_length_le R _ p (hp.length_le.trans length)).symm
    have prefixes := hi.interconnect_eq_on_prefixes (pair_eq_on_prefixes_right α same)
    rw [apply_eq] at hr ⊢
    exact (replies_congr_of_prefix prefixes ys).mp hr

/-- Canonical outside cuts agree when the inside horizon covers every possible query. -/
lemma IsDDCFrom.cutSystem_trim_apply_cutSystem
    (ha : IsDDCFrom E F b α) {k : ℕ → ℕ}
    (hk : InsideQueriesBounded α k) (mono : Monotone k)
    (hR : RepliesAtQueriedInterface R) (hRE : ∀ xs, (R xs).Dom ↔ E xs) (q : ℕ) :
    cutSystem (trim (apply α (cutSystem R (k q)))) q =
      cutSystem (trim (apply α R)) q := by
  have canonical (S : InterfaceSystem J X Y) : IsDDS (trim (apply α S)) :=
    SilentAtEmpty.isDDS_trim (by
      simp only [SilentAtEmpty, apply_eq, interconnect_nil, Part.not_none_dom, not_false_eq_true])
  apply IsDDS.eq_of_replies_iff ((canonical _).cutSystem q) ((canonical _).cutSystem q)
  intro xs ys
  by_cases hq : xs.length ≤ q
  · rw [replies_cutSystem_iff _ q hq, replies_cutSystem_iff _ q hq,
      replies_trim_iff, replies_trim_iff]
    exact ha.replies_apply_cutSystem_iff hk mono hR hRE hq
  · have hn : xs ≠ [] := by intro he; subst xs; exact hq (Nat.zero_le q)
    have absent (s : System (Σ o, U o) (Σ o, V o)) : ¬ Replies (cutSystem s q) xs ys := by
      intro hr
      have hd := hr.dom hn
      rw [cutSystem_apply_of_bound_lt s q xs (Nat.lt_of_not_ge hq)] at hd
      exact hd
    exact iff_of_false (absent _) (absent _)

end SystemAlgebra
