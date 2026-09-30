import RandomSystems.PDS.PDS

/-!
# Systems given by their conditional replies

A partial reply function on transcripts determines a deterministic system: the
reply to an input history is the reply to its last input after the transcript of
the earlier inputs.

## Main definitions

* `DDS.conditionalHistory q xs`: the transcript produced along the inputs `xs`
* `DDS.ofConditional q`: the deterministic system replying by `q`

## Main results

* `DDS.ofConditional_snoc`: after a transcript `h`, the system replies `q h x`
* `DDS.conditionalHistory_replies`, `DDS.replies_conditionalHistory`: its transcripts
  are exactly the reconstructed ones
-/

namespace SystemAlgebra.DDS

variable {A B : Type} (q : List (A × B) → A →. B)

/-- Reconstruct the replies to an ordinary input list. -/
def conditionalHistory (xs : List A) : Part (List (A × B)) :=
  List.reverseRecOn xs (Part.some []) fun _ x prior =>
    prior.bind fun h => (q h x).map fun y => h ++ [(x, y)]

@[simp] theorem conditionalHistory_nil : conditionalHistory q [] = Part.some [] := by
  simp [conditionalHistory]

theorem conditionalHistory_snoc (xs : List A) (x : A) :
    conditionalHistory q (xs ++ [x]) =
      (conditionalHistory q xs).bind fun h => (q h x).map fun y => h ++ [(x, y)] := by
  unfold conditionalHistory
  rw [List.reverseRecOn_concat]

theorem conditionalHistory_queries {xs : List A} {h : List (A × B)}
    (hh : h ∈ conditionalHistory q xs) : h.map Prod.fst = xs := by
  induction xs using List.reverseRecOn generalizing h with
  | nil =>
    have he : h = [] := by simpa using hh
    simp [he]
  | append_singleton xs x ih =>
    rw [conditionalHistory_snoc] at hh
    obtain ⟨h, hh', hy⟩ := Part.mem_bind_iff.mp hh
    simp only [Part.mem_map_iff] at hy
    obtain ⟨y, _, rfl⟩ := hy
    simpa using congrArg (· ++ [x]) (ih hh')

theorem conditionalHistory_prefix {xs ys : List A} (hp : xs <+: ys)
    (hd : (conditionalHistory q ys).Dom) : (conditionalHistory q xs).Dom := by
  obtain ⟨e, rfl⟩ := hp
  induction e using List.reverseRecOn with
  | nil => simpa using hd
  | append_singleton e x ih =>
    rw [← List.append_assoc, conditionalHistory_snoc] at hd
    obtain ⟨h, hh, _⟩ := Part.mem_bind_iff.mp (Part.get_mem hd)
    exact ih hh.1

/-- The last reconstructed reply, with silence on the empty input list. -/
def conditionalReply (xs : List A) : Part B :=
  (conditionalHistory q xs).bind fun h => (h.getLast?.map Prod.snd : Part B)

@[simp] theorem conditionalReply_nil : conditionalReply q [] = Part.none := by
  simp [conditionalReply]

theorem conditionalReply_snoc {xs : List A} {h : List (A × B)}
    (hh : h ∈ conditionalHistory q xs) (x : A) :
    conditionalReply q (xs ++ [x]) = q h x := by
  rw [conditionalReply, conditionalHistory_snoc, Part.eq_some_iff.mpr hh]
  simp only [Part.bind_some, Part.bind_map]
  apply Part.ext
  intro y
  simp

theorem conditionalReply_dom {xs : List A} (hn : xs ≠ []) :
    (conditionalReply q xs).Dom ↔ (conditionalHistory q xs).Dom := by
  constructor
  · intro hd
    obtain ⟨h, hh, _⟩ := Part.mem_bind_iff.mp (Part.get_mem hd)
    exact hh.1
  · intro hd
    have hh := conditionalHistory_queries q (Part.get_mem hd)
    have he : (conditionalHistory q xs).get hd ≠ [] := by
      intro he
      rw [he, List.map_nil] at hh
      exact hn hh.symm
    obtain ⟨h, z, hz⟩ := List.eq_nil_or_concat _ |>.resolve_left he
    refine Part.dom_iff_mem.mpr ⟨z.2, Part.mem_bind_iff.mpr
      ⟨_, Part.get_mem hd, ?_⟩⟩
    simp [hz]

/-- No extra state is part of the resulting system: its argument is still `List A`. -/
def ofConditional : DDS A B :=
  ⟨conditionalReply q, by
    refine ⟨by simp [SilentAtEmpty], ?_⟩
    intro xs ys hp hn hd
    apply (conditionalReply_dom q hn).mpr
    apply conditionalHistory_prefix q hp
    have hyn : ys ≠ [] := by rintro rfl; simp at hd
    exact (conditionalReply_dom q hyn).mp hd⟩

theorem conditionalHistory_replies {xs : List A} {h : List (A × B)}
    (hh : h ∈ conditionalHistory q xs) :
    Replies (ofConditional q).1 (h.map Prod.fst) (h.map Prod.snd) := by
  induction xs using List.reverseRecOn generalizing h with
  | nil =>
    have he : h = [] := by simpa using hh
    rw [he]
    exact replies_nil _
  | append_singleton xs x ih =>
    rw [conditionalHistory_snoc] at hh
    obtain ⟨h, hh', hy⟩ := Part.mem_bind_iff.mp hh
    simp only [Part.mem_map_iff] at hy
    obtain ⟨y, hy, rfl⟩ := hy
    simp only [List.map_append, List.map_cons, List.map_nil]
    refine replies_snoc.mpr ⟨ih hh', ?_⟩
    change conditionalReply q _ = _
    rw [conditionalHistory_queries q hh', conditionalReply_snoc q hh']
    exact Part.eq_some_iff.mpr hy

theorem replies_conditionalHistory {h : List (A × B)}
    (hr : Replies (ofConditional q).1 (h.map Prod.fst) (h.map Prod.snd)) :
    h ∈ conditionalHistory q (h.map Prod.fst) := by
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h z ih =>
    simp only [List.map_append, List.map_cons, List.map_nil] at hr ⊢
    obtain ⟨hr, hy⟩ := replies_snoc.mp hr
    have hh := ih hr
    change conditionalReply q _ = _ at hy
    rw [conditionalReply_snoc q hh] at hy
    rw [conditionalHistory_snoc]
    refine Part.mem_bind_iff.mpr ⟨h, hh, ?_⟩
    simp only [Part.mem_map_iff]
    exact ⟨z.2, Part.eq_some_iff.mp hy, rfl⟩

theorem ofConditional_snoc {h : List (A × B)}
    (hr : Replies (ofConditional q).1 (h.map Prod.fst) (h.map Prod.snd)) (x : A) :
    (ofConditional q).1 (h.map Prod.fst ++ [x]) = q h x :=
  conditionalReply_snoc q (replies_conditionalHistory q hr) x

end SystemAlgebra.DDS
