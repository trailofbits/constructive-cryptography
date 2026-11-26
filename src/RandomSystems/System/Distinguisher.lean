module

public import RandomSystems.System.Observation
public import RandomSystems.System.DDE

/-!
# Deterministic distinguisher laws

`ddeOf` takes the reachable query function of a distinguisher; `ddeOf_bounded` carries
its stopping bound to that environment. `DPort.map` fixes the trigger and decision ports
while mapping resource labels, and `IsDDD.relabel` preserves the caller's interaction
discipline. These are laws of partial systems, independent of a probability law or distance.
-/

@[expose] public section

namespace SystemAlgebra

section OfDDD

variable
  -- `K` indexes resource ports; `Xi i`, `Yi i` are their queries and replies.
  -- `D` is the caller, with trigger and final-decision ports in addition to its resource ports.
  {K : Type} {Xi Yi : K → Type} {D : DDD K Xi Yi}

/-- The environment of the queries of a distinguisher, on its reachable part. -/
noncomputable def ddeOf (hD : IsDDD D) : DDE (Σ i, Xi i) (Σ i, Yi i) :=
  ⟨envOf (trim D), fun ys y hd => by
    classical
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hd
    rw [mem_envOf] at hx
    have hr : Reach D (dHist (ys ++ [y])) := by
      by_contra h; simp [trim, h] at hx
    rw [show dHist (ys ++ [y]) = dHist ys ++ [envIn y] by simp [dHist]] at hr
    have hr₀ := (reach_snoc_iff.mp hr).1
    have hd₀ : (D (dHist ys)).Dom := hr₀ _ [] (by simp) (dHist_ne_nil ys)
    have hne := hD.2.2.2.2 _ _ hr
    obtain ⟨o, ho⟩ := Part.dom_iff_mem.mp hd₀
    rcases o with ⟨_ | _ | i, v⟩
    · exact v.elim
    · exact absurd (replyLabel_of_mem D ho) hne
    · refine Part.dom_iff_mem.mpr ⟨⟨i, v⟩, mem_envOf.mpr ?_⟩
      simp only [trim, ite_eq_left hr₀]
      exact ho⟩

/-- The environment of a distinguisher's queries is bounded by the distinguisher's bound. -/
lemma ddeOf_bounded (hD : IsDDD D) : QueryBounded hD.2.1.choose (ddeOf hD) := by
  classical
  intro ys hd
  obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hd
  have hx : x ∈ envOf (trim D) ys := hx
  rw [mem_envOf] at hx
  have hd' : (D (dHist ys)).Dom := by
    by_cases h : Reach D (dHist ys)
    · simp only [trim, ite_eq_left h] at hx; exact Part.dom_iff_mem.mpr ⟨_, hx⟩
    · simp [trim, h] at hx
  have := hD.2.1.choose_spec _ hd'
  simp [dHist] at this
  omega

end OfDDD

section RelabelDDD

/-- Rename the labels of an environment port. -/
def DPort.map {L L' : Type} (σ : L → L') : DPort L → DPort L'
  | .start => .start
  | .dec => .dec
  | .res i => .res (σ i)

variable
  -- `L`, `L'` label old and new resource ports. `F`, `G` and `F'`, `G'` include trigger,
  -- resource and decision alphabets before and after relabeling.
  {L L' : Type} {F G : DPort L → Type} {F' G' : DPort L' → Type}

lemma reach_relabel_iff (D : InterfaceSystem (DPort L) F G) (f : (Σ p, F' p) → Σ p, F p)
    (g : (Σ p, G p) → Σ p, G' p) (h : List (Σ p, F' p)) :
    Reach (relabel D f g) h ↔ Reach D (h.map f) := by
  classical
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h z ih =>
    rw [reach_snoc_iff, ih, List.map_append, List.map_singleton, reach_snoc_iff]
    simp [relabel]

lemma replyLabel_relabel (D : InterfaceSystem (DPort L) F G) (f : (Σ p, F' p) → Σ p, F p)
    (g : (Σ p, G p) → Σ p, G' p) (σ : L' ≃ L) (hg : ∀ y, (g y).1 = DPort.map σ.symm y.1)
    (h : List (Σ p, F' p)) :
    replyLabel (relabel D f g) h = (replyLabel D (h.map f)).map (DPort.map σ.symm) := by
  classical
  unfold replyLabel
  by_cases hd : (D (h.map f)).Dom
  · have hd' : (relabel D f g h).Dom := by simpa [relabel] using hd
    rw [dite_eq_left hd, dite_eq_left hd']
    exact congrArg some (hg _)
  · have hd' : ¬ (relabel D f g h).Dom := by simpa [relabel] using hd
    rw [dite_eq_right hd, dite_eq_right hd']
    rfl

/-- Relabeling preserves the caller discipline when query and reply ports follow `σ`. -/
lemma IsDDD.relabel {D : InterfaceSystem (DPort L) F G} (hD : IsDDD D)
    (f : (Σ p, F' p) → Σ p, F p)
    (g : (Σ p, G p) → Σ p, G' p) (σ : L' ≃ L) (hf : ∀ z, (f z).1 = DPort.map σ z.1)
    (hg : ∀ y, (g y).1 = DPort.map σ.symm y.1) :
    IsDDD (SystemAlgebra.relabel D f g) := by
  classical
  obtain ⟨hre, ⟨n, hn⟩, htr, hres, hdec⟩ := hD
  have hstart : ∀ p : DPort L', DPort.map σ p = .start ↔ p = .start := by
    intro p; cases p <;> simp [DPort.map]
  refine ⟨?_, ⟨n, fun h hd => ?_⟩, fun h z hr => ?_,
    fun h z i hr hl => ?_, fun h z hr hl => ?_⟩
  · simpa [SilentAtEmpty, SystemAlgebra.relabel] using hre
  · have := hn _ (by simpa [SystemAlgebra.relabel] using hd)
    simpa using this
  · rw [reach_relabel_iff, List.map_append, List.map_singleton] at hr
    have := htr _ _ hr
    rw [List.map_eq_nil_iff, hf, hstart] at this
    exact this
  · rw [reach_relabel_iff, List.map_append, List.map_singleton] at hr
    rw [replyLabel_relabel D f g σ hg] at hl
    obtain ⟨q, hq, e⟩ := Option.map_eq_some_iff.mp hl
    rcases q with _ | _ | i'
    · simp [DPort.map] at e
    · simp [DPort.map] at e
    · simp only [DPort.map, DPort.res.injEq] at e
      have := hres _ _ _ hr hq
      rw [hf] at this
      rcases hz : z.1 with _ | _ | i''
      · rw [hz] at this; simp [DPort.map] at this
      · rw [hz] at this; simp [DPort.map] at this
      · rw [hz] at this
        simp only [DPort.map, DPort.res.injEq] at this
        rw [← e, ← this]
        simp
  · rw [reach_relabel_iff, List.map_append, List.map_singleton] at hr
    rw [replyLabel_relabel D f g σ hg] at hl
    obtain ⟨q, hq, e⟩ := Option.map_eq_some_iff.mp hl
    rcases q with _ | _ | i'
    · simp [DPort.map] at e
    · exact hdec _ _ hr hq
    · simp [DPort.map] at e

end RelabelDDD

end SystemAlgebra
