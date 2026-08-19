import RandomSystems.System.Par

/-!
# The fully defined carrier (CR18 Def 3.3 promoted to official object)

Everything is built from objects already in the tree: `keptPrefix`,
`fullyDefined` (`S⊥`), and the splitting `par`.  Validated here, in order:

1. CR18 §3.2.1's prose as a theorem: a refused query never affects later
   answers (`keptPrefix_delete`, `fullyDefined_delete`).
2. The crux: `keptPrefix` of a composition projects to the components'
   `keptPrefix` of their own sub-histories.
3. The go/no-go homomorphism receipt, as an honest equality:
   `(par c R S)⊥ = par c R⊥ S⊥`.
-/

namespace RandomSystems.System

universe u v

variable {X : Type u} {Y : Type v}

noncomputable section
open Classical

/-! ## 1. The deletion property, stated once -/

theorem keptPrefix_append_foldl (S : DDS X Y) (l₁ l₂ : List X) :
    keptPrefix S (l₁ ++ l₂) =
      l₂.foldl (fun z x => if z ++ [x] ∈ dom S then z ++ [x] else z)
        (keptPrefix S l₁) := by
  simp [keptPrefix, List.foldl_append]

/-- CR18 §3.2.1's prose as a theorem: a refused query is invisible to the
system's later state. -/
theorem keptPrefix_delete (S : DDS X Y) (l₁ l₂ : List X) (x : X)
    (h : keptPrefix S l₁ ++ [x] ∉ dom S) :
    keptPrefix S (l₁ ++ [x] ++ l₂) = keptPrefix S (l₁ ++ l₂) := by
  rw [keptPrefix_append_foldl S (l₁ ++ [x]) l₂, keptPrefix_append_foldl S l₁ l₂,
    keptPrefix_append_singleton, if_neg h]

/-! ## 2. Output of `S⊥` at an arbitrary extended history -/

theorem output_fullyDefined_append (S : DDS X Y) (m : List X) (x : X)
    (h : m ++ [x] ∈ dom S⊥) :
    output S⊥ (m ++ [x]) h =
      if hc : keptPrefix S m ++ [x] ∈ dom S then
        some (output S (keptPrefix S m ++ [x]) hc)
      else none := by
  rw [output_fullyDefined]
  have hdrop : (m ++ [x]).dropLast = m := by simp
  have hlast : (m ++ [x]).getLast (by simp) = x := by simp
  rw [hdrop, hlast]

/-- Observable form of the deletion property: after a refusal, the answers
are the series of answers without the refused attempt. -/
theorem fullyDefined_delete (S : DDS X Y) (l₁ l₂ : List X) (x q : X)
    (h : keptPrefix S l₁ ++ [x] ∉ dom S)
    (hL : l₁ ++ [x] ++ l₂ ++ [q] ∈ dom S⊥)
    (hR : l₁ ++ l₂ ++ [q] ∈ dom S⊥) :
    output S⊥ (l₁ ++ [x] ++ l₂ ++ [q]) hL = output S⊥ (l₁ ++ l₂ ++ [q]) hR := by
  rw [output_fullyDefined_append, output_fullyDefined_append,
    keptPrefix_delete S l₁ l₂ x h]

/-! ## 3. The crux and the homomorphism receipt -/

/-- **The crux**: the kept prefix of the composition projects to the
components' kept prefixes of their own sub-histories. -/
theorem keptPrefix_par_proj (c : Set X) (R S : DDS X Y) (l : List X) :
    historyAt c (keptPrefix (par c R S) l) =
        keptPrefix R (historyAt c l) ∧
      historyAt cᶜ (keptPrefix (par c R S) l) =
        keptPrefix S (historyAt cᶜ l) := by
  induction l using List.reverseRecOn with
  | nil => simp [keptPrefix]
  | append_singleton l x ih =>
    obtain ⟨ihR, ihS⟩ := ih
    have hinv := (keptPrefix_mem_or (par c R S) l).symm
    by_cases hx : x ∈ c
    · have hxc : x ∉ cᶜ := by simpa using hx
      have hiff : (keptPrefix (par c R S) l ++ [x] ∈ dom (par c R S)) ↔
          keptPrefix R (historyAt c l) ++ [x] ∈ dom R := by
        rw [mem_dom_par_concat_mem c R S hx hinv, ihR, ihS]
        exact and_iff_left (keptPrefix_mem_or S (historyAt cᶜ l)).symm
      rw [keptPrefix_append_singleton, historyAt_append_mem c l x hx,
        historyAt_append_not_mem cᶜ l x hxc, keptPrefix_append_singleton]
      by_cases hd : keptPrefix (par c R S) l ++ [x] ∈ dom (par c R S)
      · rw [if_pos hd, if_pos (hiff.mp hd),
          historyAt_append_mem c _ x hx, historyAt_append_not_mem cᶜ _ x hxc,
          ihR, ihS]
        exact ⟨rfl, rfl⟩
      · rw [if_neg hd, if_neg (fun h => hd (hiff.mpr h)), ihR, ihS]
        exact ⟨rfl, rfl⟩
    · have hxc : x ∈ cᶜ := hx
      have hiff : (keptPrefix (par c R S) l ++ [x] ∈ dom (par c R S)) ↔
          keptPrefix S (historyAt cᶜ l) ++ [x] ∈ dom S := by
        rw [mem_dom_par_concat_not_mem c R S hx hinv, ihR, ihS]
        exact and_iff_right (keptPrefix_mem_or R (historyAt c l)).symm
      rw [keptPrefix_append_singleton, historyAt_append_not_mem c l x hx,
        historyAt_append_mem cᶜ l x hxc, keptPrefix_append_singleton]

      by_cases hd : keptPrefix (par c R S) l ++ [x] ∈ dom (par c R S)
      · rw [if_pos hd, if_pos (hiff.mp hd),
          historyAt_append_not_mem c _ x hx, historyAt_append_mem cᶜ _ x hxc,
          ihR, ihS]
        exact ⟨rfl, rfl⟩
      · rw [if_neg hd, if_neg (fun h => hd (hiff.mpr h)), ihR, ihS]
        exact ⟨rfl, rfl⟩

/-- Fully defined systems are closed under `par`: the composition of two
full-domain systems has full domain. -/
theorem dom_par_fullyDefined (c : Set X) (R S : DDS X Y) :
    dom (par c R⊥ S⊥) = {l : List X | l ≠ []} := by
  ext l
  simp only [Set.mem_setOf_eq, mem_dom_par, dom_fullyDefined]
  exact ⟨fun h => h.1, fun h => ⟨h, Classical.em _, Classical.em _⟩⟩

/-- **The go/no-go receipt**: `s⊥` is a homomorphism for parallel composition
at a splitting — CR18's `[s₁,…,sₙ]⊥ = [s₁⊥,…,sₙ⊥]` remark, at our `par`,
as an honest equality. -/
theorem fullyDefined_par (c : Set X) (R S : DDS X Y) :
    (par c R S)⊥ = par c R⊥ S⊥ := by
  apply Subtype.ext
  funext l
  apply Part.ext'
  · show l ∈ dom ((par c R S)⊥) ↔ l ∈ dom (par c R⊥ S⊥)
    rw [dom_fullyDefined, dom_par_fullyDefined]
  · intro h₁ h₂
    show output ((par c R S)⊥) l h₁ = output (par c R⊥ S⊥) l h₂
    have hne : l ≠ [] := by
      have : l ∈ dom ((par c R S)⊥) := h₁
      rwa [dom_fullyDefined] at this
    obtain ⟨m, x, rfl⟩ : ∃ m q, l = m ++ [q] := by
      rcases l.eq_nil_or_concat with rfl | ⟨m, q, rfl⟩
      · exact absurd rfl hne
      · exact ⟨m, q, by simp⟩
    obtain ⟨ihR, ihS⟩ := keptPrefix_par_proj c R S m
    have hinv := (keptPrefix_mem_or (par c R S) m).symm
    by_cases hx : x ∈ c
    · have hRbot : historyAt c m ++ [x] ∈ dom R⊥ := by
        rw [dom_fullyDefined]; simp
      rw [output_par_mem c R⊥ S⊥ m x hx h₂ hRbot,
        output_fullyDefined_append (par c R S) m x h₁,
        output_fullyDefined_append R (historyAt c m) x hRbot]
      have hiff : (keptPrefix (par c R S) m ++ [x] ∈ dom (par c R S)) ↔
          keptPrefix R (historyAt c m) ++ [x] ∈ dom R := by
        rw [mem_dom_par_concat_mem c R S hx hinv, ihR, ihS]
        exact and_iff_left (keptPrefix_mem_or S (historyAt cᶜ m)).symm
      by_cases hd : keptPrefix (par c R S) m ++ [x] ∈ dom (par c R S)
      · have hR' : historyAt c (keptPrefix (par c R S) m) ++ [x] ∈ dom R := by
          rw [ihR]; exact hiff.mp hd
        rw [dif_pos hd, dif_pos (hiff.mp hd),
          output_par_mem c R S _ x hx hd hR']
        exact congrArg some (output_congr R (by rw [ihR]) hR' (hiff.mp hd))
      · rw [dif_neg hd, dif_neg (fun h => hd (hiff.mpr h))]
    · have hSbot : historyAt cᶜ m ++ [x] ∈ dom S⊥ := by
        rw [dom_fullyDefined]; simp
      rw [output_par_not_mem c R⊥ S⊥ m x hx h₂ hSbot,
        output_fullyDefined_append (par c R S) m x h₁,
        output_fullyDefined_append S (historyAt cᶜ m) x hSbot]
      have hiff : (keptPrefix (par c R S) m ++ [x] ∈ dom (par c R S)) ↔
          keptPrefix S (historyAt cᶜ m) ++ [x] ∈ dom S := by
        rw [mem_dom_par_concat_not_mem c R S hx hinv, ihR, ihS]
        exact and_iff_right (keptPrefix_mem_or R (historyAt c m)).symm
      by_cases hd : keptPrefix (par c R S) m ++ [x] ∈ dom (par c R S)
      · have hS' : historyAt cᶜ (keptPrefix (par c R S) m) ++ [x] ∈ dom S := by
          rw [ihS]; exact hiff.mp hd
        rw [dif_pos hd, dif_pos (hiff.mp hd),
          output_par_not_mem c R S _ x hx hd hS']
        exact congrArg some (output_congr S (by rw [ihS]) hS' (hiff.mp hd))
      · rw [dif_neg hd, dif_neg (fun h => hd (hiff.mpr h))]

/-! ## 4. Blocking is parallel composition with the empty system -/

/-- The nowhere-defined DDS: the system that refuses every query.  CR18 has
no name for it; it is what a blocked query set answers with
(`fullyDefined_blockSet`). -/
def emptySystem : DDS X Y :=
  ⟨fun _ => Part.none, ⟨fun h => h, fun _ _ h => h⟩⟩

@[simp]
theorem dom_emptySystem : dom (emptySystem : DDS X Y) = ∅ :=
  rfl

/-- The deletion pass of a blocked system is the unblocked system's pass on
the sub-history of the queries it still answers: a blocked query is refused
outright, so it never enters the kept prefix, and the surviving queries meet
exactly the unblocked frontier test. -/
theorem keptPrefix_blockSet (Q : Set X) (S : DDS X Y) (l : List X) :
    keptPrefix (blockSet Q S) l = keptPrefix S (historyAt Qᶜ l) := by
  induction l using List.reverseRecOn with
  | nil => simp [keptPrefix]
  | append_singleton l x ih =>
    have havoid : ∀ q ∈ keptPrefix (blockSet Q S) l, q ∉ Q := by
      rcases keptPrefix_mem_or (blockSet Q S) l with hd | he
      · exact ((mem_dom_blockSet Q S _).mp hd).2
      · rw [he]
        exact fun q hq => absurd hq (by simp)
    by_cases hx : x ∈ Q
    · have hxc : x ∉ Qᶜ := by simpa using hx
      have hno : keptPrefix (blockSet Q S) l ++ [x] ∉ dom (blockSet Q S) :=
        fun hc => ((mem_dom_blockSet Q S _).mp hc).2 x (by simp) hx
      rw [keptPrefix_append_singleton, if_neg hno,
        historyAt_append_not_mem Qᶜ l x hxc, ih]
    · have hxc : x ∈ Qᶜ := hx
      have hiff : keptPrefix S (historyAt Qᶜ l) ++ [x] ∈ dom (blockSet Q S) ↔
          keptPrefix S (historyAt Qᶜ l) ++ [x] ∈ dom S := by
        rw [mem_dom_blockSet]
        refine and_iff_left (fun q hq => ?_)
        rcases List.mem_append.mp hq with hq' | hq'
        · rw [← ih] at hq'
          exact havoid q hq'
        · rw [List.mem_singleton.mp hq']
          exact hx
      rw [keptPrefix_append_singleton, historyAt_append_mem Qᶜ l x hxc,
        keptPrefix_append_singleton, ih]
      by_cases hd : keptPrefix S (historyAt Qᶜ l) ++ [x] ∈ dom S
      · rw [if_pos hd, if_pos (hiff.mpr hd)]
      · rw [if_neg hd, if_neg (fun h => hd (hiff.mp h))]

/-- **Blocking is `par` with the empty system** (Φ-SPEC ruling R3): silencing
a query set is composing at that splitting with the system that answers
nothing.  Addressing is the splitting; refusal is `⊥`. -/
theorem fullyDefined_blockSet (Q : Set X) (S : DDS X Y) :
    (blockSet Q S)⊥ = par Q (emptySystem : DDS X Y)⊥ S⊥ := by
  apply Subtype.ext
  funext l
  apply Part.ext'
  · show l ∈ dom ((blockSet Q S)⊥) ↔
      l ∈ dom (par Q (emptySystem : DDS X Y)⊥ S⊥)
    rw [dom_fullyDefined, dom_par_fullyDefined]
  · intro h₁ h₂
    show output ((blockSet Q S)⊥) l h₁ =
      output (par Q (emptySystem : DDS X Y)⊥ S⊥) l h₂
    have hne : l ≠ [] := by
      have : l ∈ dom ((blockSet Q S)⊥) := h₁
      rwa [dom_fullyDefined] at this
    obtain ⟨m, x, rfl⟩ : ∃ m q, l = m ++ [q] := by
      rcases l.eq_nil_or_concat with rfl | ⟨m, q, rfl⟩
      · exact absurd rfl hne
      · exact ⟨m, q, by simp⟩
    by_cases hx : x ∈ Q
    · have hEbot : historyAt Q m ++ [x] ∈ dom (emptySystem : DDS X Y)⊥ := by
        rw [dom_fullyDefined]
        simp
      rw [output_par_mem Q (emptySystem : DDS X Y)⊥ S⊥ m x hx h₂ hEbot,
        output_fullyDefined_append (blockSet Q S) m x h₁,
        output_fullyDefined_append (emptySystem : DDS X Y) (historyAt Q m) x
          hEbot]
      have hno : keptPrefix (blockSet Q S) m ++ [x] ∉ dom (blockSet Q S) :=
        fun hc => ((mem_dom_blockSet Q S _).mp hc).2 x (by simp) hx
      have hnoE : keptPrefix (emptySystem : DDS X Y) (historyAt Q m) ++ [x] ∉
          dom (emptySystem : DDS X Y) := by
        rw [dom_emptySystem]
        simp
      rw [dif_neg hno, dif_neg hnoE]
    · have hSbot : historyAt Qᶜ m ++ [x] ∈ dom S⊥ := by
        rw [dom_fullyDefined]
        simp
      rw [output_par_not_mem Q (emptySystem : DDS X Y)⊥ S⊥ m x hx h₂ hSbot,
        output_fullyDefined_append (blockSet Q S) m x h₁,
        output_fullyDefined_append S (historyAt Qᶜ m) x hSbot]
      have havoid : ∀ q ∈ keptPrefix (blockSet Q S) m, q ∉ Q := by
        rcases keptPrefix_mem_or (blockSet Q S) m with hd | he
        · exact ((mem_dom_blockSet Q S _).mp hd).2
        · rw [he]
          exact fun q hq => absurd hq (by simp)
      have hkept := keptPrefix_blockSet Q S m
      have hiff : keptPrefix (blockSet Q S) m ++ [x] ∈ dom (blockSet Q S) ↔
          keptPrefix S (historyAt Qᶜ m) ++ [x] ∈ dom S := by
        rw [mem_dom_blockSet, hkept]
        refine and_iff_left (fun q hq => ?_)
        rcases List.mem_append.mp hq with hq' | hq'
        · rw [← hkept] at hq'
          exact havoid q hq'
        · rw [List.mem_singleton.mp hq']
          exact hx
      by_cases hd : keptPrefix (blockSet Q S) m ++ [x] ∈ dom (blockSet Q S)
      · rw [dif_pos hd, dif_pos (hiff.mp hd)]
        exact congrArg some ((output_blockSet Q S _ hd).trans
          (output_congr S (by rw [hkept]) hd.1 (hiff.mp hd)))
      · rw [dif_neg hd, dif_neg (fun h => hd (hiff.mpr h))]

/-- **The relabelling crux** (A7): a relabelled system's kept prefix is the
original's kept prefix of the translated history.  Pointwise, with no window:
the relabelling has no state, so a query is accepted exactly when its
translation is, and a refusal on one side is a refusal on the other. -/
theorem keptPrefix_relabel {X' : Type*} {Y' : Type*} (f : X' → X) (g : Y → Y')
    (S : DDS X Y) (l : List X') :
    (keptPrefix (relabel f g S) l).map f = keptPrefix S (l.map f) := by
  induction l using List.reverseRecOn with
  | nil => simp [keptPrefix]
  | append_singleton l x ih =>
      have hiff : keptPrefix (relabel f g S) l ++ [x] ∈ dom (relabel f g S) ↔
          keptPrefix S (l.map f) ++ [f x] ∈ dom S := by
        rw [mem_dom_relabel, List.map_append, ih]
        simp
      rw [keptPrefix_append_singleton]
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [keptPrefix_append_singleton]
      by_cases hd : keptPrefix (relabel f g S) l ++ [x] ∈ dom (relabel f g S)
      · rw [if_pos hd, if_pos (hiff.mp hd)]
        simp only [List.map_append, List.map_cons, List.map_nil, ih]
      · rw [if_neg hd, if_neg fun hc => hd (hiff.mpr hc), ih]

/-- **The tagged block's receipt** (A7): silencing an *interface* set is the
query-set block at the tag cylinder (`block_eq_blockSet`, definitional), so its
`s⊥`-receipt is `fullyDefined_blockSet` there — blocking an interface is `par`
with the empty system at the cylinder of its queries. -/
theorem fullyDefined_block {P : Type u} {A : Type v} {B : Type*}
    (Z : Set P) (S : Resource P A B) :
    (block Z S)⊥ =
      par {p : P × A | p.1 ∈ Z} (emptySystem : Resource P A B)⊥ S⊥ := by
  rw [block_eq_blockSet]
  exact fullyDefined_blockSet _ S

end

end RandomSystems.System

namespace RandomSystems

/-! ## 5. The fully defined slice inside Φ -/

noncomputable section

open Probability (Distribution)

universe u

/-- **The fully defined slice of Φ** (Φ-SPEC ruling R1): the laws supported on
systems that answer every nonempty history.  This is the official interaction
carrier one level up — `S⊥` lands here for every `S`, and so does everything
built from full-domain systems by `par`.

Attach-closure is **not** claimed, and does not hold: attaching a partial
converter to a member leaves the slice, since the composite is undefined
wherever the converter is.  Per ruling R4 that is the metric layer's business,
not the carrier's — statements are made about `Adv⊥`, which completes both
sides before comparing them, so leaving the slice costs nothing. -/
def fullyDefinedSpec : Set Phi.{u} :=
  {L | ∀ S ∈ L.support, System.dom S = {l : List Uni.{u} | l ≠ []}}

/-- The slice is closed under parallel composition: `par` on Φ samples the two
components independently and runs the pair as `System.par`, and a composition
of two full-domain systems answers every nonempty history. -/
theorem par_mem_fullyDefinedSpec {c : Set Uni.{u}} {RL SL : Phi.{u}}
    (hR : RL ∈ fullyDefinedSpec) (hS : SL ∈ fullyDefinedSpec) :
    par c RL SL ∈ fullyDefinedSpec := by
  intro T hT
  have hT' : T ∈ (Distribution.fTransform
      (fun p : System.DDS Uni.{u} Uni.{u} × System.DDS Uni.{u} Uni.{u} =>
        System.par c p.1 p.2) (Distribution.prod RL SL)).support := hT
  obtain ⟨p, hp, rfl⟩ :=
    Distribution.exists_mem_support_of_mem_support_fTransform _ _ hT'
  obtain ⟨hp₁, hp₂⟩ :=
    Finset.mem_product.mp (Distribution.support_prod_subset RL SL hp)
  have hdomR : System.dom p.1 = {l : List Uni.{u} | l ≠ []} := hR p.1 hp₁
  have hdomS : System.dom p.2 = {l : List Uni.{u} | l ≠ []} := hS p.2 hp₂
  show System.dom (System.par c p.1 p.2) = {l : List Uni.{u} | l ≠ []}
  ext l
  rw [System.mem_dom_par, hdomR, hdomS]
  simp only [Set.mem_setOf_eq]
  exact ⟨fun h => h.1, fun h => ⟨h, Classical.em _, Classical.em _⟩⟩

end

end RandomSystems

