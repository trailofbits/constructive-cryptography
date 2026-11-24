module

public import RandomSystems.Typed.CallFunctional
public import RandomSystems.Typed.ParallelAttachment
public import RandomSystems.Typed.SamplingAlgebra
public import RandomSystems.Typed.DSL.Converters

/-!
# Write-only record erasure

A write-only recording converter `record : TypedConverter A (Interface.tensor A B)` forwards each
query of `A` to the left component `Y` while making side calls to the right component `H` whose
replies do not affect the visible outputs on `A`. When attached to `Y ∥ H`, the right component
erases completely: `record • (Y ∥ H) = Y`, preserving state, shared randomness, and domains for
arbitrary typed systems `Y` and `H`.

## Main definitions

* `TypedConverter.WriteOnlyRecord A B`: reusable erasure contract packaging legal-call domain
  certification (`isDDCFrom`) with reply faithfulness and non-interference (`realizes`)
* `TypedConverter.recordAndForwardProgram`, `TypedConverter.recordAndForward`: function-backed
  write-only recorder forwarding `A` and optionally issuing one write-only query to `B`

## Main results

* `TypedConverter.WriteOnlyRecord.smul_parallel`: `w.toConverter • (Y ∥ H) = Y`
* `TypedConverter.comp_smul_parallel_of_erases`, `TypedConverter.smul_sample_parallel_of_erases`,
  `TypedConverter.comp_smul_sample_parallel_of_erases`,
  `TypedConverter.parallel_smul_parallel_of_erases`: transport through outer converters, retained
  sampling, and parallel contexts from existing attachment laws
* `TypedConverter.recordAndForward_writeOnlyRecord`,
  `TypedConverter.recordAndForward_smul_parallel`,
  `TypedConverter.recordAndForward_smul_parallel_ofFunction`: erasure for the function-backed
  recorder
-/

@[expose] public section

set_option autoImplicit false

namespace SystemAlgebra.TypedConverter

open Probability

/-! ### Parallel exchange projections -/

/-- Left-side (`A`) projection of an exchange list on `Interface.tensor A B`. -/
def leftExchanges {A B : Interface}
    (qs : List ((Σ l, (Interface.tensor A B).X l) × (Σ l, (Interface.tensor A B).Y l))) :
    List ((Σ i, A.X i) × (Σ i, A.Y i)) :=
  RandomSystem.parallelLeft
    (qs.map ((sumAlphabet (Sum.rec A.X B.X)).symm.prodCongr
      (sumAlphabet (Sum.rec A.Y B.Y)).symm))

/-- Right-side (`B`) projection of an exchange list on `Interface.tensor A B`. -/
def rightExchanges {A B : Interface}
    (qs : List ((Σ l, (Interface.tensor A B).X l) × (Σ l, (Interface.tensor A B).Y l))) :
    List ((Σ j, B.X j) × (Σ j, B.Y j)) :=
  RandomSystem.parallelRight
    (qs.map ((sumAlphabet (Sum.rec A.X B.X)).symm.prodCongr
      (sumAlphabet (Sum.rec A.Y B.Y)).symm))

lemma leftExchanges_append {A B : Interface}
    (qs₁ qs₂ : List ((Σ l, (Interface.tensor A B).X l) × (Σ l, (Interface.tensor A B).Y l))) :
    leftExchanges (qs₁ ++ qs₂) = leftExchanges qs₁ ++ leftExchanges qs₂ := by
  simp [leftExchanges, RandomSystem.parallelLeft, List.filterMap_append]

lemma rightExchanges_append {A B : Interface}
    (qs₁ qs₂ : List ((Σ l, (Interface.tensor A B).X l) × (Σ l, (Interface.tensor A B).Y l))) :
    rightExchanges (qs₁ ++ qs₂) = rightExchanges qs₁ ++ rightExchanges qs₂ := by
  simp [rightExchanges, RandomSystem.parallelRight, List.filterMap_append]

lemma leftExchanges_inl_singleton {A B : Interface} (i : A.I) (x : A.X i) (y : A.Y i) :
    leftExchanges (A := A) (B := B) [(⟨Sum.inl i, x⟩, ⟨Sum.inl i, y⟩)] = [(⟨i, x⟩, ⟨i, y⟩)] :=
  rfl

lemma rightExchanges_inl_singleton {A B : Interface} (i : A.I) (x : A.X i) (y : A.Y i) :
    rightExchanges (A := A) (B := B) [(⟨Sum.inl i, x⟩, ⟨Sum.inl i, y⟩)] = [] :=
  rfl

lemma leftExchanges_inr_singleton {A B : Interface} (j : B.I) (x : B.X j) (y : B.Y j) :
    leftExchanges (A := A) (B := B) [(⟨Sum.inr j, x⟩, ⟨Sum.inr j, y⟩)] = [] :=
  rfl

lemma rightExchanges_inr_singleton {A B : Interface} (j : B.I) (x : B.X j) (y : B.Y j) :
    rightExchanges (A := A) (B := B) [(⟨Sum.inr j, x⟩, ⟨Sum.inr j, y⟩)] = [(⟨j, x⟩, ⟨j, y⟩)] :=
  rfl

/-- A parallel deterministic resource answers a combined transcript iff the transcript stays
side-consistent and both components answer their projections. -/
lemma replies_parallelSystem_iff {A B : Interface}
    (s : InterfaceSystem A.I A.X A.Y) (t : InterfaceSystem B.I B.X B.Y)
    (qs : List ((Σ l, (Interface.tensor A B).X l) × (Σ l, (Interface.tensor A B).Y l))) :
    Replies (relabel (trim (pair s t))
        (sumAlphabet (Sum.rec A.X B.X)).symm
        (sumAlphabet (Sum.rec A.Y B.Y)))
      (qs.map Prod.fst) (qs.map Prod.snd) ↔
      RandomSystem.parallelConsistent
        (qs.map ((sumAlphabet (Sum.rec A.X B.X)).symm.prodCongr
          (sumAlphabet (Sum.rec A.Y B.Y)).symm)) ∧
      Replies s ((leftExchanges qs).map Prod.fst) ((leftExchanges qs).map Prod.snd) ∧
      Replies t ((rightExchanges qs).map Prod.fst) ((rightExchanges qs).map Prod.snd) := by
  rw [replies_relabel_iff, replies_trim_iff]
  exact RandomSystem.replies_pair_iff s t _

/-! ### Reusable write-only erasure contract -/

/-- Reusable write-only recording contract on `A ⟶ A ⊗ B`: a certified DDC (`isDDCFrom`) that
realizes every admitted `A`-transcript against any `B`-system `t` by forwarding exactly `h` to
`A` while making side calls answered by `t` without affecting the outputs on `A`. -/
structure WriteOnlyRecord (A B : Interface) where
  /-- Underlying deterministic converter. -/
  converter : InsideOutsideSystem A.I (Interface.tensor A B).I A.X A.Y
    (Interface.tensor A B).X (Interface.tensor A B).Y
  /-- Consecutive inside-query bound. -/
  bound : ℕ
  /-- Legal-call and domain certificate from `A ⊗ B` to `A`. -/
  isDDCFrom : IsDDCFrom (Interface.tensor A B).domain A.domain bound converter
  /-- Reply faithfulness and non-interference: for every admitted `A`-transcript `h` (with replies
  at queried ports) and every deterministic `B`-system `t` on `B.domain`, `converter` executes a
  completed call sequence matching `h` outside, forwarding exactly `h` on the left, and issuing
  only side-consistent right queries answered by `t`. -/
  realizes :
    ∀ (h : List ((Σ i, A.X i) × (Σ i, A.Y i))) (t : InterfaceSystem B.I B.X B.Y),
      A.domain (h.map Prod.fst) →
      (∀ z ∈ h, z.2.1 = z.1.1) →
      IsDDS t → RepliesAtQueriedInterface t → (∀ xs, (t xs).Dom ↔ B.domain xs) →
      ∃ calls : List ((Σ i, A.X i) ×
          List ((Σ l, (Interface.tensor A B).X l) × (Σ l, (Interface.tensor A B).Y l)) ×
          (Σ i, A.Y i)),
        calls.map (fun c => (c.1, c.2.2)) = h ∧
        Replies converter
          ((calls.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.fst)
          ((calls.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.snd) ∧
        RandomSystem.parallelConsistent
          ((calls.flatMap (·.2.1)).map
            ((sumAlphabet (Sum.rec A.X B.X)).symm.prodCongr
              (sumAlphabet (Sum.rec A.Y B.Y)).symm)) ∧
        leftExchanges (calls.flatMap (·.2.1)) = h ∧
        Replies t
          ((rightExchanges (calls.flatMap (·.2.1))).map Prod.fst)
          ((rightExchanges (calls.flatMap (·.2.1))).map Prod.snd)

/-- The typed converter presented by a write-only recording contract. -/
noncomputable def WriteOnlyRecord.toConverter {A B : Interface} (w : WriteOnlyRecord A B) :
    TypedConverter A (Interface.tensor A B) :=
  TypedConverter.ofDDC w.converter w.isDDCFrom

/-- Deterministic erasure: attaching `w.converter` to `s ∥ t` produces the same transcripts as `s`
for every deterministic `s` on `A.domain` and `t` on `B.domain`. -/
lemma WriteOnlyRecord.replies_trim_apply_iff {A B : Interface} (w : WriteOnlyRecord A B)
    {s : InterfaceSystem A.I A.X A.Y} {t : InterfaceSystem B.I B.X B.Y}
    (hs : IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ xs, (s xs).Dom ↔ A.domain xs)
    (ht : IsDDS t ∧ RepliesAtQueriedInterface t ∧ ∀ xs, (t xs).Dom ↔ B.domain xs)
    (xs : List (Σ i, A.X i)) (ys : List (Σ i, A.Y i)) :
    Replies (trim (apply w.converter
      (relabel (trim (pair s t))
        (sumAlphabet (Sum.rec A.X B.X)).symm
        (sumAlphabet (Sum.rec A.Y B.Y))))) xs ys ↔
      Replies s xs ys := by
  let st := relabel (trim (pair s t))
    (sumAlphabet (Sum.rec A.X B.X)).symm
    (sumAlphabet (Sum.rec A.Y B.Y))
  have hst := parallel_system_valid hs ht
  have hdom : ∀ h, (s h).Dom ↔ (trim (apply w.converter st) h).Dom := fun h =>
    (hs.2.2 h).trans ((w.isDDCFrom.mapsDomain A.nonempty_prefix st hst.1 hst.2.1 hst.2.2).2 h).symm
  refine (replies_iff_of_dom_iff hdom (fun xs ys hr => ?_) xs ys).symm
  by_cases hne : xs = []
  · subst hne
    obtain rfl : ys = [] := List.eq_nil_of_length_eq_zero hr.length
    exact replies_nil _
  · have hA : A.domain xs := (hs.2.2 xs).mp (hr.dom hne)
    have hlen : ys.length = xs.length := hr.length
    let h := xs.zip ys
    have hfst : h.map Prod.fst = xs := List.map_fst_zip hlen.ge
    have hsnd : h.map Prod.snd = ys := List.map_snd_zip hlen.le
    have hport : ∀ z ∈ h, z.2.1 = z.1.1 := by
      intro z hz
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
      have hi1 : i < xs.length := by
        simpa [h, List.length_zip, hlen] using hi
      have hi2 : i < ys.length := by omega
      have hrep := hr.2 i hi1 hi2
      have htake : xs.take (i + 1) = xs.take i ++ [xs[i]] := List.take_succ_eq_append_getElem hi1
      rw [htake] at hrep
      have hmem : ys[i] ∈ s (xs.take i ++ [xs[i]]) := Part.eq_some_iff.mp hrep
      simpa [h, List.getElem_zip] using hs.2.1 (xs.take i) xs[i] ys[i] hmem
    obtain ⟨calls, hmap, hconv, hcons, hleft, hright⟩ :=
      w.realizes h t (by rwa [hfst]) hport ht.1 ht.2.1 ht.2.2
    have hst_rep : Replies st
        ((calls.flatMap (·.2.1)).map Prod.fst) ((calls.flatMap (·.2.1)).map Prod.snd) := by
      refine (replies_parallelSystem_iff s t _).mpr ⟨hcons, ?_, hright⟩
      rw [hleft, hfst, hsnd]
      exact hr
    have happ := replies_apply_of_calls calls hconv hst_rep
    have hcfst : calls.map (·.1) = xs := by
      have := congrArg (List.map Prod.fst) hmap
      simpa only [List.map_map, Function.comp_def, hfst] using this
    have hcsnd : calls.map (·.2.2) = ys := by
      have := congrArg (List.map Prod.snd) hmap
      simpa only [List.map_map, Function.comp_def, hsnd] using this
    rw [hcfst, hcsnd] at happ
    rwa [replies_trim_iff]

/-- **Write-only record erasure**: attaching a write-only recorder to `Y ∥ H` erases `H` and
returns `Y`, for arbitrary typed systems `Y` and `H`. -/
theorem WriteOnlyRecord.smul_parallel {A B : Interface} (w : WriteOnlyRecord A B)
    (Y : TypedSystem A) (H : TypedSystem B) :
    w.toConverter • TypedSystem.parallel Y H = Y := by
  obtain ⟨P, rfl⟩ := Y.exists_ofPDS
  obtain ⟨Q, rfl⟩ := H.exists_ofPDS
  rw [TypedSystem.parallel_ofPDS]
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [WriteOnlyRecord.toConverter, ofDDC_smul_ofPDS_mass w.isDDCFrom (parallelPDS P Q) h]
  simp only [parallelPDS, Distribution.mass_fTransform]
  have hcongr : (Distribution.prod P.1 Q.1).mass (fun st =>
      Replies (trim (apply w.converter
        (relabel (trim (pair st.1.1 st.2.1))
          (sumAlphabet (Sum.rec A.X B.X)).symm
          (sumAlphabet (Sum.rec A.Y B.Y)))))
        (h.map Prod.fst) (h.map Prod.snd)) =
      (Distribution.prod P.1 Q.1).mass (fun st =>
        Replies st.1.1 (h.map Prod.fst) (h.map Prod.snd)) :=
    Distribution.mass_congr _ fun st => w.replies_trim_apply_iff st.1.2 st.2.2 _ _
  rw [hcongr,
    Distribution.mass_prod_fst P.1 Q.1 (fun s => Replies s.1 (h.map Prod.fst) (h.map Prod.snd)),
    Q.2.2, mul_one]
  rfl

/-! ### Transport through outer converters, shared randomness, and parallel contexts -/

/-- Transporting erasure through an arbitrary outer converter `α`. -/
lemma comp_smul_parallel_of_erases {A B C : Interface}
    {record : TypedConverter A (Interface.tensor A B)} (α : TypedConverter C A)
    {Y : TypedSystem A} {H : TypedSystem B}
    (herase : record • TypedSystem.parallel Y H = Y) :
    TypedConverter.comp α record • TypedSystem.parallel Y H = α • Y := by
  rw [TypedConverter.comp_smul, herase]

/-- Transporting erasure inside a retained sample preserves shared randomness. -/
lemma smul_sample_parallel_of_erases {A B : Interface} {K : Type}
    {record : TypedConverter A (Interface.tensor A B)}
    (P : Distribution.ProbDist K) (Y : K → TypedSystem A) (H : K → TypedSystem B)
    (herase : ∀ k, record • TypedSystem.parallel (Y k) (H k) = Y k) :
    record • TypedSystem.sample P (fun k => TypedSystem.parallel (Y k) (H k)) =
      TypedSystem.sample P Y := by
  rw [TypedConverter.smul_sample]
  exact congrArg (TypedSystem.sample P) (funext herase)

/-- Transporting erasure under both an outer converter `α` and a retained sample `P`. -/
lemma comp_smul_sample_parallel_of_erases {A B C : Interface} {K : Type}
    {record : TypedConverter A (Interface.tensor A B)} (α : TypedConverter C A)
    (P : Distribution.ProbDist K) (Y : K → TypedSystem A) (H : K → TypedSystem B)
    (herase : ∀ k, record • TypedSystem.parallel (Y k) (H k) = Y k) :
    TypedConverter.comp α record •
        TypedSystem.sample P (fun k => TypedSystem.parallel (Y k) (H k)) =
      TypedSystem.sample P (fun k => α • Y k) := by
  rw [TypedConverter.comp_smul, smul_sample_parallel_of_erases P Y H herase,
    TypedConverter.smul_sample]

/-- Transporting erasure beside an arbitrary parallel context `β` and `Z`. -/
lemma parallel_smul_parallel_of_erases {A B C D : Interface}
    {record : TypedConverter A (Interface.tensor A B)} (β : TypedConverter C D)
    {Y : TypedSystem A} {H : TypedSystem B} (Z : TypedSystem D)
    (herase : record • TypedSystem.parallel Y H = Y) :
    TypedConverter.parallel record β • TypedSystem.parallel (TypedSystem.parallel Y H) Z =
      TypedSystem.parallel Y (β • Z) := by
  rw [TypedConverter.parallel_attach, herase]

lemma WriteOnlyRecord.comp_smul_parallel {A B C : Interface} (w : WriteOnlyRecord A B)
    (α : TypedConverter C A) (Y : TypedSystem A) (H : TypedSystem B) :
    TypedConverter.comp α w.toConverter • TypedSystem.parallel Y H = α • Y :=
  comp_smul_parallel_of_erases α (w.smul_parallel Y H)

lemma WriteOnlyRecord.smul_sample {A B : Interface} {K : Type} (w : WriteOnlyRecord A B)
    (P : Distribution.ProbDist K) (Y : K → TypedSystem A) (H : K → TypedSystem B) :
    w.toConverter • TypedSystem.sample P (fun k => TypedSystem.parallel (Y k) (H k)) =
      TypedSystem.sample P Y :=
  smul_sample_parallel_of_erases P Y H fun k => w.smul_parallel (Y k) (H k)

lemma WriteOnlyRecord.comp_smul_sample {A B C : Interface} {K : Type} (w : WriteOnlyRecord A B)
    (α : TypedConverter C A) (P : Distribution.ProbDist K) (Y : K → TypedSystem A)
    (H : K → TypedSystem B) :
    TypedConverter.comp α w.toConverter •
        TypedSystem.sample P (fun k => TypedSystem.parallel (Y k) (H k)) =
      TypedSystem.sample P (fun k => α • Y k) :=
  comp_smul_sample_parallel_of_erases α P Y H fun k => w.smul_parallel (Y k) (H k)

lemma WriteOnlyRecord.parallel_smul_parallel {A B C D : Interface} (w : WriteOnlyRecord A B)
    (β : TypedConverter C D) (Y : TypedSystem A) (H : TypedSystem B) (Z : TypedSystem D) :
    TypedConverter.parallel w.toConverter β •
        TypedSystem.parallel (TypedSystem.parallel Y H) Z =
      TypedSystem.parallel Y (β • Z) :=
  parallel_smul_parallel_of_erases β Z (w.smul_parallel Y H)

/-! ### Function-backed write-only recorder -/

open Classical in
/-- Extract the optional right-side record query from a port-consistent `A`-exchange. -/
noncomputable def recordExchange {A B : Interface}
    (record : ∀ i : A.I, A.X i → A.Y i → Option (Σ j : B.I, B.X j))
    (z : (Σ i, A.X i) × (Σ i, A.Y i)) : Option (Σ j, B.X j) :=
  if h : z.2.1 = z.1.1 then record z.1.1 z.1.2 (h ▸ z.2.2) else none

/-- Program forwarding each outside query `i(x)` to the left component `A`, optionally sending
one write-only record query `record i x y` to `B` while ignoring its reply, and returning `y`. -/
noncomputable def recordAndForwardProgram {A B : Interface}
    (record : ∀ i : A.I, A.X i → A.Y i → Option (Σ j : B.I, B.X j)) :
    Program Unit A.I (Interface.tensor A B).I A.X A.Y
      (Interface.tensor A B).X (Interface.tensor A B).Y :=
  fun _ i x =>
    DSL.callProg (Sum.inl i) x fun y =>
      match record i x y with
      | none => DSL.returnProg ((), y)
      | some q => DSL.callProg (Sum.inr q.1) q.2 fun _ => DSL.returnProg ((), y)

lemma recordAndForwardProgram_bounded {A B : Interface}
    (record : ∀ i : A.I, A.X i → A.Y i → Option (Σ j : B.I, B.X j)) :
    (recordAndForwardProgram record).Bounded 2 := by
  intro _ i x
  refine DSL.callBound_call (X := (Interface.tensor A B).X) (Y := (Interface.tensor A B).Y)
    (Sum.inl i) x _ fun y => ?_
  cases record i x y with
  | none => exact DSL.callBound_return 1 ((), y)
  | some q =>
    exact DSL.callBound_call (X := (Interface.tensor A B).X) (Y := (Interface.tensor A B).Y)
      (Sum.inr q.1) q.2 _ fun _ => DSL.callBound_return 0 ((), y)

/-- Along every transcript of `recordAndForwardProgram`, the left inside queries match the outside
inputs and the right inside queries are the recorded queries of a port-consistent prefix of the
outside exchanges. -/
lemma recordAndForwardProgram_queries_invariant {A B : Interface}
    (record : ∀ i : A.I, A.X i → A.Y i → Option (Σ j : B.I, B.X j))
    {t : List ((Σ l, twoFam A.X (Interface.tensor A B).Y l) ×
      (Σ l, twoFam A.Y (Interface.tensor A B).X l))}
    (hr : Replies (DDC.ofProgram () (recordAndForwardProgram record))
      (t.map Prod.fst) (t.map Prod.snd)) :
    ∃ m, (recordAndForwardProgram record).after () (t.map Prod.fst) = some m ∧
      restrict none ((insideQueries (t.map Prod.snd)).map
          (sumAlphabet (Sum.rec A.X B.X)).symm) =
        outsideInputs (t.map Prod.fst) ∧
      ∃ h : List ((Σ i, A.X i) × (Σ i, A.Y i)),
        (∀ z ∈ h, z.2.1 = z.1.1) ∧
        restrict (some ()) ((insideQueries (t.map Prod.snd)).map
            (sumAlphabet (Sum.rec A.X B.X)).symm) =
          h.filterMap (recordExchange record) ∧
        match m with
        | .idle () => h.map Prod.fst = outsideInputs (t.map Prod.fst)
        | .busy i () x [] ⟨.inl i', x'⟩ =>
            i' = i ∧ HEq x' x ∧
              h.map Prod.fst ++ [⟨i, x⟩] = outsideInputs (t.map Prod.fst)
        | .busy i () x [(⟨.inl i', x'⟩, ⟨.inl i'', _⟩)] ⟨.inr _, _⟩ =>
            i' = i ∧ i'' = i ∧ HEq x' x ∧
              h.map Prod.fst = outsideInputs (t.map Prod.fst)
        | _ => False := by
  induction t using List.reverseRecOn with
  | nil =>
    exact ⟨.idle (), rfl, rfl, [], fun _ h => False.elim (List.not_mem_nil h), rfl, rfl⟩
  | append_singleton t z ih =>
    rcases z with ⟨x, y⟩
    simp only [List.map_append, List.map_singleton] at hr ⊢
    obtain ⟨hr₀, hy⟩ := replies_snoc.mp hr
    obtain ⟨m₀, hm₀, hleft₀, h, hport, hright₀, hmode⟩ := ih hr₀
    have hmem : y ∈ DDC.ofProgram () (recordAndForwardProgram record) (t.map Prod.fst ++ [x]) := by
      rw [hy]; exact Part.mem_some y
    obtain ⟨m₁, m', h₁, hstep⟩ := (DDC.mem_ofProgram_snoc () _ _ x y).mp hmem
    rw [hm₀] at h₁
    obtain rfl := Option.some.inj h₁
    have hm' : (recordAndForwardProgram record).after () (t.map Prod.fst ++ [x]) = some m' :=
      (Program.after_snoc_eq_some _ () _ x m').mpr ⟨m₀, y, hm₀, hstep⟩
    refine ⟨m', hm', ?_, ?_⟩
    · rw [insideQueries_append, outsideInputs_append, List.map_append, restrict_append, hleft₀]
      rcases Program.step_cases _ hstep with
          ⟨⟨⟩, o, u, rfl, rfl, he⟩ | ⟨o, ⟨⟩, u, hs, q, v, rfl, rfl, he⟩
      · simp only [Program.emit, recordAndForwardProgram, DSL.callProg] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        simp [insideQueries, outsideInputs, splitIn, sumAlphabet, restrict]
      · rcases hs with _ | ⟨e₁, hs'⟩
        · rcases q with ⟨i' | j', qx⟩
          · obtain ⟨hi, hx', -⟩ := hmode
            subst i'
            have hx : qx = u := eq_of_heq hx'
            subst qx
            simp only [Program.emit, recordAndForwardProgram, DSL.callProg, List.nil_append,
              ↓reduceDIte] at he
            cases hrec : record o u v with
            | none =>
              simp only [hrec, DSL.returnProg] at he
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
              simp [insideQueries, outsideInputs, splitIn, restrict]
            | some q' =>
              simp only [hrec, DSL.callProg] at he
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
              simp [insideQueries, outsideInputs, splitIn, sumAlphabet, restrict]
          · simp at hmode
        · rcases hs' with _ | ⟨e₂, hs''⟩
          · rcases e₁ with ⟨⟨i₁ | j₁, x₁⟩, ⟨i₂ | j₂, y₁⟩⟩
            · rcases q with ⟨i' | j', qx⟩
              · simp at hmode
              · obtain ⟨hi₁, hi₂, hx', -⟩ := hmode
                subst i₁ i₂
                have hx : x₁ = u := eq_of_heq hx'
                subst x₁
                simp only [Program.emit, recordAndForwardProgram, DSL.callProg,
                  List.singleton_append, ↓reduceDIte] at he
                cases hrec : record o u y₁ with
                | none =>
                  simp only [hrec, DSL.returnProg] at he
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
                  simp [insideQueries, outsideInputs, splitIn, restrict]
                | some q' =>
                  simp only [hrec, DSL.callProg] at he
                  split_ifs at he with hq'
                  · simp only [DSL.returnProg] at he
                    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
                    simp [insideQueries, outsideInputs, splitIn, restrict]
                  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
                    simp [insideQueries, outsideInputs, splitIn, sumAlphabet, restrict]
            all_goals simp at hmode
          · simp at hmode
    · rw [insideQueries_append, outsideInputs_append, List.map_append, restrict_append, hright₀]
      rcases Program.step_cases _ hstep with
          ⟨⟨⟩, o, u, rfl, rfl, he⟩ | ⟨o, ⟨⟩, u, hs, q, v, rfl, rfl, he⟩
      · simp only [Program.emit, recordAndForwardProgram, DSL.callProg] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        refine ⟨h, hport, ?_, rfl, HEq.rfl, ?_⟩
        · simp [insideQueries, splitIn, sumAlphabet, restrict]
        · simpa [outsideInputs, splitIn, restrict] using congrArg (· ++ [⟨o, u⟩]) hmode
      · rcases hs with _ | ⟨e₁, hs'⟩
        · rcases q with ⟨i' | j', qx⟩
          · obtain ⟨hi, hx', hpref⟩ := hmode
            subst i'
            have hx : qx = u := eq_of_heq hx'
            subst qx
            simp only [Program.emit, recordAndForwardProgram, DSL.callProg, List.nil_append,
              ↓reduceDIte] at he
            cases hrec : record o u v with
            | none =>
              simp only [hrec, DSL.returnProg] at he
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
              refine ⟨h ++ [(⟨o, u⟩, ⟨o, v⟩)], ?_, ?_, ?_⟩
              · intro z hz
                rcases List.mem_append.mp hz with hz | hz
                · exact hport z hz
                · rw [List.mem_singleton.mp hz]
              · simp [insideQueries, splitIn, restrict, List.filterMap_append, recordExchange, hrec]
              · simpa [outsideInputs, splitIn, restrict] using hpref
            | some q' =>
              simp only [hrec, DSL.callProg] at he
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
              refine ⟨h ++ [(⟨o, u⟩, ⟨o, v⟩)], ?_, ?_, rfl, rfl, HEq.rfl, ?_⟩
              · intro z hz
                rcases List.mem_append.mp hz with hz | hz
                · exact hport z hz
                · rw [List.mem_singleton.mp hz]
              · simp [insideQueries, splitIn, sumAlphabet, restrict,
                  List.filterMap_append, recordExchange, hrec]
              · simpa [outsideInputs, splitIn, restrict] using hpref
          · simp at hmode
        · rcases hs' with _ | ⟨e₂, hs''⟩
          · rcases e₁ with ⟨⟨i₁ | j₁, x₁⟩, ⟨i₂ | j₂, y₁⟩⟩
            · rcases q with ⟨i' | j', qx⟩
              · simp at hmode
              · obtain ⟨hi₁, hi₂, hx', hpref⟩ := hmode
                subst i₁ i₂
                have hx : x₁ = u := eq_of_heq hx'
                subst x₁
                simp only [Program.emit, recordAndForwardProgram, DSL.callProg,
                  List.singleton_append, ↓reduceDIte] at he
                cases hrec : record o u y₁ with
                | none =>
                  simp only [hrec, DSL.returnProg] at he
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
                  refine ⟨h, hport, ?_, ?_⟩
                  · simp [insideQueries, splitIn, restrict]
                  · simpa [outsideInputs, splitIn, restrict] using hpref
                | some q' =>
                  simp only [hrec, DSL.callProg] at he
                  split_ifs at he with hq'
                  · simp only [DSL.returnProg] at he
                    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
                    refine ⟨h, hport, ?_, ?_⟩
                    · simp [insideQueries, splitIn, restrict]
                    · simpa [outsideInputs, splitIn, restrict] using hpref
                  · have hsound := (DDC.after_invariant hm₀).1
                    have hqeq := hsound.2
                    simp only [recordAndForwardProgram, DSL.callProg, ↓reduceDIte, hrec] at hqeq
                    have hsum := Sum.inr.inj hqeq
                    exact absurd (congrArg Sigma.fst hsum).symm hq'
            all_goals simp at hmode
          · simp at hmode

/-- Legal-call certificate for `recordAndForwardProgram` whenever every admitted `A`-exchange
history produces either no record queries or a record-query history in `B.domain`. -/
lemma recordAndForwardProgram_isDDCFrom {A B : Interface}
    (record : ∀ i : A.I, A.X i → A.Y i → Option (Σ j : B.I, B.X j))
    (hrec : ∀ h : List ((Σ i, A.X i) × (Σ i, A.Y i)),
      A.domain (h.map Prod.fst) → (∀ z ∈ h, z.2.1 = z.1.1) →
      h.filterMap (recordExchange record) = [] ∨
        B.domain (h.filterMap (recordExchange record))) :
    IsDDCFrom (Interface.tensor A B).domain A.domain 2
      (DDC.ofProgramOn () (recordAndForwardProgram record) A.domain) := by
  refine DDC.ofProgramOn_isDDCFrom (recordAndForwardProgram_bounded record) A.nonempty_prefix.2 ?_
  intro t hr hF
  by_cases hne : insideQueries (t.map Prod.snd) = []
  · exact Or.inl hne
  · obtain ⟨m, -, hleft, h, hport, hright, hmode⟩ :=
      recordAndForwardProgram_queries_invariant record hr
    refine Or.inr ⟨hne, ?_, ?_⟩
    · rw [hleft]
      exact hF
    · rw [hright]
      by_cases hrn : h.filterMap (recordExchange record) = []
      · exact Or.inl hrn
      · have hne_h : h ≠ [] := by
          rintro rfl
          exact hrn rfl
        have hpref : h.map Prod.fst <+: outsideInputs (t.map Prod.fst) := by
          cases m with
          | idle u => cases u; rw [hmode]
          | busy o u x hs q =>
            cases u
            rcases hs with _ | ⟨e₁, hs'⟩
            · rcases q with ⟨i' | j', qx⟩
              · exact ⟨[⟨o, x⟩], hmode.2.2⟩
              · exact False.elim hmode
            · rcases hs' with _ | ⟨e₂, hs''⟩
              · rcases e₁ with ⟨⟨i₁ | j₁, x₁⟩, ⟨i₂ | j₂, y₁⟩⟩
                · rcases q with ⟨i' | j', qx⟩
                  · simp at hmode
                  · rw [hmode.2.2.2]
                all_goals simp at hmode
              · simp at hmode
        have hAh : A.domain (h.map Prod.fst) := by
          rcases hF with he | hF
          · exfalso
            rw [he] at hpref
            exact hne_h (List.map_eq_nil_iff.mp (List.prefix_nil.mp hpref))
          · exact A.nonempty_prefix.2 hpref (by simpa using hne_h) hF
        exact hrec h hAh hport

/-- Single-call execution of `recordAndForwardProgram` when `record i x y = none`. -/
lemma recordAndForward_exec_none {A B : Interface}
    (record : ∀ i : A.I, A.X i → A.Y i → Option (Σ j : B.I, B.X j))
    {xs : List (Σ l, twoFam A.X (Interface.tensor A B).Y l)}
    {ys : List (Σ l, twoFam A.Y (Interface.tensor A B).X l)}
    (hafter : (recordAndForwardProgram record).after () xs = some (.idle ()))
    (hrep : Replies (DDC.ofProgramOn () (recordAndForwardProgram record) A.domain) xs ys)
    {i : A.I} {x : A.X i} {y : A.Y i} (hq : record i x y = none)
    (hA : A.domain (outsideInputs xs ++ [⟨i, x⟩])) :
    (recordAndForwardProgram record).after ()
        (xs ++ [⟨⟨none, i⟩, x⟩, ⟨⟨some (), Sum.inl i⟩, y⟩]) = some (.idle ()) ∧
      Replies (DDC.ofProgramOn () (recordAndForwardProgram record) A.domain)
        (xs ++ [⟨⟨none, i⟩, x⟩, ⟨⟨some (), Sum.inl i⟩, y⟩])
        (ys ++ [⟨⟨some (), Sum.inl i⟩, x⟩, ⟨⟨none, i⟩, y⟩]) := by
  have h1 : (recordAndForwardProgram record).after () (xs ++ [⟨⟨none, i⟩, x⟩]) =
      some (.busy i () x [] ⟨Sum.inl i, x⟩) := by
    rw [Program.after_snoc, hafter]
    simp [Program.step, Program.emit, recordAndForwardProgram, DSL.callProg]
  have h2 : (recordAndForwardProgram record).after ()
      ((xs ++ [⟨⟨none, i⟩, x⟩]) ++ [⟨⟨some (), Sum.inl i⟩, y⟩]) = some (.idle ()) := by
    rw [Program.after_snoc, h1]
    simp [Program.step, Program.emit, recordAndForwardProgram, DSL.callProg, hq, DSL.returnProg]
  rw [show xs ++ [⟨⟨none, i⟩, x⟩, ⟨⟨some (), Sum.inl i⟩, y⟩] =
      (xs ++ [⟨⟨none, i⟩, x⟩]) ++ [⟨⟨some (), Sum.inl i⟩, y⟩] by simp,
    show ys ++ [⟨⟨some (), Sum.inl i⟩, x⟩, ⟨⟨none, i⟩, y⟩] =
      (ys ++ [⟨⟨some (), Sum.inl i⟩, x⟩]) ++ [⟨⟨none, i⟩, y⟩] by simp]
  refine ⟨h2, replies_snoc.mpr ⟨replies_snoc.mpr ⟨hrep, ?_⟩, ?_⟩⟩
  · rw [DDC.ofProgramOn, filterDom, ite_eq_left]
    · rw [DDC.ofProgram_snoc, hafter]
      simp [Program.step, Program.emit, recordAndForwardProgram, DSL.callProg]
    · right
      rw [outsideInputs_append]
      simpa [outsideInputs, splitIn, restrict] using hA
  · rw [DDC.ofProgramOn, filterDom, ite_eq_left]
    · rw [DDC.ofProgram_snoc, h1]
      simp [Program.step, Program.emit, recordAndForwardProgram, DSL.callProg, hq, DSL.returnProg]
    · right
      rw [outsideInputs_append, outsideInputs_append]
      simpa [outsideInputs, splitIn, restrict] using hA

/-- Single-call execution of `recordAndForwardProgram` when `record i x y = some ⟨jq, xq⟩`. -/
lemma recordAndForward_exec_some {A B : Interface}
    (record : ∀ i : A.I, A.X i → A.Y i → Option (Σ j : B.I, B.X j))
    {xs : List (Σ l, twoFam A.X (Interface.tensor A B).Y l)}
    {ys : List (Σ l, twoFam A.Y (Interface.tensor A B).X l)}
    (hafter : (recordAndForwardProgram record).after () xs = some (.idle ()))
    (hrep : Replies (DDC.ofProgramOn () (recordAndForwardProgram record) A.domain) xs ys)
    {i : A.I} {x : A.X i} {y : A.Y i} {jq : B.I} {xq : B.X jq} (yr : B.Y jq)
    (hq : record i x y = some ⟨jq, xq⟩)
    (hA : A.domain (outsideInputs xs ++ [⟨i, x⟩])) :
    (recordAndForwardProgram record).after ()
        (xs ++ [⟨⟨none, i⟩, x⟩, ⟨⟨some (), Sum.inl i⟩, y⟩, ⟨⟨some (), Sum.inr jq⟩, yr⟩]) =
      some (.idle ()) ∧
      Replies (DDC.ofProgramOn () (recordAndForwardProgram record) A.domain)
        (xs ++ [⟨⟨none, i⟩, x⟩, ⟨⟨some (), Sum.inl i⟩, y⟩, ⟨⟨some (), Sum.inr jq⟩, yr⟩])
        (ys ++ [⟨⟨some (), Sum.inl i⟩, x⟩, ⟨⟨some (), Sum.inr jq⟩, xq⟩, ⟨⟨none, i⟩, y⟩]) := by
  have h1 : (recordAndForwardProgram record).after () (xs ++ [⟨⟨none, i⟩, x⟩]) =
      some (.busy i () x [] ⟨Sum.inl i, x⟩) := by
    rw [Program.after_snoc, hafter]
    simp only [Option.bind_some, Program.step, Program.emit, recordAndForwardProgram, DSL.callProg,
      Option.map_some]
  have h2 : (recordAndForwardProgram record).after ()
      ((xs ++ [⟨⟨none, i⟩, x⟩]) ++ [⟨⟨some (), Sum.inl i⟩, y⟩]) =
      some (.busy i () x [(⟨Sum.inl i, x⟩, ⟨Sum.inl i, y⟩)] ⟨Sum.inr jq, xq⟩) := by
    rw [Program.after_snoc, h1]
    simp only [Option.bind_some, Program.step, ↓reduceIte, Program.emit, recordAndForwardProgram,
      DSL.callProg, List.nil_append, ↓reduceDIte, hq, Option.map_some]
  have h3 : (recordAndForwardProgram record).after ()
      (((xs ++ [⟨⟨none, i⟩, x⟩]) ++ [⟨⟨some (), Sum.inl i⟩, y⟩]) ++
        [⟨⟨some (), Sum.inr jq⟩, yr⟩]) = some (.idle ()) := by
    rw [Program.after_snoc, h2]
    simp only [Option.bind_some, Program.step, ↓reduceIte, Program.emit, recordAndForwardProgram,
      DSL.callProg, List.singleton_append, ↓reduceDIte, hq, DSL.returnProg, Option.map_some]
  rw [show xs ++ [⟨⟨none, i⟩, x⟩, ⟨⟨some (), Sum.inl i⟩, y⟩, ⟨⟨some (), Sum.inr jq⟩, yr⟩] =
      ((xs ++ [⟨⟨none, i⟩, x⟩]) ++ [⟨⟨some (), Sum.inl i⟩, y⟩]) ++
        [⟨⟨some (), Sum.inr jq⟩, yr⟩] by simp,
    show ys ++ [⟨⟨some (), Sum.inl i⟩, x⟩, ⟨⟨some (), Sum.inr jq⟩, xq⟩, ⟨⟨none, i⟩, y⟩] =
      ((ys ++ [⟨⟨some (), Sum.inl i⟩, x⟩]) ++ [⟨⟨some (), Sum.inr jq⟩, xq⟩]) ++
        [⟨⟨none, i⟩, y⟩] by simp]
  refine ⟨h3, replies_snoc.mpr ⟨replies_snoc.mpr ⟨replies_snoc.mpr ⟨hrep, ?_⟩, ?_⟩, ?_⟩⟩
  · rw [DDC.ofProgramOn, filterDom, ite_eq_left]
    · rw [DDC.ofProgram_snoc, hafter]
      simp only [Option.bind_some, Program.step, Program.emit, recordAndForwardProgram,
        DSL.callProg, Option.map_some, Part.coe_some]
    · right
      rw [outsideInputs_append]
      simpa [outsideInputs, splitIn, restrict] using hA
  · rw [DDC.ofProgramOn, filterDom, ite_eq_left]
    · rw [DDC.ofProgram_snoc, h1]
      simp only [Option.bind_some, Program.step, ↓reduceIte, Program.emit, recordAndForwardProgram,
        DSL.callProg, List.nil_append, ↓reduceDIte, hq, Option.map_some, Part.coe_some]
    · right
      rw [outsideInputs_append, outsideInputs_append]
      simpa [outsideInputs, splitIn, restrict] using hA
  · rw [DDC.ofProgramOn, filterDom, ite_eq_left]
    · rw [DDC.ofProgram_snoc, h2]
      simp only [Option.bind_some, Program.step, ↓reduceIte, Program.emit, recordAndForwardProgram,
        DSL.callProg, List.singleton_append, ↓reduceDIte, hq, DSL.returnProg, Option.map_some,
        Part.coe_some]
    · right
      rw [outsideInputs_append, outsideInputs_append, outsideInputs_append]
      simpa [outsideInputs, splitIn, restrict] using hA

/-- The function-backed recorder satisfies the reusable `WriteOnlyRecord` contract. -/
noncomputable def recordAndForward_writeOnlyRecord {A B : Interface}
    (record : ∀ i : A.I, A.X i → A.Y i → Option (Σ j : B.I, B.X j))
    (hrec : ∀ h : List ((Σ i, A.X i) × (Σ i, A.Y i)),
      A.domain (h.map Prod.fst) → (∀ z ∈ h, z.2.1 = z.1.1) →
      h.filterMap (recordExchange record) = [] ∨
        B.domain (h.filterMap (recordExchange record))) :
    WriteOnlyRecord A B where
  converter := DDC.ofProgramOn () (recordAndForwardProgram record) A.domain
  bound := 2
  isDDCFrom := recordAndForwardProgram_isDDCFrom record hrec
  realizes := by
    intro h t hA hport ht_dds ht_port ht_dom
    suffices key : ∀ h : List ((Σ i, A.X i) × (Σ i, A.Y i)),
        (h = [] ∨ A.domain (h.map Prod.fst)) → (∀ z ∈ h, z.2.1 = z.1.1) →
        ∃ calls : List ((Σ i, A.X i) ×
            List ((Σ l, (Interface.tensor A B).X l) × (Σ l, (Interface.tensor A B).Y l)) ×
            (Σ i, A.Y i)),
          calls.map (fun c => (c.1, c.2.2)) = h ∧
          (recordAndForwardProgram record).after ()
            ((calls.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.fst) =
              some (.idle ()) ∧
          Replies (DDC.ofProgramOn () (recordAndForwardProgram record) A.domain)
            ((calls.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.fst)
            ((calls.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.snd) ∧
          RandomSystem.parallelConsistent
            ((calls.flatMap (·.2.1)).map
              ((sumAlphabet (Sum.rec A.X B.X)).symm.prodCongr
                (sumAlphabet (Sum.rec A.Y B.Y)).symm)) ∧
          leftExchanges (calls.flatMap (·.2.1)) = h ∧
          (rightExchanges (calls.flatMap (·.2.1))).map Prod.fst =
            h.filterMap (recordExchange record) ∧
          Replies t
            ((rightExchanges (calls.flatMap (·.2.1))).map Prod.fst)
            ((rightExchanges (calls.flatMap (·.2.1))).map Prod.snd) by
      obtain ⟨calls, hmap, -, hconv, hcons, hleft, -, hright⟩ := key h (Or.inr hA) hport
      exact ⟨calls, hmap, hconv, hcons, hleft, hright⟩
    intro h hA hport
    induction h using List.reverseRecOn with
    | nil =>
      refine ⟨[], rfl, rfl, replies_nil _, ?_, rfl, rfl, replies_nil _⟩
      intro _ hz; exact False.elim (List.not_mem_nil hz)
    | append_singleton h z ih =>
      rcases z with ⟨⟨i, x⟩, ⟨i', y⟩⟩
      have hi : i' = i := hport _ (List.mem_append_right _ (List.mem_singleton_self _))
      subst i'
      have hA' : A.domain (h.map Prod.fst ++ [⟨i, x⟩]) := by
        rcases hA with he | hA
        · exact False.elim (by simp at he)
        · simpa using hA
      have hA₀ : h = [] ∨ A.domain (h.map Prod.fst) := by
        by_cases hn : h = []
        · exact Or.inl hn
        · exact Or.inr (A.nonempty_prefix.2 (List.prefix_append _ _) (by simpa using hn) hA')
      have hport₀ : ∀ z ∈ h, z.2.1 = z.1.1 := fun z hz => hport z (List.mem_append_left _ hz)
      obtain ⟨calls₀, hmap₀, hafter₀, hrep₀, hcons₀, hleft₀, hrq₀, hrt₀⟩ := ih hA₀ hport₀
      let T₀ := calls₀.flatMap fun c => callTranscript c.1 c.2.1 c.2.2
      have hout₀ : outsideInputs (T₀.map Prod.fst) = h.map Prod.fst := by
        have hout_calls : ∀ cs : List ((Σ i, A.X i) ×
            List ((Σ l, (Interface.tensor A B).X l) × (Σ l, (Interface.tensor A B).Y l)) ×
            (Σ i, A.Y i)),
            outsideInputs ((cs.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.fst) =
              cs.map (·.1) := by
          intro cs
          induction cs with
          | nil => rfl
          | cons c cs ihc =>
            simp only [List.flatMap_cons, List.map_append, outsideInputs_append, ihc,
              List.map_cons]
            rcases c with ⟨u, qs, v⟩
            have hstep_out : ∀ (first : Σ l, twoFam A.X (Interface.tensor A B).Y l)
                (qs : List ((Σ l, (Interface.tensor A B).X l) ×
                  (Σ l, (Interface.tensor A B).Y l))) (v : Σ i, A.Y i),
                outsideInputs ((callSteps first qs v).map Prod.fst) =
                  outsideInputs [first] := by
              intro first qs v
              induction qs generalizing first with
              | nil => rfl
              | cons xy qs ihq =>
                rw [callSteps, List.map_cons, ← List.singleton_append, outsideInputs_append, ihq]
                simp [outsideInputs, splitIn, restrict]
            rw [callTranscript, hstep_out]
            simp [outsideInputs, splitIn, restrict]
        rw [show outsideInputs (T₀.map Prod.fst) = calls₀.map (·.1) from hout_calls calls₀,
          ← congrArg (List.map Prod.fst) hmap₀]
        simp [List.map_map, Function.comp_def]
      cases hq : record i x y with
      | none =>
        let c : (Σ i, A.X i) ×
            List ((Σ l, (Interface.tensor A B).X l) × (Σ l, (Interface.tensor A B).Y l)) ×
            (Σ i, A.Y i) :=
          (⟨i, x⟩, [(⟨Sum.inl i, x⟩, ⟨Sum.inl i, y⟩)], ⟨i, y⟩)
        have hct : callTranscript c.1 c.2.1 c.2.2 =
            [(⟨⟨none, i⟩, x⟩, ⟨⟨some (), Sum.inl i⟩, x⟩),
              (⟨⟨some (), Sum.inl i⟩, y⟩, ⟨⟨none, i⟩, y⟩)] := rfl
        have hexec := recordAndForward_exec_none record hafter₀ hrep₀ hq (hout₀.symm ▸ hA')
        refine ⟨calls₀ ++ [c], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [c] using hmap₀
        · rw [List.flatMap_append, List.flatMap_singleton, hct, List.map_append]
          exact hexec.1
        · rw [List.flatMap_append, List.flatMap_singleton, hct, List.map_append, List.map_append]
          exact hexec.2
        · rw [List.flatMap_append, List.flatMap_singleton, List.map_append]
          exact RandomSystem.parallelConsistent_snoc.mpr ⟨hcons₀, rfl⟩
        · rw [List.flatMap_append, List.flatMap_singleton, leftExchanges_append, hleft₀]
          dsimp only [c]
          rw [leftExchanges_inl_singleton]
        · rw [List.flatMap_append, List.flatMap_singleton, rightExchanges_append,
            List.map_append, hrq₀, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
          have hre1 : recordExchange record (⟨i, x⟩, ⟨i, y⟩) = none := by
            simp [recordExchange, hq]
          dsimp only [c]
          rw [rightExchanges_inl_singleton, hre1, List.map_nil, List.append_nil]
        · rw [List.flatMap_append, List.flatMap_singleton, rightExchanges_append,
            List.map_append, List.map_append]
          dsimp only [c]
          rw [rightExchanges_inl_singleton, List.map_nil, List.map_nil,
            List.append_nil, List.append_nil]
          exact hrt₀
      | some q =>
        have hBq : B.domain (h.filterMap (recordExchange record) ++ [q]) := by
          have hmemB := hrec (h ++ [(⟨i, x⟩, ⟨i, y⟩)]) (by simpa using hA') hport
          rw [List.filterMap_append, List.filterMap_cons, List.filterMap_nil] at hmemB
          have hre1 : recordExchange record (⟨i, x⟩, ⟨i, y⟩) = some q := by
            simp [recordExchange, hq]
          rw [hre1] at hmemB
          exact hmemB.resolve_left (by simp)
        have hdom_t : (t ((rightExchanges (calls₀.flatMap (·.2.1))).map Prod.fst ++ [q])).Dom := by
          rw [ht_dom, hrq₀]
          exact hBq
        obtain ⟨r, hr_mem⟩ := Part.dom_iff_mem.mp hdom_t
        have hr_port : r.1 = q.1 := ht_port _ q r hr_mem
        rcases q with ⟨jq, xq⟩
        rcases r with ⟨jr, yr⟩
        dsimp only at hr_port
        subst jr
        let c : (Σ i, A.X i) ×
            List ((Σ l, (Interface.tensor A B).X l) × (Σ l, (Interface.tensor A B).Y l)) ×
            (Σ i, A.Y i) :=
          (⟨i, x⟩,
            [(⟨Sum.inl i, x⟩, ⟨Sum.inl i, y⟩), (⟨Sum.inr jq, xq⟩, ⟨Sum.inr jq, yr⟩)], ⟨i, y⟩)
        have hct : callTranscript c.1 c.2.1 c.2.2 =
            [(⟨⟨none, i⟩, x⟩, ⟨⟨some (), Sum.inl i⟩, x⟩),
              (⟨⟨some (), Sum.inl i⟩, y⟩, ⟨⟨some (), Sum.inr jq⟩, xq⟩),
              (⟨⟨some (), Sum.inr jq⟩, yr⟩, ⟨⟨none, i⟩, y⟩)] := rfl
        have hexec := recordAndForward_exec_some record hafter₀ hrep₀ yr hq (hout₀.symm ▸ hA')
        refine ⟨calls₀ ++ [c], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [c] using hmap₀
        · rw [List.flatMap_append, List.flatMap_singleton, hct, List.map_append]
          exact hexec.1
        · rw [List.flatMap_append, List.flatMap_singleton, hct, List.map_append, List.map_append]
          exact hexec.2
        · rw [List.flatMap_append, List.flatMap_singleton, List.map_append]
          have hc_map : c.2.1.map ((sumAlphabet (Sum.rec A.X B.X)).symm.prodCongr
              (sumAlphabet (Sum.rec A.Y B.Y)).symm) =
              [(⟨none, ⟨i, x⟩⟩, ⟨none, ⟨i, y⟩⟩)] ++ [(⟨some (), ⟨jq, xq⟩⟩, ⟨some (), ⟨jq, yr⟩⟩)] :=
            rfl
          rw [hc_map, ← List.append_assoc]
          exact RandomSystem.parallelConsistent_snoc.mpr
            ⟨RandomSystem.parallelConsistent_snoc.mpr ⟨hcons₀, rfl⟩, rfl⟩
        · rw [List.flatMap_append, List.flatMap_singleton, leftExchanges_append, hleft₀]
          have hle : leftExchanges c.2.1 = [(⟨i, x⟩, ⟨i, y⟩)] := rfl
          rw [hle]
        · rw [List.flatMap_append, List.flatMap_singleton, rightExchanges_append,
            List.map_append, hrq₀, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
          have hre : rightExchanges c.2.1 = [(⟨jq, xq⟩, ⟨jq, yr⟩)] := rfl
          have hre1 : recordExchange record (⟨i, x⟩, ⟨i, y⟩) = some ⟨jq, xq⟩ := by
            simp [recordExchange, hq]
          rw [hre, hre1, List.map_singleton]
        · rw [List.flatMap_append, List.flatMap_singleton, rightExchanges_append,
            List.map_append, List.map_append]
          have hre : rightExchanges c.2.1 = [(⟨jq, xq⟩, ⟨jq, yr⟩)] := rfl
          rw [hre, List.map_singleton, List.map_singleton]
          exact replies_snoc.mpr ⟨hrt₀, Part.eq_some_iff.mpr hr_mem⟩

/-- The function-backed write-only recording converter on `A ⟶ A ⊗ B`. -/
noncomputable def recordAndForward {A B : Interface}
    (record : ∀ i : A.I, A.X i → A.Y i → Option (Σ j : B.I, B.X j))
    (hrec : ∀ h : List ((Σ i, A.X i) × (Σ i, A.Y i)),
      A.domain (h.map Prod.fst) → (∀ z ∈ h, z.2.1 = z.1.1) →
      h.filterMap (recordExchange record) = [] ∨
        B.domain (h.filterMap (recordExchange record))) :
    TypedConverter A (Interface.tensor A B) :=
  (recordAndForward_writeOnlyRecord record hrec).toConverter

/-- **Function-backed record erasure**: `recordAndForward` erases any right-hand system `H`
beside any left-hand system `Y`. -/
theorem recordAndForward_smul_parallel {A B : Interface}
    (record : ∀ i : A.I, A.X i → A.Y i → Option (Σ j : B.I, B.X j))
    (hrec : ∀ h : List ((Σ i, A.X i) × (Σ i, A.Y i)),
      A.domain (h.map Prod.fst) → (∀ z ∈ h, z.2.1 = z.1.1) →
      h.filterMap (recordExchange record) = [] ∨
        B.domain (h.filterMap (recordExchange record)))
    (Y : TypedSystem A) (H : TypedSystem B) :
    recordAndForward record hrec • TypedSystem.parallel Y H = Y :=
  (recordAndForward_writeOnlyRecord record hrec).smul_parallel Y H

/-- **Function-backed record erasure beside a fixed function**: specialization of
`recordAndForward_smul_parallel` when `H` is `TypedSystem.ofFunction f`. -/
theorem recordAndForward_smul_parallel_ofFunction {A B : Interface}
    (record : ∀ i : A.I, A.X i → A.Y i → Option (Σ j : B.I, B.X j))
    (hrec : ∀ h : List ((Σ i, A.X i) × (Σ i, A.Y i)),
      A.domain (h.map Prod.fst) → (∀ z ∈ h, z.2.1 = z.1.1) →
      h.filterMap (recordExchange record) = [] ∨
        B.domain (h.filterMap (recordExchange record)))
    (Y : TypedSystem A) (f : ∀ j, B.X j → B.Y j) :
    recordAndForward record hrec • TypedSystem.parallel Y (TypedSystem.ofFunction f) = Y :=
  recordAndForward_smul_parallel record hrec Y (TypedSystem.ofFunction f)

end SystemAlgebra.TypedConverter
