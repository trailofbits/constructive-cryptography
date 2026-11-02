module

public import Commons.Definitions.Ideal
public import Probability.Conditioning

/-!
# Lazy presentation of the uniform random permutation

`URP.lazy` retains input/output pairs at each port. A repeated input reads its stored reply;
a fresh input samples uniformly outside the recorded range [2, §4.1.2, p. 101].
The existing `URP A` uses per-port `A.X i ≃ A.Y i`; this transports the rule across finite
alphabets of equal cardinality.

The set `URP.completions` consists of the existing bijections agreeing with those pairs.
Its nonemptiness is the state invariant, preserved by `URP.tableLaw_preserves_completions`.
`URP.completionLaw` is uniform on that set. Output-swap symmetry gives
`URP.completionLaw_map_eq_unusedLaw`: a fresh reply is uniform over the unused range.
`URP.completionLaw_eq_bind` conditions the completion on that reply and records its pair.
`URP.tableLaw_simulates` combines this miss identity with exact replay on a hit.
`TypedSystem.ofProbAutomaton_eq_of_simulation` in `RandomSystems.Typed.ProbAutomaton` lifts it
to cumulative equality. `URP.completionLaw_nil` gives the initial uniform family; the retained-key
laws `TypedSystem.ofProbAutomaton_eq_keyed` and `TypedSystem.keyed_single` in
`RandomSystems.Typed.KeyedAutomaton` finish `URP.lazy_eq` on every history in the interface
domain, including adaptive queries. This is equality of the
"cumulative description of the behavior" [1, Definition 3.20, p. 69].

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
2. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

noncomputable section

namespace Commons.URP

open SystemAlgebra Probability Probability.Distribution

-- `A` fixes finite alphabets, ports and domain. Every port admits a bijection, even when empty.
variable (A : Interface) [∀ i, Nonempty (A.X i ≃ A.Y i)]

open Classical in
/-- The bijection families agreeing with every recorded pair, independently at each port. -/
def completions
    -- `table i` records the already answered input/output pairs at port `i`.
    (table : ∀ i, List (A.X i × A.Y i)) : Finset (∀ i, A.X i ≃ A.Y i) :=
  Finset.univ.filter fun π => ∀ i p, p ∈ table i → π i p.1 = p.2

open Classical in
/-- Completing the records means sampling a uniform family conditioned on agreement.
The unconditional family law supplies the explicit fallback for inconsistent ambient tables. -/
def completionLaw
    -- `table i` records the constraints on the retained bijection at port `i`.
    (table : ∀ i, List (A.X i × A.Y i)) :
    ProbDist (∀ i, A.X i ≃ A.Y i) :=
  ProbDist.uniformOn (· ∈ completions A table) 𝒰[∀ i, A.X i ≃ A.Y i]

open Classical in
/-- At a fresh input, draw uniformly outside the recorded range. [2, §4.1.2, p. 101]:
"he chooses yi at random from the set" of outputs excluding prior replies. The current input
and a port bijection provide an explicit fallback when that set is empty. For consistent
records and a fresh input, `apply_not_mem_range_of_mem_completions` supplies an unused output. -/
def unusedLaw
    -- `table` records prior replies; `i(x)` is the current query, supplying a fallback image.
    (table : ∀ i, List (A.X i × A.Y i)) (i : A.I) (x : A.X i) :
    ProbDist (A.Y i) :=
  let y := (Classical.choice (inferInstance : Nonempty (A.X i ≃ A.Y i))) x
  let : Nonempty (A.Y i) := ⟨y⟩
  ProbDist.uniformOn (fun z => z ∉ (table i).map Prod.snd) (ProbDist.single y)

open Classical in
/-- Replay a stored reply; otherwise use the uniform unused-output law.
[1, Definition 3.15, p. 64]: “equal inputs are always answered by identical outputs”. -/
def replyLaw
    -- `table i` determines whether `i(x)` replays a pair or samples outside the recorded range.
    (table : ∀ i, List (A.X i × A.Y i)) (i : A.I) (x : A.X i) :
    ProbDist (A.Y i) :=
  ((table i).lookup x).elim (unusedLaw A table i x) ProbDist.single

open Classical in
/-- After a miss, append the newly sampled pair at its port; a hit leaves every record intact. -/
def tableLaw : ProbStep (∀ i, List (A.X i × A.Y i)) A.I A.X A.Y :=
  ProbStep.recordReplies (replyLaw A)

open Classical in
/-- The lazy permutation starts with empty records, samples unused replies on misses, and
replays hits, on exactly `A.domain`; [2, §4.1.2, p. 101] records "input/output pairs". -/
def lazy : TypedSystem A :=
  TypedSystem.ofProbAutomaton A (tableLaw A) (ProbDist.single (fun _ => []))

omit [∀ i, Nonempty (A.X i ≃ A.Y i)] in
open Classical in
/-- A completion maps each recorded input to its recorded output. -/
lemma mem_completions_iff
    -- `table` lists the constraints; `π` is the candidate family of port bijections.
    (table : ∀ i, List (A.X i × A.Y i))
    (π : ∀ i, A.X i ≃ A.Y i) :
    π ∈ completions A table ↔ ∀ i p, p ∈ table i → π i p.1 = p.2 := by
  simp only [completions, Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in
/-- The completion law has exactly the consistent bijections in its support. -/
lemma mem_support_completionLaw_iff
    -- `h` witnesses a consistent `table`; `π` is tested for positive completion mass.
    (table : ∀ i, List (A.X i × A.Y i))
    (h : (completions A table).Nonempty) (π : ∀ i, A.X i ≃ A.Y i) :
    π ∈ (completionLaw A table).1.support ↔ π ∈ completions A table := by
  exact ProbDist.mem_support_uniformOn_iff _ h _ π

omit [∀ i, Nonempty (A.X i ≃ A.Y i)] in
open Classical in
/-- A fresh input has an unused image under every completion. In particular, a consistent
table cannot exhaust its outputs while leaving a fresh input. -/
lemma apply_not_mem_range_of_mem_completions
    -- `fresh` excludes `x` from the recorded inputs at `i`; `hπ` makes `π` obey every record.
    (table : ∀ i, List (A.X i × A.Y i))
    (i : A.I) (x : A.X i) (fresh : (table i).lookup x = none)
    (π : ∀ i, A.X i ≃ A.Y i) (hπ : π ∈ completions A table) :
    π i x ∉ (table i).map Prod.snd := by
  intro hm
  obtain ⟨p, hp, he⟩ := List.mem_map.mp hm
  have hx := List.lookup_eq_none_iff.mp fresh p hp
  have eqInput := (π i).injective ((mem_completions_iff A table π).mp hπ i p hp |>.trans he)
  have hx' : x ≠ p.1 := by simpa only [bne_iff_ne] using hx
  exact hx' eqInput.symm

omit [∀ i, Nonempty (A.X i ≃ A.Y i)] in
open Classical in
/-- Recording a reply restricts completions to the fiber of that reply. -/
lemma mem_completions_update_iff
    -- The candidate `π` completes the updated `table` precisely when it also answers `i(x)` by `y`.
    (table : ∀ i, List (A.X i × A.Y i))
    (i : A.I) (x : A.X i) (y : A.Y i) (π : ∀ i, A.X i ≃ A.Y i) :
    π ∈ completions A (Function.update table i (table i ++ [(x, y)])) ↔
      π ∈ completions A table ∧ π i x = y := by
  simp only [mem_completions_iff]
  constructor
  · intro h
    refine ⟨fun j p hp => ?_, ?_⟩
    · by_cases hj : j = i
      · subst j
        exact h i p (by simpa only [Function.update_self, List.mem_append,
          List.mem_singleton] using Or.inl hp)
      · exact h j p (by simpa only [Function.update_of_ne hj] using hp)
    · exact h i (x, y) (by simp only [Function.update_self, List.mem_append,
        List.mem_singleton, or_true])
  · rintro ⟨h, hxy⟩ j p hp
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self, List.mem_append, List.mem_singleton] at hp
      exact hp.elim (h i p) (fun he => he ▸ hxy)
    · exact h j p (by simpa only [Function.update_of_ne hj] using hp)

open Classical in
/-- Swapping two unused outputs at a port maps the completion set onto itself. Thus those
outputs have equal probability as the next answer under the completion law. -/
lemma completionLaw_apply_eq_of_unused
    -- `table` records previous replies; `h` ensures its uniform completion law is defined.
    (table : ∀ i, List (A.X i × A.Y i))
    (h : (completions A table).Nonempty) (i : A.I) (x : A.X i)
    -- `hy`, `hz` make the output swap fix every record at the queried port `i`.
    (y z : A.Y i) (hy : y ∉ (table i).map Prod.snd) (hz : z ∉ (table i).map Prod.snd) :
    (completionLaw A table).map (fun π => π i x) y =
      (completionLaw A table).map (fun π => π i x) z := by
  let e : (∀ j, A.X j ≃ A.Y j) ≃ (∀ j, A.X j ≃ A.Y j) :=
    Equiv.piCongrRight (Function.update (fun j => Equiv.refl (A.X j ≃ A.Y j)) i
      (Equiv.equivCongr (Equiv.refl (A.X i)) (Equiv.swap y z)))
  have hi (π : ∀ j, A.X j ≃ A.Y j) (u : A.X i) :
      e π i u = Equiv.swap y z (π i u) := by
    simp only [e, Equiv.piCongrRight_apply, Pi.map_apply, Function.update_self,
      Equiv.equivCongr_apply_apply, Equiv.refl_symm, Equiv.refl_apply]
  -- Recorded outputs are fixed by the swap, so every agreement constraint is unchanged.
  have he (π : ∀ j, A.X j ≃ A.Y j) :
      e π ∈ completions A table ↔ π ∈ completions A table := by
    simp only [mem_completions_iff]
    apply forall_congr'
    intro j
    apply forall_congr'
    intro p
    apply imp_congr_right
    intro hp
    by_cases hj : j = i
    · subst j
      have hy' : p.2 ≠ y := fun heq => hy (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
      have hz' : p.2 ≠ z := fun heq => hz (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
      rw [hi, Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne hy' hz']
    · simp only [e, Equiv.piCongrRight_apply, Pi.map_apply,
        Function.update_of_ne hj, Equiv.refl_apply]
  -- The swap preserves the normalized uniform law on the agreement event.
  have invariant : fTransform e (completionLaw A table).1 = (completionLaw A table).1 :=
    congrArg Subtype.val (ProbDist.map_uniformOn_of_equiv _ h _ e he)
  -- Evaluate the same law after the swap; `swap y z v = y` means `v = z`.
  simp only [ProbDist.map_val, fTransform_apply_eq_mass]
  calc
    _ = (fTransform e (completionLaw A table).1).mass (fun π => π i x = y) := by
      rw [invariant]
    _ = _ := by
      rw [mass_fTransform]
      exact mass_congr _ fun π => by rw [hi, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]

open Classical in
/-- At a fresh input, the completion's next answer is uniform over precisely the unused
outputs: injectivity excludes the recorded range, and swaps equalize the remaining masses. -/
lemma completionLaw_map_eq_unusedLaw
    -- `h` supplies a completion of `table`; `fresh` says that `i(x)` has not been recorded.
    (table : ∀ i, List (A.X i × A.Y i))
    (h : (completions A table).Nonempty) (i : A.I) (x : A.X i)
    (fresh : (table i).lookup x = none) :
    (completionLaw A table).map (fun π => π i x) = unusedLaw A table i x := by
  let : Nonempty (A.Y i) := ⟨(Classical.choice (inferInstance : Nonempty (A.X i ≃ A.Y i))) x⟩
  -- Supported outputs are unused; output swaps equate all masses in that range.
  apply ProbDist.eq_uniformOn_of_constant
  · intro y hy
    obtain ⟨π, hπ, rfl⟩ := mem_support_fTransform _ _ hy
    exact apply_not_mem_range_of_mem_completions A table i x fresh π
      ((mem_support_completionLaw_iff A table h π).mp hπ)
  · exact fun y hy z hz => completionLaw_apply_eq_of_unused A table h i x y z hy hz

open Classical in
/-- Reveal a fresh reply and then complete the extended records. This is exactly the
original completion law disintegrated along evaluation at the queried input. -/
lemma completionLaw_eq_bind
    -- `h` makes conditioning on the records defined; `fresh` selects unused-output sampling.
    (table : ∀ i, List (A.X i × A.Y i))
    (h : (completions A table).Nonempty) (i : A.I) (x : A.X i)
    (fresh : (table i).lookup x = none) :
    completionLaw A table = (unusedLaw A table i x).bind
      (fun y => completionLaw A (Function.update table i (table i ++ [(x, y)]))) := by
  -- The unused-output law is the completion marginal at the fresh input.
  rw [← completionLaw_map_eq_unusedLaw A table h i x fresh]
  apply Subtype.ext
  rw [ProbDist.bind_val, ProbDist.map_val]
  -- Disintegrate the restricted uniform law; a zero-mass fiber keeps its explicit fallback.
  conv_lhs => unfold completionLaw ProbDist.uniformOn
  rw [normalizeOr_eq_bindK_restrict _ _ _ (weight_restrict_uniform_ne_zero _ h)
    (fun π => π i x)]
  apply bindK_congr
  intro y _
  -- Appending the pair imposes exactly the old agreement event and this evaluation fiber.
  simp only [completionLaw, ProbDist.uniformOn, restrict_restrict]
  congr 2
  exact restrict_congr _ fun π => (mem_completions_update_iff A table i x y π).symm

open Classical in
/-- Every supported fresh reply leaves a nonempty set of completions. -/
lemma completions_update_nonempty
    -- `h` makes the current records consistent; `hy` selects a supported fresh reply `y`.
    (table : ∀ i, List (A.X i × A.Y i))
    (h : (completions A table).Nonempty) (i : A.I) (x : A.X i)
    (fresh : (table i).lookup x = none) (y : A.Y i)
    (hy : y ∈ (unusedLaw A table i x).1.support) :
    (completions A (Function.update table i (table i ++ [(x, y)]))).Nonempty := by
  rw [← completionLaw_map_eq_unusedLaw A table h i x fresh] at hy
  obtain ⟨π, hπ, hxy⟩ := mem_support_fTransform _ _ hy
  exact ⟨π, (mem_completions_update_iff A table i x y π).mpr
    ⟨(mem_support_completionLaw_iff A table h π).mp hπ, hxy⟩⟩

open Classical in
/-- A stored reply is fixed by every supported completion. -/
lemma completionLaw_apply_eq_of_lookup
    -- `hit` stores `y` at `i(x)`; `hπ` is a supported completion of the consistent records `h`.
    (table : ∀ i, List (A.X i × A.Y i))
    (h : (completions A table).Nonempty) (i : A.I) (x : A.X i) (y : A.Y i)
    (hit : (table i).lookup x = some y) (π : ∀ i, A.X i ≃ A.Y i)
    (hπ : π ∈ (completionLaw A table).1.support) : π i x = y := by
  obtain ⟨l₁, l₂, he, _⟩ := List.lookup_eq_some_iff.mp hit
  have hp : (x, y) ∈ table i := by
    rw [he]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  exact (mem_completions_iff A table π).mp
    ((mem_support_completionLaw_iff A table h π).mp hπ) i (x, y) hp

open Classical in
/-- A supported table transition preserves the existence of a completing bijection. -/
lemma tableLaw_preserves_completions
    -- `h` makes `table` consistent; `hp` selects a possible next state and tagged reply `p`.
    (table : ∀ i, List (A.X i × A.Y i))
    (h : (completions A table).Nonempty) (query : Σ i, A.X i)
    (p : (∀ i, List (A.X i × A.Y i)) × (Σ i, A.Y i))
    (hp : p ∈ ((tableLaw A).outcome table query).support) :
    (completions A p.1).Nonempty := by
  obtain ⟨i, x⟩ := query
  simp only [ProbStep.outcome, tableLaw, ProbStep.recordReplies, ProbDist.map_val,
    fTransform_fTransform,
    Function.comp_def] at hp
  obtain ⟨y, hy, rfl⟩ := mem_support_fTransform _ _ hp
  cases lookup : (table i).lookup x with
  | none =>
    -- A supported fresh reply has a completion that already takes that value.
    simp only [ProbStep.tagged, Option.isNone_none, ite_true]
    simp only [replyLaw, lookup, Option.elim_none] at hy
    exact completions_update_nonempty A table h i x lookup y hy
  | some y =>
    -- Replaying retains every existing completion.
    simpa only [ProbStep.tagged, lookup, Option.isNone_some, Bool.false_eq_true, ite_false] using h

open Classical in
/-- Completing before answering and answering before completing have the same joint law. -/
lemma tableLaw_simulates
    -- `h` is the reachable-state invariant; `query` selects the same port/input on both sides.
    (table : ∀ i, List (A.X i × A.Y i))
    (h : (completions A table).Nonempty) (query : Σ i, A.X i) :
    ProbStep.SimulatesAt (tableLaw A)
      (fun (π : ∀ i, A.X i ≃ A.Y i) i x => (ProbDist.single (π i x)).map (fun y => (π, y)))
      (completionLaw A) table query := by
  obtain ⟨i, x⟩ := query
  simp only [ProbStep.SimulatesAt, ProbStep.outcome, ProbDist.map_val, ProbDist.single,
    fTransform_single]
  rw [bindK_single_comp]
  cases lookup : (table i).lookup x with
  | none =>
    -- Reveal the fresh output; each conditional completion then fixes that same output.
    simp only [tableLaw, ProbStep.recordReplies, replyLaw, lookup, Option.elim_none,
      Option.isNone_none,
      ite_true, ProbDist.map_val, fTransform_fTransform, Function.comp_def,
      bindK_fTransform, ProbStep.tagged]
    have disintegration := congrArg Subtype.val (completionLaw_eq_bind A table h i x lookup)
    rw [disintegration, ProbDist.bind_val, fTransform_bindK]
    apply bindK_congr
    intro y hy
    apply fTransform_congr_support
    intro π hπ
    have hnew := completions_update_nonempty A table h i x lookup y hy
    have pin := ((mem_completions_update_iff A table i x y π).mp
      ((mem_support_completionLaw_iff A _ hnew π).mp hπ)).2
    rw [pin]
  | some y =>
    -- A hit retains all records, and their completions return the stored reply.
    simp only [tableLaw, ProbStep.recordReplies, replyLaw, lookup, Option.elim_some,
      Option.isNone_some,
      ProbDist.map_val, ProbDist.single, fTransform_single,
      bindK_single, one_smul, ProbStep.tagged]
    apply fTransform_congr_support
    intro π hπ
    rw [completionLaw_apply_eq_of_lookup A table h i x y lookup π hπ]

omit [∀ i, Nonempty (A.X i ≃ A.Y i)] in
open Classical in
/-- Every family `π` of port bijections agrees with the empty records. -/
lemma mem_completions_nil (π : ∀ i, A.X i ≃ A.Y i) :
    π ∈ completions A (fun _ => []) := by
  rw [mem_completions_iff]
  exact fun _ _ hp => (List.not_mem_nil hp).elim

open Classical in
/-- Empty records impose no condition on the uniform family of bijections. -/
lemma completionLaw_nil : completionLaw A (fun _ => []) = 𝒰[∀ i, A.X i ≃ A.Y i] :=
  ProbDist.uniformOn_of_forall _ (mem_completions_nil A) _

open Classical in
/-- The forward lazy permutation equals the existing URP on every admitted history,
including adaptive queries, repeats and exhausted ranges. [2, §4.1.2, p. 101]:
"We can do this by using a “lazy” implementation of f". The equivalence is
"if they have the same behavior" [1, Definition 3.19, p. 68]. -/
theorem lazy_eq : lazy A = Commons.URP A := by
  -- The completion invariant and local simulation identify every admitted cumulative law.
  have simulation := TypedSystem.ofProbAutomaton_eq_of_simulation (A := A) (tableLaw A)
    (fun (π : ∀ i, A.X i ≃ A.Y i) i x => (ProbDist.single (π i x)).map (fun y => (π, y)))
    (completionLaw A)
    (fun _ table => (completions A table).Nonempty)
    (fun _ table query h _ p hp => tableLaw_preserves_completions A table h query p hp)
    (fun _ table query h _ => tableLaw_simulates A table h query)
    (ProbDist.single (fun _ => [])) (by
      intro table ht
      have ht' : table = fun _ => [] := by
        simpa only [ProbDist.single, Finsupp.support_single _ one_ne_zero,
          Finset.mem_singleton] using ht
      subst table
      -- Empty records admit every family of the port bijections supplied by the interface.
      refine ⟨fun i => Classical.choice (inferInstance : Nonempty (A.X i ≃ A.Y i)), ?_⟩
      exact mem_completions_nil A _)
  -- Completing the empty table samples exactly the retained key of the existing URP.
  have initial : (ProbDist.single (fun _ => [])).bind (completionLaw A) =
      𝒰[∀ i, A.X i ≃ A.Y i] := by
    apply Subtype.ext
    simp only [ProbDist.bind_val, ProbDist.single, bindK_single, one_smul, completionLaw_nil]
  rw [initial, TypedSystem.ofProbAutomaton_eq_keyed, TypedSystem.keyed_single] at simulation
  exact simulation

end Commons.URP
