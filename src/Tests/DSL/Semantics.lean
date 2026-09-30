import Examples.DSL.Components

/-!
# DSL semantics across calls

Checks on the systems of `Examples.DSL.Components`: sampling inside a procedure is fresh on
every call (`freshBits_independent`), sampling at initialization persists
(`secretBit_retained`), two ports share the private state (`counter_interleaving`), also at
per-port budgets, where a port exhausts only its own budget (`counter_perPort_interleaving`,
`counter_perPort_exceeded`); the write-through converter maps its writes to the store and its
reads to nothing, so the store's budget is that of the writes. A system that samples is its program attached to its sources, the
automaton combining the program with the source's table of samples; the first two checks
compute that automaton.
-/

open Classical SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface Probability
open scoped SystemAlgebra.DSL

namespace DSLTests.Semantics
open DSLExamples

/-- One call samples the source's next entry and returns it. -/
theorem freshBits_invoke {K : ℕ} (t : Fin K → Bool) (st : Option Unit) (k : ℕ) :
    FreshBits.body.invoke (sourceStep FreshBits.law1) st .bit () 1 (t, k) [] =
      some ((some (), (t, k + 1)),
        if hk : k < K then t ⟨k, hk⟩ else Classical.choice FreshBits.law1.nonempty) := by
  cases st <;> simp [Program.invoke, FreshBits.body, callProg, returnProg, sourceStep]

theorem freshBits_stateAfter {K : ℕ} (t : Fin K → Bool) (bs : List Bool) :
    stateAfter (FreshBits.body.combine (sourceStep FreshBits.law1) FreshBits.bound_spec)
        (none, (t, 0)) (bs.map fun _ => ⟨.bit, ()⟩) =
      (if bs = [] then none else some (), (t, bs.length)) := by
  induction bs using List.reverseRecOn with
  | nil => rfl
  | append_singleton bs b ih =>
    rw [List.map_append, List.map_singleton, stateAfter_snoc, ih]
    rw [Program.combine_eq_of_invoke _ _ (freshBits_invoke t _ bs.length)]
    simp

theorem freshBits_replies {K : ℕ} (t : Fin K → Bool) (bs : List Bool) (hn : bs.length ≤ K) :
    Replies (automatonSystem (FreshBits.body.combine (sourceStep FreshBits.law1)
        FreshBits.bound_spec) (none, (t, 0)))
        (bs.map fun _ => ⟨.bit, ()⟩) (bs.map fun b => ⟨.bit, b⟩) ↔
      ∀ k (hk : k < bs.length), t ⟨k, by omega⟩ = bs[k] := by
  induction bs using List.reverseRecOn with
  | nil => simp
  | append_singleton bs b ih =>
    simp only [List.length_append, List.length_singleton] at hn
    rw [List.map_append, List.map_append, List.map_singleton, List.map_singleton, replies_snoc,
      ih (by omega), automatonSystem_snoc, freshBits_stateAfter,
      Program.combine_eq_of_invoke _ _ (freshBits_invoke t _ bs.length)]
    simp only [dif_pos (show bs.length < K by omega), Part.some_inj, Sigma.mk.injEq, heq_eq_eq,
      true_and]
    constructor
    · rintro ⟨h, hb⟩ k hk
      rcases Nat.lt_or_ge k bs.length with hk' | hk'
      · rw [List.getElem_append_left hk']
        exact h k hk'
      · obtain rfl : k = bs.length := by simp at hk; omega
        simpa using hb
    · intro h
      refine ⟨fun k hk => ?_, by simpa using h bs.length (by simp)⟩
      have hk' := h k (by simp; omega)
      rwa [List.getElem_append_left hk] at hk'

theorem mass_prefix {K : ℕ} (bs : List Bool) (hn : bs.length ≤ K) :
    (Distribution.pi fun _ : Fin K => (𝒰[Bool]).1).mass
        (fun tbl => ∀ k (hk : k < bs.length), tbl ⟨k, by omega⟩ = bs[k]) =
      (1 / 2) ^ bs.length := by
  induction bs using List.reverseRecOn with
  | nil =>
    simp only [List.length_nil, Nat.not_lt_zero, IsEmpty.forall_iff, forall_const, pow_zero,
      Distribution.mass_true, Distribution.weight_pi]
    simp [uniform, Distribution.weight_uniform]
  | append_singleton bs b ih =>
    simp only [List.length_append, List.length_singleton] at hn ⊢
    have hev : ∀ tbl : Fin K → Bool,
        (∀ k (hk : k < bs.length + 1), tbl ⟨k, by omega⟩ = (bs ++ [b])[k]'(by simpa using hk)) ↔
          (∀ k (hk : k < bs.length), tbl ⟨k, by omega⟩ = bs[k]) ∧
            tbl ⟨bs.length, by omega⟩ = b := by
      intro tbl
      constructor
      · intro h
        refine ⟨fun k hk => ?_, by simpa using h bs.length (by omega)⟩
        have hk' := h k (by omega)
        rwa [List.getElem_append_left hk] at hk'
      · rintro ⟨h, hb⟩ k hk
        rcases Nat.lt_or_ge k bs.length with hk' | hk'
        · rw [List.getElem_append_left hk']
          exact h k hk'
        · obtain rfl : k = bs.length := by omega
          simpa using hb
    rw [Distribution.mass_congr _ hev, Distribution.mass_pi_and_eq (fun _ : Fin K => (𝒰[Bool]).1)
      (fun _ => (𝒰[Bool]).2.2) ⟨bs.length, by omega⟩ b _ ?indep, ih (by omega)]
    · simp [uniform, Distribution.uniform_apply, pow_succ]
    · intro f a'
      refine forall_congr' fun k => forall_congr' fun hk => ?_
      rw [Function.update_of_ne (by simp [Fin.ext_iff]; omega)]

/-- Fresh sampling is independent for every number of calls within the budget. -/
theorem freshBits_independent {q : ℕ} (bs : List Bool) (hq : bs.length ≤ q) :
    (FreshBits (budget := q)).1 (bs.map fun b => (⟨.bit, ()⟩, ⟨.bit, b⟩)) =
      (1 / 2) ^ bs.length := by
  have hb : 1 ≤ FreshBits.bound := FreshBits.bound_spec none .bit () [] ⟨(), ()⟩
    (Program.consistent_nil FreshBits.body none _ _) (by simp [FreshBits.body, callProg])
  have hK : bs.length ≤ FreshBits.bound * q := hq.trans (Nat.le_mul_of_pos_left q hb)
  rw [FreshBits, FreshBits.randomness, FreshBits.program, Resource.source,
    Converter.ofProgram_smul_ofAutomaton, Resource.ofAutomaton_mass,
    Distribution.mass_fTransform, Distribution.mass_fTransform, ← mass_prefix bs hK]
  refine Distribution.mass_congr _ fun t => ?_
  simp only [List.map_map, Function.comp_def]
  rw [replies_filterDom_iff (FreshBits.outer q).nonempty_prefix.2 _
    (fun hne => ⟨by simpa using hne, by simpa using hq⟩)]
  exact freshBits_replies t bs hK

/-- The first call samples the secret; later calls return it without sampling. -/
theorem secretBit_combine_first {K : ℕ} (t : Fin K → Bool) :
    SecretBit.body.combine (sourceStep SecretBit.law1) SecretBit.bound_spec (none, (t, 0)) .bit () =
      ((some (if h : 0 < K then t ⟨0, h⟩ else Classical.choice SecretBit.law1.nonempty), (t, 1)),
        if h : 0 < K then t ⟨0, h⟩ else Classical.choice SecretBit.law1.nonempty) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    simp [Program.invoke, SecretBit.body, callProg, returnProg, sourceStep])

theorem secretBit_combine_later {K : ℕ} (v : Bool) (r : (Fin K → Bool) × ℕ) :
    SecretBit.body.combine (sourceStep SecretBit.law1) SecretBit.bound_spec (some v, r) .bit () =
      ((some v, r), v) :=
  Program.combine_eq_of_invoke _ _ (n := 0) (by simp [Program.invoke, SecretBit.body, returnProg])

/-- Sampling at initialization retains the same bit on later calls, at every budget. -/
theorem secretBit_retained (q : ℕ) (b : Bool) :
    (SecretBit (budget := q)).1 [(⟨.bit, ()⟩, ⟨.bit, b⟩), (⟨.bit, ()⟩, ⟨.bit, !b⟩)] = 0 := by
  rw [SecretBit, SecretBit.randomness, SecretBit.program, Resource.source,
    Converter.ofProgram_smul_ofAutomaton, Resource.ofAutomaton_mass,
    Distribution.mass_fTransform, Distribution.mass_fTransform]
  refine Distribution.mass_eq_zero_of_forall_not _ fun t hr => ?_
  have hr := replies_filterDom _ _ hr
  change Replies _ ([] ++ [(⟨.bit, ()⟩ : Sigma SecretBit.Input)] ++ [⟨.bit, ()⟩])
    ([] ++ [(⟨.bit, b⟩ : Sigma SecretBit.Output)] ++ [⟨.bit, !b⟩]) at hr
  obtain ⟨hr, h₂⟩ := replies_snoc.mp hr
  obtain ⟨-, h₁⟩ := replies_snoc.mp hr
  rw [automatonSystem_snoc] at h₁ h₂
  rw [stateAfter_snoc, stateAfter_nil] at h₂
  rw [stateAfter_nil, secretBit_combine_first] at h₁
  rw [secretBit_combine_first, secretBit_combine_later] at h₂
  simp only [Part.some_inj, Sigma.mk.injEq, heq_eq_eq, true_and] at h₁ h₂
  cases b <;> simp_all

/-- The two ports share the counter. -/
theorem counter_interleaving {q : ℕ} (hq : 3 ≤ q) :
    (Counter (budget := q)).1 [(⟨.next, ()⟩, ⟨.next, 1⟩), (⟨.read, ()⟩, ⟨.read, 1⟩),
      (⟨.next, ()⟩, ⟨.next, 2⟩)] = 1 := by
  rw [Counter, Interface.Resource.ofAutomaton_mass]
  refine (Distribution.mass_single _ _ _).trans (if_pos ?_)
  change Replies _ ([] ++ [(⟨.next, ()⟩ : Sigma Counter.Input)] ++ [⟨.read, ()⟩] ++ [⟨.next, ()⟩])
    ([] ++ [(⟨.next, 1⟩ : Sigma Counter.Output)] ++ [⟨.read, 1⟩] ++ [⟨.next, 2⟩])
  refine replies_snoc.mpr ⟨replies_snoc.mpr ⟨replies_snoc.mpr ⟨replies_nil _, ?_⟩, ?_⟩, ?_⟩ <;>
    rw [filterDom, if_pos ⟨by simp, by simp; omega⟩, automatonSystem_snoc] <;> rfl

/-- Budgets of two queries at `next` and one at `read`. -/
def counterBudget : Counter.Port → ℕ
  | .next => 2
  | .read => 1

/-- At per-port budgets, the two ports share the counter within their own budgets. -/
theorem counter_perPort_interleaving :
    (Counter.perPort (budget := counterBudget)).1 [(⟨.next, ()⟩, ⟨.next, 1⟩),
      (⟨.read, ()⟩, ⟨.read, 1⟩), (⟨.next, ()⟩, ⟨.next, 2⟩)] = 1 := by
  rw [Counter.perPort, Interface.Resource.ofAutomaton_mass]
  refine (Distribution.mass_single _ _ _).trans (if_pos ?_)
  change Replies _ ([] ++ [(⟨.next, ()⟩ : Sigma Counter.Input)] ++ [⟨.read, ()⟩] ++ [⟨.next, ()⟩])
    ([] ++ [(⟨.next, 1⟩ : Sigma Counter.Output)] ++ [⟨.read, 1⟩] ++ [⟨.next, 2⟩])
  refine replies_snoc.mpr ⟨replies_snoc.mpr ⟨replies_snoc.mpr ⟨replies_nil _, ?_⟩, ?_⟩, ?_⟩ <;>
    rw [filterDom, if_pos ⟨by simp, by intro i; cases i <;> simp [counterBudget]⟩,
      automatonSystem_snoc] <;> rfl

/-- A second query at `read` exceeds its budget. -/
theorem counter_perPort_exceeded (n m : Fin 16) :
    (Counter.perPort (budget := counterBudget)).1 [(⟨.read, ()⟩, ⟨.read, n⟩),
      (⟨.read, ()⟩, ⟨.read, m⟩)] = 0 := by
  rw [Counter.perPort, Interface.Resource.ofAutomaton_mass]
  refine (Distribution.mass_single _ _ _).trans (if_neg fun hr => ?_)
  change Replies _ ([] ++ [(⟨.read, ()⟩ : Sigma Counter.Input)] ++ [⟨.read, ()⟩])
    ([] ++ [(⟨.read, n⟩ : Sigma Counter.Output)] ++ [⟨.read, m⟩]) at hr
  have hd := (replies_snoc.mp hr).2
  rw [filterDom, if_neg] at hd
  · exact Part.some_ne_none _ hd.symm
  · rintro ⟨-, h⟩
    simpa [counterBudget] using h .read

/-- At per-port budgets, the write-through converter maps `Cache` to `Store`, with the store's
budget that of the writes. -/
noncomputable example (q : Cache.Port → ℕ) :
    Cache.perPort q ⟶ Store.perPort (WriteThrough.insideBudget q) :=
  WriteThrough.perPort (budget := q)

/-- Writes query the store; reads query nothing inside. -/
example : WriteThrough.portMap .write = some .put ∧ WriteThrough.portMap .read = none := ⟨rfl, rfl⟩

example (q : Cache.Port → ℕ) : WriteThrough.insideBudget q .put = q .write := rfl

end DSLTests.Semantics
