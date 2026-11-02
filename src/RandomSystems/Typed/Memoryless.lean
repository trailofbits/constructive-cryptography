module

public import RandomSystems.Typed.DSL.Converters
public import RandomSystems.Typed.Context
public import RandomSystems.System.Memoryless

/-!
# Memoryless systems on interfaces

`TypedSystem.ofMemoryless A ν` answers each admitted query `i(x)` with a fresh reply
`y ∼ ν i x`, independently of earlier exchanges [1, Definition 3.1, p. 55; §3.6.1, p. 65].
`ofMemoryless_val` identifies this typed system with its cumulative behavior;
`eq_memoryless_of_eq_ofMemoryless` projects a supplied typed contract to that behavior.

`source_eq_memoryless` proves the source law by exposing its table of independent samples.
`parallel_eq_memoryless` transports the raw parallel law through the tensor's port labels.
Their typed forms, `source_eq_ofMemoryless`, `parallel_ofMemoryless` and
`parallel_eq_ofMemoryless`, compose these contracts without projecting cumulative behavior.

The program contracts `TypedConverter.ofProgram_smul_ofMemoryless`,
`ofPreservingProgram_smul_ofMemoryless` and `ofCostedProgram_smul_ofMemoryless` give
`α • ofMemoryless B ν = ofMemoryless A κ` for the converter `α` of a program `P` with
call bound `b`, when `∀ s o u, P.memorylessReplyLaw ν s o u b [] = (κ o u).1`.
They reuse `PDCBehavior.attach_ofDDC_ofProgramOn_memoryless`; the corresponding
`_smul_memoryless` lemmas state the same laws on cumulative behavior.

`ofPreservingProgram_comp_rightContext_smul_memoryless` places an independent memoryless
resource `T` beside the inside resource `R`:

```text
              ┌───┐ ── j(x) ──► R     reply y ∼ ν j x
  o(u) ──────►│ P │ ◄──── y ───
       ◄── v ─│   │ ── k(w) ──► T     independent reply z ∼ ν' k w
              └───┘ ◄──── z ───
  (comp α (rightContext B T) • R).1 = memoryless A.inputDomain (portLaw κ)
```

Here the invocation hypothesis is
`∀ s o u, P.memorylessReplyLaw (parallelLaw ν ν') s o u b [] = (κ o u).1`.

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

@[expose] public section

namespace SystemAlgebra

open Probability Probability.Distribution RandomSystem Interface

namespace TypedSystem

/-- At each admitted query `i(x)`, draw a fresh reply `y ∼ ν i x` at port `i`.
Each query independently uses the “discrete memoryless channel” of [1, §3.6.1, p. 65]
on `A.domain`. -/
noncomputable def ofMemoryless
    -- `A` fixes the ports, query/reply types and admitted input histories.
    (A : Interface)
    -- `ν i x` is the reply law for `x : A.X i`, independent of earlier queries and replies.
    (ν : ∀ i, A.X i → ProbDist (A.Y i)) : TypedSystem A :=
  ofConditional fun _ i x _ => ν i x

/-- The random system of `ofMemoryless A ν` is `memoryless A.inputDomain (portLaw ν)`. -/
@[simp] lemma ofMemoryless_val {A : Interface} (ν : ∀ i, A.X i → ProbDist (A.Y i)) :
    (ofMemoryless A ν).1 = memoryless A.inputDomain (portLaw ν) := rfl

/-- A typed fresh-reply contract identifies the same cumulative memoryless behavior. -/
lemma eq_memoryless_of_eq_ofMemoryless
    -- `R` is the system on `A`; `ν i x` is its fresh reply law at query `i(x)`.
    {A : Interface} {R : TypedSystem A} {ν : ∀ i, A.X i → ProbDist (A.Y i)}
    (hR : R = ofMemoryless A ν) :
    R.1 = memoryless A.inputDomain (portLaw ν) :=
  congrArg Subtype.val hR

/-- The source of `q` independent samples has next-reply law `law` at every admitted trigger.
[1, Definition 3.1, p. 55]: "A source can be memoryless or have memory". -/
lemma source_eq_memoryless
    -- `Z` carries replies; `law` is sampled independently at each of the `q` triggers.
    {Z : Type} [Fintype Z] (law : ProbDist Z) (q : ℕ) :
    (TypedSystem.source law q).1 =
      memoryless (Interface.source Z q).inputDomain (portLaw fun _ _ => law) := by
  -- The source reads its independent table in order:
  --   () ──► [t ∼ law^q, counter k] ──► t k, then k := k + 1.
  -- The chain rule follows from independence of the next unread coordinate:
  --   P[h · ((), z)] = law^q[t gives h ∧ t h.length = z] = P[h] · law z.
  classical
  -- `event h t` means that reading table `t` produces transcript `h`.
  let event : List ((Σ _ : Unit, Unit) × (Σ _ : Unit, Z)) → (Fin q → Z) → Prop := fun h t =>
    Replies (filterDom (Interface.source Z q).domain (automatonSystem (sourceStep law) (t, 0)))
      (h.map Prod.fst) (h.map Prod.snd)
  have hmass : ∀ h,
      (TypedSystem.source law q).1 h = (pi fun _ : Fin q => law.1).mass (event h) := by
    intro h
    -- The transcript probability is the mass of its producing tables under `law^q`.
    rw [TypedSystem.source, ofAutomaton_mass, ProbDist.map_val, ProbDist.pi_val,
      mass_fTransform]
  -- A table gives `h · ((), z)` iff it gives `h` and `t h.length = z`.
  have hsnoc : ∀ h z (hlt : h.length < q), ((Interface.source Z q).domain
      (h.map Prod.fst ++ [⟨(), ()⟩])) → ∀ t, event (h ++ [(⟨(), ()⟩, ⟨(), z⟩)]) t ↔
        event h t ∧ t ⟨h.length, hlt⟩ = z := by
    intro h z hlt hd t
    -- After `h`, state `(t, h.length)` reads the next entry; `hd` admits this trigger.
    simp only [event, List.map_append, List.map_cons, List.map_nil, replies_snoc,
      SystemAlgebra.filterDom, automatonSystem_snoc, stateAfter_sourceStep, ite_eq_left hd]
    simp [sourceStep, hlt, Part.some_inj, eq_comm]
  -- Producing `h` depends only on table entries before `h.length`.
  have hread : ∀ h t t', (∀ j : Fin q, j.val < h.length → t j = t' j) →
      (event h t ↔ event h t') := by
    intro h
    induction h using List.reverseRecOn with
    -- No exchange: every table gives the empty transcript.
    | nil => intro t t' _; simp [event]
    -- The next exchange reads one more agreeing entry.
    | append_singleton h e ih =>
      intro t t' ht
      obtain ⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟨⟩, z⟩⟩ := e
      -- The earlier exchanges agree by the induction hypothesis.
      have hpre := ih t t' fun j hj => ht j (by simp; omega)
      -- One step of the automaton after `h`, for both tables.
      simp only [event, List.map_append, List.map_cons, List.map_nil, replies_snoc,
        SystemAlgebra.filterDom, automatonSystem_snoc, stateAfter_sourceStep] at hpre ⊢
      -- The earlier exchanges are given by `t` iff by `t'`.
      rw [hpre]
      -- Split on whether the domain still admits a trigger after `h`.
      by_cases hlt : h.length < q
      -- `h.length < q`: the new reply is `t h.length = t' h.length`.
      · simp [sourceStep, hlt, ht ⟨h.length, hlt⟩ (by simp)]
      -- Past `q` triggers the domain admits no more trigger, under either table.
      · simp [hlt]
  -- The cumulative criterion reduces equality to `P[h · ((), z)] = P[h] · law z`.
  refine eq_memoryless_of_snoc fun h x y hd => ?_
  -- The query is the trigger `()`, the reply some `z`.
  obtain ⟨⟨⟩, ⟨⟩⟩ := x
  obtain ⟨⟨⟩, z⟩ := y
  -- The domain admits the trigger after `h`: at most `q` triggers, so `h.length < q`.
  have hd' : (Interface.source Z q).domain (h.map Prod.fst ++ [⟨(), ()⟩]) := hd
  have hlt : h.length < q := by
    have := hd'.2
    simp only [List.length_append, List.length_map, List.length_singleton] at this
    omega
  -- Express the extended transcript as `event h ∧ t h.length = z`.
  rw [hmass, hmass, mass_congr _ (hsnoc h z hlt hd')]
  -- `hread` makes the next coordinate independent of `event h`, giving the product mass.
  rw [mass_pi_and_eq (fun _ : Fin q => law.1) (fun _ => law.2.2) ⟨h.length, hlt⟩ z (event h)
    fun t a => hread h _ _ fun j hj => Function.update_of_ne (Fin.ne_of_val_ne hj.ne) _ _]
  -- The reply law of the source at its port is `law`.
  rw [portLaw_apply_mk]

/-- The source of `q` independent samples is the typed memoryless system of `law`. -/
lemma source_eq_ofMemoryless
    -- `Z` carries replies; `law` is sampled independently at each of the `q` triggers.
    {Z : Type} [Fintype Z] (law : ProbDist Z) (q : ℕ) :
    source law q = ofMemoryless (Interface.source Z q) (fun _ _ => law) :=
  Subtype.ext (source_eq_memoryless law q)

/-- Independent components reply according to the queried port's law, `parallelLaw ν₁ ν₂`.
The raw parallel law is transported through the tensor's port labels. -/
lemma parallel_eq_memoryless
    -- `R` and `T` are the systems on the selected interfaces `A` and `B`.
    {A B : Interface} {R : TypedSystem A} {T : TypedSystem B}
    -- `ν₁` and `ν₂` give their portwise reply laws; `hR` and `hT` certify fresh replies.
    {ν₁ : ∀ i, A.X i → ProbDist (A.Y i)} {ν₂ : ∀ j, B.X j → ProbDist (B.Y j)}
    (hR : R.1 = memoryless A.inputDomain (portLaw ν₁))
    (hT : T.1 = memoryless B.inputDomain (portLaw ν₂)) :
    (parallel R T).1 = memoryless (tensor A B).inputDomain (portLaw (parallelLaw ν₁ ν₂)) := by
  -- `e` below relabels the tensor transcript as a raw parallel transcript:
  --   inl i(x) ──► R ──► y ∼ ν₁ i x
  --   inr j(x) ──► T ──► y ∼ ν₂ j x.
  -- For e(x, y) = (x', y'), the raw chain rule gives
  --   P∥[e(h · (x, y))] = P∥[e h] · portLaw (twoLaw ν₁' ν₂') x' y',
  -- with ν₁' = portLaw ν₁ and ν₂' = portLaw ν₂; comparing port labels gives
  -- P∥[e h] · portLaw (parallelLaw ν₁ ν₂) x y.
  have hsys := RandomSystem.parallel_memoryless A.inputDomain B.inputDomain (portLaw ν₁)
    (portLaw ν₂)
  -- Write the two memoryless systems of `hsys` as `R.1` and `T.1` (`hR`, `hT`).
  rw [← hR, ← hT] at hsys
  -- Reduce to the chain rule for `parallelLaw` at each admitted exchange `(x, y)`.
  refine eq_memoryless_of_snoc fun h x y hd => ?_
  -- The typed system is the systems-level one on the transcript with relabelled ports.
  let eX := sumAlphabet (Sum.rec A.X B.X)
  let e := eX.symm.prodCongr (sumAlphabet (Sum.rec A.Y B.Y)).symm
  change RandomSystem.parallel R.1 T.1 ((h ++ [(x, y)]).map e) =
    RandomSystem.parallel R.1 T.1 (h.map e) * (portLaw (parallelLaw ν₁ ν₂) x).1 y
  rw [List.map_append, List.map_singleton]
  -- `parallel_admits_iff` needs P∥[e h] ≠ 0, so impossible prefixes come first.
  by_cases hz : RandomSystem.parallel R.1 T.1 (h.map e) = 0
  · -- An impossible transcript stays impossible.
    rw [hz, zero_mul]
    exact (RandomSystem.parallel R.1 T.1).mass_eq_zero_of_prefix (List.prefix_append _ _) hz
  -- At a positive prefix, tensor-domain admission gives raw parallel-domain admission.
  have hadm := (parallel_admits_iff A B R T (h.map e) hz (eX.symm x)).mpr (by
    -- Relabelling the queries of `h` to the systems level and back leaves them unchanged.
    have hround : ((h.map e).map Prod.fst).map eX = h.map Prod.fst := by
      simp only [List.map_map]
      exact List.map_congr_left fun z _ => eX.apply_symm_apply _
    rw [hround, eX.apply_symm_apply]
    exact hd)
  -- The chain rule at the systems level; it remains to compare the two laws of the reply.
  rw [hsys, show e (x, y) = (eX.symm x, (sumAlphabet (Sum.rec A.Y B.Y)).symm y) from rfl,
    memoryless_snoc, ite_eq_left hadm]
  -- Cancel the common factor, the probability of `h`.
  congr 1
  -- Compare the port laws: matching ports use the component law; other ports have zero mass.
  obtain ⟨(i | j), x⟩ := x <;> obtain ⟨(k | l), y⟩ := y
  -- Left query `⟨inl i, x⟩`, left reply at `k`: `twoLaw` hands the query to `portLaw ν₁`.
  · change (portLaw (twoLaw (portLaw ν₁) (portLaw ν₂)) ⟨none, ⟨i, x⟩⟩).1 ⟨none, ⟨k, y⟩⟩ = _
    rw [portLaw_apply_mk]
    -- At `k = i` both laws are `ν₁ i x`; at `k ≠ i` both give the reply zero mass.
    by_cases hk : k = i
    · subst hk
      simp only [twoLaw, parallelLaw, portLaw_apply_mk]
    · simp only [twoLaw]
      rw [portLaw_apply_of_ne _ (by simpa using hk), portLaw_apply_of_ne _ (by simpa using hk)]
  -- Left query, right reply: zero on both sides.
  · change (portLaw (twoLaw (portLaw ν₁) (portLaw ν₂)) ⟨none, ⟨i, x⟩⟩).1 ⟨some (), ⟨l, y⟩⟩ = _
    rw [portLaw_apply_of_ne _ (by simp), portLaw_apply_of_ne _ (by simp)]
  -- Right query, left reply: zero on both sides.
  · change (portLaw (twoLaw (portLaw ν₁) (portLaw ν₂)) ⟨some (), ⟨j, x⟩⟩).1 ⟨none, ⟨k, y⟩⟩ = _
    rw [portLaw_apply_of_ne _ (by simp), portLaw_apply_of_ne _ (by simp)]
  -- Right query `⟨inr j, x⟩`, right reply at `l`: as the left case, with `portLaw ν₂`.
  · change (portLaw (twoLaw (portLaw ν₁) (portLaw ν₂)) ⟨some (), ⟨j, x⟩⟩).1 ⟨some (), ⟨l, y⟩⟩ = _
    rw [portLaw_apply_mk]
    by_cases hl : l = j
    · subst hl
      simp only [twoLaw, parallelLaw, portLaw_apply_mk]
    · simp only [twoLaw]
      rw [portLaw_apply_of_ne _ (by simpa using hl), portLaw_apply_of_ne _ (by simpa using hl)]

/-- Independent parallel composition replies with the law of the queried component. -/
lemma parallel_ofMemoryless
    -- `A`, `B` retain their selected domains in the tensor interface.
    {A B : Interface}
    -- `ν₁ i x` and `ν₂ j y` are fresh reply laws at the two components' ports.
    (ν₁ : ∀ i, A.X i → ProbDist (A.Y i)) (ν₂ : ∀ j, B.X j → ProbDist (B.Y j)) :
    parallel (ofMemoryless A ν₁) (ofMemoryless B ν₂) =
      ofMemoryless (tensor A B) (parallelLaw ν₁ ν₂) :=
  Subtype.ext (parallel_eq_memoryless rfl rfl)

/-- Two supplied fresh-reply contracts compose to the side-by-side law `parallelLaw ν₁ ν₂`. -/
lemma parallel_eq_ofMemoryless
    -- `R` and `T` retain their selected interfaces `A` and `B`.
    {A B : Interface} {R : TypedSystem A} {T : TypedSystem B}
    -- `ν₁` and `ν₂` give portwise laws; `hR` and `hT` identify the two fresh-reply systems.
    {ν₁ : ∀ i, A.X i → ProbDist (A.Y i)} {ν₂ : ∀ j, B.X j → ProbDist (B.Y j)}
    (hR : R = ofMemoryless A ν₁) (hT : T = ofMemoryless B ν₂) :
    parallel R T = ofMemoryless (tensor A B) (parallelLaw ν₁ ν₂) := by
  rw [hR, hT, parallel_ofMemoryless]

end TypedSystem

namespace TypedConverter

-- `A` is the outside interface, `B` the inside interface, and `S` the program state type.
variable {A B : Interface} {S : Type}

/-- If every invocation against fresh replies `ν` has law `κ`, attachment gives `memoryless κ`.
The domain guarantee `hB` admits all inside histories generated by the bound `hb`. -/
lemma ofProgram_smul_memoryless
    -- `P` starts at `s`, answers at `A`, and calls `B`; `b` bounds each invocation.
    (s : S) (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ}
    -- `hb` certifies the call bound; `hB` admits the resulting inside histories.
    (hb : P.Bounded b) (hB : ∀ xs, xs ≠ [] → xs.length ≤ b * A.bound → B.domain xs)
    -- `R` is the inside system, with fresh reply law `ν` certified by `hR`; `κ` is the target law.
    {R : TypedSystem B} {ν : ∀ j, B.X j → ProbDist (B.Y j)} {κ : ∀ o, A.X o → ProbDist (A.Y o)}
    (hR : R.1 = memoryless B.inputDomain (portLaw ν))
    -- `hκ` gives reply law `κ o u` from every program state `s'`.
    (hκ : ∀ s' o u, P.memorylessReplyLaw ν s' o u b [] = (κ o u).1) :
    (ofProgram s P hb hB • R).1 = memoryless A.inputDomain (portLaw κ) :=
  -- `ofProgram` is the behavior of `DDC.ofProgramOn s P A.domain`; `R.2` keeps replies
  -- at the queried port. The attachment theorem therefore gives the memoryless system of `κ`.
  PDCBehavior.attach_ofDDC_ofProgramOn_memoryless B.nonempty_prefix A.nonempty_prefix s P hb _ hκ hR
    R.2

/-- A port-preserving program with state-independent reply law `κ` gives `memoryless κ`.
`ι` routes outside ports; `q`, `hA` and `hB` retain their selected query allowances. -/
lemma ofPreservingProgram_smul_memoryless
    -- `P` starts at `s`; `hb` bounds each invocation by `b` inside calls.
    (s : S) (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    -- `ι o` selects a controlled port; `hι` permits at most one call there from `o`.
    (ι : A.I → Option B.I) (hι : P.PortPreserving ι)
    -- `q o` bounds outside calls at `o`; `hA` certifies this on `A.domain`.
    (q : A.I → ℕ)
    (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    -- `hB` admits histories respecting the total bound and the controlled ports' allowances.
    (hB : ∀ ys, ys ≠ [] → ys.length ≤ b * A.bound →
      (∀ o j, ι o = some j → (SystemAlgebra.restrict j ys).length ≤ q o) → B.domain ys)
    -- `R` has fresh portwise law `ν` by `hR`; `κ` is the claimed outside law.
    {R : TypedSystem B} {ν : ∀ j, B.X j → ProbDist (B.Y j)} {κ : ∀ o, A.X o → ProbDist (A.Y o)}
    (hR : R.1 = memoryless B.inputDomain (portLaw ν))
    -- `hκ` gives reply law `κ o u` from every program state `s'`.
    (hκ : ∀ s' o u, P.memorylessReplyLaw ν s' o u b [] = (κ o u).1) :
    (ofPreservingProgram s P hb ι hι q hA hB • R).1 = memoryless A.inputDomain (portLaw κ) :=
  -- Port preservation supplies the domain guarantee for the same underlying program DDC.
  PDCBehavior.attach_ofDDC_ofProgramOn_memoryless B.nonempty_prefix A.nonempty_prefix s P hb _ hκ hR
    R.2

/-- A costed program with state-independent reply law `κ` gives `memoryless κ` on `A.domain`.
`hc` certifies inside-call costs; `hA` limits their accumulated cost to `q`. -/
lemma ofCostedProgram_smul_memoryless
    -- `P` starts at `s`; `hb` bounds each invocation by `b` inside calls.
    (s : S) (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    -- `cost x` counts inside calls for query `x`; `hc` certifies it, and `q` bounds the total.
    (cost : (Σ o, A.X o) → ℕ) (hc : P.Costs cost) {q : ℕ}
    -- `hA` bounds accumulated outside cost; `hB` admits inside histories up to that bound.
    (hA : ∀ us, A.domain us → (us.map cost).sum ≤ q)
    (hB : ∀ xs, xs ≠ [] → xs.length ≤ q → B.domain xs)
    -- `R` has fresh portwise law `ν` by `hR`; `κ` is the claimed outside law.
    {R : TypedSystem B} {ν : ∀ j, B.X j → ProbDist (B.Y j)} {κ : ∀ o, A.X o → ProbDist (A.Y o)}
    (hR : R.1 = memoryless B.inputDomain (portLaw ν))
    -- `hκ` gives reply law `κ o u` from every program state `s'`.
    (hκ : ∀ s' o u, P.memorylessReplyLaw ν s' o u b [] = (κ o u).1) :
    (ofCostedProgram s P hb cost hc hA hB • R).1 =
      memoryless A.inputDomain (portLaw κ) :=
  -- The accumulated-cost guarantee types the same underlying program DDC.
  PDCBehavior.attach_ofDDC_ofProgramOn_memoryless B.nonempty_prefix A.nonempty_prefix s P hb _ hκ hR
    R.2

/-- Attaching a program with its own memoryless source gives `memoryless κ` when every
invocation against the side-by-side law `parallelLaw ν ν'` has law `κ`. -/
lemma ofPreservingProgram_comp_rightContext_smul_memoryless
    -- `C` is the auxiliary resource's interface; `P` starts at `s` and calls both `B` and `C`.
    {C : Interface} (s : S)
    (P : Program S A.I (tensor B C).I A.X A.Y (tensor B C).X (tensor B C).Y) {b : ℕ}
    -- `hb` bounds each invocation by `b`; `hι` limits calls to each port selected by `ι`.
    (hb : P.Bounded b) (ι : A.I → Option (tensor B C).I) (hι : P.PortPreserving ι)
    -- `q o` bounds calls at outside port `o`; `hA` certifies it on `A.domain`.
    (q : A.I → ℕ) (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    -- `hB` admits the resulting histories of the combined inside interface `B ⊗ C`.
    (hB : ∀ ys, ys ≠ [] → ys.length ≤ b * A.bound →
      (∀ o j, ι o = some j → (SystemAlgebra.restrict j ys).length ≤ q o) → (tensor B C).domain ys)
    -- `R` and `T` have fresh portwise laws `ν` and `ν'`; `κ` is the claimed outside law.
    {R : TypedSystem B} {T : TypedSystem C} {ν : ∀ j, B.X j → ProbDist (B.Y j)}
    {ν' : ∀ k, C.X k → ProbDist (C.Y k)} {κ : ∀ o, A.X o → ProbDist (A.Y o)}
    -- `hR` and `hT` certify those laws for the two independent components.
    (hR : R.1 = memoryless B.inputDomain (portLaw ν))
    (hT : T.1 = memoryless C.inputDomain (portLaw ν'))
    -- `hκ` gives reply law `κ o u` from every state `s'` against their side-by-side law.
    (hκ : ∀ s' o u, P.memorylessReplyLaw (parallelLaw ν ν') s' o u b [] = (κ o u).1) :
    (comp (ofPreservingProgram s P hb ι hι q hA hB) (rightContext B T) • R).1 =
      memoryless A.inputDomain (portLaw κ) := by
  -- The right context places the independent source `T` beside `R`.
  rw [comp_smul, attach_rightContext]
  -- Their parallel reply law is the inside law required by the program contract.
  exact ofPreservingProgram_smul_memoryless s P hb ι hι q hA hB
    (TypedSystem.parallel_eq_memoryless hR hT) hκ

/-- If every invocation has reply law `κ`, attachment gives `ofMemoryless A κ`.
This is `ofProgram_smul_memoryless` as an equality of typed systems. -/
lemma ofProgram_smul_ofMemoryless
    -- `s` is the initial state; `P` queries `B` while answering queries at `A`.
    (s : S) (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ}
    -- `hb` bounds each invocation by `b`; `hB` admits the resulting inside histories.
    (hb : P.Bounded b) (hB : ∀ xs, xs ≠ [] → xs.length ≤ b * A.bound → B.domain xs)
    -- `R` is the inside system; `ν` gives its reply laws and `κ` the claimed outside laws.
    {R : TypedSystem B} {ν : ∀ j, B.X j → ProbDist (B.Y j)}
    {κ : ∀ o, A.X o → ProbDist (A.Y o)}
    -- `hR` certifies that `R` gives fresh replies with law `ν`.
    (hR : R = TypedSystem.ofMemoryless B ν)
    -- `hκ` requires the same reply law from every state, including resumed invocations.
    (hκ : ∀ s' o u, P.memorylessReplyLaw ν s' o u b [] = (κ o u).1) :
    ofProgram s P hb hB • R = TypedSystem.ofMemoryless A κ :=
  Subtype.ext (ofProgram_smul_memoryless s P hb hB
    (TypedSystem.eq_memoryless_of_eq_ofMemoryless hR) hκ)

/-- A port-preserving program with state-independent reply law `κ` gives `ofMemoryless A κ`.
The selected domains and per-port allowances are those of the supplied converter. -/
lemma ofPreservingProgram_smul_ofMemoryless
    -- `P` starts at `s`; `hb` bounds each invocation by `b` inside calls.
    (s : S) (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    -- `ι o = some j` selects a controlled port; `hι` permits at most one call there from `o`.
    -- Auxiliary calls remain bounded by `hb`.
    (ι : A.I → Option B.I) (hι : P.PortPreserving ι) (q : A.I → ℕ)
    -- `hA` bounds outside calls by `q`; `hB` admits the corresponding routed inside histories.
    (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    (hB : ∀ ys, ys ≠ [] → ys.length ≤ b * A.bound →
      (∀ o j, ι o = some j → (SystemAlgebra.restrict j ys).length ≤ q o) → B.domain ys)
    -- `hR` identifies the inside system `R` with fresh law `ν`; `κ` is the outside reply law.
    {R : TypedSystem B} {ν : ∀ j, B.X j → ProbDist (B.Y j)}
    {κ : ∀ o, A.X o → ProbDist (A.Y o)} (hR : R = TypedSystem.ofMemoryless B ν)
    -- `hκ` gives reply law `κ o u` from every state `s'`, including resumed invocations.
    (hκ : ∀ s' o u, P.memorylessReplyLaw ν s' o u b [] = (κ o u).1) :
    ofPreservingProgram s P hb ι hι q hA hB • R = TypedSystem.ofMemoryless A κ :=
  Subtype.ext (ofPreservingProgram_smul_memoryless s P hb ι hι q hA hB
    (TypedSystem.eq_memoryless_of_eq_ofMemoryless hR) hκ)

/-- A costed program with state-independent reply law `κ` gives `ofMemoryless A κ`.
The outside domain retains the converter's cumulative cost restriction. -/
lemma ofCostedProgram_smul_ofMemoryless
    -- `P` starts at `s`; `hb` bounds each invocation by `b` inside calls.
    (s : S) (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    -- `cost x` counts the inside calls for query `x`; `hc` certifies those counts.
    (cost : (Σ o, A.X o) → ℕ) (hc : P.Costs cost) {q : ℕ}
    -- `hA` limits the accumulated cost to `q`; `hB` admits the resulting inside histories.
    (hA : ∀ us, A.domain us → (us.map cost).sum ≤ q)
    (hB : ∀ xs, xs ≠ [] → xs.length ≤ q → B.domain xs)
    -- `hR` identifies the inside system `R` with fresh law `ν`; `κ` is the outside reply law.
    {R : TypedSystem B} {ν : ∀ j, B.X j → ProbDist (B.Y j)}
    {κ : ∀ o, A.X o → ProbDist (A.Y o)} (hR : R = TypedSystem.ofMemoryless B ν)
    -- `hκ` gives reply law `κ o u` from every state `s'`, including resumed invocations.
    (hκ : ∀ s' o u, P.memorylessReplyLaw ν s' o u b [] = (κ o u).1) :
    ofCostedProgram s P hb cost hc hA hB • R = TypedSystem.ofMemoryless A κ :=
  Subtype.ext (ofCostedProgram_smul_memoryless s P hb cost hc hA hB
    (TypedSystem.eq_memoryless_of_eq_ofMemoryless hR) hκ)

end TypedConverter

end SystemAlgebra
