import RandomSystems.Typed.DSL.Converters
import RandomSystems.Typed.Context
import RandomSystems.System.Memoryless

/-!
# Memoryless systems on interfaces

A system on an interface whose random system is memoryless [1, Definition 3.1, §3.6.1] replies to
each query with a fresh sample of a law of that query. A source of independent samples is
memoryless, two memoryless systems side by side are memoryless, and the converter of a program maps
memoryless systems to memoryless systems, with the reply law of the program
(`PDCBehavior.attach_ofDDC_ofProgramOn_memoryless`), also when the converter has its own sources
beside its inside interface:

```
        o(u)       ┌───┐ ── j(q) ───► R, memoryless with ν
  ────────────────►│ P │
  ◄────────────────┤   │ ── k(()) ──► T, memoryless with ν'   (the converter's own randomness)
        o ⇒ v      └───┘
               comp P (rightContext B T) • R  =  mem(κ),   κ = P's reply law against ν, ν'
```

Statements about typed systems are equalities of their random systems (`.1`).

## Main results

* `TypedSystem.source_eq_memoryless`: a source of independent samples of `law` is memoryless
* `TypedSystem.parallel_eq_memoryless`: memoryless systems side by side are memoryless
* `TypedConverter.ofProgram_smul_memoryless`,
  `TypedConverter.ofPreservingProgram_smul_memoryless`,
  `TypedConverter.ofPreservingProgram_comp_rightContext_smul_memoryless`: the composition law
  `P • mem(ν) = mem(κ)` for the converters of programs

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

namespace SystemAlgebra

open Probability Probability.Distribution RandomSystem Interface

namespace TypedSystem

/-- **A source of independent samples is memoryless** [1, Definition 3.1]: the source of `q`
samples of `law` replies to each trigger with a fresh sample of `law`. -/
lemma source_eq_memoryless {Z : Type} [Fintype Z] (law : ProbDist Z) (q : ℕ) :
    (TypedSystem.source law q).1 =
      memoryless (Interface.source Z q).inputDomain (portLaw fun _ _ => law) := by
  -- Plan:
  -- 1. The typed source's random system is presented by a table `t ← law^q` of independent
  --    samples: a transcript `h` has the mass of the tables that give it (`hmass`).
  -- 2. One more trigger reads entry `h.length` of the table (`hsnoc`).
  -- 3. Whether a table gives `h` depends only on its entries before `h.length` (`hread`).
  -- 4. The systems-level criterion `eq_memoryless_of_snoc` asks for the chain rule of `law`:
  --    entry `h.length` is independent of the earlier ones, so each admitted trigger
  --    multiplies the probability by `law z`.
  --
  --              ┌─────────────────────────────┐
  --   () ──────▶ │ table t = (t 0, …, t (q-1)) │   entries independent, each ∼ law
  --   ◀── t k ── │ trigger k ↦ entry t k       │   (k = 0, 1, …; at most q triggers)
  --              └─────────────────────────────┘
  --
  --   P[h · ((), z)] = law^q[t gives h ∧ t h.length = z]
  --                  = law^q[t gives h] · law z      (entry h.length independent of the rest)
  --                  = P[h] · law z
  classical
  -- Step 1: the probability of a transcript is a mass of tables.
  -- The source reads its `k`-th reply from the `k`-th entry of a table `t` of independent
  -- samples. A transcript `h` has the probability of the tables from which it is read.
  let event : List ((Σ _ : Unit, Unit) × (Σ _ : Unit, Z)) → (Fin q → Z) → Prop := fun h t =>
    Replies (filterDom (Interface.source Z q).domain (automatonSystem (sourceStep law) (t, 0)))
      (h.map Prod.fst) (h.map Prod.snd)
  have hmass : ∀ h,
      (TypedSystem.source law q).1 h = (pi fun _ : Fin q => law.1).mass (event h) := by
    intro h
    -- The source is the automaton `sourceStep` started in `(t, 0)` (table `t`, counter `0`)
    -- for `t ← law^q`: a transcript has the mass of the initial states, hence of the tables,
    -- from which the automaton gives it.
    rw [TypedSystem.source, ofAutomaton_mass, mass_fTransform]
  -- Step 2: one more trigger reads the next entry of the table.
  -- One more exchange: the table also gives `h · ((), z)` when the domain admits one more query
  -- and its entry `h.length` is `z`.
  have hsnoc : ∀ h z (hlt : h.length < q), ((Interface.source Z q).domain
      (h.map Prod.fst ++ [⟨(), ()⟩])) → ∀ t, event (h ++ [(⟨(), ()⟩, ⟨(), z⟩)]) t ↔
        event h t ∧ t ⟨h.length, hlt⟩ = z := by
    intro h z hlt hd t
    -- After `h` the automaton is in state `(t, h.length)` (`stateAfter_sourceStep`); the
    -- domain admits the new trigger (`hd`), so the domain filter keeps its reply, the entry
    -- `t h.length`.
    simp only [event, List.map_append, List.map_cons, List.map_nil, replies_snoc,
      SystemAlgebra.filterDom, automatonSystem_snoc, stateAfter_sourceStep, if_pos hd]
    simp [sourceStep, hlt, Part.some_inj, eq_comm]
  -- Step 3: tables agreeing on the entries that `h` reads give `h` alike.
  -- The event of `h` reads only the entries before `h.length`.
  have hread : ∀ h t t', (∀ j : Fin q, j.val < h.length → t j = t' j) →
      (event h t ↔ event h t') := by
    intro h
    -- Induction on `h`, one exchange added at the end at a time.
    induction h using List.reverseRecOn with
    -- No exchange: every table gives the empty transcript.
    | nil => intro t t' _; simp [event]
    -- One more exchange `((), z)` after `h`, for tables `t`, `t'` agreeing below
    -- `h.length + 1`.
    | append_singleton h e ih =>
      intro t t' ht
      obtain ⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟨⟩, z⟩⟩ := e
      -- the earlier entries agree
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
  -- Step 4: the chain rule, by the systems-level criterion `eq_memoryless_of_snoc`.
  -- The chain rule of `law`: each admitted trigger multiplies the probability by `law z`.
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
  -- Both sides as masses of tables (`hmass`); the tables giving `h · ((), z)` are those giving
  -- `h` with `t h.length = z` (`hsnoc`).
  rw [hmass, hmass, mass_congr _ (hsnoc h z hlt hd')]
  -- Independent entries: the entry `h.length` is independent of the earlier ones.
  rw [mass_pi_and_eq (fun _ : Fin q => law.1) (fun _ => law.2.2) ⟨h.length, hlt⟩ z (event h)
    fun t a => hread h _ _ fun j hj => Function.update_of_ne (Fin.ne_of_val_ne hj.ne) _ _]
  -- The reply law of the source at its port is `law`.
  rw [portLaw_apply_mk]

/-- **Memoryless systems side by side are memoryless**: a query at a left port has the reply
law of the left system, one at a right port the reply law of the right system. The typed parallel
composition is the systems-level one, `RandomSystem.parallel_memoryless`, with the ports of the
two interfaces relabelled as the ports of their tensor. -/
lemma parallel_eq_memoryless {A B : Interface} {R : TypedSystem A} {T : TypedSystem B}
    {ν₁ : ∀ i, A.X i → ProbDist (A.Y i)} {ν₂ : ∀ j, B.X j → ProbDist (B.Y j)}
    (hR : R.1 = memoryless A.inputDomain (portLaw ν₁))
    (hT : T.1 = memoryless B.inputDomain (portLaw ν₂)) :
    (parallel R T).1 = memoryless (tensor A B).inputDomain (portLaw (parallelLaw ν₁ ν₂)) := by
  -- Plan:
  -- 1. Systems level: `RandomSystem.parallel_memoryless` gives the parallel composition of the
  --    two memoryless systems as the memoryless system of the side-by-side law `twoLaw`.
  -- 2. The typed system `parallel R T` has as random system that systems-level composition,
  --    read through the relabelling `e` of the tensor's ports `inl i`, `inr j` as left and
  --    right ports. The systems-level criterion `eq_memoryless_of_snoc` asks for the chain
  --    rule of `parallelLaw` at each admitted exchange.
  -- 3. An impossible transcript stays impossible. For a possible one, the systems-level domain
  --    admits the relabelled query, and the chain rule `memoryless_snoc` of `hsys` applies.
  -- 4. Port by port, the law `twoLaw` of the relabelled reply is `parallelLaw`.
  --
  --              ┌───┐
  --   inl i ─x─▶ │ R │   reply ∼ ν₁ i x
  --              ├───┤
  --   inr j ─x─▶ │ T │   reply ∼ ν₂ j x
  --              └───┘
  --
  -- Step 1: the systems-level statement.
  -- At the systems level, the two memoryless systems side by side are the memoryless system of
  -- their side-by-side laws.
  have hsys := RandomSystem.parallel_memoryless A.inputDomain B.inputDomain (portLaw ν₁)
    (portLaw ν₂)
  -- Write the two memoryless systems of `hsys` as `R.1` and `T.1` (`hR`, `hT`).
  rw [← hR, ← hT] at hsys
  -- Step 2: reduce to the chain rule on relabelled transcripts.
  -- The chain rule of the laws of the ports of the tensor, at each admitted exchange `(x, y)`.
  refine eq_memoryless_of_snoc fun h x y hd => ?_
  -- The typed system is the systems-level one on the transcript with relabelled ports.
  let eX := sumAlphabet (Sum.rec A.X B.X)
  let e := eX.symm.prodCongr (sumAlphabet (Sum.rec A.Y B.Y)).symm
  change RandomSystem.parallel R.1 T.1 ((h ++ [(x, y)]).map e) =
    RandomSystem.parallel R.1 T.1 (h.map e) * (portLaw (parallelLaw ν₁ ν₂) x).1 y
  rw [List.map_append, List.map_singleton]
  -- Step 3: split on whether the relabelled transcript `h` has probability zero.
  by_cases hz : RandomSystem.parallel R.1 T.1 (h.map e) = 0
  · -- An impossible transcript stays impossible.
    rw [hz, zero_mul]
    exact (RandomSystem.parallel R.1 T.1).mass_eq_zero_of_prefix (List.prefix_append _ _) hz
  -- A possible transcript: the systems-level parallel domain admits the relabelled query, as the
  -- domain of the tensor admits `x`.
  have hadm := (parallel_admits_iff A B R T (h.map e) hz (eX.symm x)).mpr (by
    -- Relabelling the queries of `h` to the systems level and back leaves them unchanged.
    have hround : ((h.map e).map Prod.fst).map eX = h.map Prod.fst := by
      simp only [List.map_map]
      exact List.map_congr_left fun z _ => eX.apply_symm_apply _
    rw [hround, eX.apply_symm_apply]
    exact hd)
  -- The chain rule at the systems level; it remains to compare the two laws of the reply.
  rw [hsys, show e (x, y) = (eX.symm x, (sumAlphabet (Sum.rec A.Y B.Y)).symm y) from rfl,
    memoryless_snoc, if_pos hadm]
  -- Cancel the common factor, the probability of `h`.
  congr 1
  -- Step 4: the two reply laws agree.
  -- The relabelled query goes to the system of its port, and its law there is the law of that
  -- port; a reply at another port has probability zero on both sides.
  -- Four cases: the query at a left or a right port, the reply at a left or a right port.
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

end TypedSystem

namespace TypedConverter

variable {A B : Interface} {S : Type}

/-- **The composition law** for the converter of a program: on a memoryless system with the
reply law `ν`, the converter of a program whose reply law against `ν` is `κ` in every state gives
the memoryless system with the reply law `κ`. -/
lemma ofProgram_smul_memoryless (s : S) (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ}
    (hb : P.Bounded b) (hB : ∀ xs, xs ≠ [] → xs.length ≤ b * A.bound → B.domain xs)
    {R : TypedSystem B} {ν : ∀ j, B.X j → ProbDist (B.Y j)} {κ : ∀ o, A.X o → ProbDist (A.Y o)}
    (hR : R.1 = memoryless B.inputDomain (portLaw ν))
    (hκ : ∀ s' o u, P.memorylessReplyLaw ν s' o u b [] = (κ o u).1) :
    (ofProgram s P hb hB • R).1 = memoryless A.inputDomain (portLaw κ) :=
  -- The typed attachment's random system is the systems-level attachment of the behavior of
  -- the program's DDC (`DDC.ofProgramOn s P A.domain`) to `R.1`. The systems-level
  -- composition law `PDCBehavior.attach_ofDDC_ofProgramOn_memoryless` gives it: both interface
  -- domains exclude `[]` and are closed under nonempty prefixes (`nonempty_prefix`), and `R`
  -- replies at the queried port (`R.2`):
  --
  --   o(u) ──▶ ┌───┐ ── j(x) ──▶ ┌────────┐
  --            │ P │             │ mem(ν) │   y ∼ ν j x, fresh at each query
  --   ◀── v ── └───┘ ◀── y ───── └────────┘
  --
  --   v ∼ κ o u: the law of P's reply when each inside query gets a fresh sample of ν.
  PDCBehavior.attach_ofDDC_ofProgramOn_memoryless B.nonempty_prefix A.nonempty_prefix s P hb _ hκ hR
    R.2

/-- **The composition law** for the converter of a port-preserving program. -/
lemma ofPreservingProgram_smul_memoryless (s : S) (P : Program S A.I B.I A.X A.Y B.X B.Y)
    {b : ℕ} (hb : P.Bounded b) (ι : A.I → Option B.I) (hι : P.PortPreserving ι) (q : A.I → ℕ)
    (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    (hB : ∀ ys, ys ≠ [] → ys.length ≤ b * A.bound →
      (∀ o j, ι o = some j → (SystemAlgebra.restrict j ys).length ≤ q o) → B.domain ys)
    {R : TypedSystem B} {ν : ∀ j, B.X j → ProbDist (B.Y j)} {κ : ∀ o, A.X o → ProbDist (A.Y o)}
    (hR : R.1 = memoryless B.inputDomain (portLaw ν))
    (hκ : ∀ s' o u, P.memorylessReplyLaw ν s' o u b [] = (κ o u).1) :
    (ofPreservingProgram s P hb ι hι q hA hB • R).1 = memoryless A.inputDomain (portLaw κ) :=
  -- As for `ofProgram_smul_memoryless`: this converter is again the converter of the DDC
  -- `DDC.ofProgramOn s P A.domain`, and the same systems-level composition law applies.
  PDCBehavior.attach_ofDDC_ofProgramOn_memoryless B.nonempty_prefix A.nonempty_prefix s P hb _ hκ hR
    R.2

/-- **The composition law** for the converter of a port-preserving program with a memoryless
system `T` beside its inside interface (its own randomness, `rightContext B T`): the program
is run against the side-by-side reply laws of `R` and `T`. -/
lemma ofPreservingProgram_comp_rightContext_smul_memoryless {C : Interface} (s : S)
    (P : Program S A.I (tensor B C).I A.X A.Y (tensor B C).X (tensor B C).Y) {b : ℕ}
    (hb : P.Bounded b) (ι : A.I → Option (tensor B C).I) (hι : P.PortPreserving ι)
    (q : A.I → ℕ) (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    (hB : ∀ ys, ys ≠ [] → ys.length ≤ b * A.bound →
      (∀ o j, ι o = some j → (SystemAlgebra.restrict j ys).length ≤ q o) → (tensor B C).domain ys)
    {R : TypedSystem B} {T : TypedSystem C} {ν : ∀ j, B.X j → ProbDist (B.Y j)}
    {ν' : ∀ k, C.X k → ProbDist (C.Y k)} {κ : ∀ o, A.X o → ProbDist (A.Y o)}
    (hR : R.1 = memoryless B.inputDomain (portLaw ν))
    (hT : T.1 = memoryless C.inputDomain (portLaw ν'))
    (hκ : ∀ s' o u, P.memorylessReplyLaw (parallelLaw ν ν') s' o u b [] = (κ o u).1) :
    (comp (ofPreservingProgram s P hb ι hι q hA hB) (rightContext B T) • R).1 =
      memoryless A.inputDomain (portLaw κ) := by
  -- Attaching `rightContext B T` places `T` beside `R` ...
  -- (`comp_smul`: `comp P K • R = P • (K • R)`; `attach_rightContext`:
  -- `rightContext B T • R = parallel R T`.)
  rw [comp_smul, attach_rightContext]
  -- ... a memoryless system with the side-by-side law, to which the program is attached.
  -- `parallel_eq_memoryless`: `parallel R T` is the memoryless system of `parallelLaw ν ν'`.
  exact ofPreservingProgram_smul_memoryless s P hb ι hι q hA hB
    (TypedSystem.parallel_eq_memoryless hR hT) hκ

end TypedConverter

end SystemAlgebra
