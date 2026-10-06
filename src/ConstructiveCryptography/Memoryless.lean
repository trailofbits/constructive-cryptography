import ConstructiveCryptography.DSL.Converters
import ConstructiveCryptography.Context
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
                   (P ≫ rightContext B T) • R  =  mem(κ),   κ = P's reply law against ν, ν'
```

Statements about typed systems are equalities of their random systems (`.1`).

## Main results

* `Interface.source_eq_memoryless`: a source of independent samples of `law` is memoryless
* `Interface.parallel_eq_memoryless`: memoryless systems side by side are memoryless
* `Interface.Converter.ofProgram_smul_memoryless`,
  `Interface.Converter.ofPreservingProgram_smul_memoryless`,
  `Interface.Converter.ofPreservingProgram_comp_rightContext_smul_memoryless`: the composition law
  `P • mem(ν) = mem(κ)` for the converters of programs

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

namespace SystemAlgebra.Interface

open Probability Probability.Distribution Classical CategoryTheory RandomSystem

/-- **A source of independent samples is memoryless** [1, Definition 3.1]: the source of `q`
samples of `law` replies to each trigger with a fresh sample of `law`. -/
theorem source_eq_memoryless {Z : Type} [Fintype Z] (law : ProbDist Z) (q : ℕ) :
    (Resource.source law q).1 =
      memoryless (Interface.source Z q).inputDomain (portLaw fun _ _ => law) := by
  -- The source reads its `k`-th reply from the `k`-th entry of a table `t` of independent
  -- samples. A transcript `h` has the probability of the tables from which it is read.
  let event : List ((Σ _ : Unit, Unit) × (Σ _ : Unit, Z)) → (Fin q → Z) → Prop := fun h t =>
    Replies (filterDom (Interface.source Z q).domain (automatonSystem (sourceStep law) (t, 0)))
      (h.map Prod.fst) (h.map Prod.snd)
  have hmass : ∀ h, (Resource.source law q).1 h = (pi fun _ : Fin q => law.1).mass (event h) := by
    intro h
    rw [Resource.source, Resource.ofAutomaton_mass, mass_fTransform]
  -- One more exchange: the table also gives `h · ((), z)` when the domain admits one more query
  -- and its entry `h.length` is `z`.
  have hsnoc : ∀ h z (hlt : h.length < q), ((Interface.source Z q).domain
      (h.map Prod.fst ++ [⟨(), ()⟩])) → ∀ t, event (h ++ [(⟨(), ()⟩, ⟨(), z⟩)]) t ↔
        event h t ∧ t ⟨h.length, hlt⟩ = z := by
    intro h z hlt hd t
    simp only [event, List.map_append, List.map_cons, List.map_nil, replies_snoc,
      SystemAlgebra.filterDom, automatonSystem_snoc, stateAfter_sourceStep, if_pos hd]
    simp [sourceStep, hlt, Part.some_inj, eq_comm]
  -- The event of `h` reads only the entries before `h.length`.
  have hread : ∀ h t t', (∀ j : Fin q, j.val < h.length → t j = t' j) →
      (event h t ↔ event h t') := by
    intro h
    induction h using List.reverseRecOn with
    | nil => intro t t' _; simp [event]
    | append_singleton h e ih =>
      intro t t' ht
      obtain ⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟨⟩, z⟩⟩ := e
      -- the earlier entries agree, and so does the entry read now
      have hpre := ih t t' fun j hj => ht j (by simp; omega)
      simp only [event, List.map_append, List.map_cons, List.map_nil, replies_snoc,
        SystemAlgebra.filterDom, automatonSystem_snoc, stateAfter_sourceStep] at hpre ⊢
      rw [hpre]
      by_cases hlt : h.length < q
      · simp [sourceStep, hlt, ht ⟨h.length, hlt⟩ (by simp)]
      · simp [hlt]
  -- The chain rule of `law`: each admitted trigger multiplies the probability by `law z`.
  refine eq_memoryless_of_snoc fun h x y hd => ?_
  obtain ⟨⟨⟩, ⟨⟩⟩ := x
  obtain ⟨⟨⟩, z⟩ := y
  have hd' : (Interface.source Z q).domain (h.map Prod.fst ++ [⟨(), ()⟩]) := hd
  have hlt : h.length < q := by
    have := hd'.2
    simp only [List.length_append, List.length_map, List.length_singleton] at this
    omega
  rw [hmass, hmass, mass_congr _ (hsnoc h z hlt hd')]
  -- Independent entries: the entry `h.length` is independent of the earlier ones.
  rw [mass_pi_and_eq (fun _ : Fin q => law.1) (fun _ => law.2.2) ⟨h.length, hlt⟩ z (event h)
    fun t a => hread h _ _ fun j hj => Function.update_of_ne (Fin.ne_of_val_ne hj.ne) _ _]
  -- The reply law of the source at its port is `law`.
  rw [portLaw_apply_mk]

/-- **Memoryless systems side by side are memoryless**: a query at a left port has the reply
law of the left system, one at a right port the reply law of the right system. -/
lemma parallel_eq_memoryless {A B : Interface} {R : Resource A} {T : Resource B}
    {ν₁ : ∀ i, A.X i → ProbDist (A.Y i)} {ν₂ : ∀ j, B.X j → ProbDist (B.Y j)}
    (hR : R.1 = memoryless A.inputDomain (portLaw ν₁))
    (hT : T.1 = memoryless B.inputDomain (portLaw ν₂)) :
    (parallel R T).1 = memoryless (tensor A B).inputDomain (portLaw (parallelLaw ν₁ ν₂)) := by
  -- The chain rule of the side-by-side law, at each admitted exchange `(x, y)`.
  refine eq_memoryless_of_snoc fun h x y hd => ?_
  -- The parallel system is the product of its two components on the projected transcripts.
  let e := (sumAlphabet (Sum.rec A.X B.X)).symm.prodCongr (sumAlphabet (Sum.rec A.Y B.Y)).symm
  change RandomSystem.parallel R.1 T.1 ((h ++ [(x, y)]).map e) =
    RandomSystem.parallel R.1 T.1 (h.map e) * (portLaw (parallelLaw ν₁ ν₂) x).1 y
  rw [List.map_append, List.map_singleton]
  by_cases hz : RandomSystem.parallel R.1 T.1 (h.map e) = 0
  · -- an impossible transcript stays impossible
    rw [hz, zero_mul]
    exact (RandomSystem.parallel R.1 T.1).mass_eq_zero_of_prefix (List.prefix_append _ _) hz
  -- A possible transcript: the components' own domains admit the query (the parallel domain
  -- of the two random systems agrees with the domain of the parallel interface there).
  have hadm := (parallel_admits_iff A B R T (h.map e) hz
    ((sumAlphabet (Sum.rec A.X B.X)).symm x)).mpr (by
      have hround : ((h.map e).map Prod.fst).map (sumAlphabet (Sum.rec A.X B.X)) =
          h.map Prod.fst := by
        simp only [List.map_map]
        exact List.map_congr_left fun z _ => (sumAlphabet (Sum.rec A.X B.X)).apply_symm_apply _
      rw [hround, (sumAlphabet (Sum.rec A.X B.X)).apply_symm_apply]
      exact hd)
  have hcons : RandomSystem.parallelConsistent (h.map e) := hadm.1
  -- So the transcript so far is a left and a right transcript, side by side.
  have hsplit : RandomSystem.parallel R.1 T.1 (h.map e) =
      R.1 (RandomSystem.parallelLeft (h.map e)) * T.1 (RandomSystem.parallelRight (h.map e)) := by
    rw [RandomSystem.parallel_mass, if_pos hcons]
  rw [hsplit, RandomSystem.parallel_mass]
  -- Case on the ports of the query and of the reply.
  obtain ⟨(i | j), x⟩ := x <;> obtain ⟨(k | l), y⟩ := y
  · -- A left query with a left reply: the left component steps, with the law `ν₁`.
    have hA : A.inputDomain (RandomSystem.parallelLeft (h.map e)) ⟨i, x⟩ := hadm.2.2
    -- the exchange is the left exchange `(⟨i, x⟩, ⟨k, y⟩)`
    have hz : e (⟨.inl i, x⟩, ⟨.inl k, y⟩) = (⟨none, ⟨i, x⟩⟩, ⟨none, ⟨k, y⟩⟩) := rfl
    have hleft : RandomSystem.parallelLeft (h.map e ++ [(⟨none, ⟨i, x⟩⟩, ⟨none, ⟨k, y⟩⟩)]) =
        RandomSystem.parallelLeft (h.map e) ++ [(⟨i, x⟩, ⟨k, y⟩)] := by
      simp [RandomSystem.parallelLeft]
    have hright : RandomSystem.parallelRight (h.map e ++ [(⟨none, ⟨i, x⟩⟩, ⟨none, ⟨k, y⟩⟩)]) =
        RandomSystem.parallelRight (h.map e) := by
      simp [RandomSystem.parallelRight]
    rw [hz, if_pos (RandomSystem.parallelConsistent_snoc.mpr ⟨hcons, rfl⟩), hleft, hright]
    -- the left component is memoryless: its chain rule at an admitted query
    have hstep : R.1 (RandomSystem.parallelLeft (h.map e) ++ [(⟨i, x⟩, ⟨k, y⟩)]) =
        R.1 (RandomSystem.parallelLeft (h.map e)) * (portLaw ν₁ ⟨i, x⟩).1 ⟨k, y⟩ := by
      rw [hR, memoryless_snoc, if_pos hA]
    rw [hstep]
    -- the side-by-side law at a left query is the left law
    by_cases hk : k = i
    · subst hk
      rw [portLaw_apply_mk, portLaw_apply_mk]
      simp only [parallelLaw]
      ring
    · rw [portLaw_apply_of_ne _ (by simpa using hk), portLaw_apply_of_ne _ (by simpa using hk)]
      ring
  · -- A left query with a right reply: impossible on both sides.
    have hz : e (⟨.inl i, x⟩, ⟨.inr l, y⟩) = (⟨none, ⟨i, x⟩⟩, ⟨some (), ⟨l, y⟩⟩) := rfl
    rw [hz, if_neg fun h => absurd (RandomSystem.parallelConsistent_snoc.mp h).2 (by simp),
      portLaw_apply_of_ne _ (by simp), mul_zero]
  · -- A right query with a left reply: impossible on both sides.
    have hz : e (⟨.inr j, x⟩, ⟨.inl k, y⟩) = (⟨some (), ⟨j, x⟩⟩, ⟨none, ⟨k, y⟩⟩) := rfl
    rw [hz, if_neg fun h => absurd (RandomSystem.parallelConsistent_snoc.mp h).2 (by simp),
      portLaw_apply_of_ne _ (by simp), mul_zero]
  · -- A right query with a right reply: the right component steps, with the law `ν₂`.
    have hB : B.inputDomain (RandomSystem.parallelRight (h.map e)) ⟨j, x⟩ := hadm.2.2
    have hz : e (⟨.inr j, x⟩, ⟨.inr l, y⟩) = (⟨some (), ⟨j, x⟩⟩, ⟨some (), ⟨l, y⟩⟩) := rfl
    have hleft : RandomSystem.parallelLeft (h.map e ++ [(⟨some (), ⟨j, x⟩⟩, ⟨some (), ⟨l, y⟩⟩)]) =
        RandomSystem.parallelLeft (h.map e) := by
      simp [RandomSystem.parallelLeft]
    have hright :
        RandomSystem.parallelRight (h.map e ++ [(⟨some (), ⟨j, x⟩⟩, ⟨some (), ⟨l, y⟩⟩)]) =
          RandomSystem.parallelRight (h.map e) ++ [(⟨j, x⟩, ⟨l, y⟩)] := by
      simp [RandomSystem.parallelRight]
    rw [hz, if_pos (RandomSystem.parallelConsistent_snoc.mpr ⟨hcons, rfl⟩), hleft, hright]
    -- the right component is memoryless: its chain rule at an admitted query
    have hstep : T.1 (RandomSystem.parallelRight (h.map e) ++ [(⟨j, x⟩, ⟨l, y⟩)]) =
        T.1 (RandomSystem.parallelRight (h.map e)) * (portLaw ν₂ ⟨j, x⟩).1 ⟨l, y⟩ := by
      rw [hT, memoryless_snoc, if_pos hB]
    rw [hstep]
    -- the side-by-side law at a right query is the right law
    by_cases hl : l = j
    · subst hl
      rw [portLaw_apply_mk, portLaw_apply_mk]
      simp only [parallelLaw]
      ring
    · rw [portLaw_apply_of_ne _ (by simpa using hl), portLaw_apply_of_ne _ (by simpa using hl)]
      ring

namespace Converter

variable {A B : Interface} {S : Type}

/-- **The composition law** for the converter of a program: on a memoryless system with the
reply law `ν`, the converter of a program whose reply law against `ν` is `κ` in every state gives
the memoryless system with the reply law `κ`. -/
lemma ofProgram_smul_memoryless (s : S) (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ}
    (hb : P.Bounded b) (hB : ∀ xs, xs ≠ [] → xs.length ≤ b * A.bound → B.domain xs)
    {R : Resource B} {ν : ∀ j, B.X j → ProbDist (B.Y j)} {κ : ∀ o, A.X o → ProbDist (A.Y o)}
    (hR : R.1 = memoryless B.inputDomain (portLaw ν))
    (hκ : ∀ s o u, P.replyLaw ν s o u b [] = (κ o u).1) :
    (ofProgram s P hb hB • R).1 = memoryless A.inputDomain (portLaw κ) :=
  PDCBehavior.attach_ofDDC_ofProgramOn_memoryless B.nonempty_prefix A.nonempty_prefix s P hb _ hκ hR
    R.2

/-- **The composition law** for the converter of a port-preserving program. -/
lemma ofPreservingProgram_smul_memoryless (s : S) (P : Program S A.I B.I A.X A.Y B.X B.Y)
    {b : ℕ} (hb : P.Bounded b) (ι : A.I → Option B.I) (hι : P.PortPreserving ι) (q : A.I → ℕ)
    (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    (hB : ∀ ys, ys ≠ [] → ys.length ≤ b * A.bound →
      (∀ o j, ι o = some j → (SystemAlgebra.restrict j ys).length ≤ q o) → B.domain ys)
    {R : Resource B} {ν : ∀ j, B.X j → ProbDist (B.Y j)} {κ : ∀ o, A.X o → ProbDist (A.Y o)}
    (hR : R.1 = memoryless B.inputDomain (portLaw ν))
    (hκ : ∀ s o u, P.replyLaw ν s o u b [] = (κ o u).1) :
    (ofPreservingProgram s P hb ι hι q hA hB • R).1 = memoryless A.inputDomain (portLaw κ) :=
  PDCBehavior.attach_ofDDC_ofProgramOn_memoryless B.nonempty_prefix A.nonempty_prefix s P hb _ hκ hR
    R.2

/-- **The composition law** for the converter of a port-preserving program with a memoryless
system `T` beside its inside interface (its own randomness, `≫ rightContext B T`): the program
is run against the side-by-side reply laws of `R` and `T`. -/
lemma ofPreservingProgram_comp_rightContext_smul_memoryless {C : Interface} (s : S)
    (P : Program S A.I (tensor B C).I A.X A.Y (tensor B C).X (tensor B C).Y) {b : ℕ}
    (hb : P.Bounded b) (ι : A.I → Option (tensor B C).I) (hι : P.PortPreserving ι)
    (q : A.I → ℕ) (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    (hB : ∀ ys, ys ≠ [] → ys.length ≤ b * A.bound →
      (∀ o j, ι o = some j → (SystemAlgebra.restrict j ys).length ≤ q o) → (tensor B C).domain ys)
    {R : Resource B} {T : Resource C} {ν : ∀ j, B.X j → ProbDist (B.Y j)}
    {ν' : ∀ k, C.X k → ProbDist (C.Y k)} {κ : ∀ o, A.X o → ProbDist (A.Y o)}
    (hR : R.1 = memoryless B.inputDomain (portLaw ν))
    (hT : T.1 = memoryless C.inputDomain (portLaw ν'))
    (hκ : ∀ s o u, P.replyLaw (parallelLaw ν ν') s o u b [] = (κ o u).1) :
    ((ofPreservingProgram s P hb ι hι q hA hB ≫ rightContext B T) • R).1 =
      memoryless A.inputDomain (portLaw κ) := by
  -- Attaching `rightContext B T` places `T` beside `R` ...
  rw [Interface.comp_smul, attach_rightContext]
  -- ... a memoryless system with the side-by-side law, to which the program is attached.
  exact ofPreservingProgram_smul_memoryless s P hb ι hι q hA hB (parallel_eq_memoryless hR hT) hκ

end Converter

end SystemAlgebra.Interface
