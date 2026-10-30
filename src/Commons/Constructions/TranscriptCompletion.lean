import Commons.Definitions.Ideal
import Probability.FiniteSupport

/-!
# Converters for conditional completion of an experiment

A closed public experiment has one terminal trigger `eval(())` and replies `eval ⇒ h` with
`h ← μ` in a finite public alphabet `H`. Given a conditional record law `K h` on records `Z`,
the converter `complete K` replies `(h, f h)`, where `f : H → Z` is a private table drawn from
the product law `∏_{h'} K h'`, independently of the experiment's call. Since `f h ~ K h` given
`h`, the completed experiment has the joint law `jointLaw μ K (h, z) = μ(h) · K h z`.
`forget` returns the first component.

```text
                complete K                         experiment μ
           ┌─────────────────────────┐            ┌─────────┐
 eval(()) ▶│ h ← experiment.eval(()) │ eval(()) ─▶│ h ← μ   │
           │ f ←$ tableLaw K         │◀─ eval ⇒ h │         │
 ◀ eval ⇒  │ return (h, f h)         │            └─────────┘
  (h, f h) └─────────────────────────┘
```

The DSL wires the source of `f` inside `complete K`. These converters act on closed
one-trigger experiments whose single reply is the whole public outcome, such as a complete
transcript.

## Main definitions

* `tableLaw K`: the private table's law
* `Probability.Distribution.ProbDist.jointLaw μ K`: the completed law from `Probability.Kernel`
* `complete K`, `forget H Z`: the completing and the forgetting converter
* `experimentInterface H`, `experiment μ`: the one-trigger experiment with outcome law `μ`

## Main results

```text
  complete K • experiment μ = experiment (jointLaw μ K)       complete_smul_source
  forget • experiment ν = experiment (fst_* ν)                forget_smul_source
  fst_* (jointLaw μ K) = μ                                    jointLaw_fst
  forget • (complete K • experiment μ) = experiment μ         forget_complete_smul_source
  (decodeH × decodeZ)_* (jointLaw μ' K') = jointLaw μ K       jointLaw_map
```

The joint law and its marginal and decoding laws come from `Probability.Kernel`.
`exists_completion_converters` assembles them for a real kernel `K` and an ideal kernel `L`:
converters `cR`, `cS` and one common forgetting converter `h` are chosen before every public
law `μ`, and `h • (cR • experiment μ) = experiment μ = h • (cS • experiment μ)`. The record
type `Z` need not be finite; the finite union of the kernels' supports is the record alphabet.
For a bounded interface `A`, `TypedSystem.BoundedTranscript A` serves as `H`, and
`TypedSystem.transcriptDistance_le_of_completion` gives the distance bound from the completed
laws.
-/

namespace Commons.TranscriptCompletion

open Commons Probability Probability.Distribution Probability.Distribution.ProbDist
  SystemAlgebra SystemAlgebra.DSL
  SystemAlgebra.Interface RandomSystem
open scoped SystemAlgebra SystemAlgebra.DSL

-- `H`: the finite public outcome alphabet; `Z`: the record type, finite where a converter
-- carries it.
variable {H Z : Type} [Fintype H] [Fintype Z]

open Classical in
/-- The law of the private table `f : H → Z`: independent entries `f h' ← K h'`,
`tableLaw K f = ∏_{h'} K h' (f h')`. -/
noncomputable def tableLaw (K : H → ProbDist Z) : ProbDist (H → Z) :=
  ⟨Distribution.pi fun h => (K h).1, Distribution.pi_isProbDist fun h => (K h).2⟩

-- **The completing converter** `complete K`: on `eval(())` it queries the inner experiment
-- once, `experiment.eval(()) ⇒ h`, draws a table `f ← tableLaw K` independent of that call,
-- and replies `eval ⇒ (h, f h)`. Only the entry at the returned `h` is used.
open Classical in
converter complete(K : H → ProbDist Z) : Evaluation Unit (H × Z)
  inside experiment : Evaluation Unit H
  on eval(_input : Unit) → H × Z
    h ← experiment.eval(())
    f ←$ tableLaw K
    return (h, f h)

-- **The forgetting converter** `forget H Z`: on `eval(())` it queries the completed
-- experiment, `completed.eval(()) ⇒ (h, z)`, and replies `eval ⇒ h`.
converter forget(H Z : Type) [Fintype H] [Fintype Z] : Evaluation Unit H
  inside completed : Evaluation Unit (H × Z)
  on eval(_input : Unit) → H
    hz ← completed.eval(())
    return hz.1

/-- Completing a memoryless source of `μ` gives a memoryless source of the joint law,
`complete K • source(μ) = source(jointLaw μ K)`, for every query budget `q`. -/
lemma complete_smul_source (K : H → ProbDist Z) (μ : ProbDist H)
    (q : Evaluation.Port → ℕ) :
    complete.perPort K (budget := q) • MemorylessSource.perPort H μ =
      MemorylessSource.perPort (H × Z) (jointLaw μ K) := by
  classical
  apply Subtype.ext
  -- Both sides are memoryless; compare the reply laws of one `eval(())`.
  have attached : (complete.perPort K (budget := q) •
      MemorylessSource.perPort H μ (budget := complete.insideBudget K q)).1 =
      memoryless _ (portLaw fun _ _ => jointLaw μ K) := by
    -- `inline` attaches the program to the memoryless inner source and to its internal
    -- source of tables; one invocation has reply law `h ← μ; f ← tableLaw K; (h, f h)`.
    inline using (MemorylessSource.memoryless_eq μ _), (TypedSystem.source_eq_memoryless _ _)
    all_goals
      simp only [parallelLaw, complete.law1]
      change μ.1.bindK (fun h => fTransform (fun f => (h, f h)) (tableLaw K).1) = _
      -- For each `h`, it remains `(f ↦ (h, f h))_* tableLaw K = (z ↦ (h, z))_* K h`.
      apply Distribution.bindK_congr
      intro h _
      rw [show (fun f : H → Z => (h, f h)) = (fun z => (h, z)) ∘ (fun f => f h) from rfl,
        ← Distribution.fTransform_fTransform]
      congr 1
      -- The coordinate `h` of the product law `∏_{h'} K h'` is `K h`; the other factors
      -- have weight one.
      simpa only [Distribution.marginalAt, Distribution.fTransform, tableLaw,
        (K _).2.weight_eq, Finset.prod_const_one, one_smul] using
          Distribution.marginalAt_pi (fun h => (K h).1) h
  rw [attached, MemorylessSource.memoryless_eq]

/-- Forgetting the record of a memoryless source of `μ : ProbDist (H × Z)` gives the source
of its first marginal, `forget • source(μ) = source(fst_* μ)`. -/
lemma forget_smul_source (μ : ProbDist (H × Z)) (q : Evaluation.Port → ℕ) :
    forget.perPort H Z (budget := q) • MemorylessSource.perPort (H × Z) μ =
      MemorylessSource.perPort H (ProbDist.map Prod.fst μ) := by
  apply Subtype.ext
  -- One invocation replies with the first component of a fresh sample of `μ`.
  have attached : (forget.perPort H Z (budget := q) •
      MemorylessSource.perPort (H × Z) μ (budget := forget.insideBudget H Z q)).1 =
      memoryless _ (portLaw fun _ _ => ProbDist.map Prod.fst μ) := by
    inline using (MemorylessSource.memoryless_eq μ _)
    all_goals rfl
  rw [attached, MemorylessSource.memoryless_eq]

/-- The common forgetting converter recovers the experiment exactly,
`forget • (complete K • source(μ)) = source(μ)`. -/
lemma forget_complete_smul_source (K : H → ProbDist Z) (μ : ProbDist H)
    (q : Evaluation.Port → ℕ) :
    forget.perPort H Z (budget := q) •
        (complete.perPort K • MemorylessSource.perPort H μ) =
      MemorylessSource.perPort H μ := by
  -- `source(jointLaw μ K)`, then `source(fst_* (jointLaw μ K)) = source(μ)`.
  rw [complete_smul_source, forget_smul_source, jointLaw_fst]

/-- One completed experiment: the port `eval` with input `()`, reply in `H` and budget one, a
single terminal trigger. -/
abbrev experimentInterface (H : Type) [Fintype H] : Interface :=
  Evaluation.perPort Unit H (fun _ => 1)

/-- The experiment with outcome law `μ`: its only reply is `eval ⇒ h` with `h ← μ`. -/
noncomputable abbrev experiment (μ : ProbDist H) : TypedSystem (experimentInterface H) :=
  MemorylessSource.perPort H μ (budget := fun _ => 1)

omit [Fintype Z] in
/-- Two fixed completion kernels on a finite public alphabet have two completion converters
and one common forgetting converter, chosen before every public law `μ`:
`cR • experiment μ = experiment (jointLaw μ K')`, likewise `cS` with `L'`, and
`h • (cR • experiment μ) = experiment μ = h • (cS • experiment μ)`. Decoding `Z' → Z` returns
`jointLaw μ K` and `jointLaw μ L` (`jointLaw_map`), so the record type `Z` need not be finite. -/
theorem exists_completion_converters
    -- `H` is the finite public outcome alphabet; `K h` and `L h` are the real and ideal
    -- conditional laws of the record `z : Z` given `h`.
    (K L : H → ProbDist Z) :
    -- `Z'` is a finite record alphabet with decoding `decodeZ`, and `K'`, `L'` are the
    -- kernels re-indexed by it.
    ∃ (Z' : Type) (instZ : Fintype Z'),
      letI := instZ
      ∃ (decodeZ : Z' → Z) (K' L' : H → ProbDist Z')
        -- `cR`, `cS` expose the completed experiment `eval ⇒ (h, z')` and call `eval ⇒ h`
        -- inside; the forgetting converter `h` (not a history) does the converse. All three
        -- are chosen before `μ`, hence before any environment.
        (cR cS : experimentInterface (H × Z') ⟶ experimentInterface H)
        (h : experimentInterface H ⟶ experimentInterface (H × Z')),
        ∀ μ : ProbDist H,
        cR • experiment μ = experiment (jointLaw μ K') ∧
        cS • experiment μ = experiment (jointLaw μ L') ∧
        h • (cR • experiment μ) = experiment μ ∧
        h • (cS • experiment μ) = experiment μ ∧
        -- Decoding the completed outcomes gives exactly the requested conditional laws.
        ProbDist.map (Prod.map id decodeZ) (jointLaw μ K') = jointLaw μ K ∧
        ProbDist.map (Prod.map id decodeZ) (jointLaw μ L') = jointLaw μ L := by
  classical
  -- The record alphabet `zs = ⋃_h (supp K h ∪ supp L h)` is finite because `H` is.
  let zs := Finset.univ.biUnion fun h => (K h).1.support ∪ (L h).1.support
  have hK : ∀ h, (K h).1.support ⊆ zs := fun h z hz =>
    Finset.mem_biUnion.mpr ⟨h, Finset.mem_univ h, Finset.mem_union_left _ hz⟩
  have hL : ∀ h, (L h).1.support ⊆ zs := fun h z hz =>
    Finset.mem_biUnion.mpr ⟨h, Finset.mem_univ h, Finset.mem_union_right _ hz⟩
  -- Re-index both kernels by `zs` without changing any mass.
  let K' := fun h => (K h).onFinset zs (hK h)
  let L' := fun h => (L h).onFinset zs (hL h)
  -- `cR = complete K'`, `cS = complete L'`, `h = forget H zs`; none depends on `μ`.
  refine ⟨zs, inferInstance, Subtype.val, K', L', complete.perPort K',
    complete.perPort L', forget.perPort H zs, fun μ => ?_⟩
  refine ⟨complete_smul_source K' μ _, complete_smul_source L' μ _,
    forget_complete_smul_source K' μ _, forget_complete_smul_source L' μ _, ?_, ?_⟩
  -- Decoding by `jointLaw_map` with `decodeH = id`, `decodeZ = val`: the public law is
  -- unchanged, `id_* μ = μ`, and `val_* (K' h) = K h` (`map_onFinset_val`).
  · exact jointLaw_map id _ μ μ K K' (by apply Subtype.ext; exact fTransform_id _) fun h =>
      (K h).map_onFinset_val zs (hK h)
  · exact jointLaw_map id _ μ μ L L' (by apply Subtype.ext; exact fTransform_id _) fun h =>
      (L h).map_onFinset_val zs (hL h)

end Commons.TranscriptCompletion
