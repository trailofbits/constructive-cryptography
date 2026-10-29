import RandomSystems.Converter.CallTranscript
import RandomSystems.Typed.Functional

/-!
# DDCs attached to fixed functions

A certified DDC `a` that answers every outside history `us` in the domain with the completed
calls in which each `u` queries `queries u`, receives the replies of the fixed function `f` and
returns `g u`, turns the functional system of `f` into that of `g`:

```text
            o(u)   ┌───────┐   j(x), x ∈ queries u   ┌──────────────┐
  ────────────────►│       ├────────────────────────►│              │
                   │   a   │                         │ ofFunction f │
  ◄────────────────┤       │◄────────────────────────┤              │
          o ⇒ g u  └───────┘   j ⇒ f x               └──────────────┘
```

## Main results

* `ofDDC_smul_ofPDS_mass`: a DDC attached to a mixture of deterministic systems, through the
  existing deterministic attachment
* `ofDDC_smul_ofFunction`: `ofDDC a ha • ofFunction f = ofFunction g`
-/

namespace SystemAlgebra.TypedConverter

open Probability

/-- **A DDC attached to a mixture of deterministic systems** gives each history the mixture's
probability that the composed deterministic system answers it. -/
lemma ofDDC_smul_ofPDS_mass {A B : Interface}
    {a : InsideOutsideSystem A.I B.I A.X A.Y B.X B.Y} {b : ℕ}
    (ha : IsDDCFrom B.domain A.domain b a)
    (Q : Distribution.ProbDist {s : InterfaceSystem B.I B.X B.Y //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ B.domain h})
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i))) :
    (ofDDC a ha • TypedSystem.ofPDS Q).1 h =
      Q.1.mass fun s => Replies (trim (apply a s.1)) (h.map Prod.fst) (h.map Prod.snd) := by
  -- Present the DDC by its point distribution and apply the library's attachment law.
  rw [smul_val, PDCBehavior.attach_presents B.nonempty_prefix A.nonempty_prefix (ofDDC a ha)
    (TypedSystem.ofPDS Q).1 (TypedSystem.ofPDS Q).2
    ⟨Finsupp.single ⟨a, ha⟩ 1, Distribution.isProbDist_single _⟩ Q (fun _ => rfl) (fun _ => rfl) h,
    behaviorMass_attachPDS, Distribution.prod_single_left, Distribution.mass_fTransform]

/-- **A DDC computing a function**: if on every admitted outside history the DDC answers each
query `u` by querying `f` at `queries u` and replying `g u`, it turns the function `f` into the
function `g`. Each deterministic sample answering the inside history with `f`, an event of
probability one, makes the attachment answer the outside history with `g`
(`replies_apply_of_calls`); so every admitted functional transcript of `g` has probability one. -/
lemma ofDDC_smul_ofFunction {A B : Interface} {a : InsideOutsideSystem A.I B.I A.X A.Y B.X B.Y}
    {b : ℕ} (ha : IsDDCFrom B.domain A.domain b a) (f : ∀ j, B.X j → B.Y j)
    (g : ∀ o, A.X o → A.Y o) (queries : (Σ o, A.X o) → List (Σ j, B.X j))
    (hcalls : ∀ us : List (Σ o, A.X o), A.domain us →
      Replies a ((us.flatMap fun u => callTranscript u ((queries u).map fun x =>
          (x, ⟨x.1, f x.1 x.2⟩)) ⟨u.1, g u.1 u.2⟩).map Prod.fst)
        ((us.flatMap fun u => callTranscript u ((queries u).map fun x =>
          (x, ⟨x.1, f x.1 x.2⟩)) ⟨u.1, g u.1 u.2⟩).map Prod.snd)) :
    ofDDC a ha • TypedSystem.ofFunction f = TypedSystem.ofFunction g := by
  -- It suffices to give probability one to every admitted functional transcript.
  apply TypedSystem.eq_ofFunction
  intro h hd hg
  rcases hd with rfl | hd
  · exact RandomSystem.mass_nil _
  obtain ⟨Q, hQ⟩ := (TypedSystem.ofFunction f).exists_ofPDS
  -- Expand each outside query into its inside exchanges and its prescribed reply.
  let calls : List ((Σ o, A.X o) × List ((Σ j, B.X j) × (Σ j, B.Y j)) × (Σ o, A.Y o)) :=
    h.map fun z => (z.1, (queries z.1).map fun x => (x, ⟨x.1, f x.1 x.2⟩), z.2)
  have hct : (calls.flatMap fun c => callTranscript c.1 c.2.1 c.2.2) =
      (h.map Prod.fst).flatMap fun u => callTranscript u ((queries u).map fun x =>
        (x, ⟨x.1, f x.1 x.2⟩)) ⟨u.1, g u.1 u.2⟩ := by
    simp only [calls, List.flatMap_map]
    exact List.flatMap_congr fun z hz => by rw [hg z hz]
  have hα := hcalls (h.map Prod.fst) hd
  rw [← hct] at hα
  -- The domain certificate admits the inside history, all of whose replies come from `f`.
  have hin : (TypedSystem.ofFunction f).1 (calls.flatMap (·.2.1)) = 1 := by
    refine TypedSystem.ofFunction_mass_eq_one f _ ?_ ?_
    · have hq := ha.queries _ hα
      rw [insideQueries_flatMap_callTranscript] at hq
      rcases hq with hq | hq
      · exact Or.inl (List.map_eq_nil_iff.mp hq)
      · exact Or.inr hq
    · intro w hw
      obtain ⟨c, hc, hw⟩ := List.mem_flatMap.mp hw
      obtain ⟨z, -, rfl⟩ := List.mem_map.mp hc
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hw
      rfl
  have hI : ∀ T, (TypedSystem.ofFunction f).1 T =
      Q.1.mass fun s => Replies s.1 (T.map Prod.fst) (T.map Prod.snd) := fun T => by
    rw [← hQ]
    rfl
  rw [← hQ, ofDDC_smul_ofPDS_mass]
  -- Every presentation sample answering the inside history also answers the outside history.
  refine le_antisymm ((Distribution.mass_le_weight Q.2.1 _).trans (le_of_eq Q.2.2)) ?_
  rw [← hin, hI]
  refine Distribution.mass_mono Q.2.1 fun s hs => ?_
  rw [replies_trim_iff]
  have hc := replies_apply_of_calls calls hα hs
  dsimp only [calls] at hc
  simpa only [List.map_map, Function.comp_def] using hc

end SystemAlgebra.TypedConverter
