import RandomSystems.Typed.ParallelAll
import RandomSystems.Cumulative.ParallelAllPresentation

/-!
# Deterministic presentations of typed finite parallel systems

Each `P k` is a probability law on DDSs on `A k` that reply at the queried port and have
domain exactly `(A k).domain`. A tuple `st ∼ piDep P` of independent samples, drawn once,
gives the DDS on `tensorAll A`

  `r st = relabel (trim (parAll st)) regroup regroup⁻¹`,  `regroup ⟨⟨k, i⟩, x⟩ = ⟨k, ⟨i, x⟩⟩`,

and the law of `r st` presents `TypedSystem.parallelAll (fun k => ofPDS (P k))`.

```text
                 regroup                ┌─ trim (parAll st) ─┐
  ── ⟨k, i⟩(x) ──────────▶ k(⟨i, x⟩) ──▶│  st k₁ on h|k₁     │
  ◀─ ⟨k, i⟩ ⇒ y ◀───────── k ⇒ ⟨i, y⟩ ◀─│   ⋮                │
                 regroup⁻¹              │  st k₂ on h|k₂     │
                                        └────────────────────┘
```

`trim` keeps only the reachable histories, so `r st` is a DDS with the exact combined
domain. The presentation equality is behavioral: the trimmed system has the transcripts of
`parAll st` (`replies_trim_iff`), not its raw off-tree values.

## Main definitions

* `TypedSystem.parallelAllPDS P`: the law of `r st` for `st ∼ piDep P`

## Main results

* `TypedSystem.parallelAll_system_valid`: `r st` is a DDS replying at the queried port with
  domain `(tensorAll A).domain`
* `TypedSystem.parallelAll_ofPDS`: `parallelAll (fun k => ofPDS (P k)) = ofPDS (parallelAllPDS P)`

Jost, Thesis, printed p. 17: “A finite set of resources with disjoint interface sets can be
viewed as a single one”. The independent sampling of the components is this repository's
chosen specialization of that view.
-/

namespace SystemAlgebra.TypedSystem

open Probability Interface

variable {K : Type} [Fintype K] {A : K → Interface}

/-- **The combined system is a certified DDS.** For DDSs `s k` on `A k` replying at the queried
port with domain exactly `(A k).domain`, `r = relabel (trim (parAll s)) regroup regroup⁻¹`

* is a DDS: silent at `[]`, with prefix-closed domain;
* replies at the queried port: `⟨k, i⟩(x)` is answered `⟨k, i⟩ ⇒ y`, the tag `k` by
  `parAll` and the local port `i` by `s k`;
* has domain `(tensorAll A).domain h ↔ h ≠ [] ∧ ∀ k, h|k = [] ∨ (A k).domain (h|k)`,
  with `h|k = restrict k (h.map regroup)`. -/
lemma parallelAll_system_valid
    (s : ∀ k, {t : InterfaceSystem (A k).I (A k).X (A k).Y //
      IsDDS t ∧ RepliesAtQueriedInterface t ∧ ∀ h, (t h).Dom ↔ (A k).domain h}) :
    let r := relabel (trim (parAll (fun k => (s k).1)))
      (Equiv.sigmaAssoc fun k i => (A k).X i)
      (Equiv.sigmaAssoc fun k i => (A k).Y i).symm
    IsDDS r ∧ RepliesAtQueriedInterface r ∧
      ∀ h, (r h).Dom ↔ (tensorAll A).domain h := by
  let xAssoc := Equiv.sigmaAssoc fun k i => (A k).X i
  let yAssoc := (Equiv.sigmaAssoc fun k i => (A k).Y i).symm
  let S := parAll fun k => (s k).1
  change IsDDS (relabel (trim S) xAssoc yAssoc) ∧
    RepliesAtQueriedInterface (relabel (trim S) xAssoc yAssoc) ∧ _
  refine ⟨?_, ?_, ?_⟩
  · -- DDS: `relabel (trim S) = trim (relabel S)`, and `relabel S` is silent at `[]`, as
    -- `parAll` is; trimming a silent system leaves a prefix-closed domain.
    rw [← trim_relabel]
    exact SilentAtEmpty.isDDS_trim (by simp only [SilentAtEmpty, relabel, List.map_nil, parAll_nil,
      Part.map_none, Part.not_none_dom, not_false_eq_true, S])
  · -- The regrouped `parAll` keeps tag and local port (`RepliesAtQueriedInterface.parallelAll`);
    -- trimming preserves that reply law.
    rw [← trim_relabel]
    exact (RepliesAtQueriedInterface.parallelAll (fun k => (s k).2.2.1)).trim
  · -- Domain: for component DDSs, `trim_parAll_dom` gives
    --   (trim S h').Dom ↔ h' ≠ [] ∧ ∀ k, h'|k = [] ∨ (s k (h'|k)).Dom,
    -- regrouping keeps `h ≠ []`, and the exact component domains turn `Dom` into `(A k).domain`.
    intro h
    change (trim S (h.map xAssoc)).Dom ↔ (tensorAll A).domain h
    rw [trim_parAll_dom (fun k => (s k).2.1)]
    change (h.map xAssoc ≠ [] ∧
        ∀ k, restrict k (h.map xAssoc) = [] ∨
          ((s k).1 (restrict k (h.map xAssoc))).Dom) ↔
      h ≠ [] ∧ ∀ k, restrict k (h.map xAssoc) = [] ∨
        (A k).domain (restrict k (h.map xAssoc))
    have hnonempty : h.map xAssoc ≠ [] ↔ h ≠ [] :=
      not_congr List.map_eq_nil_iff
    rw [hnonempty]
    exact and_congr_right fun _ => forall_congr' fun k =>
      or_congr Iff.rfl ((s k).2.2.2 _)

open Classical in
/-- **The independent parallel PDS** on `tensorAll A`: sample `st ∼ piDep P`, one DDS per
component, once; then answer by `r st = relabel (trim (parAll st)) regroup regroup⁻¹`, which
retains each `st k` and feeds it its own history `h|k`. As a law,
`parallelAllPDS P = fTransform r (piDep P)`, a probability law by `piDep_isProbDist`. -/
noncomputable def parallelAllPDS [DecidableEq K]
    (P : ∀ k, Distribution.ProbDist {s : InterfaceSystem (A k).I (A k).X (A k).Y //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ (A k).domain h}) :
    Distribution.ProbDist {r : InterfaceSystem (tensorAll A).I (tensorAll A).X
        (tensorAll A).Y //
      IsDDS r ∧ RepliesAtQueriedInterface r ∧
        ∀ h, (r h).Dom ↔ (tensorAll A).domain h} :=
  ⟨Distribution.fTransform (fun s =>
      ⟨relabel (trim (parAll (fun k => (s k).1)))
        (Equiv.sigmaAssoc fun k i => (A k).X i)
        (Equiv.sigmaAssoc fun k i => (A k).Y i).symm,
       parallelAll_system_valid s⟩)
      (Distribution.piDep (fun k => (P k).1)),
    Distribution.fTransform_isProbDist _
      (Distribution.piDep_isProbDist (fun k => (P k).2))⟩

open Classical in
/-- **The independent parallel PDS presents the parallel typed system**:
`parallelAll (fun k => ofPDS (P k)) = ofPDS (parallelAllPDS P)`. This is equality of typed
systems, i.e. of all cumulative masses, not of the raw systems `r st`: on each transcript
`h`, with `h'` its regrouping,

  (parallelAll (ofPDS ∘ P)) h
    = (piDep P).mass {st | parAll st answers h'}             (`parallelAll_mass_of_presentations`)
    = (piDep P).mass {st | r st answers h}           (`replies_relabel_iff`, `replies_trim_iff`)
    = ofPDS (parallelAllPDS P) h.                                      (`mass_fTransform`) -/
lemma parallelAll_ofPDS [DecidableEq K]
    (P : ∀ k, Distribution.ProbDist {s : InterfaceSystem (A k).I (A k).X (A k).Y //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ (A k).domain h}) :
    parallelAll (fun k => ofPDS (P k)) = ofPDS (parallelAllPDS P) := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  -- Each `ofPDS (P k)` is presented by `P k` with the sample's own system, by definition.
  rw [parallelAll_mass, RandomSystem.parallelAll_mass_of_presentations
    (fun k => (ofPDS (P k)).1) (fun k => (P k).1)
    (fun k i => (i : {s : InterfaceSystem (A k).I (A k).X (A k).Y //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧
        ∀ h, (s h).Dom ↔ (A k).domain h}).1) (fun _ _ => rfl)]
  -- The right side is the `piDep P`-mass of `{st | r st answers h}`, pulled back along `r`.
  change _ = behaviorMass _ _ _
  simp only [behaviorMass, parallelAllPDS, Distribution.mass_fTransform]
  symm
  apply Distribution.mass_congr
  intro s
  -- Per tuple: `r s` answers `h` iff `parAll s` answers the regrouped `h'`; `trim` removes no
  -- transcript.
  rw [replies_relabel_iff, replies_trim_iff]
  simp only [Equiv.symm_symm]

end SystemAlgebra.TypedSystem
