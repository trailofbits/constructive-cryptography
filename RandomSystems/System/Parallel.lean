/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.Phi
import RandomSystems.System.Relabel

/-!
# Parallel composition of resources — the interface union

Jost §2.2.2 / LiuZhang §3.3.2: resources with disjoint interface sets
compose in parallel, and the interface set of `[R, S]` is the disjoint
union.  This is **derived, not primitive**: the tagged two-component
parallel (`System.parallel`, Lanzenberger Def 2.13 = CR18 Def 3.4) followed
by a relabelling of addresses — the first consumer of the `relabel`
generator.  No new interaction semantics is introduced; the alphabet
`(P ⊕ Q) × A` is a re-encoding of `Σ (i : Fin 2), ![P × A, Q × A] i`.

The engine of `connect` (the trace generator) consumes exactly this shape:
an engine joins a resource by `Resource.parLaw`, then the loop is closed.
-/

namespace RandomSystems

namespace System

namespace Resource

noncomputable section

open Classical

open Probability (Distribution)

universe u v w

variable {P Q : Type u} {A : Type v} {B : Type w}

/-- Address translation: a query at the disjoint-union interface set is the
same query at the corresponding slot of the two-component tagged alphabet. -/
def parAddr (p : (P ⊕ Q) × A) : Sigma (PDS.parAlphabet (P × A) (Q × A)) :=
  match p with
  | (Sum.inl p₁, a) => ⟨0, (p₁, a)⟩
  | (Sum.inr p₂, a) => ⟨1, (p₂, a)⟩

/-- Answer translation: both slots answer in `B`, so the tagged answer
projects to its value. -/
def parAns (s : Sigma (PDS.parAlphabet B B)) : B :=
  Fin.cases (motive := fun i => PDS.parAlphabet B B i → B)
    id (fun i => Fin.cases (motive := fun j : Fin 1 =>
      PDS.parAlphabet B B j.succ → B) id (fun k => k.elim0) i) s.1 s.2

/-- Jost's parallel composition of deterministic resources: disjoint
interface sets, union — the tagged two-component parallel, re-addressed. -/
def par (S : Resource P A B) (T : Resource Q A B) :
    Resource (P ⊕ Q) A B :=
  relabel parAddr parAns
    (parallel (Xs := PDS.parAlphabet (P × A) (Q × A))
      (Ys := PDS.parAlphabet B B)
      (Fin.cases S (Fin.cases T (fun i => i.elim0))))

/-- The domain of the parallel resource, by construction: the re-addressed
history is accepted by the tagged parallel. -/
theorem mem_dom_par_iff (S : Resource P A B) (T : Resource Q A B)
    (l : List ((P ⊕ Q) × A)) :
    l ∈ dom (par S T) ↔
      l.map parAddr ∈ parallelDom
        (Xs := PDS.parAlphabet (P × A) (Q × A))
        (Ys := PDS.parAlphabet B B)
        (Fin.cases S (Fin.cases T (fun i => i.elim0))) :=
  Iff.rfl

/-- The law of Jost's `[R, S]`: the independent product of the component
laws, pushed forward along the deterministic parallel composition — the
same shape as `PDS.parLaw`, at the re-addressed alphabet. -/
def parLaw (S : PDS (P × A) B) (T : PDS (Q × A) B) :
    PDS ((P ⊕ Q) × A) B :=
  Distribution.fTransform
    (fun p : DDS (P × A) B × DDS (Q × A) B => par p.1 p.2)
    (Distribution.prod S T)

end

end Resource

end System

end RandomSystems
