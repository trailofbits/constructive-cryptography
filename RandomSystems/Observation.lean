/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.DDE
import RandomSystems.PDS

/-!
# Probabilistic observation

Lanzenberger, Definition 2.15 (printed p. 15): a PDE “is a distribution over
`(Y, X)`-DDE.”  Probabilistic transcript laws are the finite-support
pushforwards of Definition 2.12's deterministic transcript (printed p. 14).
-/

namespace RandomSystems

noncomputable section

open Classical

open Probability (Distribution)

universe u v

variable {X : Type u} {Y : Type v}

/-- Lanzenberger, Definition 2.15 (printed p. 15): a PDE “is a distribution
over `(Y, X)`-DDE.” -/
abbrev PDE (Y : Type v) (X : Type u) : Type (max u v) :=
  Distribution (System.DDE Y X)

namespace PDS

/-- Definition 2.12's requirement that “the environment must not query `s`
outside of the system's domain” (printed p. 14), imposed on every DDS in a PDS
support. -/
def Compatible (e : System.DDE Y X) (S : PDS X Y) : Prop :=
  ∀ s ∈ S.support, System.Compatible e s

/-- Definition 2.12 says “the transcript ends” when the environment stops
(printed p. 14); this predicate imposes that condition on every DDS in a PDS
support. -/
def Stops (e : System.DDE Y X) (S : PDS X Y) : Prop :=
  ∀ s ∈ S.support, System.Stops e s

/-- The probabilistic transcript law obtained by pushing the PDS law through
Definition 2.12's “sequence of pairs” (printed p. 14).  Lean uses `none` for an
unstopped partial transcript. -/
def trLaw (e : System.DDE Y X) (S : PDS X Y) :
    Distribution (Option (System.Transcript X Y)) :=
  Distribution.fTransform (fun s => (System.tr e s).toOption) S

/-- Lanzenberger's `tr(S, e)` notation for the transcript distribution
(Definition 2.17, printed p. 16). -/
scoped notation "tr(" S ", " e ")" => trLaw e S

/-- A domain-compatible environment is compatible with every system in a PDS
presenting that domain. -/
theorem compatible_of_compatibleD {e : System.DDE Y X} {D : Set (List X)}
    {S : PDS X Y} (he : System.CompatibleD e D) (hS : HasDomain S D) :
    Compatible e S :=
  fun s hs => he s (hS s hs)

/-- A halting environment stops on every deterministic system in a PDS. -/
theorem stops_of_halts {e : System.DDE Y X} (he : System.DDE.Halts e)
    (S : PDS X Y) : Stops e S :=
  fun s _ => System.stops_of_halts he s

end PDS

end

end RandomSystems
