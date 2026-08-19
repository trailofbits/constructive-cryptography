/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.Cascade
import Probability.Distribution
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.Action.End
import Mathlib.Topology.MetricSpace.Basic

/-!
# Probabilistic discrete systems, and the specification layer on them

Lanzenberger, *A Theory of Random Systems, Games, and Hardness Amplification*
(Diss. ETH 29554), **Definition 2.14**: "A probabilistic discrete
`(𝒳, 𝒴)`-system (or `(𝒳, 𝒴)`-PDS) is a distribution over `(𝒳, 𝒴)`-DDS such that
all DDS in the support of `S` have the same domain."  Note the preamble to
§2.3.2: "even though we use the term *probabilistic*, we do not assume that the
corresponding distributions are probability distributions."

The carrier is therefore the plain distribution over deterministic systems, and
Definition 2.14's common-domain clause and the probability condition are
**mixins**, imposed where they are needed rather than built into the type.  That
follows the source, which keeps the clause as a separate predicate, and it keeps
the arbitrary-weight generality the successor-system arguments rely on.

## What is instantiated here

The target is Jost's specification layer (*Towards Practical and Sound
Cryptography from Composable Security*, §2.2), whose objects `Θ` are a
parameter: "we model specifications as sets of objects `𝓡 ⊆ Θ`, where `Θ`
denotes some basic set of objects under consideration."  A PDS is such a `Θ`.

| Jost | here |
|---|---|
| §2.2.2, protocols with `π' ∘ π` and `id` | `Protocol`, `act`, `instMulAction` |
| Definition 2.2.8, a distinguisher outputting one bit | `Distinguisher`, `outputOne` |
| Definition 2.2.4, `π𝓡 ⊆ 𝒮` | `AbstractCryptography.Constructs` |
| Definitions 2.2.6, 2.2.9, 2.2.12 | supplied by the class instance |

`Resource.distinguishers` *is* Definition 2.2.8, and everything from the
construction relation to Corollary 2.2.13 follows from it and the action.  It
now lives one module out, in `RandomSystems.System.DistinguisherClass`, because
`AbstractCryptography.Metric.Distinguisher` documents itself against MauRen11
Definitions 15–16 and is behind the provenance fence (`LEDGER.md` PROVENANCE
FENCE).  Nothing else in this file, or in the `RandomSystems` tree, needed it.

## Not to be confused with the random-systems distance

Lanzenberger **Definition 2.26** measures with transcripts,
`Adv(S,T) := sup_e δ(tr(S,e), tr(T,e))` over deterministic environments, and
remarks that in the information-theoretic setting this agrees with "the
supremum difference of the probability that a (probabilistic) distinguisher
outputs 1".  That is the random-systems-layer distance, in the form the counting
bounds are proved in.  The specification layer asks for the output-bit form, so
that is what is instantiated; relating the two is a theorem about `edistD`, not
a second definition, and it is not on the path to a construction statement.
-/

namespace RandomSystems

open Probability (Distribution)

open scoped ENNReal

universe u v

/-! ## The carrier -/

/-- Lanzenberger **Definition 2.14**: a probabilistic discrete `(X, Y)`-system
is a distribution over deterministic discrete `(X, Y)`-systems.  Definition
2.14's common-domain clause is `HasFixedDomain`. -/
abbrev PDS (X : Type u) (Y : Type v) : Type (max u v) :=
  Distribution (System.DDS X Y)

namespace PDS

variable {U : Type u} {V : Type v} {X : Type u} {Y : Type v}

/-- Lanzenberger Definition 2.14's clause: "all DDS in the support of `S` have
the same domain".  A mixin, not a field: the source keeps it as a separate
predicate and imposes it where the arguments need it, and converter application
is not obviously domain-uniform — a converter may branch on the answers it
receives, not only on where the system is undefined. -/
class HasFixedDomain (S : PDS X Y) : Prop where
  exists_common : ∃ D : Set (List X), ∀ s ∈ S.support, System.dom s = D

/-- The case §2.3.2 sets aside as needing explicit statement: the law is an
honest probability distribution.  Jost Definition 2.2.1's resources are
sequences of conditional *probability* distributions, so this is what the
specification layer works with, while the arbitrary-weight carrier stays
available to the arguments that need it. -/
class IsProbability (S : PDS X Y) : Prop where
  nonNeg : S.NonNeg
  weight_le_one : S.weight ≤ 1

/-- The degenerate PDS concentrated on one deterministic system. -/
noncomputable def ofDDS (S : System.DDS X Y) : PDS X Y :=
  Finsupp.single S 1

/-! ## Converter application (CR18 Definition 3.9, lifted)

A PDS is a random variable over deterministic systems, so application lifts by
pushforward: the law of `α ▷ S` is the law of `S` transported along `α ▷ ·`.
The probabilistic layer adds no operation of its own. -/

/-- Definition 3.9 lifted to laws. -/
noncomputable def applyLaw (α : Converter.DDC U V X Y) (S : PDS X Y) : PDS U V :=
  Distribution.fTransform (Converter.DDC.apply α) S

@[simp] theorem applyLaw_ofDDS (α : Converter.DDC U V X Y) (S : System.DDS X Y) :
    applyLaw α (ofDDS S) = ofDDS (Converter.DDC.apply α S) := by
  simp [applyLaw, ofDDS, Distribution.fTransform]

@[simp] theorem weight_applyLaw (α : Converter.DDC U V X Y) (S : PDS X Y) :
    (applyLaw α S).weight = S.weight :=
  Distribution.weight_fTransform _ _

/-! ## Protocols and their action (Jost §2.2.2)

"We define a protocol to be a (partial) tuple of converter-connection pairs …
For two protocols `π` and `π'` we denote by `π' ∘ π` their sequential
composition … we denote by `id` the identity protocol, for which `idR = R`."

Serial composition of protocol functions is associative only up to trace
equality, so a protocol is a **word** over the admissible converters and its
action is the composite of the letters' actions.  `idR = R` and
`(π' ∘ π)R = π'(πR)` then hold on the nose, by construction rather than by
proof, which is why the carrier needs no quotient by behavioural equivalence. -/

/-- A protocol at a fixed signature: a word over the converters admitted by
CR18 Definition 3.8. -/
abbrev Protocol (X : Type u) (Y : Type v) : Type (max u v) :=
  FreeMonoid {α : Converter.ProtocolFn X Y X Y // Converter.IsDDC α}

/-- Protocol application, as a monoid homomorphism into the endomorphisms of the
carrier: each letter acts by its Definition 3.9 application, a word by the
composite. -/
noncomputable def act : Protocol X Y →* Function.End (PDS X Y) :=
  FreeMonoid.lift fun α => (applyLaw (Converter.toDDC α.val) : Function.End (PDS X Y))

/-- **Jost §2.2.2 on the PDS carrier**: `idR = R` and `(π' ∘ π)R = π'(πR)`. -/
noncomputable instance instMulAction : MulAction (Protocol X Y) (PDS X Y) :=
  MulAction.compHom _ act

@[simp] theorem smul_def (α : {α : Converter.ProtocolFn X Y X Y // Converter.IsDDC α})
    (S : PDS X Y) :
    (FreeMonoid.of α : Protocol X Y) • S = applyLaw (Converter.toDDC α.val) S := by
  show act (FreeMonoid.of α) S = _
  simp [act]

/-! ## Distinguishers (Jost Definition 2.2.8)

"A distinguisher `D` for resources with interfaces `ℐ` is a system that can be
attached to them with one additional interface, where it outputs a single bit."
The distinguishing advantage is `Δ^D(R,S) := Pr[D(S)=1] − Pr[D(R)=1]`.

Attaching a system that outputs one bit is a converter into the one-shot Boolean
signature, and CR18 Definition 3.8's class is exactly the admissible ones:
`AnswersInY` forbids continuing past a `⊥`, `AnswersWithin` bounds the
consecutive inner calls.  Divergence is not a third verdict — it contributes no
mass to the output-`1` event. -/

/-- Jost Definition 2.2.8's `D`: a system attached to the resource with one
additional interface, at which it outputs a bit. -/
abbrev Distinguisher (X : Type u) (Y : Type v) : Type (max u v) :=
  {d : Converter.ProtocolFn Unit Bool X Y // Converter.IsDDC d}

/-- The bit a distinguisher outputs against one deterministic system.
`Part.none` is divergence, and has no continuation. -/
noncomputable def verdict (d : Distinguisher X Y) (S : System.DDS X Y) : Part Bool :=
  (Converter.DDC.apply (Converter.toDDC d.val) S).val [Unit.unit]

/-- Jost Definition 2.2.8's `Pr[D(S) = 1]`: the mass a law puts on the
deterministic systems against which `d` outputs `1`. -/
noncomputable def outputOne (d : Distinguisher X Y) (S : PDS X Y) : ℝ :=
  S.mass fun deterministic => true ∈ verdict d deterministic

theorem outputOne_le_weight {S : PDS X Y} (hS : S.NonNeg) (d : Distinguisher X Y) :
    outputOne d S ≤ S.weight :=
  Distribution.mass_le_weight hS _

theorem outputOne_nonneg {S : PDS X Y} (hS : S.NonNeg) (d : Distinguisher X Y) :
    0 ≤ outputOne d S :=
  hS.mass_nonneg _

open Classical in
@[simp] theorem outputOne_ofDDS (d : Distinguisher X Y) (S : System.DDS X Y) :
    outputOne d (ofDDS S) = if true ∈ verdict d S then 1 else 0 := by
  simp [outputOne, ofDDS, Distribution.mass]

/-! ## Emulation closure

A distinguisher class must be closed under emulating a protocol: measuring
`π R` with `D` is measuring `R` with a distinguisher that first runs `π`.  Here
that is a theorem, and its content is the single identity the instantiation
turns on — attaching a converter and then observing is observing with the serial
composite.  CR18 Definition 3.8's class is closed under composition, so the
absorbed distinguisher is again one. -/

/-- The distinguisher that first attaches `α`, then runs `d`. -/
noncomputable def absorb (d : Distinguisher U V)
    (α : {α : Converter.ProtocolFn U V X Y // Converter.IsDDC α}) : Distinguisher X Y :=
  ⟨Converter.comp d.val α.val,
    Converter.serial_composition_is_ddc d.property α.property⟩

/-- **The absorption identity.**  `apply_toDDC` moves between the `DDC`
presentation `verdict` is written in and the `ν` presentation composition is
proved in; `apply_comp` is Definition 3.9's serial law, its `AnswersInY` premise
being the first half of Definition 3.8. -/
theorem verdict_absorb (d : Distinguisher U V)
    (α : {α : Converter.ProtocolFn U V X Y // Converter.IsDDC α}) (S : System.DDS X Y) :
    verdict d (Converter.DDC.apply (Converter.toDDC α.val) S)
      = verdict (absorb d α) S := by
  unfold verdict absorb
  rw [Converter.apply_toDDC, Converter.apply_toDDC, Converter.apply_toDDC,
    Converter.apply_comp _ _ _ d.property.1]

theorem outputOne_applyLaw (d : Distinguisher U V)
    (α : {α : Converter.ProtocolFn U V X Y // Converter.IsDDC α}) (S : PDS X Y) :
    outputOne d (applyLaw (Converter.toDDC α.val) S) = outputOne (absorb d α) S := by
  unfold outputOne applyLaw
  rw [Distribution.mass_fTransform]
  exact Distribution.mass_congr _ fun s => by rw [verdict_absorb]

/-- Emulation closure for a whole protocol, by induction on the word: each
letter is absorbed in turn.  The induction generalizes over the distinguisher,
because absorption pushes it inward. -/
theorem exists_absorb_smul (w : Protocol X Y) (d : Distinguisher X Y) :
    ∃ d' : Distinguisher X Y, ∀ S : PDS X Y, outputOne d (w • S) = outputOne d' S := by
  induction w using FreeMonoid.recOn generalizing d with
  | h0 => exact ⟨d, fun S => by rw [one_smul]⟩
  | ih α w ih =>
      obtain ⟨d', hd'⟩ := ih (absorb d α)
      refine ⟨d', fun S => ?_⟩
      rw [show ((FreeMonoid.of α * w : Protocol X Y) • S)
            = (FreeMonoid.of α : Protocol X Y) • (w • S) from mul_smul _ _ _,
        smul_def, outputOne_applyLaw, hd']

/-! ## The distance (MauRen16 fn. 9; Jost Definition 2.2.8)

`d(R,S) := sup_{D∈𝒟} Δ^D(R,S)` with `𝒟` the strict tests: `maxEDist` is the
supremum over distinguishers of the acceptance-mass gap.  Lanzenberger
Definition 2.26's transcript distance is the random-systems-layer
characterization of this quantity, related by theorem, not a second
definition. -/

/-- Equality under every finite strict deterministic observation. -/
def Equivalent (S T : PDS X Y) : Prop :=
  ∀ d : Distinguisher X Y, outputOne d S = outputOne d T

theorem Equivalent.refl (S : PDS X Y) : Equivalent S S := fun _ => rfl

theorem Equivalent.symm {S T : PDS X Y} (h : Equivalent S T) : Equivalent T S :=
  fun d => (h d).symm

theorem Equivalent.trans {S T U : PDS X Y}
    (h : Equivalent S T) (h' : Equivalent T U) : Equivalent S U :=
  fun d => (h d).trans (h' d)

/-- Every deterministic stateful `IsDDC` converter preserves strict
contextual equivalence. -/
theorem Equivalent.applyLaw
    (α : {α : Converter.ProtocolFn U V X Y // Converter.IsDDC α})
    {S T : PDS X Y} (h : Equivalent S T) :
    Equivalent (applyLaw (Converter.toDDC α.val) S)
      (applyLaw (Converter.toDDC α.val) T) := by
  intro d
  rw [outputOne_applyLaw, outputOne_applyLaw]
  exact h (absorb d α)

/-- MauRen16 fn. 9's `d`: the supremum distinguishing gap over the strict
test class. -/
noncomputable def maxEDist (S T : PDS X Y) : ℝ≥0∞ :=
  ⨆ d : Distinguisher X Y, edist (outputOne d S) (outputOne d T)

theorem maxEDist_self (S : PDS X Y) : maxEDist S S = 0 := by
  simp [maxEDist]

theorem maxEDist_comm (S T : PDS X Y) : maxEDist S T = maxEDist T S := by
  simp only [maxEDist, edist_comm]

theorem maxEDist_triangle (S T U : PDS X Y) :
    maxEDist S U ≤ maxEDist S T + maxEDist T U := by
  unfold maxEDist
  refine iSup_le fun d => ?_
  exact (edist_triangle (outputOne d S) (outputOne d T) (outputOne d U)).trans
    (add_le_add
      (le_iSup (fun d' : Distinguisher X Y =>
        edist (outputOne d' S) (outputOne d' T)) d)
      (le_iSup (fun d' : Distinguisher X Y =>
        edist (outputOne d' T) (outputOne d' U)) d))

theorem maxEDist_eq_of_equivalent {S S' T T' : PDS X Y}
    (hS : Equivalent S S') (hT : Equivalent T T') :
    maxEDist S T = maxEDist S' T' := by
  unfold maxEDist
  apply iSup_congr
  intro d
  rw [hS d, hT d]

/-- **Def 2's non-expansion, derived**: absorbing the converter into the
test makes every deterministic `IsDDC` converter one-Lipschitz. -/
theorem maxEDist_applyLaw_le
    (α : {α : Converter.ProtocolFn U V X Y // Converter.IsDDC α})
    (S T : PDS X Y) :
    maxEDist (applyLaw (Converter.toDDC α.val) S)
        (applyLaw (Converter.toDDC α.val) T) ≤ maxEDist S T := by
  unfold maxEDist
  refine iSup_le fun d => ?_
  rw [outputOne_applyLaw, outputOne_applyLaw]
  exact le_iSup
    (fun d' : Distinguisher X Y => edist (outputOne d' S) (outputOne d' T))
    (absorb d α)

/-- The contextual relation is exactly the zero kernel of the distance. -/
theorem maxEDist_eq_zero_iff (S T : PDS X Y) :
    maxEDist S T = 0 ↔ Equivalent S T := by
  constructor
  · intro h d
    have hb : edist (outputOne d S) (outputOne d T) ≤ maxEDist S T :=
      le_iSup (fun d' : Distinguisher X Y =>
        edist (outputOne d' S) (outputOne d' T)) d
    rw [h] at hb
    exact edist_eq_zero.mp (bot_unique hb)
  · intro h
    refine le_antisymm (iSup_le fun d => ?_) bot_le
    rw [h d, edist_self]

/-! ## The resource carrier

Jost Definition 2.2.8 reads `Pr[D(S) = 1]` as a probability, and a distinguisher
class bounds every test by `1`.  The laws satisfying `IsProbability` are
therefore where the specification layer's distinguisher lives; the general
carrier stays available to the random-systems arguments.

Protocol application restricts there because it is a pushforward: it preserves
non-negativity and preserves weight exactly. -/

theorem nonNeg_smul (w : Protocol X Y) {S : PDS X Y} (hS : S.NonNeg) :
    (w • S).NonNeg := by
  induction w using FreeMonoid.recOn generalizing S with
  | h0 => rwa [one_smul]
  | ih α w ih =>
      rw [show ((FreeMonoid.of α * w : Protocol X Y) • S)
            = (FreeMonoid.of α : Protocol X Y) • (w • S) from mul_smul _ _ _,
        smul_def]
      exact Distribution.NonNeg.fTransform (ih hS) _

@[simp] theorem weight_smul (w : Protocol X Y) (S : PDS X Y) :
    (w • S).weight = S.weight := by
  induction w using FreeMonoid.recOn generalizing S with
  | h0 => rw [one_smul]
  | ih α w ih =>
      rw [show ((FreeMonoid.of α * w : Protocol X Y) • S)
            = (FreeMonoid.of α : Protocol X Y) • (w • S) from mul_smul _ _ _,
        smul_def, weight_applyLaw, ih]

/-- Jost's `Θ` for the specification layer: the PDS carrying `IsProbability`. -/
abbrev Resource (X : Type u) (Y : Type v) : Type (max u v) :=
  {S : PDS X Y // IsProbability S}

namespace Resource

noncomputable instance instSMul : SMul (Protocol X Y) (Resource X Y) where
  smul w S := ⟨w • S.1,
    ⟨nonNeg_smul w S.2.nonNeg, (weight_smul w S.1).trans_le S.2.weight_le_one⟩⟩

@[simp] theorem coe_smul (w : Protocol X Y) (S : Resource X Y) :
    ((w • S : Resource X Y) : PDS X Y) = w • (S : PDS X Y) := rfl

noncomputable instance instMulAction : MulAction (Protocol X Y) (Resource X Y) where
  one_smul S := Subtype.ext (by simp)
  mul_smul a b S := Subtype.ext (by simp [mul_smul])

end Resource

end PDS

end RandomSystems
