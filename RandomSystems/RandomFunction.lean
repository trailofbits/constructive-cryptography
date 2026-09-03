import RandomSystems.Uniform
import RandomSystems.Converter.RandomSystemAction
import RandomSystems.Tactics.ProofAutomationAttributes

set_option autoImplicit false

/-!
# Finite random functions

A finite random function is represented once, as a normalized distribution on
functions.  Its fixed-interface PDS and cumulative random-system forms are the
canonical function-evaluator interpretations of that distribution.
-/

namespace RandomSystems

noncomputable section

open Probability

universe u v

/-- A finite random function from `X` to `Y`. -/
structure RandomFunction (X : Type u) (Y : Type v) where
  law : Distribution.ProbDist (X → Y)

namespace RandomFunction

/-- The uniform random function from `X` to `Y`. -/
def uniform (X : Type u) (Y : Type v)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] :
    RandomFunction X Y :=
  ⟨⟨Distribution.uniform (X → Y), Distribution.uniform_isProbDist⟩⟩

/-- Interpret a finite random function as a fixed-interface PDS. -/
def toPDS {X : Type u} {Y : Type v} (system : RandomFunction X Y) :
    RandomSystems.PDS X Y :=
  (Distribution.PMF system.law System.functionEvaluator).1

/-- Interpret a finite random function as a normalized query-indexed PDS. -/
def toAmbientPDS {X : Type u} {Y : Type v} (system : RandomFunction X Y) :
    Ambient.PDS (Ambient.Interface.single X Y) :=
  Distribution.PMF system.law
    (Ambient.DDS.ofFunction (A := Ambient.Interface.single X Y))

/-- Interpret a finite random function as a cumulative random system. -/
def toRandomSystem {X : Type u} {Y : Type v}
    (system : RandomFunction X Y) :
    Ambient.RandomSystem (Ambient.Interface.single X Y) :=
  Ambient.PDS.toRandomSystem system.toAmbientPDS

theorem isProbDist_toPDS {X : Type u} {Y : Type v}
    (system : RandomFunction X Y) : system.toPDS.isProbDist :=
  (Distribution.PMF system.law System.functionEvaluator).2

theorem hasDomain_toPDS {X : Type u} {Y : Type v}
    (system : RandomFunction X Y) :
    PDS.HasDomain system.toPDS {history : List X | history ≠ []} :=
  PDS.hasDomain_fTransform_functionEvaluator
    (fun function : X → Y => function) system.law.1

/-- A domain filter maps a finite random function directly to its normalized
fixed-interface law. -/
noncomputable instance instHSMulDomainFilter {X : Type u} {Y : Type v} :
    HSMul (DomainFilter X) (RandomFunction X Y)
      (Distribution.ProbDist (System.DDS X Y)) where
  hSMul restriction system :=
    ⟨PDS.filterDom restriction.predicate restriction.prefixClosed system.toPDS,
      PDS.isProbDist_filterDom restriction.predicate restriction.prefixClosed
        system.isProbDist_toPDS⟩

instance {X : Type u} {Y : Type v} :
    Coe (RandomFunction X Y) (Distribution (X → Y)) :=
  ⟨fun system => system.law.1⟩

instance {X : Type u} {Y : Type v} :
    Coe (RandomFunction X Y) (RandomSystems.PDS X Y) :=
  ⟨toPDS⟩

instance {X : Type u} {Y : Type v} :
    Coe (RandomFunction X Y)
      (Ambient.RandomSystem (Ambient.Interface.single X Y)) :=
  ⟨toRandomSystem⟩

instance {A : Ambient.Interface} {X : Type u} {Y : Type v} :
    HSMul (Ambient.DDC A (Ambient.Interface.single X Y))
      (RandomFunction X Y) (Ambient.RandomSystem A) where
  hSMul converter system :=
    Ambient.RandomSystem.applyDDC converter system.toRandomSystem

@[simp]
theorem toPDS_uniform_eq_urf (X : Type u) (Y : Type v)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] :
    toPDS (uniform X Y) = PDS.urf X Y :=
  rfl

@[simp]
theorem toAmbientPDS_uniform_eq (X : Type u) (Y : Type v)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] :
    toAmbientPDS (uniform X Y) =
      Ambient.PDS.uniformFunction (Ambient.Interface.single X Y) :=
  rfl

end RandomFunction

namespace Ambient.DDC

open CategoryTheory

/-- Categorical converter attachment uses the cumulative interpretation of a
finite random function. -/
noncomputable scoped instance homActionRandomFunction
    {A : Ambient.Interface} {X : Type u} {Y : Type v} :
    HSMul (A ⟶ Ambient.Interface.single X Y)
      (RandomFunction X Y) (Ambient.RandomSystem A) where
  hSMul converter system :=
    Ambient.RandomSystem.applyDDC converter system.toRandomSystem

/-- Categorical deterministic attachment to a finite random function
normalizes to attachment to its cumulative random-system interpretation. -/
@[rs_normalization]
theorem hom_smul_randomFunction_eq
    {A : Ambient.Interface} {X : Type u} {Y : Type v}
    (converter : A ⟶ Ambient.Interface.single X Y)
    (system : RandomFunction X Y) :
    (converter • system : Ambient.RandomSystem A) =
      converter • system.toRandomSystem :=
  rfl

end Ambient.DDC

end

end RandomSystems
