/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC

set_option autoImplicit false

/-!
# Query-indexed resource-algebra checks

This module checks the selected category, ordered monoidal structure, and
resource algebra through the public `RandomSystemsCC` root.
-/

namespace RandomSystemsCC.Checks

noncomputable section

open CategoryTheory
open RandomSystems.Ambient

universe u v

example : AbstractCryptography.Categorical.ResourceAlgebra
    RandomSystems.Ambient.Interface.{u, v}
    RandomSystems.Ambient.Interface.randomSystems :=
  inferInstance

example {A B : RandomSystems.Ambient.Interface.{u, v}}
    (converter : RandomSystems.Ambient.DDC A B)
    (system : RandomSystems.Ambient.RandomSystem B) :
    AbstractCryptography.Categorical.ResourceAlgebra.attach
        (Phi := RandomSystems.Ambient.Interface.randomSystems)
        converter system =
      RandomSystems.Ambient.RandomSystem.apply converter system :=
  rfl

example {A B : RandomSystems.Ambient.Interface.{u, v}}
    (left : RandomSystems.Ambient.RandomSystem A)
    (right : RandomSystems.Ambient.RandomSystem B) :
    AbstractCryptography.Categorical.ResourceAlgebra.parallel
        (Phi := RandomSystems.Ambient.Interface.randomSystems)
        left right =
      RandomSystems.Ambient.RandomSystem.parallel left right :=
  rfl

end


end RandomSystemsCC.Checks
