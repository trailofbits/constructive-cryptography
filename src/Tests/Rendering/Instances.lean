import Rendering.Instances
import Tests.Rendering.Widget

/-! The selected interface instances and their direct system operations must
project to the same ordered tree. No application library is imported. -/

-- These tests deliberately retain the commands that drive the infoview.
set_option linter.hashCommand false

open CategoryTheory CategoryTheory.MonoidalCategory
open SystemAlgebra ConstructiveCryptography.CryptographicAlgebra
open Rendering.Tests Rendering.Adversarial

namespace Rendering.InterfaceTests
variable {A B D E : Interface} (c : A ⟶ B) (d : B ⟶ D)
variable (R : TypedSystem D) (S : TypedSystem E) (T : TypedSystem B)

assert_diagram c • (d • R) shape "attach(c,attach(d,R))"
assert_diagram (c ≫ d) • R shape "attach(serial(c,d),R)"
assert_diagram TypedConverter.comp c d shape "serial(c,d)"
assert_diagram TypedConverter.attach c T shape "attach(c,T)"
assert_diagram TypedSystem.parallel R S shape "parallel(R,S)"
assert_diagram parallel R S shape "parallel(R,S)"
assert_diagram (d ⊗ₘ 𝟙 E) • parallel R S
  shape "attach(tensor(d,𝟙 E),parallel(R,S))"
assert_boundaries c • T
#guard_msgs in
#cc_diagram_check (c ≫ d)
#guard_msgs in
#cc_diagram_check SystemAlgebra.Interface.comp_smul c d R
#guard_msgs in
#cc_diagram_check R

end Rendering.InterfaceTests
