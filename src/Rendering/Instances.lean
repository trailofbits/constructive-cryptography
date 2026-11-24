import Rendering.Widget
import ConstructiveCryptography.Instances.Algebra

/-!
# Diagrams for CC's interface instances

The concrete carriers selected by `ConstructiveCryptography.Instances.Algebra`
receive the same typed boundaries and ordered composition as the abstract view.
These registrations use existing declarations; they add no system model or law.
-/

cc_diagram_resource_type SystemAlgebra.TypedSystem 0
cc_diagram_converter_type SystemAlgebra.TypedConverter 1 0
cc_diagram_application SystemAlgebra.TypedConverter.attach 1 0
cc_diagram_action SystemAlgebra.TypedConverter.instHSMulTypedSystem
cc_diagram_action SystemAlgebra.Interface.instHSMulHomTypedSystem_constructiveCryptography
cc_diagram_serial SystemAlgebra.TypedConverter.comp 1 0
cc_diagram_identity SystemAlgebra.TypedConverter.id
cc_diagram_tensor SystemAlgebra.TypedConverter.parallel 1 0
cc_diagram_parallel SystemAlgebra.TypedSystem.parallel 1 0
cc_diagram_interface_tensor SystemAlgebra.Interface.tensor 1 0
cc_diagram_interface_constructor SystemAlgebra.Interface.queryBudget
cc_diagram_interface_constructor SystemAlgebra.Interface.portBudget
cc_diagram_interface SystemAlgebra.Interface SystemAlgebra.Interface.I
  SystemAlgebra.Interface.X SystemAlgebra.Interface.Y SystemAlgebra.Interface.domain
