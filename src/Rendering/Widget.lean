import Rendering.CCWidget
import ConstructiveCryptography.Notation.Basic
import ConstructiveCryptography.CryptographicAlgebra.Indifferentiability

/-!
# CC diagrams in the Lean infoview

This optional adapter registers the current abstract CC declarations. It connects
`ResourceTheory.attach`, ordered `CryptographicAlgebra.parallel`, categorical
serial and tensor composition, the selected distance, construction judgments,
indifferentiability relaxations, and game equivalences to the theory-free renderer.
Argument positions count from the end.

An abstract carrier `Phi A` is recognized through the explicit `ResourceTheory`
capability in the local context. Categorical arrows become converters only in
such a resource theory. Each boundary label comes from the inferred type.
See `Rendering/README.md` for the display contract and the scenario matrix.
-/

cc_diagram_resource_family ConstructiveCryptography.ResourceTheory 1 0
cc_diagram_specification_type ConstructiveCryptography.Specification 0
cc_diagram_specification_type Set 0
cc_diagram_arrow_type Quiver.Hom 2 1 0
cc_diagram_arrow_type ConstructiveCryptography.CryptographicAlgebra.Converter 2 1 0
cc_diagram_application ConstructiveCryptography.ResourceTheory.attach 1 0
cc_diagram_action ConstructiveCryptography.CryptographicAlgebra.instHSMulConverterResource
cc_diagram_serial CategoryTheory.CategoryStruct.comp 1 0
cc_diagram_identity CategoryTheory.CategoryStruct.id
cc_diagram_tensor CategoryTheory.MonoidalCategoryStruct.tensorHom 1 0
cc_diagram_interface_tensor CategoryTheory.MonoidalCategoryStruct.tensorObj 1 0
cc_diagram_parallel ConstructiveCryptography.CryptographicAlgebra.parallel 1 0
cc_diagram_parallel ConstructiveCryptography.CryptographicAlgebra.Specification.parallel 1 0
cc_diagram_application ConstructiveCryptography.CryptographicAlgebra.Specification.map 1 0
cc_diagram_distance ConstructiveCryptography.CryptographicAlgebra.distance 1 0 "Δ"
cc_diagram_construction
  ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs 1 2 0
cc_diagram_construction_within
  ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin 2 3 1 0
cc_diagram_transparent ConstructiveCryptography.CryptographicAlgebra.Specification.simulatorImage 0
cc_diagram_transparent ConstructiveCryptography.CryptographicAlgebra.Specification.star 0
cc_diagram_transparent ConstructiveCryptography.Relaxation.relaxedBy 1
cc_diagram_conditional ConstructiveCryptography.DistinctionGames.ConditionallyEquivalent 1 0
cc_diagram_transparent ConstructiveCryptography.DistinctionGames.visible 0

