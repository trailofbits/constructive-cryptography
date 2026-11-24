import Tests.Rendering.Pseudocode

/-! Representative source-backed cards and expandable leaves for infoview and browser QA. -/

set_option linter.hashCommand false

open DSLExamples Rendering.PseudocodeTests
open SystemAlgebra CategoryTheory

#cc_pseudocode_show Counter
#cc_pseudocode_show FreshBits
#cc_pseudocode_show SecretBit
#cc_pseudocode_show Arithmetic
#cc_pseudocode_show BoundedCounter
#cc_pseudocode_show Branches
#cc_pseudocode_show Pad
#cc_pseudocode_show Padding
#cc_pseudocode_show WriteThrough
#cc_pseudocode_show FirstRequests
#cc_pseudocode_show DSLTests.ParallelOutside.Store
#cc_pseudocode_show DSLTests.ParallelOutside.SharedBit
#cc_pseudocode_show DSLTests.ParallelOutside.Forwarded
#cc_pseudocode_show Rendering.PseudocodeTests.Literal
#cc_pseudocode_show «σ with spaces»

#cc_diagram_show Counter (budget := 3)
#cc_diagram_show BoundedCounter 7 (budget := 2)
#cc_diagram_show DSLTests.ParallelOutside.Forward (budget := (2, 2)) •
  DSLTests.ParallelOutside.EmptyCell
    (budget := DSLTests.ParallelOutside.Forward.bound * (2 + 2))
