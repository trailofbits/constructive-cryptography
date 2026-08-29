/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import Rendering.CCWidget
import AbstractCryptography.Categorical.ResourceAlgebra

/-! Semantic diagram roles for the typed Abstract Cryptography surface.  They
are registered in this adapter rather than hardcoded into the theory-free
renderer.  Indices count arguments from the end. -/
cc_diagram_application AbstractCryptography.Categorical.ResourceAlgebra.attach 1 0
cc_diagram_parallel AbstractCryptography.Categorical.ResourceAlgebra.parallel 1 0
cc_diagram_distance AbstractCryptography.Categorical.ResourceAlgebra.distance 1 0 "d"
cc_diagram_construction
  AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs 1 2 0
#cc_diagram_rule_check AbstractCryptography.Categorical.ResourceAlgebra.attach
#cc_diagram_rule_check AbstractCryptography.Categorical.ResourceAlgebra.parallel
#cc_diagram_rule_check
  AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs

/-!
# Abstract Cryptography adapter for the `CCDiagram` proof widget

The widget engine lives in the theory-free `Rendering.CCWidget` module.  This
adapter registers the typed `ResourceAlgebra` declaration roles and re-exports
the widget under the established `ConstructiveCryptography` names.

The panel is shown automatically in every module importing `Rendering.CCWidget`
(transitively) — including this one — and renders nothing on non-CC
goals.  See `Rendering.CCWidget` for the recognized judgment shapes, the
`@[cc_diagram]` label attribute, and the `#cc_diagram_check` /
`#cc_diagram_view` commands.
-/

namespace ConstructiveCryptography

export CCWidget (CCDiagram)

namespace Widget

export CCWidget (parseJudgment? renderJudgment stylesheet
  renderSystemComponent JudgmentView SystemView Iface Elem BoxKind AdvCard
  DeclRole DeclRule ccDiagramLabels ccDiagramRules)

end Widget
end ConstructiveCryptography
