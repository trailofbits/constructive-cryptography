/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import Rendering.CCWidget

/-! Semantic diagram roles for the abstract surface.  These declarations are
registered here, beside the compatibility import, rather than hardcoded into
the theory-free renderer.  Indices count arguments from the end. -/
cc_diagram_attachment ConstructiveCryptography.CCAlgebra.apply 2 1 0
cc_diagram_parallel AbstractCryptography.Par.par 1 0
cc_diagram_distance ConstructiveCryptography.CCAlgebra.dist 1 0 "d"
cc_diagram_construction AbstractCryptography.HasReduction.Red 2 1 0
cc_diagram_construction AbstractCryptography.Constructs 1 2 0
#cc_diagram_rule_check ConstructiveCryptography.CCAlgebra.apply
#cc_diagram_rule_check AbstractCryptography.Par.par
#cc_diagram_rule_check AbstractCryptography.Constructs

/-!
# Back-compat shim for the `CCDiagram` proof widget

The widget engine lives in the theory-free `Rendering.CCWidget` module
(imports only ProofWidgets; matches goal heads by name), so that the
random-systems surface can import it without depending on any
constructive-cryptography theory.  This module re-exports it under the
historical `ConstructiveCryptography` names.

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
