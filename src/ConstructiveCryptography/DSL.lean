import ConstructiveCryptography.DSL.Elaborator
import ConstructiveCryptography.DSL.Inlining

/-!
# The cryptographic component DSL

`interface`, `system`, `converter` and `filter` declarations elaborate to typed systems and
typed converters at every query budget: each component compiles to a deterministic program
(`RandomSystems.Typed.DSL`), and its sampling to sources of fresh samples. Open
`SystemAlgebra.DSL` and `open scoped SystemAlgebra SystemAlgebra.DSL` for the declarations and
assembly operations. Each declaration also gets kernel-checked invocation equations
(`DSL.Equations`), which `inline` (`DSL.Inlining`) uses to rewrite an attachment as a combined
automaton or, from memorylessness certificates, as a memoryless system.
`DSL/GRAMMAR.md` specifies the syntax and what each declaration generates.
-/
