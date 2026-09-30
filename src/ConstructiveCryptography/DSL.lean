import ConstructiveCryptography.DSL.Elaborator

/-!
# The cryptographic component DSL

`interface`, `system`, `converter` and `filter` declarations elaborate to finite systems and
converters at every query budget: each component compiles to a deterministic program, and its
sampling to sources of fresh samples. Open `SystemAlgebra.DSL` and
`open scoped SystemAlgebra SystemAlgebra.DSL` for the declarations and assembly operations.
`DSL/GRAMMAR.md` specifies the syntax and what each declaration generates.
-/
