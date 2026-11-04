module

public import ConstructiveCryptography.DSL

/-!
# Documentation on component declarations

Leading docstrings document the component and its `.perPort` and `.exact` forms, when generated.
The examples cover typed and generated interfaces, deterministic and sampling systems, converters,
and a named assembly. Metadata lookup checks the text a reader sees through Lean's documentation.
-/

@[expose] public section

open SystemAlgebra SystemAlgebra.DSL Probability.Distribution

namespace Tests.DSL.Documentation

interface BitSource
  draw() → Bool

/-- Every `draw()` returns `false`. -/
system Fixed : BitSource
  on draw() → Bool
    return false

/-- Every `draw()` returns a fresh uniform bit. -/
system Fresh
  on draw() → Bool
    b ←$ 𝒰[Bool]
    return b

/-- Every `draw()` forwards one inside draw and negates its reply. -/
converter Negate : BitSource
  inside source : BitSource
  on draw() → Bool
    b ← source.draw()
    return !b

/-- Every `get()` forwards one inside draw and returns its reply. -/
converter Forward
  inside source : BitSource
  on get() → Bool
    b ← source.draw()
    return b

/-- `Negate • Fixed`: every `draw()` returns `true`. -/
system Combined ≔ Negate • Fixed

-- Fully qualified metadata names also check components declared in a namespace.
run_cmd do
  let env ← Lean.getEnv
  for (name, expected) in [
      (``Fixed, "Every `draw()` returns `false`."),
      (``Fixed.perPort, "Every `draw()` returns `false`."),
      (``Fresh, "Every `draw()` returns a fresh uniform bit."),
      (``Fresh.perPort, "Every `draw()` returns a fresh uniform bit."),
      (``Negate, "Every `draw()` forwards one inside draw and negates its reply."),
      (``Negate.perPort, "Every `draw()` forwards one inside draw and negates its reply."),
      (``Negate.exact, "Every `draw()` forwards one inside draw and negates its reply."),
      (``Forward, "Every `get()` forwards one inside draw and returns its reply."),
      (``Forward.exact, "Every `get()` forwards one inside draw and returns its reply."),
      (``Combined, "`Negate • Fixed`: every `draw()` returns `true`.")] do
    let some actual ← Lean.findDocString? env name
      | throwError "Missing documentation for {name}"
    unless actual.trimAscii.toString == expected do
      throwError "Unexpected documentation for {name}: {actual}"

end Tests.DSL.Documentation
