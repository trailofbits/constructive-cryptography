import Rendering

/-!
The H-coefficient argument supplies a distance bound between two named systems on their common
interface. Put the cursor on `argument` to inspect the data, or on the applied theorem below
to include its conclusion. The sample, reveals, classes and local inequalities remain explicit
fields of the supplied argument. In the calculation, the H application is the first recorded
step and `widen` is the second. The widget keeps precisely those two steps.
-/

open SystemAlgebra ConstructiveCryptography.CryptographicAlgebra

namespace Rendering.HMethodGallery

variable {A : Interface} (R S : TypedSystem A) (ε : NNReal)
variable (argument : RandomSystem.HCoefficient R.1 S.1 ε)

example : distance R S ≤ ε :=
  Interface.distance_le_of_hCoefficient argument

example (δ : NNReal) (widen : (ε : ENNReal) ≤ δ) : distance R S ≤ δ := by
  calc
    distance R S ≤ ε := Interface.distance_le_of_hCoefficient argument
    _ ≤ δ := widen

end Rendering.HMethodGallery
