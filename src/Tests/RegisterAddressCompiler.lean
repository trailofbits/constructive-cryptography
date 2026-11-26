module

public import Commons.Definitions.AbstractModel.RegisterDDC.AddressMap
public import Tests.AbstractModelAddressMap

/-!
# Register-converter address transport

The existing natural-register fixture uses integer internal values and the shift `n ↦ n + 5`.
Tests apply the compiler correspondence to a terminal guess and a compute-then-observe history.
-/

@[expose] public section

namespace Tests.RegisterAddressCompiler

open SystemAlgebra Commons.AbstractModel

open Tests.AbstractModel Tests.AbstractModelRegisters Tests.AbstractModelAddressMap

/-- Address renaming leaves a zero-query terminal submission unchanged. -/
example : (model.registersDDC 0 0 operate (7 : ℤ)).1 [⟨⟨none, .submit⟩, 3⟩] =
    (model.registersDDC (shift 0) 0 operate (7 : ℤ)).1 [⟨⟨none, .submit⟩, 3⟩] :=
  registersDDC_mapCommand model shift 0 0 operate 7 _

/-- A stored value is observed through the same pending call after renaming both addresses. -/
example : (model.registersDDC 0 2 operate (7 : ℤ)).1
      [⟨⟨none, .compute ()⟩, (fun _ => 0, 7)⟩, ⟨⟨none, .query false⟩, fun _ => 7⟩] =
    (model.registersDDC (shift 0) 2 operate (7 : ℤ)).1
      [⟨⟨none, .compute ()⟩, (fun _ => 5, 12)⟩, ⟨⟨none, .query false⟩, fun _ => 12⟩] :=
  registersDDC_mapCommand model shift 0 2 operate 7 _

#print axioms Commons.AbstractModel.registerProgram_mapCommand
#print axioms Commons.AbstractModel.registersDDC_mapCommand

end Tests.RegisterAddressCompiler
