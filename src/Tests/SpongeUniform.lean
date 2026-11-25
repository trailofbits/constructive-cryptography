module

public import Commons.Schemes.Sponge.Uniform

/-! Uniform byte slices use the same law for capacity and digest coordinates. -/

@[expose] public section

namespace Tests.SpongeUniform

open Commons.Sponge Probability

/-- Two state bytes, with one rate byte and one output byte. -/
def parameters : Parameters := ⟨2, 1, 1, 0x06⟩

example : Fintype.card (ByteState 2) = 256 ^ 2 := card_byteState 2

example : Distribution.fTransform (capacityPart parameters)
    (Distribution.uniform (ByteState 2)) = Distribution.uniform (ByteState 1) :=
  fTransform_capacityPart_uniform parameters (by norm_num [parameters])

example : Distribution.fTransform (digestPart parameters)
    (Distribution.uniform (ByteState 2)) = Distribution.uniform (ByteState 1) :=
  fTransform_digestPart_uniform parameters (by norm_num [parameters])

#print axioms fTransform_capacityPart_uniform
#print axioms fTransform_digestPart_uniform

end Tests.SpongeUniform
