import RandomSystems.Converter.ParallelAll

/-!
# Canonical n-ary converters

The empty family has zero consecutive inside-query bound. The general certificate keeps
each component's exact input domain under tagged parallel composition.
-/

namespace SystemAlgebra.Tests

noncomputable section

def emptyConverters : ∀ _k : Empty,
    InsideOutsideSystem Unit Unit (fun _ => Unit) (fun _ => Unit)
      (fun _ => Unit) (fun _ => Unit) :=
  fun k => nomatch k

example : IsDDC 0 (tensorAllL emptyConverters) := by
  have h : ∀ k : Empty, IsDDC 0 (emptyConverters k) := fun k => nomatch k
  simpa using IsDDC.tensorAllL (b := fun _ : Empty => 0) h

#print axioms SystemAlgebra.IsDDC.tensorAllL
#print axioms SystemAlgebra.IsDDCFrom.tensorAllL
#print axioms SystemAlgebra.PDCBehavior.tensorAll_ofDDC

end
end SystemAlgebra.Tests
