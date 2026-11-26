module

public import RandomSystems.Typed.ParallelAll

/-!
# Selecting one component exchange

`Interface.selectExchange k z` restricts the singleton exchange `z` to family member `k`.
It returns the local query/reply pair when both component tags are `k`, and `none` otherwise.
The operation assembles the existing transcript restriction with alphabet reassociation.
-/

@[expose] public section

namespace SystemAlgebra.Interface

/-- Read an exchange at the selected family member, retaining both local port labels. -/
noncomputable def selectExchange
    -- `A k` is the interface at family member `k`; `z` is a tagged query/reply exchange.
    {K : Type} [DecidableEq K] {A : K → Interface} (k : K)
    (z : (Σ l : Σ k, (A k).I, (A l.1).X l.2) ×
      (Σ l : Σ k, (A k).I, (A l.1).Y l.2)) :
    Option ((Σ i, (A k).X i) × (Σ i, (A k).Y i)) :=
  (RandomSystem.restrictExchanges k
    [((Equiv.sigmaAssoc (fun j i => (A j).X i)).prodCongr
      (Equiv.sigmaAssoc (fun j i => (A j).Y i))) z]).head?

end SystemAlgebra.Interface
