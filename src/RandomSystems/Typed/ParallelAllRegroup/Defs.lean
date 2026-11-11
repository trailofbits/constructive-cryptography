module

public import RandomSystems.Typed.ParallelAll

/-!
# Finite-family interface presentations

`reindexLabels` changes family indices by an equivalence. `optionSplitPorts` and
`optionSplitLabels` separate the `none` component from the `some` family. These equivalences
preserve local values; the domain and resource equations are proved in `ParallelAllRegroup`.
-/

@[expose] public section

namespace SystemAlgebra

-- `A k` is the interface at family index `k`; `e` chooses its reindexed presentation.
variable {K K' : Type} (e : K' ≃ K)

/-- The reindexing of the labels of `⨂ k, A k` along `e`. -/
def reindexLabels (A : K → Interface) (F : ∀ k, (A k).I → Type) :
    (Σ l : Σ k, (A k).I, F l.1 l.2) ≃ Σ l : Σ k', (A (e k')).I, F (e l.1) l.2 :=
  (Equiv.sigmaAssoc F).trans ((Equiv.sigmaCongrLeft e).symm.trans
    (Equiv.sigmaAssoc fun k' i => F (e k') i).symm)

-- The head interface is `A none`; the tail interfaces are `A (some j)`.
variable {J : Type} (A : Option J → Interface)

/-- The ports of `⨂ o, A o` as the ports of `A none ⊗ ⨂ j, A (some j)`. -/
def optionSplitPorts : (Σ o, (A o).I) ≃ (A none).I ⊕ Σ j, (A (some j)).I where
  toFun
    | ⟨none, i⟩ => .inl i
    | ⟨some j, i⟩ => .inr ⟨j, i⟩
  invFun
    | .inl i => ⟨none, i⟩
    | .inr ⟨j, i⟩ => ⟨some j, i⟩
  left_inv := by rintro ⟨(_ | j), i⟩ <;> rfl
  right_inv := by rintro (i | ⟨j, i⟩) <;> rfl

/-- The labels of `⨂ o, A o` as the labels of `A none ⊗ ⨂ j, A (some j)`. -/
def optionSplitLabels (F : ∀ o, (A o).I → Type) :
    (Σ l : Σ o, (A o).I, F l.1 l.2) ≃
      Σ l : (A none).I ⊕ Σ j, (A (some j)).I, Sum.rec (F none) (fun l => F (some l.1) l.2) l where
  toFun
    | ⟨⟨none, i⟩, x⟩ => ⟨.inl i, x⟩
    | ⟨⟨some j, i⟩, x⟩ => ⟨.inr ⟨j, i⟩, x⟩
  invFun
    | ⟨.inl i, x⟩ => ⟨⟨none, i⟩, x⟩
    | ⟨.inr ⟨j, i⟩, x⟩ => ⟨⟨some j, i⟩, x⟩
  left_inv := by rintro ⟨⟨(_ | j), i⟩, x⟩ <;> rfl
  right_inv := by rintro ⟨(i | ⟨j, i⟩), x⟩ <;> rfl

end SystemAlgebra
