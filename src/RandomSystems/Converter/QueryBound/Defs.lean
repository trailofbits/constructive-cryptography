module

public import RandomSystems.Converter.ConverterDomain

/-!
# Total inside-query bounds

`InsideQueriesBounded α k` bounds every partial converter transcript by the number of outside
queries it has received. An emitted inside query is counted before its reply arrives.
The function `k` is a total-query bound; its monotonicity is a separate hypothesis when used.
-/

@[expose] public section

namespace SystemAlgebra

/-- Every partial transcript uses at most `k q` inside queries after `q` outside inputs. -/
def InsideQueriesBounded
    -- `O`, `J` label outside/inside ports with query/reply families `U`, `V` and `X`, `Y`.
    {O J : Type} {U V : O → Type} {X Y : J → Type}
    -- `α` reads complete input histories.
    -- `k q` bounds total inside queries after `q` outside inputs.
    (α : InsideOutsideSystem O J U V X Y) (k : ℕ → ℕ) : Prop :=
  -- `T` includes pending inside queries among its outputs.
  ∀ T : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l)),
    Replies α (T.map Prod.fst) (T.map Prod.snd) →
      (insideQueries (T.map Prod.snd)).length ≤ k (outsideInputs (T.map Prod.fst)).length

end SystemAlgebra
