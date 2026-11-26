module

public import RandomSystems.Game.QueryRouting
public import RandomSystems.Typed.Game
public import RandomSystems.Typed.QueryRouting

/-!
# Typed routing with a hidden game bit

`TypedConverter.liftMBO_routing` routes `(y,b)` to `(answer u y,b)`. Its two domain
certificates use the same request map and query histories as the original typed router.
-/

@[expose] public section

namespace SystemAlgebra.TypedConverter

/-- The MBO lift of routing preserves the inside bit on each translated outside reply. -/
lemma liftMBO_routing
    -- `A`, `B` are the outside and inside interfaces; their domains are unchanged by `withMBO`.
    {A B : Interface}
    (request : (Σ o, A.X o) → Σ j, B.X j)
    (answer : (u : Σ o, A.X o) → (Σ j, B.Y j) → A.Y u.1)
    (hmap : ∀ us, A.domain us → B.domain (us.map request)) :
    PDCBehavior.liftMBO (routing request answer hmap) =
      routing (A := A.withMBO) (B := B.withMBO) request
        (fun u r => (answer u (forgetMBO r), r.2.2)) hmap :=
  PDCBehavior.liftMBO_ofDDC_routingConverter request answer _ _

end SystemAlgebra.TypedConverter
