module

public import RandomSystems.Game.MBOAttachment
public import RandomSystems.Converter.QueryRouting
public import RandomSystems.Converter.CallRelabel

/-!
# Routing a game's monotone bit

`PDCBehavior.liftMBO_ofDDC_routingConverter` identifies a lifted router with routing that
returns `(answer u y, b)` on the inside reply `(y,b)`. The request, domains and call bounds
are unchanged. The comparison uses legal shared converter transcripts: a pending invocation
has no prior reply, so the bit of its single reply is also the latest inside bit.
-/

@[expose] public section

namespace SystemAlgebra

-- `O`, `J` carry outside and inside ports, with query/reply alphabets `U`, `V` and `X`, `Y`.
variable {O J : Type} [Fintype O] [Fintype J] {U V : O → Type} {X Y : J → Type}
  [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] [∀ j, Fintype (X j)] [∀ j, Fintype (Y j)]
  -- `E`, `F` select the inside and outside query histories, bounded by `m`, `n`.
  {E : List (Σ j, X j) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
  {F : List (Σ o, U o) → Prop} {n : ℕ} {hF : ∀ h, F h → h.length ≤ n}

/-- Lifting a router forwards the same inside MBO: `(y,b) ↦ (answer u y,b)`. -/
theorem PDCBehavior.liftMBO_ofDDC_routingConverter
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)
    -- Both certificates retain the selected domains; only the answer alphabets carry MBOs.
    {b c : ℕ} (ha : IsDDCFrom E F b (routingConverter request answer F))
    (hb : IsDDCFrom E F c (routingConverter (V := withMBO V) request
      (fun u (r : Σ j, withMBO Y j) => (answer u (forgetMBO r), r.2.2)) F)) :
    PDCBehavior.liftMBO
        (PDCBehavior.ofDDC (routingConverter request answer F) ha :
          PDCBehavior O J U V X Y E m hE F n hF) =
      PDCBehavior.ofDDC (routingConverter (V := withMBO V) request
        (fun u (r : Σ j, withMBO Y j) => (answer u (forgetMBO r), r.2.2)) F) hb := by
  rw [PDCBehavior.liftMBO_ofDDC]
  apply PDCBehavior.ofDDC_eq_of_next_eq ha.liftMBO hb
  intro t z hleft hright legal
  have hda := (ha.liftMBO.answers t z hleft).mpr legal
  have hdb := (hb.answers t z hright).mpr legal
  rw [liftMBO_dom] at hda
  simp only [routingConverter, callConverter, filterDom_dom, canon_dom_iff] at hda hdb
  -- On their common domain, both certified presentations use their original call rule.
  dsimp only [SystemAlgebra.liftMBO, routingConverter, callConverter]
  rw [filterDom, ite_eq_left hda.1, canon_of_admissible hda.2.1,
    filterDom, ite_eq_left hdb.1, canon_of_admissible hdb.2.1]
  rcases z with ⟨⟨_ | ⟨⟩, j⟩, z⟩
  · simp only [callRule, List.map_append, List.map_singleton, List.reverse_append,
      List.reverse_singleton, List.singleton_append, insideMap, currentCall,
      routingCall, Part.map_some, outsideMap]
  · obtain ⟨u, pending⟩ := callConverter_currentCall_of_admits_inside
      (routingCall (V := withMBO V) request (fun u (r : Σ j, withMBO Y j) =>
        (answer u (forgetMBO r), r.2.2)))
      (fun u rs h => List.length_eq_zero_iff.mp
        (Nat.lt_one_iff.mp ((routingCall_phase request u _ rs).mp h)))
      F t hright ⟨j, z⟩ legal.2.1
    -- Forgetting bits preserves this invocation and its empty reply list.
    have forgotten : currentCall
        ((t.map Prod.fst).map (insideMap forgetMBO)).reverse [] = some (u, []) := by
      rw [← List.map_reverse]
      simpa only [List.map_nil, pending, Option.map_some] using
        currentCall_insideMap forgetMBO (t.map Prod.fst).reverse []
    have pendingReply : currentCall (t.map Prod.fst).reverse [⟨j, z⟩] =
        some (u, [⟨j, z⟩]) := by rw [currentCall_acc, pending]; rfl
    have forgottenReply : currentCall
        ((t.map Prod.fst).map (insideMap forgetMBO)).reverse [forgetMBO ⟨j, z⟩] =
        some (u, [forgetMBO ⟨j, z⟩]) := by rw [currentCall_acc, forgotten]; rfl
    simp only [forgetMBO] at forgottenReply
    simp only [callRule, List.map_append, List.map_singleton, List.reverse_append,
      List.reverse_singleton, List.singleton_append, insideMap, currentCall,
      pendingReply, forgottenReply,
      routingCall, Part.map_some, outsideMap, latestMBO_snoc, inputMBO,
      Option.getD_some, tagMBO, forgetMBO]

end SystemAlgebra
