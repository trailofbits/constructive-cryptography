module

public import RandomSystems.Converter.ConverterAttachment
public import RandomSystems.Cumulative.ConnectionObservation

/-!
# Equality outside an event under attachment

`PDCBehavior.attach_apply_eq_of_not_bad` transports component equality through a converter.
An inside bad event must imply the outside bad event on completed interactions supported by
either compared system. On an outside good transcript, the common converter factor then
multiplies equal component coefficients; connection-fiber equality collects those coefficients.
-/

@[expose] public section

namespace SystemAlgebra.PDCBehavior

/-- Component equality off `badIn` survives attachment off `badOut`, provided completed
interactions reflect the inside event on the union of the two joint supports. -/
theorem attach_apply_eq_of_not_bad
    -- `O,U,V` are the outside ports, queries and replies; `J,X,Y` are their inside counterparts.
    {O J : Type} [Fintype O] [Fintype J] {U V : O → Type} {X Y : J → Type}
    [∀ o, Fintype (U o)] [∀ o, Fintype (V o)]
    [∀ j, Fintype (X j)] [∀ j, Fintype (Y j)]
    -- `E,F` admit inside and outside input histories, bounded by `m,n` respectively.
    {E : List (Σ j, X j) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
    {F : List (Σ o, U o) → Prop} {n : ℕ} {hF : ∀ h, F h → h.length ≤ n}
    (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (α : PDCBehavior O J U V X Y E m hE F n hF)
    (R S : RandomSystem (Σ j, X j) (Σ j, Y j) (Domain.ofInputs E m hE))
    (hR : R.RepliesAtQueriedInterface) (hS : S.RepliesAtQueriedInterface)
    -- `badIn,badOut` are transcript predicates; `same` compares the components off `badIn`.
    (badIn : List ((Σ j, X j) × (Σ j, Y j)) → Prop)
    (badOut : List ((Σ o, U o) × (Σ o, V o)) → Prop)
    (same : ∀ u, ¬ badIn u → R u = S u)
    (h : List ((Σ o, U o) × (Σ o, V o)))
    -- `reflect` concerns only completed interactions exposing `h`, within attachment's horizon.
    (reflect : ∀ t,
      FollowsStrategy (connectionQueries resourceRoute resourceInput (h.map Prod.fst)) t →
      t.length ≤ (2 * α.2.choose + 2) * (h.map Prod.fst).length →
      ¬ (connectionQueries resourceRoute resourceInput (h.map Prod.fst)
        (t.map Prod.snd)).Dom →
      exposedReplies (resourceRoute (U := U)) (t.map Prod.snd) = h.map Prod.snd →
      (RandomSystem.parallel α.1 R t ≠ 0 ∨ RandomSystem.parallel α.1 S t ≠ 0) →
      badIn (RandomSystem.parallelRight t) → badOut h)
    (good : ¬ badOut h) :
    attach hE' hF' α R hR h = attach hE' hF' α S hS h := by
  change (RandomSystem.parallel α.1 R).connectionLaw resourceRoute resourceInput
      (h.map Prod.fst) ((2 * α.2.choose + 2) * (h.map Prod.fst).length) (h.map Prod.snd) =
    (RandomSystem.parallel α.1 S).connectionLaw resourceRoute resourceInput
      (h.map Prod.fst) ((2 * α.2.choose + 2) * (h.map Prod.fst).length) (h.map Prod.snd)
  apply RandomSystem.connectionLaw_apply_eq_of_completed
  intro t follows bounded stopped exposed
  by_cases supported : RandomSystem.parallel α.1 R t ≠ 0 ∨
      RandomSystem.parallel α.1 S t ≠ 0
  · have insideGood : ¬ badIn (RandomSystem.parallelRight t) :=
      fun bad => good (reflect t follows bounded stopped exposed supported bad)
    -- The converter coefficient is shared; only its component coefficient changes.
    simp only [RandomSystem.parallel_mass, same _ insideGood]
  · push Not at supported
    exact supported.1.trans supported.2.symm

end SystemAlgebra.PDCBehavior
