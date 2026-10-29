import RandomSystems.Typed.Interface
import RandomSystems.Game.MBOAttachment

/-!
# Typed games

A typed game on an interface `A` is a typed system on the interface of `A` with the MBO whose
MBO, once set, stays set (`RandomSystem.MonotoneMBO`): a game in the sense of CR18, §3.7.1. A
typed converter attaches to it through its MBO-forwarding lift `PDCBehavior.liftMBO`, which
keeps games games (`RandomSystem.MonotoneMBO.attach_liftMBO`), and its visible typed system is
the visible system `RandomSystem.visible`. Game attachment satisfies the attachment laws:
`id • G = G` and `(comp α β) • G = α • (β • G)`, since the lift is functorial
(`PDCBehavior.liftMBO_id`, `PDCBehavior.liftMBO_comp`).

## Main definitions

* `Interface.withMBO A`: the interface of `A` with the MBO
* `TypedGame A`: typed games on `A`
* `TypedConverter.attachGame α G`: a typed converter attached to a typed game
* `TypedGame.visible G`: the visible typed system of a typed game

## Main results

* `TypedConverter.identity_attachGame`, `TypedConverter.comp_attachGame`: the identity and
  serial laws of game attachment
-/

namespace SystemAlgebra

/-- The interface of `A` with the MBO: its replies carry the MBO. -/
abbrev Interface.withMBO (A : Interface) : Interface where
  I := A.I
  X := A.X
  Y := SystemAlgebra.withMBO A.Y
  domain := A.domain
  nonempty_prefix := A.nonempty_prefix
  bound := A.bound
  length_le := A.length_le

/-- **Typed games** on `A`: typed systems on the interface of `A` with the MBO whose MBO, once
set, stays set. -/
def TypedGame (A : Interface) := {G : TypedSystem A.withMBO // G.1.MonotoneMBO}

/-- A typed converter attached to a typed game: its lift attached to the game's typed system. -/
noncomputable def TypedConverter.attachGame {A B : Interface} (α : TypedConverter A B)
    (G : TypedGame B) : TypedGame A :=
  -- The lift runs `α` on the replies of `G` without their MBO and tags each outside reply
  -- with the MBO `a` of the latest reply of `G`:
  --
  --   ──x────▶ ┌───────────┐ ──u────▶ ┌───┐
  --            │ liftMBO α │          │ G │
  --   ◀─(y,a)─ └───────────┘ ◀─(v,a)─ └───┘
  --
  -- The result is again a game, its MBO once set stays set
  -- (`RandomSystem.MonotoneMBO.attach_liftMBO`).
  ⟨TypedConverter.attach (A := A.withMBO) (B := B.withMBO) (PDCBehavior.liftMBO α) G.1,
    G.2.attach_liftMBO B.nonempty_prefix A.nonempty_prefix α G.1.2⟩

/-- Attaching the identity converter leaves the game unchanged: `id • G = G`.
The MBO lift preserves identity, so identity attachment applies to the underlying system. -/
lemma TypedConverter.identity_attachGame {A : Interface} (G : TypedGame A) :
    TypedConverter.attachGame (TypedConverter.id A) G = G := by
  apply Subtype.ext
  change TypedConverter.attach (PDCBehavior.liftMBO (TypedConverter.id A)) G.1 = G.1
  rw [show PDCBehavior.liftMBO (TypedConverter.id A) = TypedConverter.id A.withMBO from
    PDCBehavior.liftMBO_id _]
  exact TypedConverter.identity_attach G.1

/-- Serial attachment groups the same wiring from the game end: `(αβ)G = α(βG)`.
The MBO lift preserves composition, so serial attachment applies to the underlying system. -/
lemma TypedConverter.comp_attachGame {A B C : Interface} (α : TypedConverter A B)
    (β : TypedConverter B C) (G : TypedGame C) :
    TypedConverter.attachGame (TypedConverter.comp α β) G =
      TypedConverter.attachGame α (TypedConverter.attachGame β G) := by
  -- Lift the serial converter, then apply serial attachment to the underlying typed system.
  apply Subtype.ext
  change TypedConverter.attach (PDCBehavior.liftMBO (TypedConverter.comp α β)) G.1 =
    TypedConverter.attach (A := A.withMBO) (PDCBehavior.liftMBO α)
      (TypedConverter.attach (A := B.withMBO) (PDCBehavior.liftMBO β) G.1)
  rw [show PDCBehavior.liftMBO (TypedConverter.comp α β) =
    TypedConverter.comp (A := A.withMBO) (B := B.withMBO) (C := C.withMBO)
      (PDCBehavior.liftMBO α) (PDCBehavior.liftMBO β) from PDCBehavior.liftMBO_comp α β]
  exact TypedConverter.comp_smul _ _ G.1

/-- The visible typed system of a typed game. -/
noncomputable def TypedGame.visible {A : Interface} (G : TypedGame A) : TypedSystem A :=
  ⟨G.1.1.visible, G.1.2.visible⟩

end SystemAlgebra
