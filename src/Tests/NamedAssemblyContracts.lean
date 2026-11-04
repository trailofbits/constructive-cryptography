module

public import Commons.Definitions.ReplyTransform
public import ConstructiveCryptography.Tactics.Substitution

/-!
# Contracts through named assemblies

Client definitions name a source and its reply transformation. Ordinary rewriting applies the
public contracts after opening those definitions, including under an arbitrary outer attachment.
Scalar allowances become constant per-port functions; incompatible allowances and domains fail.
The selected-test transport uses `d.absorb α` directly and requires explicit admission closure.
-/

@[expose] public section

namespace Tests.NamedAssemblyContracts

open Commons Commons.Evaluation ConstructiveCryptography SystemAlgebra Probability.Distribution

-- `S` carries finite nonempty seeds; `X`, `Y` carry finite replies.
variable {S X Y : Type} [Fintype S] [Nonempty S] [Fintype X] [Fintype Y]

/-- The evaluation interface returning `X` on at most `q` triggers. -/
abbrev samples (X : Type) [Fintype X] (q : ℕ) : Interface :=
  Evaluation.perPort Unit X (fun _ => q)

/-- Each trigger returns `F s` for an independent uniform seed `s : S`. -/
noncomputable def generated (F : S → X) (q : ℕ) : TypedSystem (samples X q) :=
  MemorylessSource.perPort X ((𝒰[S]).map F) (budget := fun _ => q)

/-- Attach the reusable reply map `f` to the named fresh-seed source. -/
noncomputable def mapped (f : X → Y) (F : S → X) (q : ℕ) : TypedSystem (samples Y q) :=
  mapReplies f (fun _ => q) • generated F q

/-- A named assembly rewrites under an arbitrary outer converter without interface casts. -/
lemma mapped_in_context
    -- `C` is the outer interface; `α` encloses the mapped source with allowance `q`.
    {C : Interface} (q : ℕ) (α : TypedConverter C (samples Y q))
    -- `F` computes a source reply and `f` transforms it.
    (F : S → X) (f : X → Y) :
    α • mapped f F q = α • generated (f ∘ F) q := by
  unfold mapped generated
  rw [mapReplies_smul_memorylessSource, ProbDist.map_map]

/-- Each trigger draws `b` independently of the source seed `s`, then returns `g (f b (F s))`.
The outer map `g` is deterministic. -/
example (q : ℕ) (F : S → X) (f : Bool → X → Y) (g : Y → X) :
    mapReplies g (fun _ => q) •
        (sampleReplies 𝒰[Bool] f (fun _ => q) • generated F q) =
      MemorylessSource.perPort X
        (((prodProbDist 𝒰[Bool] ((𝒰[S]).map F)).map (fun bx => f bx.1 bx.2)).map g)
        (budget := fun _ => q) := by
  unfold generated
  rw [sampleReplies_smul_memorylessSource, mapReplies_smul_memorylessSource]

-- An extra outside call cannot be hidden by an interface alias.
example (_q : ℕ) (_f : X → Y) : True := by
  fail_if_success
    have bad : TypedConverter (samples Y (_q + 1)) (samples X _q) :=
      mapReplies _f (fun _ => _q)
  trivial

-- A resource restricted to no admitted histories cannot fill an unrestricted inside interface.
example (q : ℕ) (_f : X → Y)
    (_R : TypedSystem (Interface.restrict (samples X q) (fun _ => False)
      (fun _ _ _ h => h))) : True := by
  fail_if_success
    have bad : TypedSystem (samples Y q) := mapReplies _f (fun _ => q) • _R
  trivial

/-- Typed test absorption is the public loss expression; admission closure remains explicit. -/
example [AdmissibleDistinguishers Interface TypedDistinguisher]
    -- `α` exposes `A` while using the systems on `B`.
    {A B : Interface} (α : TypedConverter A B)
    -- `closed` preserves the selected test class through this particular converter.
    (closed : AdmissibleDistinguishers.ClosedUnder
      (Phi := TypedSystem) (D := TypedDistinguisher) α)
    -- `h` bounds the inside comparison by `ε`, evaluated at each admitted inside test.
    {R T : TypedSystem B} {ε : TypedDistinguisher B → ENNReal} (h : R ≃[ε] T) :
    α • R ≃[fun d => ε (d.absorb α)] α • T :=
  TypedConverter.substitutesWithin_attach α closed h

#print axioms mapped_in_context
#print axioms TypedConverter.substitutesWithin_attach

end Tests.NamedAssemblyContracts
