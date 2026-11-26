module

public import RandomSystems.Game.FunctionGame

/-!
# Sampled functional-monitor regression

One retained Boolean sample has weights `1/3` and `2/3`. It determines both the constant
visible reply and the constant hidden condition. The presentation law retains that correlation.
-/

@[expose] public section

namespace SystemAlgebra.Tests.FunctionGame

open Probability Probability.Distribution

/-- One Boolean input and output alphabet at a single port. -/
abbrev Message := Σ _ : Unit, Bool

/-- Nonempty histories of at most two inputs. -/
def domain (xs : List Message) : Prop := xs ≠ [] ∧ xs.length ≤ 2

lemma domain_prefix : ¬ domain [] ∧
    ∀ {p h}, p <+: h → p ≠ [] → domain h → domain p :=
  ⟨fun h => h.1 rfl, fun hp hn hh => ⟨hn, hp.length_le.trans hh.2⟩⟩

/-- `μ(false)=1/3`, `μ(true)=2/3`. -/
noncomputable def law : Distribution Bool :=
  Finsupp.single false (1 / 3) + Finsupp.single true (2 / 3)

/-- Every visible reply returns the retained bit `k`. -/
def reply (k : Bool) (x : Message) : Message := ⟨x.1, k⟩

/-- The condition is true from the outset exactly for sample `k=true`. -/
def condition (k : Bool) : MC Message := ⟨fun _ => k = true, fun _ _ _ h => h⟩

/-- Retain one draw for both the visible function and the hidden condition. -/
noncomputable def samples :=
  PDG.ofFunction domain domain_prefix 2 (fun _ h => h.2) law reply condition

/-- Tagging this sampled game keeps the same draw for the reply and its monitor. -/
lemma tagged_presentation : samples.withMBO =
      PDS.ofFunction domain domain_prefix 2 (fun _ h => h.2)
        (fun k x => tagMBO (decide (k = true)) (reply k x)) law :=
  PDG.withMBO_ofFunction domain domain_prefix 2 (fun _ h => h.2)
    law reply condition (fun k _ => k = true) (fun _ _ _ _ => Iff.rfl)

/-- Both distinct monitor presentations receive positive, unequal weights. -/
example : law false = 1 / 3 ∧ law true = 2 / 3 := by
  simp only [law, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (Ne.symm Bool.false_ne_true),
    Finsupp.single_eq_of_ne Bool.false_ne_true,
    add_zero, zero_add, and_self]

/-- Before any query, every sampled presentation has the empty transcript. -/
example : behaviorMass samples.withMBO [] [] = 1 := by
  classical
  rw [tagged_presentation, behaviorMass, PDS.ofFunction, mass_fTransform]
  simp only [replies_nil]
  rw [mass_true, law, weight_add, weight_single, weight_single]
  norm_num

/-- A third query lies outside the retained two-query domain for every sample. -/
example : behaviorMass samples.withMBO
    [⟨(), false⟩, ⟨(), true⟩, ⟨(), false⟩]
    [⟨(), (false, false)⟩, ⟨(), (false, false)⟩, ⟨(), (false, false)⟩] = 0 := by
  classical
  rw [tagged_presentation, behaviorMass, PDS.ofFunction, mass_fTransform]
  apply mass_eq_zero_of_forall_not
  intro k hr
  rw [DDS.replies_ofFunction_iff] at hr
  rcases hr.1 with empty | admitted
  · cases empty
  · have bound := admitted.2
    simp only [List.length_cons, List.length_nil] at bound
    omega

/-- A visible `false` reply cannot carry the `true` sample's monitor bit. -/
example : behaviorMass samples.withMBO [⟨(), false⟩] [⟨(), (false, true)⟩] = 0 := by
  classical
  rw [tagged_presentation, behaviorMass, PDS.ofFunction, mass_fTransform]
  apply mass_eq_zero_of_forall_not
  intro k hr
  rw [DDS.replies_ofFunction_iff] at hr
  have values : (false, true) = (k, decide (k = true)) :=
    congrArg (fun y : Σ _ : Unit, Bool × Bool => y.2) (List.cons.inj hr.2).1
  cases k <;> cases values

#print axioms PDG.withMBO_ofFunction

end SystemAlgebra.Tests.FunctionGame
