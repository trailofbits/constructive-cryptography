module

public import RandomSystems.Cumulative.Presentation.Basic
public import Probability.Kernel

/-!
# Explicit supported-table presentations

`IsSubprobabilistic.presentationSample` realizes each supported table of conditional choices.
Its off-support branch uses a supported default table. `presentation` pushes the independent
choice-table law through that same map, so only the supported branch contributes probability.
-/

@[expose] public section

namespace SystemAlgebra.IsSubprobabilistic

open Probability Probability.Distribution Presentation

-- `hp` supplies the conditional choice laws for cumulative masses `p` over alphabets `A`, `B`.
variable {A B : Type} [Fintype A] [Fintype B]
variable {p : List (A × B) → ℝ} (hp : IsSubprobabilistic p) {n : ℕ}

open Classical in
/-- Realize supported tables, using a supported default for tables of probability zero. -/
noncomputable def presentationSample
    -- `hn` bounds the behavior; `P` is a property certified for every possible realization.
    (hn : ∀ h, n < h.length → p h = 0) (P : System A B → Prop)
    -- `hP` certifies all possible realizations; `c` chooses replies at nodes before `n`.
    (hP : ∀ g, hp.PossibleChoice g → P (realization g).1)
    (c : Node A B n → Option B) : {s : System A B // P s} :=
  if hc : c ∈ (hp.choiceLaw n).support then
    ⟨(realization (choiceAt c)).1, hP _ (hp.choiceAt_supported hn hc)⟩
  else
    ⟨(realization (choiceAt (hp.choiceLaw_support_nonempty n).choose)).1,
      hP _ (hp.choiceAt_supported hn (hp.choiceLaw_support_nonempty n).choose_spec)⟩

/-- Sample the independent conditional-choice table and return its certified realization. -/
noncomputable def presentation
    -- `hn` bounds the behavior; `hP` certifies the property `P` for possible realizations.
    (hn : ∀ h, n < h.length → p h = 0) (P : System A B → Prop)
    (hP : ∀ g, hp.PossibleChoice g → P (realization g).1) : ProbDist {s : System A B // P s} :=
  ProbDist.map (hp.presentationSample hn P hP) ⟨hp.choiceLaw n, hp.choiceLaw_isProbDist n⟩

end SystemAlgebra.IsSubprobabilistic
