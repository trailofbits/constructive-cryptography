module

public import RandomSystems.System.Basic

/-!
# Selected inputs through interconnection

`Exchange.filterMap_eq` erases internal feedback from a selected input history.
`Induces.filterMap_eq` then identifies the selected internal history with the corresponding
external inputs, in order. The laws include partial exchanges that end in silence.
`mem_restrict_iff` characterizes membership in one component of a tagged history.

```text
external input a ── inj ──► internal input ── s ──► exposed reply
                              ▲             │
                              └─ feedback ──┘  (erased by project)
```
-/

@[expose] public section

namespace SystemAlgebra

/-- A value occurs in the projected history exactly when its tagged form occurs in the history. -/
lemma mem_restrict_iff
    -- `K` labels components and `A k` is the value type carried by component `k`.
    {K : Type} {A : K → Type}
    -- `k` selects a component from `K`; `a : A k` is a value at that component.
    (k : K) (a : A k)
    -- `xs` retains every component tag, while `restrict k xs` removes the selected tag.
    (xs : List (Σ k, A k)) :
    a ∈ restrict k xs ↔ (⟨k, a⟩ : Σ k, A k) ∈ xs := by
  classical
  induction xs with
  | nil => simp only [restrict_nil, List.not_mem_nil]
  | cons x xs ih =>
    obtain ⟨j, b⟩ := x
    by_cases same : j = k
    · subst j
      simpa only [restrict_cons_self, List.mem_cons, Sigma.mk.inj_iff, heq_eq_eq,
        true_and] using (or_congr Iff.rfl ih)
    · simp only [restrict_cons_ne same, List.mem_cons, Sigma.mk.inj_iff,
        Ne.symm same, false_and, false_or, ih]

variable
  -- `A`, `B` carry external inputs/replies; `X`, `Y` carry internal inputs/outputs.
  {A B X Y : Type} {s : System X Y}
  -- `route` exposes a reply or feeds an input back; `inj` embeds each external input.
  {route : Y → B ⊕ X} {inj : A → X}

/-- Erasing every feedback input leaves the selected history unchanged during an exchange. -/
lemma Exchange.filterMap_eq {Z : Type}
    -- `project` selects observations of internal inputs; feedback contributes none.
    (project : X → Option Z)
    (feedback : ∀ y x, route y = .inr x → project x = none)
    {h o H} (exchange : Exchange s route h o H) :
    H.filterMap project = h.filterMap project := by
  induction exchange with
  | silent => rfl
  | out => rfl
  | feed h y x o H _ routed _ ih =>
    rw [ih, List.filterMap_append]
    simp only [List.filterMap_cons, feedback y x routed, List.filterMap_nil, List.append_nil]

/-- Selected internal inputs are exactly the corresponding external inputs, in order. -/
lemma Induces.filterMap_eq {Z : Type}
    -- `project` observes internal inputs, while `visible` observes the external inputs.
    (project : X → Option Z) (visible : A → Option Z)
    (feedback : ∀ y x, route y = .inr x → project x = none)
    (injected : ∀ a, project (inj a) = visible a)
    {inputs o H} (induced : Induces s route inj inputs o H) :
    H.filterMap project = inputs.filterMap visible := by
  induction induced with
  | nil => rfl
  | snoc inputs a previous H o H' _ exchange ih =>
    calc
      H'.filterMap project = (H ++ [inj a]).filterMap project :=
        exchange.filterMap_eq project feedback
      _ = inputs.filterMap visible ++ [a].filterMap visible := by
        rw [List.filterMap_append, ih]
        simp only [List.filterMap_cons, injected, List.filterMap_nil]
      _ = (inputs ++ [a]).filterMap visible := List.filterMap_append.symm

end SystemAlgebra
