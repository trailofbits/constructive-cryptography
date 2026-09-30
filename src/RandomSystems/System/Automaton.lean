import RandomSystems.System.Observation

/-!
# Automata

A deterministic automaton answers each input from its state, which the answer updates (Maurer
2002, Definition 2, without randomness). Its system answers the last input of a history from
the state the earlier inputs reach; it answers every nonempty history. Bisimilar automata have
the same system.

## Main definitions

* `stateAfter step s h`: the state reached from `s` by the inputs `h`
* `automatonSystem step s`: the system of the automaton started in `s`
* `IsBisim step step' rel`: a bisimulation between two automata

## Main results

* `automatonSystem_snoc`, `automatonSystem_dom`: the reply to the last input, on every
  nonempty history
* `automatonSystem_isDDS`, `automatonSystem_replies`: the system is a DDS replying at the
  queried interface
* `IsBisim.comp`, `isBisim_eq`: bisimulations compose, and equality is one
* `automatonSystem_eq_of_bisim`: bisimilar automata (`IsBisim`) have the same system
-/

namespace SystemAlgebra

variable {I S : Type} {X Y : I → Type} (step : S → (i : I) → X i → S × Y i)

/-- The state reached from `s` by the inputs `h`. -/
def stateAfter (s : S) (h : List (Σ i, X i)) : S :=
  h.foldl (fun s x => (step s x.1 x.2).1) s

@[simp] theorem stateAfter_nil (s : S) : stateAfter step s [] = s := rfl

theorem stateAfter_snoc (s : S) (h : List (Σ i, X i)) (x : Σ i, X i) :
    stateAfter step s (h ++ [x]) = (step (stateAfter step s h) x.1 x.2).1 := by
  simp [stateAfter]

/-- **The system of an automaton** started in `s`: it answers the last input of a history from
the state reached by the earlier inputs. -/
def automatonSystem (s : S) : InterfaceSystem I X Y := fun h =>
  Part.ofOption (h.getLast?.map fun x => ⟨x.1, (step (stateAfter step s h.dropLast) x.1 x.2).2⟩)

@[simp] theorem automatonSystem_nil (s : S) : automatonSystem step s [] = Part.none := rfl

theorem automatonSystem_snoc (s : S) (h : List (Σ i, X i)) (x : Σ i, X i) :
    automatonSystem step s (h ++ [x]) = Part.some ⟨x.1, (step (stateAfter step s h) x.1 x.2).2⟩ := by
  simp [automatonSystem]

theorem automatonSystem_dom (s : S) (h : List (Σ i, X i)) :
    (automatonSystem step s h).Dom ↔ h ≠ [] := by
  rcases List.eq_nil_or_concat h with rfl | ⟨h, x, rfl⟩
  · simp
  · simp [automatonSystem_snoc]

theorem automatonSystem_isDDS (s : S) : IsDDS (automatonSystem step s) := by
  refine ⟨by simp [SilentAtEmpty], fun p h _ hn _ => ?_⟩
  rw [automatonSystem_dom]
  exact hn

theorem automatonSystem_replies (s : S) : RepliesAtQueriedInterface (automatonSystem step s) := by
  intro h x y hy
  rw [automatonSystem_snoc] at hy
  exact congrArg Sigma.fst (Part.mem_some_iff.mp hy)

/-- **A bisimulation** between two automata: a relation between their states that their steps
preserve, while their replies agree. -/
def IsBisim {S' : Type} (step' : S' → (i : I) → X i → S' × Y i) (rel : S → S' → Prop) : Prop :=
  ∀ a a' i x, rel a a' → (step a i x).2 = (step' a' i x).2 ∧ rel (step a i x).1 (step' a' i x).1

/-- Bisimulations compose. -/
theorem IsBisim.comp {S' S'' : Type} {step' : S' → (i : I) → X i → S' × Y i}
    {step'' : S'' → (i : I) → X i → S'' × Y i} {rel : S → S' → Prop} {rel' : S' → S'' → Prop}
    (h : IsBisim step step' rel) (h' : IsBisim step' step'' rel') :
    IsBisim step step'' (fun a a'' => ∃ a', rel a a' ∧ rel' a' a'') := by
  rintro a a'' i x ⟨a', ha, ha'⟩
  obtain ⟨h₁, h₂⟩ := h a a' i x ha
  obtain ⟨h₁', h₂'⟩ := h' a' a'' i x ha'
  exact ⟨h₁.trans h₁', _, h₂, h₂'⟩

/-- Equality is a bisimulation of an automaton with itself. -/
theorem isBisim_eq : IsBisim step step (fun a a' => a = a') := by
  rintro a a' i x rfl
  exact ⟨rfl, rfl⟩

/-- **Bisimilar automata have the same system.** -/
theorem automatonSystem_eq_of_bisim {S' : Type} {step' : S' → (i : I) → X i → S' × Y i}
    {rel : S → S' → Prop} (hb : IsBisim step step' rel) {s : S} {s' : S'} (h₀ : rel s s') :
    automatonSystem step s = automatonSystem step' s' := by
  have hrel : ∀ h : List (Σ i, X i), rel (stateAfter step s h) (stateAfter step' s' h) := by
    intro h
    induction h using List.reverseRecOn with
    | nil => exact h₀
    | append_singleton h x ih =>
      rw [stateAfter_snoc, stateAfter_snoc]
      exact (hb _ _ x.1 x.2 ih).2
  funext h
  rcases List.eq_nil_or_concat h with rfl | ⟨h, x, rfl⟩
  · rfl
  · rw [List.concat_eq_append, automatonSystem_snoc, automatonSystem_snoc,
      (hb _ _ x.1 x.2 (hrel h)).1]

end SystemAlgebra
