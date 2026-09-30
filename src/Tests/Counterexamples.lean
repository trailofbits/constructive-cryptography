import RandomSystems.DDC.Serial

/-!
# The hypotheses of the laws are needed

Witnesses for `papers/SYSTEM_ALGEBRA_SPEC.md`, §6:

1. locality (C3, `parAll_interconnect`) fails without convergence (`spinner`);
2. the identity law (I, `attachAlong_forwardAll`) fails without reactivity.
-/

namespace SystemAlgebra.Counterexamples

open SystemAlgebra

/-! ## 1. Without termination, locality fails -/

/-- Reactive; after any input it feeds its output back to itself. -/
def spinner : System Unit Unit := fun h => if h = [] then Part.none else Part.some ()

/-- Reactive; answers every input. -/
def echo : System Unit Unit := fun h => if h = [] then Part.none else Part.some ()

/-- `spinner`'s only output is fed back. -/
def spinRoute : Unit → Empty ⊕ Unit := fun _ => .inr ()

/-- Once `spinner` has received an input, the exchange of the composite never stops. -/
theorem spinner_no_exchange {H : List (Σ o, optF Unit (fun _ : Unit => Unit) o)} {o H'}
    (l : Exchange (parAll (optS spinner fun _ : Unit => echo))
      (routeOpt (B := fun _ : Unit => Unit) spinRoute) H o H') :
    ∀ H₁ (x : Unit), H = H₁ ++ [⟨none, x⟩] → False := by
  induction l with
  | silent h hd =>
    rintro H₁ x rfl
    apply hd
    rw [parAll_snoc]
    simp [optS, spinner]
  | out h y b hy hr =>
    rintro H₁ x rfl
    rw [parAll_snoc] at hy
    obtain ⟨y', -, rfl⟩ := Part.mem_map_iff _ |>.mp hy
    simp [routeOpt, spinRoute] at hr
  | feed h y x o h' hy hr _ ih =>
    rintro H₁ x₀ rfl
    rw [parAll_snoc] at hy
    obtain ⟨y', -, rfl⟩ := Part.mem_map_iff _ |>.mp hy
    simp only [routeOpt, spinRoute, Sum.elim_inr, Sum.inr.injEq] at hr
    exact ih _ _ (by rw [← hr])

/-- **Locality fails for a non-terminating component.** -/
theorem locality_fails_without_termination :
    parAll (optS (interconnect spinner spinRoute id) fun _ : Unit => echo) ≠
      interconnect (parAll (optS spinner fun _ : Unit => echo))
        (routeOpt (B := fun _ : Unit => Unit) spinRoute) (injOpt (A := fun _ : Unit => Unit) id) := by
  intro e
  have := congrFun e [⟨none, ()⟩, ⟨some (), ()⟩]
  -- left: `echo` still answers
  have hl : parAll (optS (interconnect spinner spinRoute id) fun _ : Unit => echo)
      [⟨none, ()⟩, ⟨some (), ()⟩] = Part.some ⟨some (), ()⟩ := by
    rw [show ([⟨none, ()⟩, ⟨some (), ()⟩] : List (Σ o, optF Unit (fun _ : Unit => Unit) o)) =
      [⟨none, ()⟩] ++ [⟨some (), ()⟩] from rfl, parAll_snoc]
    simp [optS, echo]
  -- right: the exchange after the first input never finishes
  have hr : ¬ (interconnect (parAll (optS spinner fun _ : Unit => echo))
      (routeOpt (B := fun _ : Unit => Unit) spinRoute) (injOpt (A := fun _ : Unit => Unit) id)
      [⟨none, ()⟩, ⟨some (), ()⟩]).Dom := by
    intro d
    obtain ⟨H, r⟩ := mem_interconnect.mp (Part.get_mem d)
    obtain ⟨_, H₀, r₀, -⟩ := induces_snoc_iff.mp
      (show Induces _ _ _ ([(⟨none, ()⟩ : Σ o, optF Unit (fun _ : Unit => Unit) o)] ++
        [⟨some (), ()⟩]) _ H from r)
    obtain ⟨_, W, rW, l⟩ := induces_snoc_iff.mp
      (show Induces _ _ _ ([] ++ [(⟨none, ()⟩ : Σ o, optF Unit (fun _ : Unit => Unit) o)]) _ _ from r₀)
    obtain ⟨-, rfl⟩ := induces_nil_iff.mp rW
    exact spinner_no_exchange l [] () rfl
  rw [hl] at this
  exact hr (this ▸ trivial)

/-! ## 2. Without reactivity, the identity law fails -/

/-- Speaks first on its only interface, then stays silent. -/
def talker : InterfaceSystem Unit (fun _ => Unit) (fun _ => Unit) := fun h =>
  if h = [] then Part.some ⟨(), ()⟩ else Part.none

/-- **The identity law fails for a system that speaks first**: connection
never consults the empty history. -/
theorem identity_fails_without_reactivity :
    relabel (attachAlong (id : Unit → Unit) (forwardAll Unit (fun _ => Unit) (fun _ => Unit)) talker)
      (idAlongIn (Y := Unit) id) (idAlongOut id) ≠ talker := by
  intro e
  have := congrFun e []
  have hr := silentAtEmpty_attachAlong (ι := (id : Unit → Unit))
    (forwardAll Unit (fun _ => Unit) (fun _ => Unit)) talker
  simp only [relabel, List.map_nil] at this
  rw [Part.eq_none_iff'.mpr hr] at this
  simp [talker] at this

end SystemAlgebra.Counterexamples
