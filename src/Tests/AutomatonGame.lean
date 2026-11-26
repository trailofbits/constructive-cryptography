module

public import Tests.GameTranscript

/-!
# Automaton scores from their initial law

The echo game reuses the adaptive observer from `Tests.GameTranscript`. A fair retained
Boolean also determines the monitor: its score is `1/2` after interaction and `0` on immediate
stopping. The same observer's score law is checked at two certified horizons.
-/

@[expose] public section

namespace Tests.AutomatonGame

open SystemAlgebra Probability Probability.Distribution Tests.GameTranscript

/-- The actual adaptive winner's two-query bound is preserved by its decision-producing form. -/
lemma winner_bounded : QueryBounded 2 (ddeOf winner_isDDD) :=
  ddeOf_envProbe_queryBounded adaptive_bounded _

/-- The initial state is sampled once; both certified horizons give the same condition mass. -/
example : let G := TypedGame.ofAutomaton port echo (ProbDist.single ()) (fun _ => always)
    G.1.1.winProbability winner winner_isDDD =
      (ProbDist.single ()).1.mass (fun s =>
        let h := (port.automatonDDS echo s).1.tr (ddeOf winner_isDDD).1 2
        h ≠ [] ∧ always.1 (h.map Prod.fst)) ∧
    G.1.1.winProbability winner winner_isDDD =
      (ProbDist.single ()).1.mass (fun s =>
        let h := (port.automatonDDS echo s).1.tr (ddeOf winner_isDDD).1 3
        h ≠ [] ∧ always.1 (h.map Prod.fst)) := by
  have admitted := Domain.envProbe_decisionCompatible adaptive_compatible (fun _ => True)
  constructor
  · exact TypedGame.winProbability_ofAutomaton_at_bound _ _ _ _ _ _ admitted winner_bounded
  · exact TypedGame.winProbability_ofAutomaton_at_bound _ _ _ _ _ _ admitted
      (fun ys hd => (winner_bounded ys hd).trans_le (by omega))

/-- Echo each query while retaining the initially sampled Boolean state. -/
def retainedEcho (b : Bool) (_ : port.I) (x : port.X ()) : Bool × port.Y () := (b, x)

/-- The monitor is true exactly for the retained initial value `true`. -/
def initialTrue (b : Bool) : MC (Σ i, port.X i) :=
  ⟨fun _ => b = true, fun _ _ _ h => h⟩

/-- A fair initial Boolean is retained by the resource and by its monitor. -/
noncomputable def coinGame : TypedGame port :=
  TypedGame.ofAutomaton port retainedEcho 𝒰[Bool] initialTrue

/-- The visible transcript does not depend on the retained Boolean. -/
lemma retained_transcript (b : Bool) :
    (port.automatonDDS retainedEcho b).1.tr (ddeOf winner_isDDD).1 2 =
      [(⟨(), false⟩, ⟨(), false⟩), (⟨(), true⟩, ⟨(), true⟩)] := by
  have first : (ddeOf winner_isDDD).1 [] = Part.some ⟨(), false⟩ := by
    change envOf (trim (envProbe adaptive (fun _ => True))) [] = _
    rw [envOf_trim_envProbe EFits.nil]
    rfl
  have second : (ddeOf winner_isDDD).1 [⟨(), false⟩] = Part.some ⟨(), true⟩ := by
    have fits : EFits adaptive.1 [⟨(), false⟩] :=
      EFits.snoc EFits.nil
        (show (⟨(), false⟩ : Σ i, port.X i) ∈ adaptive.1 [] from Part.mem_some _) rfl
    exact (envOf_trim_envProbe (A := fun _ => True) fits).trans rfl
  simp only [port, Interface.queryBudget, ne_eq, System.tr, List.map_nil, first,
    Part.some_dom, ↓reduceDIte, Interface.automatonDDS, Part.get_some, List.nil_append,
    filterDom, List.cons_ne_self, not_false_eq_true, List.length_cons, List.length_nil,
    zero_add, Nat.one_le_ofNat, and_self, ↓reduceIte, automatonSystem, retainedEcho,
    List.dropLast_singleton, stateAfter_nil, Sigma.eta, List.getLast?_singleton,
    Option.map_some, Part.coe_some, List.map_cons, second, List.cons_append, reduceCtorEq,
    Nat.reduceAdd, Std.le_refl, List.dropLast_cons_cons, List.getLast?_cons_cons]

/-- After legal interaction, exactly the retained `true` half of the initial law wins. -/
example : coinGame.1.1.winProbability winner winner_isDDD = 1 / 2 := by
  have admitted := Domain.envProbe_decisionCompatible adaptive_compatible (fun _ => True)
  refine (TypedGame.winProbability_ofAutomaton_at_bound port retainedEcho 𝒰[Bool]
    initialTrue winner winner_isDDD admitted winner_bounded).trans ?_
  have event (b : Bool) :
      ((port.automatonDDS retainedEcho b).1.tr (ddeOf winner_isDDD).1 2 ≠ [] ∧
        (initialTrue b).1
          (((port.automatonDDS retainedEcho b).1.tr (ddeOf winner_isDDD).1 2).map Prod.fst)) ↔
        b = true := by
    rw [retained_transcript]
    exact and_iff_right (List.cons_ne_nil _ _)
  rw [mass_congr _ event]
  simp only [ProbDist.uniform, mass_singleton, uniform_apply, Fintype.card_bool, Nat.cast_ofNat]

/-- An environment with no queries stops before any bit can be emitted. -/
def stop : DDE (Σ i, port.X i) (Σ i, port.Y i) := DDE.ofQueries []

lemma stop_bound : QueryBounded 0 stop := by
  intro ys hd
  simpa only [stop, DDE.ofQueries, fixedQueries, Part.ofOption_dom,
    isSome_getElem?, List.length_nil] using hd

/-- The stopping probe is a certified winner, even though it makes no query. -/
noncomputable def stopped : DDD port.I port.X port.Y := envProbe stop (fun _ => True)

lemma stopped_isDDD : IsDDD stopped := envProbe_isDDD stop_bound

lemma stopped_bound : QueryBounded 0 (ddeOf stopped_isDDD) :=
  ddeOf_envProbe_queryBounded stop_bound _

/-- Initial truth does not score when the observer stops before the first reply. -/
example : coinGame.1.1.winProbability stopped stopped_isDDD = 0 := by
  have compatible : port.inputDomain.Compatible stop := by
    intro _ _ h x _ _ hx
    exact False.elim (Nat.not_lt_zero _
      (stop_bound (h.map Prod.snd) (Part.dom_iff_mem.mpr ⟨x, hx⟩)))
  have admitted := Domain.envProbe_decisionCompatible compatible (fun _ => True)
  refine (TypedGame.winProbability_ofAutomaton_at_bound port retainedEcho 𝒰[Bool]
    initialTrue stopped stopped_isDDD admitted stopped_bound).trans ?_
  simp only [System.tr, ne_eq, not_true_eq_false, false_and]
  exact mass_eq_zero_of_forall_not _ (fun _ h => h)

#print axioms TypedGame.winProbability_ofAutomaton_at_bound

end Tests.AutomatonGame
