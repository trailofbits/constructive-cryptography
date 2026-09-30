import RandomSystems.Cumulative.ConnectionObservation

/-!
# Connection of random systems

The connection of two independent random systems is a random system on a domain
when every deterministic connection of their presenting samples answers exactly
on it.

## Main definitions

* `RandomSystem.connection`: the connection of two random systems

## Main results

* `connection_isRandomSystem`: the connection is a random system
* `connection_replies`: every possible transcript comes from deterministic components
-/

namespace SystemAlgebra.RandomSystem

open Classical Probability

variable {A B X Y X' Y' : Type} [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
  [Fintype X'] [Fintype Y'] {D : Domain X Y} {D' : Domain X' Y'} {E : Domain A B}
  (R : RandomSystem X Y D) (S : RandomSystem X' Y' D')
  (route : Two Y Y' → B ⊕ Two X X') (inj : A → Two X X')
  (bound : List A → ℕ)
  {p : System X Y → Prop} {q : System X' Y' → Prop}
  (hp : ∀ g, R.2.isSubprobabilistic.PossibleChoice g → p (realization g).1)
  (hq : ∀ g, S.2.isSubprobabilistic.PossibleChoice g → q (realization g).1)
  (hb : ∀ a b, p a → q b → ∀ us xs ys,
    Transcript (pair a b) (connectionQueries route inj us) xs ys →
    ¬ (connectionQueries route inj us ys).Dom → ys.length ≤ bound us)
  (hE : ∀ a b, p a → q b → ∀ h x,
    Replies (interconnect (pair a b) route inj) (h.map Prod.fst) (h.map Prod.snd) →
    ((interconnect (pair a b) route inj (h.map Prod.fst ++ [x])).Dom ↔ E h x))

include hp hq hb hE

/-- Independent finite presentations of the components present the connection;
its samples answer exactly on the specified domain. -/
theorem connection_isRandomSystem : IsRandomSystem E (fun h =>
    (parallel R S).connectionLaw route inj (h.map Prod.fst) (bound (h.map Prod.fst))
      (h.map Prod.snd)) := by
  obtain ⟨P, Q, he⟩ := exists_parallel_connection_presentations R S route inj bound p q hp hq hb
  let attach : {s : System X Y // p s} × {s : System X' Y' // q s} →
      {s : System A B // True} :=
    fun st => ⟨interconnect (pair st.1.1 st.2.1) route inj, trivial⟩
  let M := Distribution.fTransform attach (Distribution.prod P.1 Q.1)
  have hM : M.isProbDist :=
    Distribution.fTransform_isProbDist _ (Distribution.prod_isProbDist P.1 Q.1 P.2 Q.2)
  have hD : ∀ s ∈ M.support, ∀ h x, Replies s.1 (h.map Prod.fst) (h.map Prod.snd) →
      ((s.1 (h.map Prod.fst ++ [x])).Dom ↔ E h x) := by
    intro s hs h x hr
    obtain ⟨st, _, rfl⟩ := Distribution.mem_support_fTransform _ _ hs
    exact hE st.1.1 st.2.1 st.1.2 st.2.2 h x hr
  have hfun : (fun h => (parallel R S).connectionLaw route inj (h.map Prod.fst)
      (bound (h.map Prod.fst)) (h.map Prod.snd)) = (ofPDS M hM hD).1 := by
    funext h
    change _ = M.mass (fun s => Replies s.1 (h.map Prod.fst) (h.map Prod.snd))
    rw [Distribution.mass_fTransform]
    exact he (h.map Prod.fst) (h.map Prod.snd)
  rw [hfun]
  exact (ofPDS M hM hD).2

/-- Attachment on cumulative behavior uses the existing deterministic
connection, with its proved bound and admission condition. -/
noncomputable def connection : RandomSystem A B E :=
  ⟨fun h => (parallel R S).connectionLaw route inj (h.map Prod.fst)
    (bound (h.map Prod.fst)) (h.map Prod.snd),
    connection_isRandomSystem R S route inj bound hp hq hb hE⟩

theorem connection_mass (h : List (A × B)) :
    connection R S route inj bound hp hq hb hE h =
      (parallel R S).connectionLaw route inj (h.map Prod.fst)
        (bound (h.map Prod.fst)) (h.map Prod.snd) := rfl

/-- Every possible finite attached history is witnessed by deterministic
components in the same classes. -/
theorem connection_replies {h : List (A × B)}
    (hh : connection R S route inj bound hp hq hb hE h ≠ 0) :
    ∃ a b, p a ∧ q b ∧
      Replies (interconnect (pair a b) route inj) (h.map Prod.fst) (h.map Prod.snd) := by
  obtain ⟨P, Q, he⟩ := exists_parallel_connection_presentations R S route inj
    bound p q hp hq hb
  rw [connection_mass, he] at hh
  by_contra hn
  apply hh
  exact Distribution.mass_eq_zero_of_forall_not _
    (fun st hr => hn ⟨st.1.1, st.2.1, st.1.2, st.2.2, hr⟩)

end SystemAlgebra.RandomSystem
