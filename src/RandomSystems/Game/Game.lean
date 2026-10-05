import RandomSystems.System.DDE
import RandomSystems.PDS.PDS

/-!
# Discrete games and blind winning

A deterministic game is a DDS paired with a monotone condition on query sequences; a
probabilistic game on a domain is a finite distribution over deterministic games whose
systems have that domain (Lanzenberger, Definitions 2.20–2.22, printed p. 17; with the
common domain of Lanzenberger–Maurer, Definition 8). The environment sees the replies,
not the condition, and wins when it stops on a transcript where the condition holds.
Blinding replaces every reply by `()` and keeps the domain and the condition. On a
domain of input histories all blinded samples are one system, so a blind environment
follows one fixed query sequence: its winning probability is the probability of the
condition on that sequence (Maurer 2013, Definition 7, printed p. 3151: a non-adaptive
environment "ignores the outputs").

## Main definitions

* `MC X`, `DDG X Y`, `PDG X Y D`: monotone conditions, deterministic games, and
  probabilistic games on the domain `D`
* `DDG.Wins e G`, `PDG.winProbability e G`, `PDG.supWinProbability G` (`ν(G)`): winning
* `PDG.underlying G`: the PDS of a game
* `PDG.badProbability`, `PDG.goodProbability`: the condition on a query sequence, and the
  replies jointly with the condition unset
* `DDG.blind`, `PDG.blind`: blinding

## Main results

* `PDG.winProbability_ofQueries_blind`: a fixed admitted query sequence wins the blinded
  game with the probability of the condition on it
* `PDG.badProbability_le_blind`, `PDG.supWinProbability_blind_le`: blind winning is the
  largest probability of the condition on an admitted query sequence
-/

namespace SystemAlgebra

open Classical Probability

/-- A hidden predicate which remains true under extension of the query list. -/
abbrev MC (X : Type) :=
  {bad : List X → Prop // ∀ ⦃h k⦄, h <+: k → bad h → bad k}

/-- A deterministic discrete game: its visible DDS and hidden monotone condition. -/
abbrev DDG (X Y : Type) := DDS X Y × MC X

/-- A probabilistic discrete game on the domain `D`: a finite distribution over
deterministic games whose systems have domain `D`. -/
abbrev PDG (X Y : Type) [Fintype X] [Fintype Y] (D : Domain X Y) :=
  Distribution {g : DDG X Y // HasDomain D g.1.1}

namespace DDG

variable {X Y : Type}

/-- The environment stops after a valid transcript on which the condition holds. -/
def Wins (e : DDE X Y) (G : DDG X Y) : Prop :=
  ∃ xs ys, Transcript G.1.1 e.1 xs ys ∧ ¬ (e.1 ys).Dom ∧ G.2.1 xs

/-- Hide each reply while preserving the system's exact domain. -/
noncomputable def blind (G : DDG X Y) : DDG X Unit :=
  (⟨fun h => (G.1.1 h).map (fun _ => ()), by
      refine ⟨?_, ?_⟩
      · exact G.1.2.1
      · intro p h hp hn hd
        exact G.1.2.2 hp hn hd⟩, G.2)

theorem blind_dom (G : DDG X Y) (h : List X) :
    ((blind G).1.1 h).Dom ↔ (G.1.1 h).Dom := Iff.rfl

end DDG

namespace PDG

variable {X Y : Type} [Fintype X] [Fintype Y]

section Winning

variable {D : Domain X Y}

/-- The PDS of the visible systems. -/
noncomputable def underlying (G : PDG X Y D) : PDS X Y D :=
  Distribution.fTransform (fun g => ⟨g.1.1.1, g.1.1.2, g.2⟩) G

noncomputable def winProbability (e : DDE X Y) (G : PDG X Y D) : ℝ :=
  G.mass (fun g => DDG.Wins e g.1)

noncomputable def badProbability (G : PDG X Y D) (xs : List X) : ℝ :=
  G.mass (fun g => g.1.2.1 xs)

/-- Joint probability of the visible replies and an unset condition. -/
noncomputable def goodProbability (G : PDG X Y D) (h : List (X × Y)) : ℝ :=
  G.mass (fun g => Replies g.1.1.1 (h.map Prod.fst) (h.map Prod.snd) ∧
    ¬ g.1.2.1 (h.map Prod.fst))

theorem underlying_probability {G : PDG X Y D} (hG : G.isProbDist) :
    G.underlying.isProbDist := Distribution.fTransform_isProbDist _ hG

/-- Maximal winning probability over deterministic environments. -/
noncomputable def supWinProbability (G : PDG X Y D) : ℝ :=
  sSup (Set.range (fun e : DDE X Y => winProbability e G))

theorem supWinProbability_le (G : PDG X Y D) {ε : ℝ}
    (h : ∀ e : DDE X Y, winProbability e G ≤ ε) : supWinProbability G ≤ ε := by
  apply csSup_le
  · exact ⟨_, ⟨⟨fun _ => Part.none, fun _ _ hd => hd.elim⟩, rfl⟩⟩
  · rintro _ ⟨e, rfl⟩
    exact h e

end Winning

section Blind

variable {E : List X → Prop} {bound : ℕ} {hE : ∀ h, E h → h.length ≤ bound}
  (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)

/-- Blinding keeps the domain of input histories. -/
noncomputable def blind (G : PDG X Y (Domain.ofInputs E bound hE)) :
    PDG X Unit (Domain.ofInputs E bound hE) :=
  Distribution.fTransform (fun g => ⟨DDG.blind g.1, HasDomain.ofInputs fun h =>
    (DDG.blind_dom g.1 h).trans (((hasDomain_ofInputs_iff hE' g.1.1.2).mp g.2) h)⟩) G

variable {G : PDG X Y (Domain.ofInputs E bound hE)}

omit [Fintype X] [Fintype Y] in
include hE' in
/-- On a domain of input histories, all blinded samples are one system. -/
theorem blind_system_eq {g g' : {g : DDG X Y // HasDomain (Domain.ofInputs E bound hE) g.1.1}} :
    (DDG.blind g.1).1 = (DDG.blind g'.1).1 := by
  apply Subtype.ext
  funext h
  apply Part.ext
  intro u
  cases u
  simp only [DDG.blind, Part.mem_map_iff, and_true, ← Part.dom_iff_mem,
    (hasDomain_ofInputs_iff hE' g.1.1.2).mp g.2 h, (hasDomain_ofInputs_iff hE' g'.1.1.2).mp g'.2 h]

/-- A blind environment follows one fixed query sequence. A common bound on the condition
at every admitted query sequence therefore bounds its winning probability. -/
theorem winProbability_blind_le (hG : G.NonNeg) {ε : ℝ} (hε : 0 ≤ ε)
    (hbad : ∀ xs, xs = [] ∨ E xs → G.badProbability xs ≤ ε)
    (e : DDE X Unit) : winProbability e (G.blind hE') ≤ ε := by
  rw [winProbability, blind, Distribution.mass_fTransform]
  by_cases existsWin : ∃ g ∈ G.support, DDG.Wins e (DDG.blind g.1)
  · obtain ⟨g, -, xs, ys, ht, hs, _⟩ := existsWin
    have admitted : xs = [] ∨ E xs := by
      by_cases hn : xs = []
      · exact Or.inl hn
      · exact Or.inr (((hasDomain_ofInputs_iff hE' g.1.1.2).mp g.2 xs).mp (ht.replies.dom hn))
    apply le_trans (Distribution.mass_mono_on_support hG
      (Q := fun k => k.1.2.1 xs) ?_) (hbad xs admitted)
    intro k _ hkWins
    obtain ⟨xs', ys', ht', hs', hb⟩ := hkWins
    rw [blind_system_eq hE' (g := k) (g' := g)] at ht'
    exact (ht.eq_of_stopped ht' hs hs').1 ▸ hb
  · have zeroBound := Distribution.mass_mono_on_support hG
      (Q := fun _ => False) (fun g hg hw => existsWin ⟨g, hg, hw⟩)
    rw [Distribution.mass_eq_zero_of_forall_not G (fun _ h => h)] at zeroBound
    exact zeroBound.trans hε

/-- Every admitted fixed query sequence is a blind winning strategy. -/
theorem winProbability_ofQueries_blind (xs : List X) (hx : xs = [] ∨ E xs) :
    winProbability (DDE.ofQueries xs) (G.blind hE') = G.badProbability xs := by
  rw [winProbability, blind, Distribution.mass_fTransform, badProbability]
  apply Distribution.mass_congr_of_support
  intro g _
  have reach : Reach (DDG.blind g.1).1.1 xs := by
    intro p e hp hn
    rcases hx with rfl | hd
    · simp only [List.nil_eq_append_iff] at hp
      exact (hn hp.1).elim
    · exact g.1.1.2.2 ⟨e, hp.symm⟩ hn
        (((hasDomain_ofInputs_iff hE' g.1.1.2).mp g.2 xs).mpr hd)
  obtain ⟨ys, tr⟩ := (transcript_fixedQueries (s := (DDG.blind g.1).1.1)
    xs [] (List.append_nil xs).symm).mp reach
  have stopped : ¬ (fixedQueries xs ys).Dom := by
    simp [fixedQueries, ← tr.length_eq]
  constructor
  · rintro ⟨xs', ys', ht, hs, hb⟩
    exact (tr.eq_of_stopped ht stopped hs).1 ▸ hb
  · intro hb
    exact ⟨xs, ys, tr, stopped, hb⟩

theorem badProbability_le_blind (hG : G.NonNeg) (xs : List X) (hx : xs = [] ∨ E xs) :
    G.badProbability xs ≤ (G.blind hE').supWinProbability := by
  rw [← winProbability_ofQueries_blind hE' xs hx]
  unfold supWinProbability
  apply le_csSup
  · refine ⟨G.weight, ?_⟩
    rintro _ ⟨e, rfl⟩
    change winProbability e (G.blind hE') ≤ G.weight
    rw [winProbability, blind, Distribution.mass_fTransform]
    exact Distribution.mass_le_weight hG _
  · exact ⟨DDE.ofQueries xs, rfl⟩

theorem supWinProbability_blind_le (hG : G.NonNeg) {ε : ℝ} (hε : 0 ≤ ε)
    (hbad : ∀ xs, xs = [] ∨ E xs → G.badProbability xs ≤ ε) :
    (G.blind hE').supWinProbability ≤ ε :=
  supWinProbability_le _ (winProbability_blind_le hE' hG hε hbad)

end Blind

end PDG

/-- The supremum winning probability, in Lanzenberger's notation. -/
scoped notation:max "ν(" G ")" => PDG.supWinProbability G

end SystemAlgebra
