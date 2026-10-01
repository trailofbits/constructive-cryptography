import RandomSystems.Distance.Decision

/-!
# Restriction to a smaller domain

The restriction of a random system on `D` to a smaller domain `D'` keeps the masses of the
transcripts `D'` admits and is zero elsewhere; it is a random system on `D'`. Restrictions
compose. An environment compatible with the restriction sees the transcript law of the system
itself, so restriction does not increase the transcript distance. On an input domain, a
transcript is admitted exactly when it is empty or its inputs lie in the domain.

## Main definitions

* `RandomSystem.restrict R D'`: the restriction of `R` to `D'`

## Main results

* `admitted_ofInputs_iff`: admission on an input domain
* `RandomSystem.restrict_restrict`: restrictions compose
* `RandomSystem.sLaw_restrict`: an environment compatible with the restriction sees the
  transcript law of the system
* `RandomSystem.transcriptDistance_restrict_le`: restriction does not increase the transcript
  distance
-/

namespace SystemAlgebra

open Classical Probability

variable {A B : Type}

theorem Admitted.mono {D D' : List (A × B) → A → Prop} (hD : ∀ h x, D' h x → D h x)
    {h : List (A × B)} (ha : Admitted D' h) : Admitted D h :=
  fun p z t he => hD _ _ (ha p z t he)

/-- **Admission on an input domain**: a transcript is admitted exactly when it is empty or its
inputs lie in the domain, for a domain without the empty history and closed under nonempty
prefixes. -/
theorem admitted_ofInputs_iff {E : List A → Prop} {bound : ℕ} {hE : ∀ h, E h → h.length ≤ bound}
    (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p) (h : List (A × B)) :
    Admitted (Domain.ofInputs E bound hE : Domain A B) h ↔ h = [] ∨ E (h.map Prod.fst) := by
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h z ih =>
    rw [admitted_snoc, ih, Domain.ofInputs_apply, List.map_append, List.map_singleton]
    refine ⟨fun hz => Or.inr hz.2, fun hz => ?_⟩
    have hz := hz.resolve_left (by simp)
    refine ⟨?_, hz⟩
    by_cases hn : h = []
    · exact Or.inl hn
    · exact Or.inr (hE'.2 (List.prefix_append _ _) (by simpa using hn) hz)

namespace RandomSystem

variable [Fintype A] [Fintype B] {D D' D'' : Domain A B}

/-- **The restriction** of a random system on `D` to a smaller domain `D'`: the masses of the
transcripts `D'` admits, and zero elsewhere. -/
noncomputable def restrict (R : RandomSystem A B D) (D' : Domain A B)
    (hD : ∀ h x, D' h x → D h x) : RandomSystem A B D' :=
  ⟨fun h => if Admitted D' h then R h else 0, R.2.restrict hD⟩

theorem restrict_apply (R : RandomSystem A B D) (hD : ∀ h x, D' h x → D h x)
    (h : List (A × B)) : R.restrict D' hD h = if Admitted D' h then R h else 0 := rfl

/-- **Restrictions compose.** -/
theorem restrict_restrict (R : RandomSystem A B D) (hD : ∀ h x, D' h x → D h x)
    (hD' : ∀ h x, D'' h x → D' h x) :
    (R.restrict D' hD).restrict D'' hD' = R.restrict D'' fun h x hx => hD h x (hD' h x hx) := by
  ext h
  simp only [restrict_apply]
  by_cases ha : Admitted D'' h
  · rw [if_pos ha, if_pos ha, if_pos (ha.mono hD')]
  · rw [if_neg ha, if_neg ha]

/-- Along the queries of a strategy compatible with the restriction, every possible transcript
of the system is admitted by the smaller domain. -/
theorem admitted_of_compatible_restrict {R : RandomSystem A B D} {hD : ∀ h x, D' h x → D h x}
    {σ : List B →. A} (hc : (R.restrict D' hD).Compatible σ) {h : List (A × B)}
    (hh : Cons σ h) (hm : R h ≠ 0) : Admitted D' h := by
  induction h using List.reverseRecOn with
  | nil => exact admitted_nil _
  | append_singleton h z ih =>
    obtain ⟨hh, hz⟩ := cons_snoc.mp hh
    have hp : R h ≠ 0 := fun h0 => hm (R.mass_eq_zero_of_prefix ⟨[z], rfl⟩ h0)
    have ha := ih hh hp
    refine admitted_snoc.mpr ⟨ha, hc h z.1 hh ?_ hz⟩
    rwa [restrict_apply, if_pos ha]

/-- A strategy compatible with the restriction is compatible with the system. -/
theorem Compatible.of_restrict {R : RandomSystem A B D} {hD : ∀ h x, D' h x → D h x}
    {σ : List B →. A} (hc : (R.restrict D' hD).Compatible σ) : R.Compatible σ := by
  intro h x hh hm hx
  have ha := admitted_of_compatible_restrict hc hh hm
  exact hD h x (hc h x hh (by rwa [restrict_apply, if_pos ha]) hx)

/-- **An environment compatible with the restriction** sees the transcript law of the system. -/
theorem sLaw_restrict {R : RandomSystem A B D} {hD : ∀ h x, D' h x → D h x}
    {σ : List B →. A} (hc : (R.restrict D' hD).Compatible σ) (n : ℕ) :
    (R.restrict D' hD).sLaw σ n = R.sLaw σ n := by
  ext h
  rw [sLaw_apply, sLaw_apply, restrict_apply]
  by_cases hg : Good σ n h
  · by_cases hm : R h = 0
    · simp [hm]
    · rw [if_pos hg, if_pos hg, if_pos (admitted_of_compatible_restrict hc hg.1 hm)]
  · rw [if_neg hg, if_neg hg]

end RandomSystem

variable {I : Type} [Fintype I] {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {𝒟 𝒟' : Domain (Σ i, X i) (Σ i, Y i)}

theorem RandomSystem.RepliesAtQueriedInterface.restrict
    {R : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟} (hR : R.RepliesAtQueriedInterface)
    (hD : ∀ h x, 𝒟' h x → 𝒟 h x) : (R.restrict 𝒟' hD).RepliesAtQueriedInterface := by
  intro h x y hy
  rw [RandomSystem.restrict_apply, hR h x y hy, ite_self]

/-- An environment compatible with a smaller domain is compatible with the larger one. -/
theorem Domain.Compatible.of_restrict {E : DDE (Σ i, X i) (Σ i, Y i)}
    (hD : ∀ h x, 𝒟' h x → 𝒟 h x) (hc : 𝒟'.Compatible E) : 𝒟.Compatible E :=
  fun _ hR => RandomSystem.Compatible.of_restrict (hc _ (hR.restrict hD))

namespace RandomSystem

/-- **Restriction does not increase the transcript distance**: an environment compatible with
the smaller domain sees the transcript laws of the systems themselves. -/
theorem transcriptDistance_restrict_le {R S : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟}
    (hR : R.RepliesAtQueriedInterface) (hS : S.RepliesAtQueriedInterface)
    (hD : ∀ h x, 𝒟' h x → 𝒟 h x) :
    (R.restrict 𝒟' hD).transcriptDistance (S.restrict 𝒟' hD) ≤ R.transcriptDistance S := by
  refine iSup_le fun E => iSup_le fun n => iSup_le fun hn => iSup_le fun hc => ?_
  rw [sLaw_restrict (hc _ (hR.restrict hD)), sLaw_restrict (hc _ (hS.restrict hD))]
  exact statDist_le_transcriptDistance hn (hc.of_restrict hD) R S

end RandomSystem

end SystemAlgebra
