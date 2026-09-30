import Examples.AuthenticatedEncryption.Oracle

/-!
# Authenticated encryption: the systems as oracles

Each system of the corrected hybrid is an automaton with sampled tables, and at each sample its
system is an oracle automaton. The four transformations of the real system,
`ρ^ptxt ∘ ρ^cca ∘ ρ^ptxt ∘ ρ^cca`, give the double-randomized hybrid oracle; the ideal system is
the ideal oracle.

## Main definitions

* `Hybrid scheme q`: the corrected hybrid `ρ^ptxt ∘ ρ^cca ∘ ρ^ptxt ∘ ρ^cca(⟦E_k, D_k⟧)`

## Main results

* `real_eq`, `encryptionReal_eq`: the real system and the real encryption system are automata
  on their key and encryption tables
* `ptxt_smul`, `cca_smul`, `aeIdeal_smul`: each transformation of an automaton is an automaton
* `real_system`, `encryptionReal_system`, `ptxt_system`, `cca_system`, `aeIdeal_system`: at each
  sample, each stage is an oracle automaton, or an encryption oracle automaton
* `hybrid_mass`, `ideal_mass`: the hybrid and the ideal are the hybrid and the ideal oracles on
  independent tables
-/

open SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface Probability
open Commons

namespace AuthenticatedEncryption

variable {K M C : Type} [Fintype K] [Fintype M] [Fintype C] [DecidableEq K] [DecidableEq M]

/-- The law of a source's table: `k` independent samples. -/
noncomputable abbrev tableLaw {X : Type} (law : Distribution.ProbDist X) (k : ℕ) : Distribution (Fin k → X) :=
  Distribution.pi fun _ => law.1

omit [Fintype K] [Fintype M] [Fintype C] [DecidableEq K] [DecidableEq M] in
theorem tableLaw_isProbDist {X : Type} (law : Distribution.ProbDist X) (k : ℕ) :
    (tableLaw law k).isProbDist :=
  Distribution.pi_isProbDist fun _ => law.2

/-- **The real system is an automaton** on its key and encryption tables. -/
theorem real_eq (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ) :
    AE.Real.perPort scheme (budget := q) = Resource.ofAutomaton (AE.perPort M C q)
      (realStep scheme (AE.Real.bound scheme * ∑ i, q i))
      ⟨Distribution.fTransform (fun ω => (none, ((ω.1, 0), (ω.2, 0))))
          (Distribution.prod (tableLaw (AE.Real.law1 scheme) (AE.Real.bound scheme * ∑ i, q i))
            (tableLaw (AE.Real.law2 scheme) (AE.Real.bound scheme * ∑ i, q i))),
        Distribution.fTransform_isProbDist _ (Distribution.prod_isProbDist _ _
          (Distribution.pi_isProbDist fun _ => (AE.Real.law1 scheme).2)
          (Distribution.pi_isProbDist fun _ => (AE.Real.law2 scheme).2))⟩ := by
  rw [AE.Real.perPort, AE.Real.randomness, Resource.source, Resource.source, parallel_ofAutomaton,
    Converter.ofProgram_smul_ofAutomaton]
  congr 1
  apply Subtype.ext
  dsimp only
  rw [← Distribution.fTransform_prod, Distribution.fTransform_comp]
  rfl

/-- **The real encryption system is an automaton** on its key and encryption tables. -/
theorem encryptionReal_eq (scheme : SymmetricEncryption K M C) (q : Encryption.Port → ℕ) :
    Encryption.Real.perPort scheme (budget := q) = Resource.ofAutomaton (Encryption.perPort M C q)
      (encryptionRealStep scheme (Encryption.Real.bound scheme * ∑ i, q i))
      ⟨Distribution.fTransform (fun ω => (none, ((ω.1, 0), (ω.2, 0))))
          (Distribution.prod
            (tableLaw (Encryption.Real.law1 scheme) (Encryption.Real.bound scheme * ∑ i, q i))
            (tableLaw (Encryption.Real.law2 scheme) (Encryption.Real.bound scheme * ∑ i, q i))),
        Distribution.fTransform_isProbDist _ (Distribution.prod_isProbDist _ _
          (Distribution.pi_isProbDist fun _ => (Encryption.Real.law1 scheme).2)
          (Distribution.pi_isProbDist fun _ => (Encryption.Real.law2 scheme).2))⟩ := by
  rw [Encryption.Real.perPort, Encryption.Real.randomness, Resource.source, Resource.source,
    parallel_ofAutomaton, Converter.ofProgram_smul_ofAutomaton]
  congr 1
  apply Subtype.ext
  dsimp only
  rw [← Distribution.fTransform_prod, Distribution.fTransform_comp]
  rfl

/-- The plaintext filter's automaton on an automaton. -/
noncomputable abbrev ptxtStep {S : Type}
    (step : S → (p : AE.Port) → AE.Input M C p → S × AE.Output M C p) :=
  (AE.PTXT.body M C).combine step (AE.PTXT.bound_spec M C)

/-- **The plaintext filter on an automaton** is its automaton on the same tables. -/
theorem ptxt_smul {Ω S : Type} (q : AE.Port → ℕ)
    (step : S → (p : AE.Port) → AE.Input M C p → S × AE.Output M C p) (L : Distribution Ω)
    (hL : L.isProbDist) (init : Ω → S) :
    AE.PTXT.perPort M C (budget := q) • Resource.ofAutomaton (AE.perPort M C q) step
        ⟨Distribution.fTransform init L, Distribution.fTransform_isProbDist _ hL⟩ =
      Resource.ofAutomaton (AE.perPort M C q) (ptxtStep step)
        ⟨Distribution.fTransform (fun ω => (none, init ω)) L,
          Distribution.fTransform_isProbDist _ hL⟩ := by
  rw [AE.PTXT.perPort, AE.PTXT.perPortProgram, Converter.ofPreservingProgram_smul_ofAutomaton]
  congr 1
  apply Subtype.ext
  dsimp only
  rw [Distribution.fTransform_comp]
  rfl

section Replacement

variable [DecidableEq C] [Nonempty M]

/-- The random-message transformation's automaton on an automaton, beside its source of
replacement messages. -/
noncomputable abbrev ccaStep {S : Type} (k : ℕ)
    (step : S → (p : AE.Port) → AE.Input M C p → S × AE.Output M C p) :=
  (AE.CCA.body M C).combine (parallelStep step (sourceStep (q := k) (AE.CCA.law1 M C)))
    (AE.CCA.bound_spec M C)

omit [DecidableEq M] in
/-- **The random-message transformation on an automaton** is its automaton on the tables beside a
table of replacement messages. -/
theorem cca_smul {Ω S : Type} (q : AE.Port → ℕ)
    (step : S → (p : AE.Port) → AE.Input M C p → S × AE.Output M C p) (L : Distribution Ω)
    (hL : L.isProbDist) (init : Ω → S) :
    AE.CCA.perPort M C (budget := q) • Resource.ofAutomaton (AE.perPort M C q) step
        ⟨Distribution.fTransform init L, Distribution.fTransform_isProbDist _ hL⟩ =
      Resource.ofAutomaton (AE.perPort M C q) (ccaStep (AE.CCA.bound M C * ∑ i, q i) step)
        ⟨Distribution.fTransform (fun p => (none, (init p.1, (p.2, 0))))
            (Distribution.prod L (tableLaw (AE.CCA.law1 M C) (AE.CCA.bound M C * ∑ i, q i))),
          Distribution.fTransform_isProbDist _ (Distribution.prod_isProbDist _ _ hL
            (Distribution.pi_isProbDist fun _ => (AE.CCA.law1 M C).2))⟩ := by
  rw [AE.CCA.perPort, Interface.comp_smul, attach_rightContext, AE.CCA.randomness, Resource.source,
    parallel_ofAutomaton, AE.CCA.perPortProgram, Converter.ofPreservingProgram_smul_ofAutomaton]
  congr 1
  apply Subtype.ext
  dsimp only
  rw [← Distribution.fTransform_prod, Distribution.fTransform_comp]
  rfl

/-- The ideal transformation's automaton on an encryption automaton, beside its source of
replacement messages. -/
noncomputable abbrev aeIdealStep {S : Type} (k : ℕ)
    (step : S → (p : Encryption.Port) → Encryption.Input M p → S × Encryption.Output C p) :=
  (AE.Ideal.body M C).combine (parallelStep step (sourceStep (q := k) (AE.Ideal.law1 M C)))
    (AE.Ideal.bound_spec M C)

omit [DecidableEq M] in
/-- **The ideal transformation on an encryption automaton** is its automaton on the tables beside
a table of replacement messages. -/
theorem aeIdeal_smul {Ω S : Type} (q : AE.Port → ℕ)
    (step : S → (p : Encryption.Port) → Encryption.Input M p → S × Encryption.Output C p)
    (L : Distribution Ω) (hL : L.isProbDist) (init : Ω → S) :
    AE.Ideal.perPort M C (budget := q) •
        Resource.ofAutomaton (Encryption.perPort M C (AE.Ideal.insideBudget M C q)) step
        ⟨Distribution.fTransform init L, Distribution.fTransform_isProbDist _ hL⟩ =
      Resource.ofAutomaton (AE.perPort M C q) (aeIdealStep (AE.Ideal.bound M C * ∑ i, q i) step)
        ⟨Distribution.fTransform (fun p => (none, (init p.1, (p.2, 0))))
            (Distribution.prod L (tableLaw (AE.Ideal.law1 M C) (AE.Ideal.bound M C * ∑ i, q i))),
          Distribution.fTransform_isProbDist _ (Distribution.prod_isProbDist _ _ hL
            (Distribution.pi_isProbDist fun _ => (AE.Ideal.law1 M C).2))⟩ := by
  rw [AE.Ideal.perPort, Interface.comp_smul, attach_rightContext, AE.Ideal.randomness,
    Resource.source, parallel_ofAutomaton, AE.Ideal.perPortProgram,
    Converter.ofPreservingProgram_smul_ofAutomaton]
  congr 1
  apply Subtype.ext
  dsimp only
  rw [← Distribution.fTransform_prod, Distribution.fTransform_comp]
  rfl

end Replacement

/-! ## Each stage is an oracle -/

theorem real_system (scheme : SymmetricEncryption K M C) {k : ℕ} (ω : (Fin k → K) × (Fin k → (K × M → C))) :
    automatonSystem (realStep scheme k) (none, ((ω.1, 0), (ω.2, 0))) =
      automatonSystem (oracleStep (realEncrypt scheme) (realDecrypt scheme)) (ω, []) :=
  automatonSystem_eq_of_bisim _ (real_bisim scheme) ⟨rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem encryptionReal_system (scheme : SymmetricEncryption K M C) {k : ℕ}
    (ω : (Fin k → K) × (Fin k → (K × M → C))) :
    automatonSystem (encryptionRealStep scheme k) (none, ((ω.1, 0), (ω.2, 0))) =
      automatonSystem (encryptionStep (realEncrypt scheme)) (ω, []) :=
  automatonSystem_eq_of_bisim _ (encryptionReal_bisim scheme) ⟨rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem ptxt_system {Ω S : Type} {step : S → (p : AE.Port) → AE.Input M C p → S × AE.Output M C p}
    {s : S} {encrypt : Ω → ℕ → M → C} {decrypt : Ω → List M → C → Option M} {ω : Ω}
    (h : automatonSystem step s = automatonSystem (oracleStep encrypt decrypt) (ω, [])) :
    automatonSystem (ptxtStep step) (none, s) =
      automatonSystem (oracleStep encrypt (ptxtDecrypt decrypt)) (ω, []) :=
  (Program.combine_congr (P := AE.PTXT.body M C) step (AE.PTXT.bound_spec M C) none h).trans
    (automatonSystem_eq_of_bisim _ (ptxt_bisim encrypt decrypt) ⟨rfl, rfl⟩)

section Replacement

variable [DecidableEq C] [Nonempty M]

omit [DecidableEq M] in
theorem cca_system {Ω S : Type} {k : ℕ}
    {step : S → (p : AE.Port) → AE.Input M C p → S × AE.Output M C p} {s : S}
    {encrypt : Ω → ℕ → M → C} {decrypt : Ω → List M → C → Option M} {ω : Ω}
    (h : automatonSystem step s = automatonSystem (oracleStep encrypt decrypt) (ω, []))
    (t : Fin k → M) :
    automatonSystem (ccaStep k step) (none, (s, (t, 0))) =
      automatonSystem (oracleStep (replacedEncrypt (AE.CCA.law1 M C) encrypt)
        (ccaDecrypt (AE.CCA.law1 M C) encrypt decrypt)) ((ω, t), []) :=
  (Program.combine_congr (P := AE.CCA.body M C) _ (AE.CCA.bound_spec M C) none
      (parallelStep_congr _ _ h rfl)).trans
    (automatonSystem_eq_of_bisim _ (cca_bisim encrypt decrypt) ⟨rfl, rfl, rfl, rfl, rfl⟩)

omit [DecidableEq M] in
theorem aeIdeal_system {Ω S : Type} {k : ℕ}
    {step : S → (p : Encryption.Port) → Encryption.Input M p → S × Encryption.Output C p} {s : S}
    {encrypt : Ω → ℕ → M → C} {ω : Ω}
    (h : automatonSystem step s = automatonSystem (encryptionStep encrypt) (ω, []))
    (t : Fin k → M) :
    automatonSystem (aeIdealStep k step) (none, (s, (t, 0))) =
      automatonSystem (oracleStep (replacedEncrypt (AE.Ideal.law1 M C) encrypt)
        (idealDecrypt (AE.Ideal.law1 M C) encrypt)) ((ω, t), []) :=
  (Program.combine_congr (P := AE.Ideal.body M C) _ (AE.Ideal.bound_spec M C) none
      (parallelStep_congr _ _ h rfl)).trans
    (automatonSystem_eq_of_bisim _ (aeIdeal_bisim encrypt) ⟨rfl, rfl, rfl, rfl, rfl⟩)

/-! ## The hybrid and the ideal as oracles -/

variable (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ)

/-- **The corrected hybrid** `ρ^ptxt ∘ ρ^cca ∘ ρ^ptxt ∘ ρ^cca` of the real system. -/
noncomputable def Hybrid : Interface.Resource (AE.perPort M C q) :=
  AE.PTXT.perPort M C • AE.CCA.perPort M C • AE.PTXT.perPort M C • AE.CCA.perPort M C •
    AE.Real.perPort scheme

/-- The hybrid's encryption: the real encryption of the inner replacement messages. -/
noncomputable abbrev hybridEncrypt {k k' : ℕ} :
    (((Fin k → K) × (Fin k → (K × M → C))) × (Fin k' → M)) × (Fin k' → M) → ℕ → M → C :=
  replacedEncrypt (AE.CCA.law1 M C) (replacedEncrypt (AE.CCA.law1 M C) (realEncrypt scheme))

/-- The hybrid's decryption: both plaintext filters around both random-message
transformations of the real decryption. -/
noncomputable abbrev hybridDecrypt {k k' : ℕ} :
    (((Fin k → K) × (Fin k → (K × M → C))) × (Fin k' → M)) × (Fin k' → M) →
      List M → C → Option M :=
  ptxtDecrypt (ccaDecrypt (AE.CCA.law1 M C) (replacedEncrypt (AE.CCA.law1 M C) (realEncrypt scheme))
    (ptxtDecrypt (ccaDecrypt (AE.CCA.law1 M C) (realEncrypt scheme) (realDecrypt scheme))))

/-- **The hybrid is the hybrid oracle** on independent key, encryption and two replacement
tables. -/
theorem hybrid_mass (h : List ((Σ i, (AE.perPort M C q).X i) × (Σ i, (AE.perPort M C q).Y i))) :
    (Hybrid scheme q).1 h =
      (Distribution.prod (Distribution.prod (Distribution.prod
          (tableLaw (AE.Real.law1 scheme) (AE.Real.bound scheme * ∑ i, q i))
          (tableLaw (AE.Real.law2 scheme) (AE.Real.bound scheme * ∑ i, q i)))
          (tableLaw (AE.CCA.law1 M C) (AE.CCA.bound M C * ∑ i, q i)))
          (tableLaw (AE.CCA.law1 M C) (AE.CCA.bound M C * ∑ i, q i))).mass fun ω =>
        Replies (filterDom (AE.perPort M C q).domain
          (automatonSystem (oracleStep (hybridEncrypt scheme) (hybridDecrypt scheme)) (ω, [])))
          (h.map Prod.fst) (h.map Prod.snd) := by
  rw [Hybrid, real_eq, cca_smul, ptxt_smul, cca_smul, ptxt_smul, Resource.ofAutomaton_mass,
    Distribution.mass_fTransform]
  refine Distribution.mass_congr _ fun ω => ?_
  dsimp only
  rw [ptxt_system (cca_system (ptxt_system (cca_system (real_system scheme ω.1.1) ω.1.2)) ω.2)]
  all_goals repeat' (first | apply Distribution.prod_isProbDist | exact tableLaw_isProbDist _ _)

/-- The ideal's encryption: the real encryption of the replacement messages. -/
noncomputable abbrev idealEncrypt {k k' : ℕ} :
    ((Fin k → K) × (Fin k → (K × M → C))) × (Fin k' → M) → ℕ → M → C :=
  replacedEncrypt (AE.Ideal.law1 M C) (realEncrypt scheme)

/-- The size of the real encryption system's tables in the ideal. -/
abbrev idealTableSize : ℕ :=
  Encryption.Real.bound scheme * ∑ i, AE.Ideal.insideBudget M C q i

/-- **The ideal is the ideal oracle** on independent key, encryption and replacement tables. -/
theorem ideal_mass (h : List ((Σ i, (AE.perPort M C q).X i) × (Σ i, (AE.perPort M C q).Y i))) :
    (AE.Ideal.perPort M C (budget := q) • Encryption.Real.perPort scheme :
        Interface.Resource (AE.perPort M C q)).1 h =
      (Distribution.prod (Distribution.prod
          (tableLaw (AE.Real.law1 scheme) (idealTableSize scheme q))
          (tableLaw (AE.Real.law2 scheme) (idealTableSize scheme q)))
          (tableLaw (AE.Ideal.law1 M C) (AE.Ideal.bound M C * ∑ i, q i))).mass fun ω =>
        Replies (filterDom (AE.perPort M C q).domain
          (automatonSystem (oracleStep (idealEncrypt scheme)
            (idealDecrypt (AE.Ideal.law1 M C) (realEncrypt scheme))) (ω, [])))
          (h.map Prod.fst) (h.map Prod.snd) := by
  rw [encryptionReal_eq, aeIdeal_smul, Resource.ofAutomaton_mass, Distribution.mass_fTransform]
  refine Distribution.mass_congr _ fun ω => ?_
  dsimp only
  rw [aeIdeal_system (encryptionReal_system scheme ω.1) ω.2]
  all_goals repeat' (first | apply Distribution.prod_isProbDist | exact tableLaw_isProbDist _ _)

end Replacement

end AuthenticatedEncryption

