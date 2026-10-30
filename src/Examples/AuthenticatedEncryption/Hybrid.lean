import Examples.AuthenticatedEncryption.Oracle

/-!
# Authenticated encryption: the systems as oracles

The hybrid and ideal transcript laws follow by composing equations between typed systems.
`oracleSystem q encrypt decrypt law` retains one draw from `law` across all queries. The
component equations come from the bisimulations in `Examples.AuthenticatedEncryption.Oracle`,
transported through sampling by `TypedSystem.ofAutomaton_map_congr`.

Write `O(e, d, L)` for `oracleSystem q e d L`, `μ` for the real system's `realTableLaw`, and
`ν` for `ccaTableLaw M C q`. With budgets and the replacement-message law suppressed, the
contracts are:

```text
Real = O(realEncrypt scheme, realDecrypt scheme, μ)                        real_system
PTXT • O(e, d, L) = O(e, ptxtDecrypt d, L)                                 ptxt_system
CCA  • O(e, d, L) = O(replacedEncrypt e, ccaDecrypt e d, L × ν)             cca_system
```

Here `Real`, `PTXT` and `CCA` are the corresponding `AE.*.perPort` objects; `×` is an
independent product of laws. Each CCA adds and owns one fresh table, while PTXT keeps the draw.
`hybrid_system` rewrites `PTXT • CCA • PTXT • CCA • Real` from the inside out, giving
`hybridLaw = (μ × ν) × ν`: two independent replacement tables with the same law `ν`.
`ideal_system` composes `encryptionReal_system` with `aeIdeal_system`; its `idealLaw` pairs real
tables of `idealTableSize` entries with the ideal converter's own table from `idealTableLaw`.
These equalities of typed systems rewrite under any surrounding converter or parallel system;
`hybrid_mass` and `ideal_mass` then obtain their transcript laws from `oracleSystem_mass`.

## Main definitions

* `realTableLaw`, `ccaTableLaw`, `idealTableLaw`: the normalized laws of the components' tables
* `hybridLaw`, `idealLaw`: the products of these laws retained by the hybrid and the ideal
* `oracleSystem`, `encryptionOracleSystem`: sampled oracles retaining one draw across all queries
* `Hybrid scheme q`: the corrected hybrid `ρ^ptxt ∘ ρ^cca ∘ ρ^ptxt ∘ ρ^cca(⟦E_k, D_k⟧)`

## Main results

* `real_eq`, `encryptionReal_eq`: the real system and the real encryption system are automata
  on their key and encryption tables
* `ptxt_smul`, `cca_smul`, `aeIdeal_smul`: each transformation of an automaton is an automaton
* `real_system`, `encryptionReal_system`, `ptxt_system`, `cca_system`, `aeIdeal_system`: the
  component contracts, equations of typed systems
* `hybrid_system`, `ideal_system`: the assembled typed systems equal their sampled oracles
* `hybrid_mass`, `ideal_mass`: the transcript laws of the hybrid and the ideal, as the mass of
  the independent table draws whose oracle gives the transcript
-/

open SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface Probability
open Commons

namespace AuthenticatedEncryption

variable {K M C : Type} [Fintype K] [Fintype M] [Fintype C] [DecidableEq K] [DecidableEq M]

/-- The law of a source's table: `k` independent samples. -/
noncomputable abbrev tableLaw {X : Type} (law : Distribution.ProbDist X) (k : ℕ) :
    Distribution (Fin k → X) :=
  Distribution.pi fun _ => law.1

omit [Fintype K] [Fintype M] [Fintype C] [DecidableEq K] [DecidableEq M] in
lemma tableLaw_isProbDist {X : Type} (law : Distribution.ProbDist X) (k : ℕ) :
    (tableLaw law k).isProbDist :=
  Distribution.pi_isProbDist fun _ => law.2

/-- The real system's tables: `k` keys from `AE.Real.law1 scheme` and `k` encryption functions
from `AE.Real.law2 scheme`, all drawn independently. -/
noncomputable def realTableLaw (scheme : SymmetricEncryption K M C) (k : ℕ) :
    Distribution.ProbDist ((Fin k → K) × (Fin k → (K × M → C))) :=
  Distribution.prodProbDist
    ⟨tableLaw (AE.Real.law1 scheme) k, tableLaw_isProbDist _ _⟩
    ⟨tableLaw (AE.Real.law2 scheme) k, tableLaw_isProbDist _ _⟩

/-- An oracle on `AE.perPort M C q`, with one retained draw and an initially empty message
history `known`. Encryption appends its input to `known`; decryption keeps the state. -/
noncomputable def oracleSystem
    -- `Ω` is the type of the retained draw `ω`; `q p` bounds the queries at port `p`.
    {Ω : Type} (q : AE.Port → ℕ)
    -- Encryption replies with `encrypt ω known.length m`; decryption with `decrypt ω known c`.
    (encrypt : Ω → ℕ → M → C) (decrypt : Ω → List M → C → Option M)
    -- `law` is the distribution of the single draw `ω`.
    (law : Distribution.ProbDist Ω) : TypedSystem (AE.perPort M C q) :=
  TypedSystem.ofAutomaton _ (oracleStep encrypt decrypt)
    (Distribution.ProbDist.map (fun ω => (ω, [])) law)

/-- The encryption-only sampled oracle, with its encryption counter starting at zero. -/
noncomputable def encryptionOracleSystem
    -- `Ω` is the type of the retained draw `ω`; `q .enc` bounds the encryption queries.
    {Ω : Type} (q : Encryption.Port → ℕ)
    -- `encrypt ω i m` answers the `i`-th encryption; `law` distributes the single draw `ω`.
    (encrypt : Ω → ℕ → M → C) (law : Distribution.ProbDist Ω) :
    TypedSystem (Encryption.perPort M C q) :=
  TypedSystem.ofAutomaton _ (encryptionStep encrypt)
    (Distribution.ProbDist.map (fun ω => (ω, [])) law)

omit [DecidableEq M] in
/-- A transcript's probability is the mass of retained draws producing it on the domain. -/
lemma oracleSystem_mass {Ω : Type} (q : AE.Port → ℕ)
    (encrypt : Ω → ℕ → M → C) (decrypt : Ω → List M → C → Option M)
    (law : Distribution.ProbDist Ω)
    -- `h` is a transcript of query–reply pairs at the ports of `AE.perPort M C q`.
    (h : List ((Σ i, (AE.perPort M C q).X i) × (Σ i, (AE.perPort M C q).Y i))) :
    (oracleSystem q encrypt decrypt law).1 h = law.1.mass fun ω =>
      Replies (filterDom (AE.perPort M C q).domain
        (automatonSystem (oracleStep encrypt decrypt) (ω, [])))
        (h.map Prod.fst) (h.map Prod.snd) := by
  rw [oracleSystem, TypedSystem.ofAutomaton_mass, Distribution.ProbDist.map,
    Distribution.mass_fTransform]

/-- **The real system is an automaton** on its key and encryption tables. -/
lemma real_eq (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ) :
    AE.Real.perPort scheme (budget := q) = TypedSystem.ofAutomaton (AE.perPort M C q)
      (realStep scheme (AE.Real.bound scheme * ∑ i, q i))
      (Distribution.ProbDist.map (fun ω => (none, ((ω.1, 0), (ω.2, 0))))
        (realTableLaw scheme (AE.Real.bound scheme * ∑ i, q i))) := by
  rw [AE.Real.perPort, AE.Real.randomness, TypedSystem.source, TypedSystem.source,
    TypedSystem.parallel_ofAutomaton, TypedConverter.ofProgram_smul_ofAutomaton]
  congr 1
  apply Subtype.ext
  dsimp only [Distribution.ProbDist.map, realTableLaw, Distribution.prodProbDist]
  rw [← Distribution.fTransform_prod, Distribution.fTransform_comp]
  rfl

/-- **The real encryption system is an automaton** on its key and encryption tables. -/
lemma encryptionReal_eq (scheme : SymmetricEncryption K M C) (q : Encryption.Port → ℕ) :
    Encryption.Real.perPort scheme (budget := q) =
      TypedSystem.ofAutomaton (Encryption.perPort M C q)
        (encryptionRealStep scheme (Encryption.Real.bound scheme * ∑ i, q i))
        (Distribution.ProbDist.map (fun ω => (none, ((ω.1, 0), (ω.2, 0))))
          (realTableLaw scheme (Encryption.Real.bound scheme * ∑ i, q i))) := by
  rw [Encryption.Real.perPort, Encryption.Real.randomness, TypedSystem.source, TypedSystem.source,
    TypedSystem.parallel_ofAutomaton, TypedConverter.ofProgram_smul_ofAutomaton]
  congr 1
  apply Subtype.ext
  dsimp only [Distribution.ProbDist.map, realTableLaw, Distribution.prodProbDist]
  rw [← Distribution.fTransform_prod, Distribution.fTransform_comp]
  rfl

/-- The plaintext filter's automaton on an automaton. -/
noncomputable abbrev ptxtStep {S : Type}
    (step : S → (p : AE.Port) → AE.Input M C p → S × AE.Output M C p) :=
  (AE.PTXT.body M C).combine step (AE.PTXT.bound_spec M C)

/-- **The plaintext filter on an automaton** is its automaton on the same tables. -/
lemma ptxt_smul
    -- `Ω` carries the draw, `S` the inside state; `q` bounds the outer queries per port.
    {Ω S : Type} (q : AE.Port → ℕ)
    -- `step` updates the inside state and replies at the queried port.
    (step : S → (p : AE.Port) → AE.Input M C p → S × AE.Output M C p)
    -- `law` is the normalized law of the single draw `ω`; `init ω` is the initial inside state.
    (law : Distribution.ProbDist Ω) (init : Ω → S) :
    AE.PTXT.perPort M C (budget := q) • TypedSystem.ofAutomaton (AE.perPort M C q) step
        (Distribution.ProbDist.map init law) =
      TypedSystem.ofAutomaton (AE.perPort M C q) (ptxtStep step)
        (Distribution.ProbDist.map (fun ω => (none, init ω)) law) := by
  rw [AE.PTXT.perPort, AE.PTXT.perPortProgram, TypedConverter.ofPreservingProgram_smul_ofAutomaton]
  congr 1
  apply Subtype.ext
  dsimp only [Distribution.ProbDist.map]
  rw [Distribution.fTransform_comp]
  rfl

section Replacement

variable [DecidableEq C] [Nonempty M]

variable (M C) in
/-- The CCA converter's retained table: `AE.CCA.bound M C * ∑ i, q i` independent
replacement messages, each drawn from `AE.CCA.law1 M C`. -/
noncomputable def ccaTableLaw (q : AE.Port → ℕ) :
    Distribution.ProbDist (Fin (AE.CCA.bound M C * ∑ i, q i) → M) :=
  ⟨tableLaw (AE.CCA.law1 M C) (AE.CCA.bound M C * ∑ i, q i), tableLaw_isProbDist _ _⟩

variable (M C) in
/-- The ideal converter's retained table: `AE.Ideal.bound M C * ∑ i, q i` independent
replacement messages, each drawn from `AE.Ideal.law1 M C`. -/
noncomputable def idealTableLaw (q : AE.Port → ℕ) :
    Distribution.ProbDist (Fin (AE.Ideal.bound M C * ∑ i, q i) → M) :=
  ⟨tableLaw (AE.Ideal.law1 M C) (AE.Ideal.bound M C * ∑ i, q i), tableLaw_isProbDist _ _⟩

/-- The random-message transformation's automaton on an automaton, beside its source of
replacement messages. -/
noncomputable abbrev ccaStep {S : Type} (k : ℕ)
    (step : S → (p : AE.Port) → AE.Input M C p → S × AE.Output M C p) :=
  (AE.CCA.body M C).combine (parallelStep step (sourceStep (q := k) (AE.CCA.law1 M C)))
    (AE.CCA.bound_spec M C)

omit [DecidableEq M] in
/-- **The random-message transformation on an automaton** is its automaton on the draw beside an
independent replacement table from `ccaTableLaw M C q`. -/
lemma cca_smul
    -- `Ω` carries the draw, `S` the inside state; `q` bounds the outer queries per port.
    {Ω S : Type} (q : AE.Port → ℕ)
    -- `step` updates the inside state and replies at the queried port.
    (step : S → (p : AE.Port) → AE.Input M C p → S × AE.Output M C p)
    -- `law` is the normalized law of the single draw `ω`; `init ω` is the initial inside state.
    (law : Distribution.ProbDist Ω) (init : Ω → S) :
    AE.CCA.perPort M C (budget := q) • TypedSystem.ofAutomaton (AE.perPort M C q) step
        (Distribution.ProbDist.map init law) =
      TypedSystem.ofAutomaton (AE.perPort M C q) (ccaStep (AE.CCA.bound M C * ∑ i, q i) step)
        (Distribution.ProbDist.map (fun p => (none, (init p.1, (p.2, 0))))
          (Distribution.prodProbDist law (ccaTableLaw M C q))) := by
  rw [AE.CCA.perPort, Interface.comp_smul, TypedConverter.attach_rightContext, AE.CCA.randomness,
    TypedSystem.source, TypedSystem.parallel_ofAutomaton, AE.CCA.perPortProgram,
    TypedConverter.ofPreservingProgram_smul_ofAutomaton]
  congr 1
  apply Subtype.ext
  dsimp only [Distribution.ProbDist.map, Distribution.prodProbDist]
  rw [← Distribution.fTransform_prod, Distribution.fTransform_comp]
  rfl

/-- The ideal transformation's automaton on an encryption automaton, beside its source of
replacement messages. -/
noncomputable abbrev aeIdealStep {S : Type} (k : ℕ)
    (step : S → (p : Encryption.Port) → Encryption.Input M p → S × Encryption.Output C p) :=
  (AE.Ideal.body M C).combine (parallelStep step (sourceStep (q := k) (AE.Ideal.law1 M C)))
    (AE.Ideal.bound_spec M C)

omit [DecidableEq M] in
/-- **The ideal transformation on an encryption automaton** is its automaton on the draw beside
an independent replacement table from `idealTableLaw M C q`. -/
lemma aeIdeal_smul
    -- `Ω` carries the draw, `S` the inside state; `q` bounds the outer queries per port.
    {Ω S : Type} (q : AE.Port → ℕ)
    -- `step` updates the inside state and returns the encryption reply.
    (step : S → (p : Encryption.Port) → Encryption.Input M p → S × Encryption.Output C p)
    -- `law` is the normalized law of the single draw `ω`; `init ω` is the initial inside state.
    (law : Distribution.ProbDist Ω) (init : Ω → S) :
    AE.Ideal.perPort M C (budget := q) •
        TypedSystem.ofAutomaton (Encryption.perPort M C (AE.Ideal.insideBudget M C q)) step
        (Distribution.ProbDist.map init law) =
      TypedSystem.ofAutomaton (AE.perPort M C q) (aeIdealStep (AE.Ideal.bound M C * ∑ i, q i) step)
        (Distribution.ProbDist.map (fun p => (none, (init p.1, (p.2, 0))))
          (Distribution.prodProbDist law (idealTableLaw M C q))) := by
  rw [AE.Ideal.perPort, Interface.comp_smul, TypedConverter.attach_rightContext,
    AE.Ideal.randomness, TypedSystem.source, TypedSystem.parallel_ofAutomaton,
    AE.Ideal.perPortProgram, TypedConverter.ofPreservingProgram_smul_ofAutomaton]
  congr 1
  apply Subtype.ext
  dsimp only [Distribution.ProbDist.map, Distribution.prodProbDist]
  rw [← Distribution.fTransform_prod, Distribution.fTransform_comp]
  rfl

end Replacement

/-! ## Component equations for sampled oracles -/

/-- The real system is its oracle on independently sampled key and encryption tables. -/
lemma real_system (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ) :
    AE.Real.perPort scheme (budget := q) =
      oracleSystem q (realEncrypt scheme) (realDecrypt scheme)
        (realTableLaw scheme (AE.Real.bound scheme * ∑ i, q i)) := by
  rw [real_eq, oracleSystem]
  -- The compiled state and oracle state retain the same two tables.
  refine TypedSystem.ofAutomaton_map_congr _ _
    (realTableLaw scheme (AE.Real.bound scheme * ∑ i, q i)) _ _ ?_
  intro ω
  exact automatonSystem_eq_of_bisim _ (real_bisim scheme)
    ⟨rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- The real encryption system is its oracle on independent key and encryption tables. -/
lemma encryptionReal_system (scheme : SymmetricEncryption K M C) (q : Encryption.Port → ℕ) :
    Encryption.Real.perPort scheme (budget := q) =
      encryptionOracleSystem q (realEncrypt scheme)
        (realTableLaw scheme (Encryption.Real.bound scheme * ∑ i, q i)) := by
  rw [encryptionReal_eq, encryptionOracleSystem]
  refine TypedSystem.ofAutomaton_map_congr _ _
    (realTableLaw scheme (Encryption.Real.bound scheme * ∑ i, q i)) _ _ ?_
  intro ω
  exact automatonSystem_eq_of_bisim _ (encryptionReal_bisim scheme)
    ⟨rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- Plaintext filtering keeps the oracle's draw and encryption rule; decryption returns only
messages previously encrypted, as specified by `ptxtDecrypt`. -/
lemma ptxt_system
    -- `Ω` carries the retained draw; `q` bounds queries at each port.
    -- `encrypt` and `decrypt` are the oracle's reply rules under the draw from `law`.
    {Ω : Type} (q : AE.Port → ℕ) (encrypt : Ω → ℕ → M → C)
    (decrypt : Ω → List M → C → Option M) (law : Distribution.ProbDist Ω) :
    AE.PTXT.perPort M C (budget := q) • oracleSystem q encrypt decrypt law =
      oracleSystem q encrypt (ptxtDecrypt decrypt) law := by
  unfold oracleSystem
  rw [ptxt_smul]
  -- The filter's message list is the oracle's list, under the same retained draw.
  refine TypedSystem.ofAutomaton_map_congr _ _ law _ _ ?_
  intro ω
  exact automatonSystem_eq_of_bisim _ (ptxt_bisim encrypt decrypt) ⟨rfl, rfl⟩

section Replacement

variable [DecidableEq C] [Nonempty M]

omit [DecidableEq M] in
/-- Random-message attachment adds an independent replacement table to the oracle's draw.
Encryption uses replacement messages; decryption replays its own ciphertexts, otherwise
using `decrypt` on the replacement-message history. -/
lemma cca_system
    -- `Ω` carries the retained draw; `q` bounds queries at each port.
    -- `encrypt` and `decrypt` are the oracle's reply rules under the draw from `law`.
    {Ω : Type} (q : AE.Port → ℕ) (encrypt : Ω → ℕ → M → C)
    (decrypt : Ω → List M → C → Option M) (law : Distribution.ProbDist Ω) :
    AE.CCA.perPort M C (budget := q) • oracleSystem q encrypt decrypt law =
      oracleSystem q (replacedEncrypt (AE.CCA.law1 M C) encrypt)
        (ccaDecrypt (AE.CCA.law1 M C) encrypt decrypt)
        (Distribution.prodProbDist law (ccaTableLaw M C q)) := by
  unfold oracleSystem
  rw [cca_smul]
  -- The bisimulation identifies both states for each pair of oracle and replacement draws.
  refine TypedSystem.ofAutomaton_map_congr _ _
    (Distribution.prodProbDist law (ccaTableLaw M C q)) _ _ ?_
  intro ω
  exact automatonSystem_eq_of_bisim _ (cca_bisim encrypt decrypt) ⟨rfl, rfl, rfl, rfl, rfl⟩

omit [DecidableEq M] in
/-- Ideal attachment adds an independent replacement table to an encryption oracle.
Decryption replays the original message for its own ciphertexts, rejecting all others. -/
lemma aeIdeal_system
    -- `Ω` carries the retained draw from `law`; `encrypt` is its encryption rule.
    -- The outer budget `q` induces `AE.Ideal.insideBudget M C q` for the encryption oracle.
    {Ω : Type} (q : AE.Port → ℕ) (encrypt : Ω → ℕ → M → C)
    (law : Distribution.ProbDist Ω) :
    AE.Ideal.perPort M C (budget := q) •
        encryptionOracleSystem (AE.Ideal.insideBudget M C q) encrypt law =
      oracleSystem q (replacedEncrypt (AE.Ideal.law1 M C) encrypt)
        (idealDecrypt (AE.Ideal.law1 M C) encrypt)
        (Distribution.prodProbDist law (idealTableLaw M C q)) := by
  unfold encryptionOracleSystem oracleSystem
  rw [aeIdeal_smul]
  refine TypedSystem.ofAutomaton_map_congr _ _
    (Distribution.prodProbDist law (idealTableLaw M C q)) _ _ ?_
  intro ω
  exact automatonSystem_eq_of_bisim _ (aeIdeal_bisim encrypt) ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The hybrid and the ideal as oracles -/

variable (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ)

/-- **The corrected hybrid** `ρ^ptxt ∘ ρ^cca ∘ ρ^ptxt ∘ ρ^cca` of the real system. -/
noncomputable def Hybrid : TypedSystem (AE.perPort M C q) :=
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

/-- Draw `((realTables, innerTable), outerTable)` with law `(μ × ν) × ν`:
`μ` is the real key/encryption-table law and `ν` the CCA replacement-table law.
The inner and outer CCA converters each own one independent replacement table. -/
noncomputable abbrev hybridLaw :=
  Distribution.prodProbDist
    (Distribution.prodProbDist
      (realTableLaw scheme (AE.Real.bound scheme * ∑ i, q i)) (ccaTableLaw M C q))
    (ccaTableLaw M C q)

/-- The assembled hybrid equals its sampled oracle on `hybridLaw`, as typed systems. -/
lemma hybrid_system : Hybrid scheme q =
    oracleSystem q (hybridEncrypt scheme) (hybridDecrypt scheme) (hybridLaw scheme q) := by
  rw [Hybrid, real_system, cca_system, ptxt_system, cca_system, ptxt_system]

/-- A hybrid transcript has the `hybridLaw`-mass of draws whose oracle produces it. -/
lemma hybrid_mass (h : List ((Σ i, (AE.perPort M C q).X i) × (Σ i, (AE.perPort M C q).Y i))) :
    (Hybrid scheme q).1 h =
      (hybridLaw scheme q).1.mass fun ω =>
        Replies (filterDom (AE.perPort M C q).domain
          (automatonSystem (oracleStep (hybridEncrypt scheme) (hybridDecrypt scheme)) (ω, [])))
          (h.map Prod.fst) (h.map Prod.snd) := by
  rw [hybrid_system, oracleSystem_mass]

/-- The ideal's encryption: the real encryption of the replacement messages. -/
noncomputable abbrev idealEncrypt {k k' : ℕ} :
    ((Fin k → K) × (Fin k → (K × M → C))) × (Fin k' → M) → ℕ → M → C :=
  replacedEncrypt (AE.Ideal.law1 M C) (realEncrypt scheme)

/-- The size of the real encryption system's tables in the ideal. -/
abbrev idealTableSize : ℕ :=
  Encryption.Real.bound scheme * ∑ i, AE.Ideal.insideBudget M C q i

/-- Draw `(realTables, replacementTable)` independently. The key and encryption tables
have `idealTableSize scheme q` entries; the replacement table belongs to the ideal converter. -/
noncomputable abbrev idealLaw :=
  Distribution.prodProbDist (realTableLaw scheme (idealTableSize scheme q)) (idealTableLaw M C q)

/-- The ideal converter attached to real encryption equals its sampled oracle on `idealLaw`. -/
lemma ideal_system :
    AE.Ideal.perPort M C (budget := q) • Encryption.Real.perPort scheme =
      oracleSystem q (idealEncrypt scheme) (idealDecrypt (AE.Ideal.law1 M C) (realEncrypt scheme))
        (idealLaw scheme q) := by
  rw [encryptionReal_system, aeIdeal_system]

/-- An ideal transcript has the `idealLaw`-mass of draws whose oracle produces it. -/
lemma ideal_mass (h : List ((Σ i, (AE.perPort M C q).X i) × (Σ i, (AE.perPort M C q).Y i))) :
    (AE.Ideal.perPort M C (budget := q) • Encryption.Real.perPort scheme :
        TypedSystem (AE.perPort M C q)).1 h =
      (idealLaw scheme q).1.mass fun ω =>
        Replies (filterDom (AE.perPort M C q).domain
          (automatonSystem (oracleStep (idealEncrypt scheme)
            (idealDecrypt (AE.Ideal.law1 M C) (realEncrypt scheme))) (ω, [])))
          (h.map Prod.fst) (h.map Prod.snd) := by
  rw [ideal_system, oracleSystem_mass]

end Replacement

end AuthenticatedEncryption

