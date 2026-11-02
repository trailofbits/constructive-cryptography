module

public import Examples.AuthenticatedEncryption.Oracle

/-!
# Authenticated encryption as sampled oracles

Fix `scheme` and outside budget `q`. Write `O` for `oracleSystem` and `Oᴱ` for
`encryptionOracleSystem`; they retain one draw across all queries. Let
`μ = realTableLaw scheme (AE.system.bound scheme * ∑ i, q i)`, `ν = ccaTableLaw M C q` and
`νᴵ = idealTableLaw M C q`. The component equations are:

```text
Real = O(realEncrypt, realDecrypt, μ)                            real_system
E = Oᴱ(realEncrypt, μᴱ)                                        encryptionReal_system
PTXT  • O(e,d,L) = O(e, ptxtDecrypt d, L)                        ptxt_system
CCA   • O(e,d,L) = O(replacedEncrypt e, ccaDecrypt e d, L × ν)    cca_system
Ideal • Oᴱ(e,L) = O(replacedEncrypt e, idealDecrypt e, L × νᴵ)    aeIdeal_system
```

`Real` is `AE.system.perPort scheme`; `PTXT`, `CCA`, `Ideal` are `AE.PTXT.perPort`,
`AE.CCA.perPort`, `AE.Ideal.perPort`: the source's `⟦E_k,D_k⟧`, `ρ^ptxt`, `ρ^cca`, `ρ^ae`
[1, §2.3.4, pp. 18–19]. `E` is `Encryption.system.perPort scheme`;
`μᴱ = realTableLaw scheme (idealTableSize scheme q)`. Both `E` and `Oᴱ` use the inside budget
`AE.Ideal.insideBudget M C q`. The last two rows use their converter's replacement law.

`real_eq`, `encryptionReal_eq`, `ptxt_smul`, `cca_smul` and `aeIdeal_smul` assemble automata.
The bisimulations in `Examples.AuthenticatedEncryption.Oracle` give per-draw system equality
via `automatonSystem_eq_of_bisim`; `TypedSystem.ofAutomaton_map_congr` lifts it under a common law.
These typed-system equalities rewrite under surrounding converters and parallel systems.

`hybrid_system` assembles `Hybrid`, with `hybridLaw = (μ × ν) × ν`; the two CCA tables are
independent. `ideal_system` gives
`idealLaw = realTableLaw scheme (idealTableSize scheme q) × νᴵ`, where `idealTableSize`
covers the inside encryption budget. Each `×` draws independently.
`oracleSystem_mass` then gives `hybrid_mass` and `ideal_mass`: the mass of draws producing
each transcript on the declared domain.

## References

1. F. Banfi. *A Composable Treatment of Anonymous Communication*. Doctoral thesis,
   Diss. ETH No. 29663, ETH Zurich, 2023.
-/

@[expose] public section

open SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface Probability
open Commons

namespace AuthenticatedEncryption

-- `K,M,C` carry keys, messages and ciphertexts.
variable {K M C : Type} [Fintype K] [Fintype M] [Fintype C] [DecidableEq K] [DecidableEq M]

/-- The raw law of `k` independent samples from `law`:
`tableLaw law k t = ∏ i, law (t i)`. -/
noncomputable abbrev tableLaw
    -- `X` carries entries; `law` distributes one entry; `Fin k` indexes independent entries.
    {X : Type} (law : Distribution.ProbDist X) (k : ℕ) :
    Distribution (Fin k → X) :=
  (Distribution.ProbDist.pi fun _ : Fin k => law).1

omit [Fintype K] [Fintype M] [Fintype C] [DecidableEq K] [DecidableEq M] in
/-- Independent table entries give nonnegative weights summing to one. -/
lemma tableLaw_isProbDist {X : Type} (law : Distribution.ProbDist X) (k : ℕ) :
    (tableLaw law k).isProbDist :=
  (Distribution.ProbDist.pi fun _ : Fin k => law).2

/-- The joint table law is `realTableLaw scheme k (tK,tE) =
(∏ i, AE.system.law1 scheme (tK i)) * (∏ i, AE.system.law2 scheme (tE i))`.
Here `law1` is `scheme.gen` and `law2` is `scheme.encryptions`. -/
noncomputable def realTableLaw
    -- `scheme` supplies the key/encryption laws; `k` is the number of entries in each table.
    (scheme : SymmetricEncryption K M C) (k : ℕ) :
    Distribution.ProbDist ((Fin k → K) × (Fin k → (K × M → C))) :=
  Distribution.prodProbDist
    (Distribution.ProbDist.pi fun _ : Fin k => AE.system.law1 scheme)
    (Distribution.ProbDist.pi fun _ : Fin k => AE.system.law2 scheme)

/-- On `AE.perPort M C q`, draw `ω` once and start at `(ω,[])`. On `enc(m)`, reply
`encrypt ω known.length m` and append `m` to `known`; on `dec(c)`, reply `decrypt ω known c`
and keep the state. -/
noncomputable def oracleSystem
    -- `Ω` is the type of the retained draw `ω`; `q p` bounds the queries at port `p`.
    {Ω : Type} (q : AE.Port → ℕ)
    -- Encryption replies with `encrypt ω known.length m`; decryption with `decrypt ω known c`.
    (encrypt : Ω → ℕ → M → C) (decrypt : Ω → List M → C → Option M)
    -- `law` is the distribution of the single draw `ω`.
    (law : Distribution.ProbDist Ω) : TypedSystem (AE.perPort M C q) :=
  TypedSystem.ofAutomaton _ (oracleStep encrypt decrypt)
    (Distribution.ProbDist.map (fun ω => (ω, [])) law)

/-- On `Encryption.perPort M C q`, draw `ω` once and start at `(ω,[])`. Each `enc(m)` replies
`encrypt ω known.length m` and appends `m` to the retained message history `known`. -/
noncomputable def encryptionOracleSystem
    -- `Ω` is the type of the retained draw `ω`; `q .enc` bounds the encryption queries.
    {Ω : Type} (q : Encryption.Port → ℕ)
    -- `encrypt ω i m` answers the `i`-th encryption; `law` distributes the single draw `ω`.
    (encrypt : Ω → ℕ → M → C) (law : Distribution.ProbDist Ω) :
    TypedSystem (Encryption.perPort M C q) :=
  TypedSystem.ofAutomaton _ (encryptionStep encrypt)
    (Distribution.ProbDist.map (fun ω => (ω, [])) law)

omit [DecidableEq M] in
/-- A transcript has the mass of draws whose domain-filtered oracle produces it. -/
lemma oracleSystem_mass
    -- `Ω` carries the retained draw; `q p` bounds admitted queries at AE port `p`.
    {Ω : Type} (q : AE.Port → ℕ)
    -- `encrypt,decrypt` are the reply rules; `law` distributes the single draw they share.
    (encrypt : Ω → ℕ → M → C) (decrypt : Ω → List M → C → Option M)
    (law : Distribution.ProbDist Ω)
    -- `h` is a transcript of query–reply pairs at the ports of `AE.perPort M C q`.
    (h : List ((Σ i, (AE.perPort M C q).X i) × (Σ i, (AE.perPort M C q).Y i))) :
    (oracleSystem q encrypt decrypt law).1 h = law.1.mass fun ω =>
      Replies (filterDom (AE.perPort M C q).domain
        (automatonSystem (oracleStep encrypt decrypt) (ω, [])))
        (h.map Prod.fst) (h.map Prod.snd) := by
  -- Read the transcript event on initialized states, then pull it back to the draw `ω`.
  rw [oracleSystem, TypedSystem.ofAutomaton_mass, Distribution.ProbDist.map,
    Distribution.mass_fTransform]

/-- `AE.system.perPort` equals the automaton with transition `realStep scheme k`, initialized at
`(none,((tK,0),(tE,0)))` for `(tK,tE) ← realTableLaw scheme k`, where
`k = AE.system.bound scheme * ∑ i, q i`.
The key is unread (`none`) and both source counters are zero. -/
lemma real_eq
    -- `scheme` fixes the cryptographic rules; `q p` bounds admitted queries at port `p`.
    (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ) :
    AE.system.perPort scheme (budget := q) = TypedSystem.ofAutomaton (AE.perPort M C q)
      (realStep scheme (AE.system.bound scheme * ∑ i, q i))
      (Distribution.ProbDist.map (fun ω => (none, ((ω.1, 0), (ω.2, 0))))
        (realTableLaw scheme (AE.system.bound scheme * ∑ i, q i))) := by
  inline
  -- Push initialization through the independent product, then compose with `(none,·)`.
  rw [Distribution.prodProbDist_map, Distribution.ProbDist.map_map]
  rfl

/-- `Encryption.system.perPort` equals the automaton with transition `encryptionRealStep scheme k`,
initialized at `(none,((tK,0),(tE,0)))` for `(tK,tE) ← realTableLaw scheme k`, with
`k = Encryption.system.bound scheme * ∑ i, q i`: key unread, both source counters zero. -/
lemma encryptionReal_eq
    -- `scheme` fixes the key/encryption laws; `q .enc` bounds admitted encryption queries.
    (scheme : SymmetricEncryption K M C) (q : Encryption.Port → ℕ) :
    Encryption.system.perPort scheme (budget := q) =
      TypedSystem.ofAutomaton (Encryption.perPort M C q)
        (encryptionRealStep scheme (Encryption.system.bound scheme * ∑ i, q i))
        (Distribution.ProbDist.map (fun ω => (none, ((ω.1, 0), (ω.2, 0))))
          (realTableLaw scheme (Encryption.system.bound scheme * ∑ i, q i))) := by
  inline
  -- Push initialization through the independent product, then compose with `(none,·)`.
  rw [Distribution.prodProbDist_map, Distribution.ProbDist.map_map]
  rfl

/-- The PTXT program forwards `enc(m)` and records `m` in its list `queried`. For `dec(c)`,
it returns `AE.retain queried r`, where `r` is the decryption reply from `step`. -/
noncomputable abbrev ptxtStep
    -- `S` carries the inside state; `step` processes an inside query and returns its reply.
    {S : Type} (step : S → (p : AE.Port) → AE.Input M C p → S × AE.Output M C p) :=
  (AE.PTXT.body M C).combine step (AE.PTXT.bound_spec M C)

/-- PTXT attachment equals `ptxtStep step` initialized at `(none,init ω)` for the same
`ω ← law`. Here `none` defers initialization of the empty message list
until the first invocation. -/
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
  inline
  -- Compose inside initialization with PTXT's initial outer state `(none,·)`.
  rw [Distribution.ProbDist.map_map]
  rfl

section Replacement

variable [DecidableEq C] [Nonempty M]

variable (M C) in
/-- `ccaTableLaw M C q t = ∏ i, AE.CCA.law1 M C (t i)`, with `AE.CCA.law1 M C = 𝒰[M]`.
The source draws the table once; each `enc` reads an unused entry, giving a fresh replacement. -/
noncomputable def ccaTableLaw
    -- `q` bounds outside queries; the program's call bound determines the table length.
    (q : AE.Port → ℕ) :
    Distribution.ProbDist (Fin (AE.CCA.bound M C * ∑ i, q i) → M) :=
  Distribution.ProbDist.pi fun _ : Fin (AE.CCA.bound M C * ∑ i, q i) => AE.CCA.law1 M C

variable (M C) in
/-- `idealTableLaw M C q t = ∏ i, AE.Ideal.law1 M C (t i)`, with `AE.Ideal.law1 M C = 𝒰[M]`.
The source draws the table once; each `enc` reads an unused entry, giving a fresh replacement. -/
noncomputable def idealTableLaw
    -- `q` bounds outside queries; the program's call bound determines the table length.
    (q : AE.Port → ℕ) :
    Distribution.ProbDist (Fin (AE.Ideal.bound M C * ∑ i, q i) → M) :=
  Distribution.ProbDist.pi fun _ : Fin (AE.Ideal.bound M C * ∑ i, q i) => AE.Ideal.law1 M C

/-- CCA runs `step` beside a source of `k` replacements: `enc(m)` encrypts the next replacement
and records `(m,c)`; `dec(c)` returns `AE.replay table c`, forwarding to `step` if absent. -/
noncomputable abbrev ccaStep
    -- `S` is the inside state; `k` counts source entries; `step` processes AE queries.
    {S : Type} (k : ℕ) (step : S → (p : AE.Port) → AE.Input M C p → S × AE.Output M C p) :=
  (AE.CCA.body M C).combine (parallelStep step (sourceStep (q := k) (AE.CCA.law1 M C)))
    (AE.CCA.bound_spec M C)

omit [DecidableEq M] in
/-- CCA attachment equals `ccaStep k step` initialized at `(none,(init ω,(t,0)))`, with
`k = AE.CCA.bound M C * ∑ i, q i`. Its own table `t ← ccaTableLaw M C q` is independent of the
inside draw `ω ← law`; `none` defers initialization of the empty replay table
until the first invocation. -/
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
  inline
  -- Push initialization through the independent product, then compose with `(none,·)`.
  rw [Distribution.prodProbDist_map, Distribution.ProbDist.map_map]
  rfl

/-- The ideal runs `step` beside `k` replacements: `enc(m)` encrypts the next replacement
and records `(m,c)`; `dec(c)` returns `AE.replay table c`. -/
noncomputable abbrev aeIdealStep
    -- `S` is the encryption state; `k` counts source entries; `step` processes encryptions.
    {S : Type} (k : ℕ)
    (step : S → (p : Encryption.Port) → Encryption.Input M p → S × Encryption.Output C p) :=
  (AE.Ideal.body M C).combine (parallelStep step (sourceStep (q := k) (AE.Ideal.law1 M C)))
    (AE.Ideal.bound_spec M C)

omit [DecidableEq M] in
/-- On inside interface `Encryption.perPort M C (AE.Ideal.insideBudget M C q)`, ideal
attachment equals `aeIdealStep k step` initialized at `(none,(init ω,(t,0)))`, with
`k = AE.Ideal.bound M C * ∑ i, q i`. Its own table `t ← idealTableLaw M C q` is independent of
`ω ← law`; `none` defers initialization of the empty replay table until the first invocation. -/
lemma aeIdeal_smul
    -- `Ω,S` carry the draw/state; `q` induces the encryption budget `AE.Ideal.insideBudget M C q`.
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
  inline
  -- Push initialization through the independent product, then compose with `(none,·)`.
  rw [Distribution.prodProbDist_map, Distribution.ProbDist.map_map]
  rfl

end Replacement

/-! ## Component equations for sampled oracles -/

/-- The real system equals its oracle on independent key and encryption tables `(tK,tE)`.
Admitted calls share `realKey scheme tK`, the first key-table entry; encryption `i` reads
entry `i` of `tE`. -/
lemma real_system (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ) :
    AE.system.perPort scheme (budget := q) =
      oracleSystem q (realEncrypt scheme) (realDecrypt scheme)
        (realTableLaw scheme (AE.system.bound scheme * ∑ i, q i)) := by
  rw [real_eq, oracleSystem]
  -- Both representations use the same key and encryption tables from `realTableLaw`.
  refine TypedSystem.ofAutomaton_map_congr _ _
    (realTableLaw scheme (AE.system.bound scheme * ∑ i, q i)) _ _ ?_
  intro ω
  -- The source counters are zero and the real program has not read its key.
  exact automatonSystem_eq_of_bisim _ (real_bisim scheme)
    ⟨rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- The real encryption system is its oracle on independent key and encryption tables. -/
lemma encryptionReal_system (scheme : SymmetricEncryption K M C) (q : Encryption.Port → ℕ) :
    Encryption.system.perPort scheme (budget := q) =
      encryptionOracleSystem q (realEncrypt scheme)
        (realTableLaw scheme (Encryption.system.bound scheme * ∑ i, q i)) := by
  rw [encryptionReal_eq, encryptionOracleSystem]
  refine TypedSystem.ofAutomaton_map_congr _ _
    (realTableLaw scheme (Encryption.system.bound scheme * ∑ i, q i)) _ _ ?_
  intro ω
  -- Initially both representations retain the same tables, with counters zero and key unread.
  exact automatonSystem_eq_of_bisim _ (encryptionReal_bisim scheme)
    ⟨rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- PTXT keeps the draw and encryption rule; `ptxtDecrypt` retains only previously encrypted
messages: “if m ∈ Q then output m, otherwise output ⊥” [1, p. 19]. -/
lemma ptxt_system
    -- `Ω` carries the retained draw; `q p` bounds queries at AE port `p`.
    {Ω : Type} (q : AE.Port → ℕ)
    -- `encrypt,decrypt` are the reply rules under the single draw from `law`.
    (encrypt : Ω → ℕ → M → C) (decrypt : Ω → List M → C → Option M)
    (law : Distribution.ProbDist Ω) :
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
/-- CCA encrypts replacements from its independent table. Decryption replays the
“first corresponding element inserted in Q” [1, p. 18, footnote 2], or applies `decrypt`
to the replacement-message history. -/
lemma cca_system
    -- `Ω` carries the retained draw; `q p` bounds queries at AE port `p`.
    {Ω : Type} (q : AE.Port → ℕ)
    -- `encrypt,decrypt` are the reply rules under the single draw from `law`.
    (encrypt : Ω → ℕ → M → C) (decrypt : Ω → List M → C → Option M)
    (law : Distribution.ProbDist Ω) :
    AE.CCA.perPort M C (budget := q) • oracleSystem q encrypt decrypt law =
      oracleSystem q (replacedEncrypt (AE.CCA.law1 M C) encrypt)
        (ccaDecrypt (AE.CCA.law1 M C) encrypt decrypt)
        (Distribution.prodProbDist law (ccaTableLaw M C q)) := by
  unfold oracleSystem
  rw [cca_smul]
  -- Each pair of draws initializes empty message/replay histories and a zero source counter.
  refine TypedSystem.ofAutomaton_map_congr _ _
    (Distribution.prodProbDist law (ccaTableLaw M C q)) _ _ ?_
  intro ω
  exact automatonSystem_eq_of_bisim _ (cca_bisim encrypt decrypt) ⟨rfl, rfl, rfl, rfl, rfl⟩

omit [DecidableEq M] in
/-- Ideal attachment encrypts replacements from its independent table. Decryption returns
the first original message recorded for its ciphertext, rejecting unrecorded ciphertexts. -/
lemma aeIdeal_system
    -- `Ω` carries the retained draw; `q` induces the inside encryption budget shown below.
    {Ω : Type} (q : AE.Port → ℕ)
    -- `encrypt` replies under the single draw from `law`.
    (encrypt : Ω → ℕ → M → C) (law : Distribution.ProbDist Ω) :
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
  -- Initially both retain the same draw and table, with counter zero and empty message
  -- histories and replay table.
  exact automatonSystem_eq_of_bisim _ (aeIdeal_bisim encrypt) ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The hybrid and the ideal as oracles -/

-- `scheme` supplies the real encryption rules; `q` is the hybrid/ideal outside budget.
variable (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ)

/-- `Hybrid = PTXT • CCA • PTXT • CCA • Real`, with two independent CCA tables.
The printed chain ends at `ρ^ptxt ∘ ρ^cca ∘ ρ^ptxt(⟦E_k,D_k⟧)` [1, p. 24]; the second
`ρ^cca` corrects that chain, as proved in `Examples.AuthenticatedEncryption.Security`. -/
noncomputable def Hybrid : TypedSystem (AE.perPort M C q) :=
  AE.PTXT.perPort M C • AE.CCA.perPort M C • AE.PTXT.perPort M C • AE.CCA.perPort M C •
    AE.system.perPort scheme

/-- `hybridEncrypt scheme ((ω,t),t') i m =
realEncrypt scheme ω i (entry (AE.CCA.law1 M C) t i)`: the ciphertext encrypts the inner
replacement; `m` and the outer table `t'` are unused. -/
noncomputable abbrev hybridEncrypt
    -- `k` counts real-source entries; `k'` counts entries in each replacement table.
    {k k' : ℕ} :
    (((Fin k → K) × (Fin k → (K × M → C))) × (Fin k' → M)) × (Fin k' → M) → ℕ → M → C :=
  replacedEncrypt (AE.CCA.law1 M C) (replacedEncrypt (AE.CCA.law1 M C) (realEncrypt scheme))

/-- With the fixed laws and encryption arguments understood,
`hybridDecrypt = ptxtDecrypt (ccaDecrypt (ptxtDecrypt (ccaDecrypt realDecrypt)))`:
filters and replacements alternate, as in `Hybrid`. -/
noncomputable abbrev hybridDecrypt
    -- `k` counts real-source entries; `k'` counts entries in each replacement table.
    {k k' : ℕ} :
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
      (realTableLaw scheme (AE.system.bound scheme * ∑ i, q i)) (ccaTableLaw M C q))
    (ccaTableLaw M C q)

/-- The assembled hybrid equals its sampled oracle on `hybridLaw`, as typed systems. -/
lemma hybrid_system : Hybrid scheme q =
    oracleSystem q (hybridEncrypt scheme) (hybridDecrypt scheme) (hybridLaw scheme q) := by
  rw [Hybrid, real_system, cca_system, ptxt_system, cca_system, ptxt_system]

/-- A hybrid transcript has the `hybridLaw`-mass of draws whose oracle produces it. -/
lemma hybrid_mass
    -- `h` records query–reply pairs at the outside AE ports.
    (h : List ((Σ i, (AE.perPort M C q).X i) × (Σ i, (AE.perPort M C q).Y i))) :
    (Hybrid scheme q).1 h =
      (hybridLaw scheme q).1.mass fun ω =>
        Replies (filterDom (AE.perPort M C q).domain
          (automatonSystem (oracleStep (hybridEncrypt scheme) (hybridDecrypt scheme)) (ω, [])))
          (h.map Prod.fst) (h.map Prod.snd) := by
  rw [hybrid_system, oracleSystem_mass]

/-- The ideal's encryption: the real encryption of the replacement messages. -/
noncomputable abbrev idealEncrypt
    -- `k` counts real-source entries; `k'` counts entries in the ideal's replacement table.
    {k k' : ℕ} :
    ((Fin k → K) × (Fin k → (K × M → C))) × (Fin k' → M) → ℕ → M → C :=
  replacedEncrypt (AE.Ideal.law1 M C) (realEncrypt scheme)

/-- The real source tables cover the ideal's inside encryption budget, with at most
`Encryption.system.bound scheme` source calls per inside query. -/
abbrev idealTableSize : ℕ :=
  Encryption.system.bound scheme * ∑ i, AE.Ideal.insideBudget M C q i

/-- Draw `(realTables, replacementTable)` independently. The key and encryption tables
have `idealTableSize scheme q` entries; the replacement table belongs to the ideal converter. -/
noncomputable abbrev idealLaw :=
  Distribution.prodProbDist (realTableLaw scheme (idealTableSize scheme q)) (idealTableLaw M C q)

/-- The ideal converter attached to real encryption equals its sampled oracle on `idealLaw`. -/
lemma ideal_system :
    AE.Ideal.perPort M C (budget := q) • Encryption.system.perPort scheme =
      oracleSystem q (idealEncrypt scheme) (idealDecrypt (AE.Ideal.law1 M C) (realEncrypt scheme))
        (idealLaw scheme q) := by
  rw [encryptionReal_system, aeIdeal_system]

/-- An ideal transcript has the `idealLaw`-mass of draws whose oracle produces it. -/
lemma ideal_mass
    -- `h` records query–reply pairs at the outside AE ports.
    (h : List ((Σ i, (AE.perPort M C q).X i) × (Σ i, (AE.perPort M C q).Y i))) :
    (AE.Ideal.perPort M C (budget := q) • Encryption.system.perPort scheme :
        TypedSystem (AE.perPort M C q)).1 h =
      (idealLaw scheme q).1.mass fun ω =>
        Replies (filterDom (AE.perPort M C q).domain
          (automatonSystem (oracleStep (idealEncrypt scheme)
            (idealDecrypt (AE.Ideal.law1 M C) (realEncrypt scheme))) (ω, [])))
          (h.map Prod.fst) (h.map Prod.snd) := by
  rw [ideal_system, oracleSystem_mass]

end Replacement

end AuthenticatedEncryption

