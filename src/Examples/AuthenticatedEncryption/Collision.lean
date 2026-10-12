import Examples.AuthenticatedEncryption.Hybrid
import ConstructiveCryptography.PresentedGame

/-!
# Authenticated encryption: the collision step

The corrected statistical step of Banfi's §2.3.4 (printed pp. 24–25). The hybrid oracle answers
as the ideal oracle unless an original message equals one of the outer replacement messages.
The outer replacement table is independent of the ideal system's tables, so the collision game,
the hybrid with the collision as its condition, is conditionally equivalent to the ideal, and the
distance is at most the collision probability, `q_e² / |M|` for `q_e` encryption queries.
Unlike the printed argument, the collision event covers every pair of an original message and a
replacement message, in either order.

## Main definitions

* `Collision law known t`: an original message equals one of the first replacement messages

## Main results

* `collision_mass_le`: the collision probability is at most `n² / |M|`
* `hybridDecrypt_eq`: without a collision, the hybrid decrypts as the ideal
* `ideal_mass_hybridTables`: the ideal oracle reads only the first entries of the real system's
  tables, so it has the same mass on the hybrid's tables as on the ideal's smaller ones
* `collisionGame_conditionallyEquivalent`: the collision game is conditionally equivalent to
  the ideal
* `collisionGame_badProbability_le`: the collision probability on admitted queries
* `hybrid_ideal_distance_le`: the hybrid is within `q_e² / |M|` of the ideal
-/

open SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface Probability
open Commons
open scoped SystemAlgebra

namespace AuthenticatedEncryption

variable {K M C : Type} [Fintype K] [Fintype M] [Fintype C] [DecidableEq K] [DecidableEq M]

/-- An original message equals one of the first replacement messages, as many as there are
original messages. -/
def Collision {k : ℕ} (law : Distribution.ProbDist M) (known : List M) (t : Fin k → M) : Prop :=
  ∃ m ∈ known, ∃ i < known.length, entry law t i = m

omit [Fintype K] [Fintype M] [DecidableEq K] [DecidableEq M] in
/-- Within the table's size, a source reads the table. -/
theorem entry_of_lt {k : ℕ} (law : Distribution.ProbDist M) (t : Fin k → M) {i : ℕ}
    (hi : i < k) : entry law t i = t ⟨i, hi⟩ := by
  -- The source's step at position `i < k` reads the table entry `t ⟨i, hi⟩`.
  simp [entry, sourceStep, hi]

omit [Fintype C] [Fintype K] [DecidableEq K] [DecidableEq M] in
/-- **The collision probability** of `n` original messages and a uniform table is at most
`n² / |M|`. -/
theorem collision_mass_le [Nonempty M] {k : ℕ} (known : List M) (hk : known.length ≤ k) :
    (tableLaw 𝒰[M] k).mass (Collision 𝒰[M] known) ≤ (known.length : ℝ) ^ 2 / Fintype.card M := by
  -- Plan, with `n = |known|` (a union bound over pairs):
  --   1. a collision is a pair `(i, m)`, `i < n` and `m` an original message, with
  --      `entry t i = m`;
  --   2. for each pair, entry `i` of the uniform table is uniform, so `Pr ≤ 1/|M|`;
  --   3. sum over the `n · |known as a set| ≤ n²` pairs.
  classical
  -- Step 1: each collision `entry t i = m` is witnessed by the pair `(i, m)` in
  -- `range n × known`; `i < n ≤ k`, so `i` indexes the table.
  have cover : ∀ t : Fin k → M, Collision 𝒰[M] known t →
      ∃ p ∈ Finset.range known.length ×ˢ known.toFinset,
        (fun p (t : Fin k → M) => p.1 < k ∧ entry 𝒰[M] t p.1 = p.2) p t := by
    rintro t ⟨m, hm, i, hi, he⟩
    exact ⟨(i, m), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, List.mem_toFinset.mpr hm⟩,
      hi.trans_le hk, he⟩
  -- The table law is nonnegative, as monotonicity and the union bound need.
  have hnn : (tableLaw 𝒰[M] k).NonNeg := (tableLaw_isProbDist 𝒰[M] k).1
  -- Step 2: each pair's event has probability at most `1/|M|`.
  have pair : ∀ p : ℕ × M, (tableLaw 𝒰[M] k).mass
      (fun t => p.1 < k ∧ entry 𝒰[M] t p.1 = p.2) ≤ 1 / (Fintype.card M : ℝ) := by
    rintro ⟨i, m⟩
    by_cases hi : i < k
    -- `i < k`: the event `entry t i = m` is `t i = m`, the marginal of coordinate `i` at `m`.
    · have e : (tableLaw 𝒰[M] k).mass (fun t => i < k ∧ entry 𝒰[M] t i = m) =
          Distribution.marginalAt (tableLaw 𝒰[M] k) ⟨i, hi⟩ m := by
        rw [Distribution.marginalAt_apply]
        refine Distribution.mass_congr _ fun t => ?_
        simp [entry_of_lt _ _ hi, hi]
      -- The marginal of an independent product is its `i`-th factor scaled by the weights of
      -- the others; the factor is uniform, `1/|M|` at `m`, and every weight is 1.
      rw [e, tableLaw, Distribution.marginalAt_pi]
      simp [DSL.uniform, Distribution.uniform_apply, Distribution.weight_uniform]
    -- `i ≥ k`: the event requires `i < k`, so it is empty: probability `0 ≤ 1/|M|`.
    · exact (Distribution.mass_eq_zero_of_forall_not _ fun t ht => hi ht.1).le.trans
        (by positivity)
  -- Step 3: the union bound.
  --
  --   Pr[Collision] ≤ Pr[∃ (i, m) ∈ range n × known, entry t i = m]    (cover, monotonicity)
  --                 ≤ Σ_(i, m) Pr[entry t i = m]                       (union bound)
  --                 ≤ Σ_(i, m) 1/|M|                                   (pair)
  --                 = n · |known as a set| / |M|
  --                 ≤ n² / |M|                                         (|known as a set| ≤ n)
  calc (tableLaw 𝒰[M] k).mass (Collision 𝒰[M] known)
      ≤ (tableLaw 𝒰[M] k).mass (fun t => ∃ p ∈ Finset.range known.length ×ˢ known.toFinset,
          p.1 < k ∧ entry 𝒰[M] t p.1 = p.2) := Distribution.mass_mono hnn cover
    _ ≤ ∑ p ∈ Finset.range known.length ×ˢ known.toFinset, (tableLaw 𝒰[M] k).mass
          (fun t => p.1 < k ∧ entry 𝒰[M] t p.1 = p.2) := Distribution.mass_exists_le hnn _ _
    _ ≤ ∑ _p ∈ Finset.range known.length ×ˢ known.toFinset, 1 / (Fintype.card M : ℝ) :=
          Finset.sum_le_sum fun p _ => pair p
    -- A constant sum over a product set: its size is `n · |known as a set|`.
    _ = (known.length * known.toFinset.card : ℝ) / Fintype.card M := by
          simp [Finset.card_product]; ring
    _ ≤ (known.length : ℝ) ^ 2 / Fintype.card M := by
          -- Dividing by `|M| ≥ 0` keeps the order; then `n · |known as a set| ≤ n · n`.
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          rw [pow_two]
          exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (List.toFinset_card_le _))
            (Nat.cast_nonneg _)

section Agreement

variable [DecidableEq C] [Nonempty M] (scheme : SymmetricEncryption K M C)

omit [Fintype K] [Fintype M] [Fintype C] [DecidableEq K] [DecidableEq M] [Nonempty M] in
/-- A replayed message is one of the recorded messages. -/
theorem replay_mem {l : List M} {l' : List C} {c : C} {m : M}
    (h : AE.replay (l.zip l') c = some m) : m ∈ l := by
  -- `replay` returns the message of the first entry `e` of the table whose ciphertext is `c`.
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  -- That entry lies in `l.zip l'`, so its message lies in `l`.
  exact (List.of_mem_zip (List.mem_of_find?_eq_some he)).1

/-- **Without a collision, the hybrid decrypts as the ideal**: a replay passes both plaintext
filters, and a fresh ciphertext survives both only if its message is an original and a
replacement message. -/
theorem hybridDecrypt_eq {k k' : ℕ}
    (ω : (((Fin k → K) × (Fin k → (K × M → C))) × (Fin k' → M)) × (Fin k' → M))
    (known : List M) (c : C) (hgood : ¬ Collision (AE.CCA.law1 M C) known ω.2) :
    hybridDecrypt scheme ω known c =
      idealDecrypt (AE.Ideal.law1 M C) (realEncrypt scheme) ω.1 known c := by
  -- Plan. Write `Q = known` for the original messages, `R` for the first `|Q|` outer
  -- replacement messages, and `cs` for the ciphertexts of the first `|Q|` encryptions.
  -- Unfolded, the two decryptions of `c` are
  --
  --   hybrid:  retain Q (replay (zip Q cs) c  orElse  retain R (inner answer to c))
  --   ideal :            replay (zip Q cs) c
  --
  -- (the outer `ρ^ptxt` keeps messages in `Q`, the inner one keeps messages in `R`).
  --   1. the outer replay finds `m`: then `m ∈ Q`, the outer filter keeps it, as the ideal;
  --   2. it finds nothing: the ideal answers ⊥, and the hybrid answers `m` only when
  --      `m ∈ R` and `m ∈ Q`, a collision, which is excluded.
  --
  -- The outer `ρ^cca`'s ciphertexts are the ideal's: the outer replacement message is not
  -- used, the `i`-th ciphertext encrypts the `i`-th inner replacement message (definitional).
  have hcs : replacedCiphertexts (AE.CCA.law1 M C) (replacedEncrypt (AE.CCA.law1 M C)
        (realEncrypt scheme)) ω.1 ω.2 known.length =
      replacedCiphertexts (AE.Ideal.law1 M C) (realEncrypt scheme) ω.1.1 ω.1.2 known.length := rfl
  -- Unfold both decryptions into the shape above.
  simp only [hybridDecrypt, ptxtDecrypt, ccaDecrypt, idealDecrypt, hcs]
  -- Case on the outer replay of the original messages' table.
  cases hr : AE.replay (known.zip (replacedCiphertexts (AE.Ideal.law1 M C) (realEncrypt scheme)
      ω.1.1 ω.1.2 known.length)) c with
  -- Step 1: the replay finds `m`; `m ∈ Q` (`replay_mem`), so `retain Q` keeps `some m`.
  | some m => simp [AE.retain, replay_mem hr]
  -- Step 2: the replay finds nothing; the ideal answers ⊥, and the hybrid passes on to the
  -- inner answer, filtered by `retain R` and then by `retain Q`.
  | none =>
    simp only [Option.orElse_none]
    -- Case on the inner answer: the inner replay, otherwise the real decryption.
    cases hy : (AE.replay ((replacements (AE.CCA.law1 M C) ω.2 known.length).zip
        (replacedCiphertexts (AE.CCA.law1 M C) (realEncrypt scheme) ω.1.1 ω.1.2
          (replacements (AE.CCA.law1 M C) ω.2 known.length).length)) c).orElse
        (fun _ => realDecrypt scheme ω.1.1
          (replacements (AE.CCA.law1 M C) ω.1.2
            (replacements (AE.CCA.law1 M C) ω.2 known.length).length) c) with
    -- No inner message: both filters pass ⊥ on.
    | none => simp [AE.retain]
    -- An inner message `m`: it survives `retain R` only if `m ∈ R`, `retain Q` only if `m ∈ Q`.
    | some m =>
      by_cases h₁ : m ∈ replacements (AE.CCA.law1 M C) ω.2 known.length
      · by_cases h₂ : m ∈ known
        -- `m ∈ R` and `m ∈ Q`: `m` is the `i`-th outer replacement message, `i < |Q|`, and an
        -- original message: a collision, which `hgood` excludes.
        · obtain ⟨i, hi, he⟩ := List.mem_map.mp h₁
          exact absurd ⟨m, h₂, i, List.mem_range.mp hi, he⟩ hgood
        -- `m ∈ R`, `m ∉ Q`: the outer filter drops it.
        · simp [AE.retain, h₁, h₂]
      -- `m ∉ R`: the inner filter drops it.
      · simp [AE.retain, h₁]

omit [DecidableEq M] [DecidableEq C] [Nonempty M] in
theorem messages_prefix {h h' : List (Σ p, AE.Input M C p)} (hp : h <+: h') :
    messages h <+: messages h' := by
  -- `h' = h ++ e`, and `messages (h ++ e) = messages h ++ messages e`.
  obtain ⟨e, rfl⟩ := hp
  exact ⟨messages e, (messages_append h e).symm⟩

/-- **Without a collision, the hybrid oracle replies as the ideal oracle.** -/
theorem hybrid_replies_iff {k k' : ℕ}
    (ω : (((Fin k → K) × (Fin k → (K × M → C))) × (Fin k' → M)) × (Fin k' → M))
    (D : List (Σ p, AE.Input M C p) → Prop) (xs : List (Σ p, AE.Input M C p))
    (ys : List (Σ p, AE.Output M C p)) (hgood : ¬ Collision (AE.CCA.law1 M C) (messages xs) ω.2) :
    Replies (filterDom D (automatonSystem (oracleStep (hybridEncrypt scheme)
        (hybridDecrypt scheme)) (ω, []))) xs ys ↔
      Replies (filterDom D (automatonSystem (oracleStep (idealEncrypt scheme)
        (idealDecrypt (AE.Ideal.law1 M C) (realEncrypt scheme))) (ω.1, []))) xs ys := by
  -- The replies to `xs` are determined by the systems on the prefixes of `xs`: compare the
  -- two systems on each prefix `p`.
  refine replies_congr_of_prefix (fun p hp => ?_) ys
  rcases List.eq_nil_or_concat p with rfl | ⟨p, x, rfl⟩
  -- The empty history: both sides agree by definition.
  · rfl
  -- A prefix `p ++ [x]`: after `p` each oracle holds its sample and `messages p`, and if
  -- `p ++ [x]` is admitted by `D` it replies to `x` by one oracle step.
  rw [List.concat_eq_append] at hp ⊢
  simp only [filterDom, automatonSystem_snoc, stateAfter_oracleStep]
  -- Case on the port of `x`.
  rcases x with ⟨(_ | _), x⟩
  -- Encryption: the hybrid's `i`-th ciphertext encrypts the `i`-th inner replacement message
  -- under the real tables, as the ideal's does (definitional).
  · rfl
  -- Decryption: the original messages of `p` are a prefix of those of `xs`, so no collision
  -- on `xs` leaves no collision on `p` (fewer messages, fewer table indices).
  · have hpre := messages_prefix ((List.prefix_append p [⟨.dec, x⟩]).trans hp)
    have hgood' : ¬ Collision (AE.CCA.law1 M C) (messages p) ω.2 := by
      rintro ⟨m, hm, i, hi, he⟩
      exact hgood ⟨m, hpre.subset hm, i, hi.trans_le hpre.length_le, he⟩
    -- Without a collision on `p`, the hybrid decrypts as the ideal (`hybridDecrypt_eq`).
    simp only [oracleStep, hybridDecrypt_eq scheme ω _ x hgood']

end Agreement

section Game

variable [DecidableEq C] [Nonempty M] (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ)

omit [Fintype K] [DecidableEq K] [DecidableEq M] [DecidableEq C] [Nonempty M] in
/-- The encrypted messages are the queries at the encryption port. -/
theorem length_messages (xs : List (Σ p, AE.Input M C p)) :
    (messages xs).length = (SystemAlgebra.restrict AE.Port.enc xs).length := by
  -- Induction on the history: an encryption query adds one message and one query at the
  -- encryption port; a decryption query adds neither.
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨(_ | _), x⟩
    · simp [messages, ih] at ih ⊢
    · simp [messages, ih] at ih ⊢

omit [Fintype K] [Fintype M] [Fintype C] [DecidableEq K] [DecidableEq M] [DecidableEq C]
  [Nonempty M] in
/-- The first `k'` entries of a table read as the table. -/
theorem entry_castLE {X : Type} (law : Distribution.ProbDist X) {k' k : ℕ} (h : k' ≤ k)
    (t : Fin k → X) {i : ℕ} (hi : i < k') :
    entry law (fun j : Fin k' => t (Fin.castLE h j)) i = entry law t i := by
  -- `i < k' ≤ k` indexes both tables, and both read the entry `t i`.
  simp [entry, sourceStep, hi, hi.trans_le h]

omit [Fintype K] in
/-- The real system's tables in the ideal are no larger than in the hybrid. -/
theorem idealTableSize_le : idealTableSize scheme q ≤ AE.Real.bound scheme * ∑ i, q i := by
  -- The encryption system inside the ideal has the single port `enc`, with budget `q enc`.
  have : ∑ i, AE.Ideal.insideBudget M C q i = q .enc := by
    rw [Fintype.sum_eq_single Encryption.Port.enc (fun j hj => absurd (by cases j; rfl) hj)]
    rfl
  -- So its tables have `bound · q enc` entries, against `bound · Σ_i q i` in the hybrid, and
  -- `q enc ≤ Σ_i q i`.
  simp only [idealTableSize, this]
  exact Nat.mul_le_mul_left _ (Finset.single_le_sum (fun i _ => Nat.zero_le (q i))
    (Finset.mem_univ AE.Port.enc))

omit [Fintype K] in
theorem lt_idealTableSize {i : ℕ} (hi : i < q .enc) : i < idealTableSize scheme q := by
  -- As in `idealTableSize_le`, the inside budget sums to `q enc`.
  have : ∑ i, AE.Ideal.insideBudget M C q i = q .enc := by
    rw [Fintype.sum_eq_single Encryption.Port.enc (fun j hj => absurd (by cases j; rfl) hj)]
    rfl
  -- The ideal's tables have `2 · q enc` entries, and `i < q enc ≤ 2 · q enc`.
  simp only [idealTableSize, this, Encryption.Real.bound]
  omega

/-- The first entries of the real system's tables, beside the replacement table. -/
noncomputable abbrev truncateTables {k₂ : ℕ} :
    ((Fin (AE.Real.bound scheme * ∑ i, q i) → K) ×
        (Fin (AE.Real.bound scheme * ∑ i, q i) → (K × M → C))) × (Fin k₂ → M) →
      ((Fin (idealTableSize scheme q) → K) × (Fin (idealTableSize scheme q) → (K × M → C))) ×
        (Fin k₂ → M) :=
  Prod.map (Prod.map (fun t j => t (Fin.castLE (idealTableSize_le scheme q) j))
    (fun t j => t (Fin.castLE (idealTableSize_le scheme q) j))) id

/-- **The ideal oracle reads only the first entries**: on the histories within the budget, it
answers on the real system's tables as on their first entries. -/
theorem ideal_truncate {k₂ : ℕ}
    (ω : ((Fin (AE.Real.bound scheme * ∑ i, q i) → K) ×
      (Fin (AE.Real.bound scheme * ∑ i, q i) → (K × M → C))) × (Fin k₂ → M)) :
    filterDom (AE.perPort M C q).domain (automatonSystem (oracleStep (idealEncrypt scheme)
        (idealDecrypt (AE.Ideal.law1 M C) (realEncrypt scheme))) (ω, [])) =
      filterDom (AE.perPort M C q).domain (automatonSystem (oracleStep (idealEncrypt scheme)
        (idealDecrypt (AE.Ideal.law1 M C) (realEncrypt scheme)))
          (truncateTables scheme q ω, [])) := by
  -- Plan: an admitted history asks at most `q enc` encryptions, so the ideal oracle reads
  -- only the key at entry 0 and the encryption functions at entries `i < q enc`, all within
  -- the first `idealTableSize` entries; off the domain both systems are undefined.
  --
  -- Step 1: the first `q enc` encryptions agree on the full and on the truncated tables.
  have henc : ∀ i < q .enc, ∀ m, idealEncrypt scheme ω i m =
      idealEncrypt scheme (truncateTables scheme q ω) i m := by
    intro i hi m
    have hk := lt_idealTableSize scheme q hi
    -- Both read the key at entry 0 and the encryption function at entry `i`, both below
    -- `idealTableSize`, where the truncated tables read as the full ones (`entry_castLE`).
    simp only [idealEncrypt, replacedEncrypt, realEncrypt, realKey, truncateTables, Prod.map,
      id, entry_castLE _ _ _ hk, entry_castLE _ _ _ (Nat.zero_lt_of_lt hk)]
  -- Step 2: compare the two systems history by history; split on whether `h` is admitted.
  funext h
  unfold filterDom
  split_ifs with hd
  -- Admitted: oracles agreeing on the first `q enc` encryptions agree on the histories with
  -- at most `q enc` encryptions (`oracle_system_congr`).
  · refine oracle_system_congr (n := q .enc) henc (fun known hk c => ?_) h ?_
    -- Decryption replays the table of the first `|known| ≤ q enc` encryptions; the two tables
    -- agree entry by entry, by Step 1.
    · change AE.replay (known.zip (replacedCiphertexts (AE.Ideal.law1 M C) (realEncrypt scheme)
            ω.1 ω.2 known.length)) c =
          AE.replay (known.zip (replacedCiphertexts (AE.Ideal.law1 M C) (realEncrypt scheme)
            (truncateTables scheme q ω).1 (truncateTables scheme q ω).2 known.length)) c
      congr 2
      exact List.map_congr_left fun i hi =>
        henc i ((List.mem_range.mp hi).trans_le hk) (entry (AE.Ideal.law1 M C) ω.2 i)
    -- The history has at most `q enc` encryptions: the domain's budget at the port `enc`.
    · rw [length_messages]
      exact hd.2 .enc
  -- Not admitted: both systems are undefined.
  · rfl

/-- **The ideal oracle on the hybrid's tables** has the mass it has on the ideal's own tables. -/
theorem ideal_mass_hybridTables (xs : List (Σ i, (AE.perPort M C q).X i))
    (ys : List (Σ i, (AE.perPort M C q).Y i)) :
    (Distribution.prod (Distribution.prod
        (tableLaw (AE.Real.law1 scheme) (AE.Real.bound scheme * ∑ i, q i))
        (tableLaw (AE.Real.law2 scheme) (AE.Real.bound scheme * ∑ i, q i)))
        (tableLaw (AE.CCA.law1 M C) (AE.CCA.bound M C * ∑ i, q i))).mass (fun ω =>
      Replies (filterDom (AE.perPort M C q).domain (automatonSystem (oracleStep
        (idealEncrypt scheme) (idealDecrypt (AE.Ideal.law1 M C) (realEncrypt scheme))) (ω, [])))
        xs ys) =
    (Distribution.prod (Distribution.prod
        (tableLaw (AE.Real.law1 scheme) (idealTableSize scheme q))
        (tableLaw (AE.Real.law2 scheme) (idealTableSize scheme q)))
        (tableLaw (AE.Ideal.law1 M C) (AE.Ideal.bound M C * ∑ i, q i))).mass (fun ω =>
      Replies (filterDom (AE.perPort M C q).domain (automatonSystem (oracleStep
        (idealEncrypt scheme) (idealDecrypt (AE.Ideal.law1 M C) (realEncrypt scheme))) (ω, [])))
        xs ys) := by
  -- Plan: truncating the hybrid's key and encryption tables to their first `idealTableSize`
  -- entries pushes the law `L_H` of the hybrid's key, encryption and inner replacement tables
  -- to the ideal's law `L_I`, and the ideal oracle replies on the truncated tables as on the
  -- full ones (`ideal_truncate`):
  --
  --   Pr_{ω ~ L_H}[ideal(ω) replies]
  --     = Pr_{ω ~ L_H}[ideal(truncate ω) replies]   (ideal_truncate)
  --     = Pr_{ω' ~ L_I}[ideal(ω') replies]          (L_I is the pushforward of L_H)
  classical
  -- Step 1: the law of the truncated tables is the ideal's law.
  have hpush : Distribution.fTransform (truncateTables scheme q (k₂ := AE.CCA.bound M C * ∑ i, q i))
      (Distribution.prod (Distribution.prod
        (tableLaw (AE.Real.law1 scheme) (AE.Real.bound scheme * ∑ i, q i))
        (tableLaw (AE.Real.law2 scheme) (AE.Real.bound scheme * ∑ i, q i)))
        (tableLaw (AE.CCA.law1 M C) (AE.CCA.bound M C * ∑ i, q i))) =
      Distribution.prod (Distribution.prod
        (tableLaw (AE.Real.law1 scheme) (idealTableSize scheme q))
        (tableLaw (AE.Real.law2 scheme) (idealTableSize scheme q)))
        (tableLaw (AE.CCA.law1 M C) (AE.CCA.bound M C * ∑ i, q i)) := by
    -- Truncation acts factor by factor on the product law (the identity on the replacement
    -- table), and the first entries of a table of independent samples are a table of
    -- independent samples (`fTransform_pi_castLE`).
    rw [truncateTables, Distribution.fTransform_prod, Distribution.fTransform_prod,
      Distribution.fTransform_id,
      Distribution.fTransform_pi_castLE _ (AE.Real.law1 scheme).2.2,
      Distribution.fTransform_pi_castLE _ (AE.Real.law2 scheme).2.2]
  -- The ideal's replacement table has the law and size of the inner `ρ^cca`'s (both uniform on
  -- `M`; definitional), so state the right side with the latter.
  change _ = (Distribution.prod (Distribution.prod
        (tableLaw (AE.Real.law1 scheme) (idealTableSize scheme q))
        (tableLaw (AE.Real.law2 scheme) (idealTableSize scheme q)))
        (tableLaw (AE.CCA.law1 M C) (AE.CCA.bound M C * ∑ i, q i))).mass _
  -- Step 2: write the right side as the pushforward, and pull the event back along truncation.
  rw [← hpush, Distribution.mass_fTransform]
  -- Step 3: pointwise, truncation does not change the replies (`ideal_truncate`).
  exact Distribution.mass_congr _ fun ω => by rw [ideal_truncate scheme q ω]

/-- The law of the hybrid's tables: the ideal's tables beside the outer replacement table. -/
noncomputable abbrev hybridLaw :=
  Distribution.prod (Distribution.prod (Distribution.prod
    (tableLaw (AE.Real.law1 scheme) (AE.Real.bound scheme * ∑ i, q i))
    (tableLaw (AE.Real.law2 scheme) (AE.Real.bound scheme * ∑ i, q i)))
    (tableLaw (AE.CCA.law1 M C) (AE.CCA.bound M C * ∑ i, q i)))
    (tableLaw (AE.CCA.law1 M C) (AE.CCA.bound M C * ∑ i, q i))

theorem hybridLaw_isProbDist : (hybridLaw scheme q).isProbDist := by
  -- A product of probability laws is one, and each table law is one.
  repeat' (first | apply Distribution.prod_isProbDist | exact tableLaw_isProbDist _ _)

/-- **The collision game**: the hybrid oracle, whose condition is a collision between the
original messages and the outer replacement messages. -/
noncomputable def collisionGame :
    PDG (Σ i, (AE.perPort M C q).X i) (Σ i, (AE.perPort M C q).Y i)
      (AE.perPort M C q).inputDomain :=
  Distribution.fTransform (fun ω =>
    -- At the sample `ω` of the hybrid's tables, the DDG: the hybrid oracle restricted to the
    -- admitted histories, ...
    ⟨(⟨filterDom (AE.perPort M C q).domain (automatonSystem
          (oracleStep (hybridEncrypt scheme) (hybridDecrypt scheme)) (ω, [])),
        (automatonSystem_isDDS _ _).filterDom _ (AE.perPort M C q).nonempty_prefix.2⟩,
      -- ... with the condition that an original message collides with the outer table `ω.2`,
      -- monotone because the messages of a prefix are a prefix of the messages.
      ⟨fun xs => Collision (AE.CCA.law1 M C) (messages xs) ω.2, fun _ _ hp ⟨m, hm, i, hi, he⟩ =>
        ⟨m, (messages_prefix hp).subset hm, i, hi.trans_le (messages_prefix hp).length_le, he⟩⟩),
      -- Its DDS is defined exactly on the admitted histories, which are nonempty.
      HasDomain.ofInputs fun h => by
        rw [filterDom_dom, automatonSystem_dom]
        exact ⟨fun hd => hd.1, fun hd =>
          ⟨hd, fun he => (AE.perPort M C q).nonempty_prefix.1 (he ▸ hd)⟩⟩⟩)
    (hybridLaw scheme q)

theorem collisionGame_isProbDist : (collisionGame scheme q).isProbDist :=
  Distribution.fTransform_isProbDist _ (hybridLaw_isProbDist scheme q)

/-- The hybrid is the behavior of the collision game's visible systems. -/
theorem hybrid_visible : (Hybrid scheme q).1 = PDS.behavior (collisionGame scheme q).underlying
    (PDG.underlying_probability (collisionGame_isProbDist scheme q)) := by
  -- Compare the two random systems transcript by transcript.
  apply RandomSystem.ext
  intro h
  -- Left: the hybrid oracle on independent tables (`hybrid_mass`). Right: the behavior of the
  -- visible PDS is the mass of the samples whose DDS gives the transcript; the visible PDS
  -- is a pushforward of the collision game, itself a pushforward of `hybridLaw`, so both
  -- sides become the same mass over `hybridLaw`.
  rw [hybrid_mass, PDS.behavior_mass, behaviorMass, PDG.underlying, collisionGame,
    Distribution.mass_fTransform, Distribution.mass_fTransform]

/-- The condition holds with the probability of a collision with the outer replacement table. -/
theorem collisionGame_badProbability (xs : List (Σ i, (AE.perPort M C q).X i)) :
    (collisionGame scheme q).badProbability xs =
      (tableLaw (AE.CCA.law1 M C) (AE.CCA.bound M C * ∑ i, q i)).mass
        (Collision (AE.CCA.law1 M C) (messages xs)) := by
  -- The condition's probability is the mass, over `hybridLaw`, of a collision with `ω.2`.
  rw [PDG.badProbability, collisionGame, Distribution.mass_fTransform]
  -- The event reads only the last factor `ω.2`: write it as `True ∧ Collision` to split it.
  rw [show (fun ω : _ × _ => Collision (AE.CCA.law1 M C) (messages xs) ω.2) =
      (fun ω => True ∧ Collision (AE.CCA.law1 M C) (messages xs) ω.2) from by simp]
  dsimp only [hybridLaw]
  -- Independence: on the product law the mass is `Pr[True] · Pr[Collision]`, ...
  refine (Distribution.mass_prod_and _ _ (fun _ => True)
    (Collision (AE.CCA.law1 M C) (messages xs))).trans ?_
  -- ... and `Pr[True] = 1`, the other tables' law being a probability law.
  rw [Distribution.mass_true, (Distribution.prod_isProbDist _ _ (Distribution.prod_isProbDist _ _
    (tableLaw_isProbDist _ _) (tableLaw_isProbDist _ _)) (tableLaw_isProbDist _ _)).2, one_mul]

/-- **The collision game is conditionally equivalent to the ideal**: the replies with no
collision are the ideal replies, independently of the outer replacement table. -/
theorem collisionGame_conditionallyEquivalent :
    Interface.Game.ofPDG (collisionGame scheme q) (collisionGame_isProbDist scheme q)
        (hybrid_visible scheme q) |≡
      (AE.Ideal.perPort M C (budget := q) • Encryption.Real.perPort scheme :
        Interface.Resource (AE.perPort M C q)) := by
  -- Plan, on a transcript `h` with queries `xs`, `ω = (ω.1, ω.2)` the hybrid's tables with
  -- `ω.2` the outer replacement table, and `Coll` the collision of `xs`'s original messages
  -- with `ω.2`:
  --   1. reduce `|≡` to the factorization of the replies with the condition unset;
  --   2. rewrite `1 − Pr[Coll]` as `Pr[¬Coll]`;
  --   3. without a collision the hybrid replies as the ideal oracle on `ω.1`;
  --   4. `ω.1` and `ω.2` are independent, so the mass factors;
  --   5. the ideal oracle on `ω.1` has the ideal's own mass.
  --
  --   Pr_ω[hybrid(ω) replies h ∧ ¬Coll(ω.2)]
  --     = Pr_ω[ideal(ω.1) replies h ∧ ¬Coll(ω.2)]       (step 3, hybrid_replies_iff)
  --     = Pr[ideal(ω.1) replies h] · Pr[¬Coll]          (step 4, independence)
  --     = Pr[¬Coll] · P_ideal(h)                        (step 5, ideal_mass_hybridTables)
  --     = (1 − Pr[Coll]) · P_ideal(h)                   (step 2, complement)
  --
  -- Step 1: the presented game is `|≡` the ideal resource exactly when its game on random
  -- systems is conditionally equivalent to the ideal's random system
  -- (`conditionallyEquivalent_ofPDG_iff`); that follows from the factorization above on every
  -- transcript `h` (`PDG.conditionallyEquivalent_behavior`).
  refine (Interface.Game.conditionallyEquivalent_ofPDG_iff _ _ _ _).mpr
    (PDG.conditionallyEquivalent_behavior _ (AE.perPort M C q).nonempty_prefix fun h => ?_)
  -- Unfold the condition's probability (`collisionGame_badProbability`), the ideal as the
  -- ideal oracle on its tables (`ideal_mass`), and the left side as a mass over `hybridLaw`.
  rw [collisionGame_badProbability, ideal_mass, PDG.goodProbability, collisionGame,
    Distribution.mass_fTransform]
  -- Step 2: `Pr[Coll] + Pr[¬Coll] = 1` on the outer table, so `1 − Pr[Coll] = Pr[¬Coll]`.
  have hcompl := Distribution.mass_add_compl
    (tableLaw (AE.CCA.law1 M C) (AE.CCA.bound M C * ∑ i, q i))
    (Collision (AE.CCA.law1 M C) (messages (h.map Prod.fst)))
  rw [(tableLaw_isProbDist _ _).2] at hcompl
  have hgood : (1 : ℝ) - (tableLaw (AE.CCA.law1 M C) (AE.CCA.bound M C * ∑ i, q i)).mass
      (Collision (AE.CCA.law1 M C) (messages (h.map Prod.fst))) =
      (tableLaw (AE.CCA.law1 M C) (AE.CCA.bound M C * ∑ i, q i)).mass
        (fun t => ¬ Collision (AE.CCA.law1 M C) (messages (h.map Prod.fst)) t) := by linarith
  rw [hgood]
  dsimp only [hybridLaw]
  -- Step 3: on the samples without a collision, the hybrid oracle's replies are the ideal
  -- oracle's on `ω.1` (`hybrid_replies_iff`).
  rw [Distribution.mass_congr _ fun ω => and_congr_left fun hgood =>
    hybrid_replies_iff scheme ω _ _ _ hgood]
  -- Step 4: the event is `A(ω.1) ∧ B(ω.2)` on the product law, so its mass is the product
  -- `Pr[A] · Pr[B]` (`mass_prod_and`).
  refine (Distribution.mass_prod_and _ _ (fun ω₁ => Replies (filterDom (AE.perPort M C q).domain
    (automatonSystem (oracleStep (idealEncrypt scheme)
      (idealDecrypt (AE.Ideal.law1 M C) (realEncrypt scheme))) (ω₁, [])))
    (h.map Prod.fst) (h.map Prod.snd))
    (fun t => ¬ Collision (AE.CCA.law1 M C) (messages (h.map Prod.fst)) t)).trans ?_
  -- Step 5: reorder the product; the ideal oracle on the hybrid's first tables has the mass
  -- it has on the ideal's own tables (`ideal_mass_hybridTables`).
  rw [mul_comm, ideal_mass_hybridTables]

/-- **The collision bound**: on each admitted query sequence, the condition holds with
probability at most `q_e² / |M|`. -/
theorem collisionGame_badProbability_le (xs : List (Σ i, (AE.perPort M C q).X i))
    (hxs : xs = [] ∨ (AE.perPort M C q).domain xs) :
    (collisionGame scheme q).badProbability xs ≤ (q .enc : ℝ) ^ 2 / Fintype.card M := by
  -- Step 1: the sequence has `n ≤ q_e = q enc` original messages: none if it is empty, and
  -- one per encryption query, at most `q enc` of them, if it is admitted.
  have hn : (messages xs).length ≤ q .enc := by
    rcases hxs with rfl | hxs
    · simp
    · rw [length_messages]
      exact hxs.2 .enc
  -- Step 2: the outer table holds the first `n` replacement messages:
  -- `n ≤ q enc ≤ Σ_i q i ≤ 2 · Σ_i q i`, its length.
  have hk : (messages xs).length ≤ AE.CCA.bound M C * ∑ i, q i := by
    refine hn.trans ((Finset.single_le_sum (fun i _ => Nat.zero_le (q i))
      (Finset.mem_univ AE.Port.enc)).trans ?_)
    unfold AE.CCA.bound
    omega
  -- Step 3: Pr[condition] = Pr[Collision with the outer table]  (collisionGame_badProbability)
  --                        ≤ n² / |M|                            (collision_mass_le)
  --                        ≤ q_e² / |M|                          (n ≤ q_e)
  rw [collisionGame_badProbability]
  refine (collision_mass_le (messages xs) hk).trans ?_
  gcongr

/-- **The collision step**: the hybrid is within `q_e² / |M|` of the ideal. -/
theorem hybrid_ideal_distance_le :
    Δ (Hybrid scheme q) (AE.Ideal.perPort M C (budget := q) • Encryption.Real.perPort scheme :
      Interface.Resource (AE.perPort M C q)) ≤
      ENNReal.ofReal ((q .enc : ℝ) ^ 2 / Fintype.card M) :=
  -- The distinguisher D on the left queries either system at the ports `enc` (sends `m`,
  -- receives `c`) and `dec` (sends `c`, receives `m` or ⊥), at most `q p` times at port `p`;
  -- replies return along the same wires.
  --
  -- The hybrid, ρ^ptxt ∘ ρ^cca ∘ ρ^ptxt ∘ ρ^cca(⟦E_k, D_k⟧):
  --
  --   ┌───┐ ─enc▶ ┌────────┐ ─enc▶ ┌───────┐ ─enc▶ ┌────────┐ ─enc▶ ┌───────┐ ─enc▶ ┌─────────┐
  --   │ D │       │ ρ^ptxt │       │ ρ^cca │       │ ρ^ptxt │       │ ρ^cca │       │⟦E_k,D_k⟧│
  --   └───┘ ─dec▶ └────────┘ ─dec▶ └───────┘ ─dec▶ └────────┘ ─dec▶ └───────┘ ─dec▶ └─────────┘
  --
  -- The ideal, ρ^ae(E_k), which answers `dec` itself by replay of its own encryptions:
  --
  --   ┌───┐ ─enc▶ ┌──────┐ ─enc▶ ┌─────┐
  --   │ D │       │ ρ^ae │       │ E_k │
  --   └───┘ ─dec▶ └──────┘       └─────┘
  --
  -- The collision game has the hybrid as its visible system (`hybrid_visible`) and is
  -- conditionally equivalent to the ideal (`collisionGame_conditionallyEquivalent`), so
  --
  --   Δ(Hybrid, ρ^ae(E_k)) ≤ sup_xs Pr[collision on xs]   (game_dist_le; xs empty or admitted)
  --                        ≤ q_e² / |M|                   (collisionGame_badProbability_le)
  game_dist_le (hybrid_visible scheme q) (collisionGame_conditionallyEquivalent scheme q)
    (collisionGame_badProbability_le scheme q)

end Game

end AuthenticatedEncryption
