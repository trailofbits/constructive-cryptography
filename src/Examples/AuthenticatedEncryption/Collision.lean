import Examples.AuthenticatedEncryption.Hybrid
import ConstructiveCryptography.GameBound

/-!
# Authenticated encryption: the collision step

The corrected statistical step of Banfi's §2.3.4 (printed pp. 24–25). The hybrid oracle answers
as the ideal oracle unless an original message equals one of the outer replacement messages.
The outer replacement table is independent of the ideal system's tables, so the hybrid is
game-equivalent to the ideal (Maurer's conditional equivalence), and the distance is at most the
collision probability, `q_e² / |M|` for `q_e` encryption queries. Unlike the printed argument,
the collision event covers every pair of an original message and a replacement message, in
either order.

## Main definitions

* `Collision law known t`: an original message equals one of the first replacement messages

## Main results

* `collision_mass_le`: the collision probability is at most `n² / |M|`
* `hybridDecrypt_eq`: without a collision, the hybrid decrypts as the ideal
* `ideal_mass_hybridTables`: the ideal oracle reads only the first entries of the real system's
  tables, so it has the same mass on the hybrid's tables as on the ideal's smaller ones
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
  simp [entry, sourceStep, hi]

omit [Fintype C] [Fintype K] [DecidableEq K] [DecidableEq M] in
/-- **The collision probability** of `n` original messages and a uniform table is at most
`n² / |M|`. -/
theorem collision_mass_le [Nonempty M] {k : ℕ} (known : List M) (hk : known.length ≤ k) :
    (tableLaw 𝒰[M] k).mass (Collision 𝒰[M] known) ≤ (known.length : ℝ) ^ 2 / Fintype.card M := by
  classical
  have cover : ∀ t : Fin k → M, Collision 𝒰[M] known t →
      ∃ p ∈ Finset.range known.length ×ˢ known.toFinset,
        (fun p (t : Fin k → M) => p.1 < k ∧ entry 𝒰[M] t p.1 = p.2) p t := by
    rintro t ⟨m, hm, i, hi, he⟩
    exact ⟨(i, m), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, List.mem_toFinset.mpr hm⟩,
      hi.trans_le hk, he⟩
  have hnn : (tableLaw 𝒰[M] k).NonNeg := (tableLaw_isProbDist 𝒰[M] k).1
  have pair : ∀ p : ℕ × M, (tableLaw 𝒰[M] k).mass
      (fun t => p.1 < k ∧ entry 𝒰[M] t p.1 = p.2) ≤ 1 / (Fintype.card M : ℝ) := by
    rintro ⟨i, m⟩
    by_cases hi : i < k
    · have e : (tableLaw 𝒰[M] k).mass (fun t => i < k ∧ entry 𝒰[M] t i = m) =
          Distribution.marginalAt (tableLaw 𝒰[M] k) ⟨i, hi⟩ m := by
        rw [Distribution.marginalAt_apply]
        refine Distribution.mass_congr _ fun t => ?_
        simp [entry_of_lt _ _ hi, hi]
      rw [e, tableLaw, Distribution.marginalAt_pi]
      simp [DSL.uniform, Distribution.uniform_apply, Distribution.weight_uniform]
    · exact (Distribution.mass_eq_zero_of_forall_not _ fun t ht => hi ht.1).le.trans
        (by positivity)
  calc (tableLaw 𝒰[M] k).mass (Collision 𝒰[M] known)
      ≤ (tableLaw 𝒰[M] k).mass (fun t => ∃ p ∈ Finset.range known.length ×ˢ known.toFinset,
          p.1 < k ∧ entry 𝒰[M] t p.1 = p.2) := Distribution.mass_mono hnn cover
    _ ≤ ∑ p ∈ Finset.range known.length ×ˢ known.toFinset, (tableLaw 𝒰[M] k).mass
          (fun t => p.1 < k ∧ entry 𝒰[M] t p.1 = p.2) := Distribution.mass_exists_le hnn _ _
    _ ≤ ∑ _p ∈ Finset.range known.length ×ˢ known.toFinset, 1 / (Fintype.card M : ℝ) :=
          Finset.sum_le_sum fun p _ => pair p
    _ = (known.length * known.toFinset.card : ℝ) / Fintype.card M := by
          simp [Finset.card_product]; ring
    _ ≤ (known.length : ℝ) ^ 2 / Fintype.card M := by
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          rw [pow_two]
          exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (List.toFinset_card_le _))
            (Nat.cast_nonneg _)

section Agreement

variable [DecidableEq C] [Nonempty M] (scheme : SymmetricEncryption K M C)

omit [Fintype K] [Fintype M] [Fintype C] [DecidableEq K] [DecidableEq M] [Nonempty M] in
/-- A replayed message is one of the recorded messages. -/
theorem replay_mem {l : List M} {l' : List C} {c : C} {m : M} (h : AE.replay (l.zip l') c = some m) :
    m ∈ l := by
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  exact (List.of_mem_zip (List.mem_of_find?_eq_some he)).1

/-- **Without a collision, the hybrid decrypts as the ideal**: a replay passes both plaintext
filters, and a fresh ciphertext survives both only if its message is an original and a
replacement message. -/
theorem hybridDecrypt_eq {k k' : ℕ}
    (ω : (((Fin k → K) × (Fin k → (K × M → C))) × (Fin k' → M)) × (Fin k' → M))
    (known : List M) (c : C) (hgood : ¬ Collision (AE.CCA.law1 M C) known ω.2) :
    hybridDecrypt scheme ω known c =
      idealDecrypt (AE.Ideal.law1 M C) (realEncrypt scheme) ω.1 known c := by
  have hcs : replacedCiphertexts (AE.CCA.law1 M C) (replacedEncrypt (AE.CCA.law1 M C)
        (realEncrypt scheme)) ω.1 ω.2 known.length =
      replacedCiphertexts (AE.Ideal.law1 M C) (realEncrypt scheme) ω.1.1 ω.1.2 known.length := rfl
  simp only [hybridDecrypt, ptxtDecrypt, ccaDecrypt, idealDecrypt, hcs]
  cases hr : AE.replay (known.zip
      (replacedCiphertexts (AE.Ideal.law1 M C) (realEncrypt scheme) ω.1.1 ω.1.2 known.length)) c with
  | some m => simp [AE.retain, replay_mem hr]
  | none =>
    simp only [Option.orElse_none]
    cases hy : (AE.replay ((replacements (AE.CCA.law1 M C) ω.2 known.length).zip
        (replacedCiphertexts (AE.CCA.law1 M C) (realEncrypt scheme) ω.1.1 ω.1.2
          (replacements (AE.CCA.law1 M C) ω.2 known.length).length)) c).orElse
        (fun _ => realDecrypt scheme ω.1.1
          (replacements (AE.CCA.law1 M C) ω.1.2
            (replacements (AE.CCA.law1 M C) ω.2 known.length).length) c) with
    | none => simp [AE.retain]
    | some m =>
      by_cases h₁ : m ∈ replacements (AE.CCA.law1 M C) ω.2 known.length
      · by_cases h₂ : m ∈ known
        · obtain ⟨i, hi, he⟩ := List.mem_map.mp h₁
          exact absurd ⟨m, h₂, i, List.mem_range.mp hi, he⟩ hgood
        · simp [AE.retain, h₁, h₂]
      · simp [AE.retain, h₁]

omit [DecidableEq M] [DecidableEq C] [Nonempty M] in
theorem messages_prefix {h h' : List (Σ p, AE.Input M C p)} (hp : h <+: h') :
    messages h <+: messages h' := by
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
  refine replies_congr_of_prefix (fun p hp => ?_) ys
  rcases List.eq_nil_or_concat p with rfl | ⟨p, x, rfl⟩
  · rfl
  rw [List.concat_eq_append] at hp ⊢
  simp only [filterDom, automatonSystem_snoc, stateAfter_oracleStep]
  rcases x with ⟨(_ | _), x⟩
  · rfl
  · have hpre := messages_prefix ((List.prefix_append p [⟨.dec, x⟩]).trans hp)
    have hgood' : ¬ Collision (AE.CCA.law1 M C) (messages p) ω.2 := by
      rintro ⟨m, hm, i, hi, he⟩
      exact hgood ⟨m, hpre.subset hm, i, hi.trans_le hpre.length_le, he⟩
    simp only [oracleStep, hybridDecrypt_eq scheme ω _ x hgood']

end Agreement

section Game

variable [DecidableEq C] [Nonempty M] (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ)

omit [Fintype K] [DecidableEq K] [DecidableEq M] [DecidableEq C] [Nonempty M] in
/-- The encrypted messages are the queries at the encryption port. -/
theorem length_messages (xs : List (Σ p, AE.Input M C p)) :
    (messages xs).length = (SystemAlgebra.restrict AE.Port.enc xs).length := by
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
  simp [entry, sourceStep, hi, hi.trans_le h]

omit [Fintype K] in
/-- The real system's tables in the ideal are no larger than in the hybrid. -/
theorem idealTableSize_le : idealTableSize scheme q ≤ AE.Real.bound scheme * ∑ i, q i := by
  have : ∑ i, AE.Ideal.insideBudget M C q i = q .enc := by
    rw [Fintype.sum_eq_single Encryption.Port.enc (fun j hj => absurd (by cases j; rfl) hj)]
    rfl
  simp only [idealTableSize, this]
  exact Nat.mul_le_mul_left _ (Finset.single_le_sum (fun i _ => Nat.zero_le (q i))
    (Finset.mem_univ AE.Port.enc))

omit [Fintype K] in
theorem lt_idealTableSize {i : ℕ} (hi : i < q .enc) : i < idealTableSize scheme q := by
  have : ∑ i, AE.Ideal.insideBudget M C q i = q .enc := by
    rw [Fintype.sum_eq_single Encryption.Port.enc (fun j hj => absurd (by cases j; rfl) hj)]
    rfl
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
        (idealDecrypt (AE.Ideal.law1 M C) (realEncrypt scheme))) (truncateTables scheme q ω, [])) := by
  have henc : ∀ i < q .enc, ∀ m, idealEncrypt scheme ω i m =
      idealEncrypt scheme (truncateTables scheme q ω) i m := by
    intro i hi m
    have hk := lt_idealTableSize scheme q hi
    simp only [idealEncrypt, replacedEncrypt, realEncrypt, realKey, truncateTables, Prod.map,
      id, entry_castLE _ _ _ hk, entry_castLE _ _ _ (Nat.zero_lt_of_lt hk)]
  funext h
  unfold filterDom
  split_ifs with hd
  · refine oracle_system_congr (n := q .enc) henc (fun known hk c => ?_) h ?_
    · show AE.replay (known.zip (replacedCiphertexts (AE.Ideal.law1 M C) (realEncrypt scheme)
            ω.1 ω.2 known.length)) c =
          AE.replay (known.zip (replacedCiphertexts (AE.Ideal.law1 M C) (realEncrypt scheme)
            (truncateTables scheme q ω).1 (truncateTables scheme q ω).2 known.length)) c
      congr 2
      exact List.map_congr_left fun i hi =>
        henc i ((List.mem_range.mp hi).trans_le hk) (entry (AE.Ideal.law1 M C) ω.2 i)
    · rw [length_messages]
      exact hd.2 .enc
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
  classical
  have hpush : Distribution.fTransform (truncateTables scheme q (k₂ := AE.CCA.bound M C * ∑ i, q i))
      (Distribution.prod (Distribution.prod
        (tableLaw (AE.Real.law1 scheme) (AE.Real.bound scheme * ∑ i, q i))
        (tableLaw (AE.Real.law2 scheme) (AE.Real.bound scheme * ∑ i, q i)))
        (tableLaw (AE.CCA.law1 M C) (AE.CCA.bound M C * ∑ i, q i))) =
      Distribution.prod (Distribution.prod
        (tableLaw (AE.Real.law1 scheme) (idealTableSize scheme q))
        (tableLaw (AE.Real.law2 scheme) (idealTableSize scheme q)))
        (tableLaw (AE.CCA.law1 M C) (AE.CCA.bound M C * ∑ i, q i)) := by
    rw [truncateTables, Distribution.fTransform_prod, Distribution.fTransform_prod,
      Distribution.fTransform_id,
      Distribution.fTransform_pi_castLE _ (AE.Real.law1 scheme).2.2,
      Distribution.fTransform_pi_castLE _ (AE.Real.law2 scheme).2.2]
  change _ = (Distribution.prod (Distribution.prod
        (tableLaw (AE.Real.law1 scheme) (idealTableSize scheme q))
        (tableLaw (AE.Real.law2 scheme) (idealTableSize scheme q)))
        (tableLaw (AE.CCA.law1 M C) (AE.CCA.bound M C * ∑ i, q i))).mass _
  rw [← hpush, Distribution.mass_fTransform]
  exact Distribution.mass_congr _ fun ω => by rw [ideal_truncate scheme q ω]

/-- The law of the hybrid's tables: the ideal's tables beside the outer replacement table. -/
noncomputable abbrev hybridLaw :=
  Distribution.prod (Distribution.prod (Distribution.prod
    (tableLaw (AE.Real.law1 scheme) (AE.Real.bound scheme * ∑ i, q i))
    (tableLaw (AE.Real.law2 scheme) (AE.Real.bound scheme * ∑ i, q i)))
    (tableLaw (AE.CCA.law1 M C) (AE.CCA.bound M C * ∑ i, q i)))
    (tableLaw (AE.CCA.law1 M C) (AE.CCA.bound M C * ∑ i, q i))

theorem hybridLaw_isProbDist : (hybridLaw scheme q).isProbDist := by
  repeat' (first | apply Distribution.prod_isProbDist | exact tableLaw_isProbDist _ _)

/-- **The collision game**: the hybrid oracle, whose condition is a collision between the
original messages and the outer replacement messages. -/
noncomputable def collisionGame :
    PDG (Σ i, (AE.perPort M C q).X i) (Σ i, (AE.perPort M C q).Y i)
      (AE.perPort M C q).inputDomain :=
  Distribution.fTransform (fun ω =>
    ⟨(⟨filterDom (AE.perPort M C q).domain (automatonSystem
          (oracleStep (hybridEncrypt scheme) (hybridDecrypt scheme)) (ω, [])),
        (automatonSystem_isDDS _ _).filterDom _ (AE.perPort M C q).nonempty_prefix.2⟩,
      ⟨fun xs => Collision (AE.CCA.law1 M C) (messages xs) ω.2, fun _ _ hp ⟨m, hm, i, hi, he⟩ =>
        ⟨m, (messages_prefix hp).subset hm, i, hi.trans_le (messages_prefix hp).length_le, he⟩⟩),
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
  apply RandomSystem.ext
  intro h
  rw [hybrid_mass, PDS.behavior_mass, behaviorMass, PDG.underlying, collisionGame,
    Distribution.mass_fTransform, Distribution.mass_fTransform]

/-- The condition holds with the probability of a collision with the outer replacement table. -/
theorem collisionGame_badProbability (xs : List (Σ i, (AE.perPort M C q).X i)) :
    (collisionGame scheme q).badProbability xs =
      (tableLaw (AE.CCA.law1 M C) (AE.CCA.bound M C * ∑ i, q i)).mass
        (Collision (AE.CCA.law1 M C) (messages xs)) := by
  rw [PDG.badProbability, collisionGame, Distribution.mass_fTransform]
  rw [show (fun ω : _ × _ => Collision (AE.CCA.law1 M C) (messages xs) ω.2) =
      (fun ω => True ∧ Collision (AE.CCA.law1 M C) (messages xs) ω.2) from by simp]
  dsimp only [hybridLaw]
  refine (Distribution.mass_prod_and _ _ (fun _ => True)
    (Collision (AE.CCA.law1 M C) (messages xs))).trans ?_
  rw [Distribution.mass_true, (Distribution.prod_isProbDist _ _ (Distribution.prod_isProbDist _ _
    (tableLaw_isProbDist _ _) (tableLaw_isProbDist _ _)) (tableLaw_isProbDist _ _)).2, one_mul]

/-- **The collision game is equivalent to the ideal**: the replies with no collision are the
ideal replies, independently of the outer replacement table. -/
theorem collisionGame_equivalent :
    GameEquivalent (collisionGame scheme q)
      (AE.Ideal.perPort M C (budget := q) • Encryption.Real.perPort scheme :
        Interface.Resource (AE.perPort M C q)).1 := by
  intro h
  rw [collisionGame_badProbability, ideal_mass, PDG.goodProbability, collisionGame,
    Distribution.mass_fTransform]
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
  rw [Distribution.mass_congr _ fun ω => and_congr_left fun hgood =>
    hybrid_replies_iff scheme ω _ _ _ hgood]
  refine (Distribution.mass_prod_and _ _ (fun ω₁ => Replies (filterDom (AE.perPort M C q).domain
    (automatonSystem (oracleStep (idealEncrypt scheme)
      (idealDecrypt (AE.Ideal.law1 M C) (realEncrypt scheme))) (ω₁, [])))
    (h.map Prod.fst) (h.map Prod.snd))
    (fun t => ¬ Collision (AE.CCA.law1 M C) (messages (h.map Prod.fst)) t)).trans ?_
  rw [mul_comm, ideal_mass_hybridTables]

/-- **The collision bound**: on each admitted query sequence, the condition holds with
probability at most `q_e² / |M|`. -/
theorem collisionGame_badProbability_le (xs : List (Σ i, (AE.perPort M C q).X i))
    (hxs : xs = [] ∨ (AE.perPort M C q).domain xs) :
    (collisionGame scheme q).badProbability xs ≤ (q .enc : ℝ) ^ 2 / Fintype.card M := by
  have hn : (messages xs).length ≤ q .enc := by
    rcases hxs with rfl | hxs
    · simp
    · rw [length_messages]
      exact hxs.2 .enc
  have hk : (messages xs).length ≤ AE.CCA.bound M C * ∑ i, q i := by
    refine hn.trans ((Finset.single_le_sum (fun i _ => Nat.zero_le (q i))
      (Finset.mem_univ AE.Port.enc)).trans ?_)
    unfold AE.CCA.bound
    omega
  rw [collisionGame_badProbability]
  refine (collision_mass_le (messages xs) hk).trans ?_
  gcongr

/-- **The collision step**: the hybrid is within `q_e² / |M|` of the ideal. -/
theorem hybrid_ideal_distance_le :
    Δ (Hybrid scheme q) (AE.Ideal.perPort M C (budget := q) • Encryption.Real.perPort scheme :
      Interface.Resource (AE.perPort M C q)) ≤
      ENNReal.ofReal ((q .enc : ℝ) ^ 2 / Fintype.card M) :=
  (GameEquivalent.game_dist_le (collisionGame_equivalent scheme q)
    (collisionGame_isProbDist scheme q) (hybrid_visible scheme q)).trans
    (ENNReal.ofReal_le_ofReal (PDG.supWinProbability_blind_le _
      (collisionGame_isProbDist scheme q).1 (by positivity)
      (collisionGame_badProbability_le scheme q)))

end Game

end AuthenticatedEncryption
