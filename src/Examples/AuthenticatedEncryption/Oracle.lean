import Commons.Definitions.AEAD

/-!
# Authenticated encryption: the oracle automata

Every system of the development, at a fixed sample, is an oracle automaton: its state is the
sample and the messages encrypted so far; the `i`-th encryption answers from `encrypt ω i` and
decryption from the messages so far. The plaintext filter and the random-message
transformation map oracle automata to oracle automata, and the real and the ideal systems are
oracle automata: each by a bisimulation of its compiled automaton.

## Main definitions

* `oracleStep encrypt decrypt`: the oracle automaton
* `encryptionStep encrypt`: the encryption oracle automaton
* `messages h`: the encrypted messages of a history

## Main results

* `stateAfter_oracleStep`: the oracle's state is the sample and the messages so far
* `ptxt_bisim`, `cca_bisim`, `aeIdeal_bisim`: the plaintext filter and the random-message
  transformation map oracles to oracles, and the ideal transformation maps encryption oracles to
  oracles
* `real_bisim`, `encryptionReal_bisim`: the real system is an oracle, and the real encryption
  system an encryption oracle
* `oracle_system_congr`: oracles agreeing on the first `n` encryptions agree on the histories of
  at most `n` encryptions
-/

open SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface Probability
open Commons

namespace AuthenticatedEncryption

variable {M C Ω : Type} [Fintype M] [Fintype C]

/-- **The oracle automaton**: the `i`-th encryption answers from `encrypt ω i`, decryption from
the messages encrypted so far; the sample `ω` never changes. -/
def oracleStep (encrypt : Ω → ℕ → M → C) (decrypt : Ω → List M → C → Option M) :
    Ω × List M → (p : AE.Port) → AE.Input M C p → (Ω × List M) × AE.Output M C p
  | (ω, known), .enc, m => ((ω, known ++ [m]), encrypt ω known.length m)
  | (ω, known), .dec, c => ((ω, known), decrypt ω known c)

/-- **The encryption oracle automaton**: the `i`-th encryption answers from `encrypt ω i`; the
sample `ω` never changes. -/
def encryptionStep (encrypt : Ω → ℕ → M → C) :
    Ω × List M → (p : Encryption.Port) → Encryption.Input M p →
      (Ω × List M) × Encryption.Output C p
  | (ω, known), .enc, m => ((ω, known ++ [m]), encrypt ω known.length m)

/-- Banfi, printed p. 18, footnote 2: the encryption inputs of a history, in order. -/
def messages : List (Σ p, AE.Input M C p) → List M :=
  List.filterMap fun
    | ⟨.enc, m⟩ => some m
    | ⟨.dec, _⟩ => none

@[simp] theorem messages_nil : messages ([] : List (Σ p, AE.Input M C p)) = [] := rfl

@[simp] theorem messages_append (h k : List (Σ p, AE.Input M C p)) :
    messages (h ++ k) = messages h ++ messages k := List.filterMap_append

@[simp] theorem messages_enc (m : M) : messages (C := C) [⟨.enc, m⟩] = [m] := rfl

@[simp] theorem messages_dec (c : C) : messages (M := M) [⟨.dec, c⟩] = [] := rfl

/-- The oracle's state is its sample and the messages so far. -/
theorem stateAfter_oracleStep (encrypt : Ω → ℕ → M → C) (decrypt : Ω → List M → C → Option M)
    (ω : Ω) (h : List (Σ p, AE.Input M C p)) :
    stateAfter (oracleStep encrypt decrypt) (ω, []) h = (ω, messages h) := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h x ih =>
    rw [stateAfter_snoc, ih]
    rcases x with ⟨(_ | _), x⟩ <;> simp [oracleStep]

section Plaintext

variable [DecidableEq M]

/-- The plaintext filter's decryption: the oracle's decryption, retained when its message was
encrypted. -/
def ptxtDecrypt (decrypt : Ω → List M → C → Option M) : Ω → List M → C → Option M :=
  fun ω known c => AE.retain known (decrypt ω known c)

theorem ptxt_combine_enc (encrypt : Ω → ℕ → M → C) (decrypt : Ω → List M → C → Option M)
    (queried : Option (List M)) (ω : Ω) (known : List M) (m : M) :
    (AE.PTXT.body M C).combine (oracleStep encrypt decrypt) (AE.PTXT.bound_spec M C)
        (queried, (ω, known)) .enc m =
      ((some (queried.getD [] ++ [m]), (ω, known ++ [m])), encrypt ω known.length m) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    cases queried <;> simp [Program.invoke, AE.PTXT.body, callProg, returnProg, oracleStep])

theorem ptxt_combine_dec (encrypt : Ω → ℕ → M → C) (decrypt : Ω → List M → C → Option M)
    (queried : Option (List M)) (ω : Ω) (known : List M) (c : C) :
    (AE.PTXT.body M C).combine (oracleStep encrypt decrypt) (AE.PTXT.bound_spec M C)
        (queried, (ω, known)) .dec c =
      ((some (queried.getD []), (ω, known)), AE.retain (queried.getD []) (decrypt ω known c)) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    cases queried <;> simp [Program.invoke, AE.PTXT.body, callProg, returnProg, oracleStep])

/-- **The plaintext filter on an oracle** answers encryptions as the oracle, and retains the
decryptions whose message was queried. -/
theorem ptxt_bisim (encrypt : Ω → ℕ → M → C) (decrypt : Ω → List M → C → Option M) :
    IsBisim ((AE.PTXT.body M C).combine (oracleStep encrypt decrypt) (AE.PTXT.bound_spec M C))
      (oracleStep encrypt (ptxtDecrypt decrypt))
      (fun a a' => a.2 = a' ∧ a.1.getD [] = a'.2) := by
  rintro ⟨queried, ω, known⟩ ⟨ω', known'⟩ (_ | _) x ⟨h₁, h₂⟩ <;>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₁ <;> dsimp only at h₂
  · rw [ptxt_combine_enc]
    simp [oracleStep, h₂]
  · rw [ptxt_combine_dec]
    simp [oracleStep, ptxtDecrypt, h₂]

end Plaintext

/-- The `n`-th entry a source reads from its table. -/
noncomputable def entry {X : Type} {k : ℕ} (law : Distribution.ProbDist X) (t : Fin k → X)
    (n : ℕ) : X :=
  (sourceStep law (t, n) () ()).2

section Replacement

variable [DecidableEq C] [Nonempty M]

/-- The ciphertexts of the first `n` encryptions of replacement messages from the table `t`. -/
noncomputable def replacedCiphertexts {k : ℕ} (law : Distribution.ProbDist M)
    (encrypt : Ω → ℕ → M → C) (ω : Ω) (t : Fin k → M) (n : ℕ) : List C :=
  (List.range n).map fun i => encrypt ω i (entry law t i)

/-- The first `n` replacement messages from the table `t`. -/
noncomputable def replacements {k : ℕ} (law : Distribution.ProbDist M) (t : Fin k → M) (n : ℕ) :
    List M :=
  (List.range n).map (entry law t)

/-- Encryption of the replacement messages from the table `t`. -/
noncomputable def replacedEncrypt {k : ℕ} (law : Distribution.ProbDist M)
    (encrypt : Ω → ℕ → M → C) : Ω × (Fin k → M) → ℕ → M → C :=
  fun ω i _ => encrypt ω.1 i (entry law ω.2 i)

/-- The random-message transformation's decryption: replay of its own encryptions, otherwise the
oracle's decryption on the replacement messages. -/
noncomputable def ccaDecrypt {k : ℕ} (law : Distribution.ProbDist M) (encrypt : Ω → ℕ → M → C)
    (decrypt : Ω → List M → C → Option M) : Ω × (Fin k → M) → List M → C → Option M :=
  fun ω known c =>
    (AE.replay (known.zip (replacedCiphertexts law encrypt ω.1 ω.2 known.length)) c).orElse
      fun _ => decrypt ω.1 (replacements law ω.2 known.length) c

/-- The ideal transformation's decryption: replay of its own encryptions only. -/
noncomputable def idealDecrypt {k : ℕ} (law : Distribution.ProbDist M) (encrypt : Ω → ℕ → M → C) :
    Ω × (Fin k → M) → List M → C → Option M :=
  fun ω known c => AE.replay (known.zip (replacedCiphertexts law encrypt ω.1 ω.2 known.length)) c

theorem cca_combine_enc {k : ℕ} (encrypt : Ω → ℕ → M → C) (decrypt : Ω → List M → C → Option M)
    (table : Option (List (M × C))) (ω : Ω) (known : List M) (t : Fin k → M) (n : ℕ) (m : M) :
    (AE.CCA.body M C).combine (parallelStep (oracleStep encrypt decrypt) (sourceStep (AE.CCA.law1 M C)))
        (AE.CCA.bound_spec M C) (table, ((ω, known), (t, n))) .enc m =
      ((some (table.getD [] ++ [(m, encrypt ω known.length (entry (AE.CCA.law1 M C) t n))]),
          ((ω, known ++ [entry (AE.CCA.law1 M C) t n]), (t, n + 1))),
        encrypt ω known.length (entry (AE.CCA.law1 M C) t n)) :=
  Program.combine_eq_of_invoke _ _ (n := 2) (by
    cases table <;> simp [Program.invoke, AE.CCA.body, callProg, returnProg, oracleStep,
      parallelStep, entry, sourceStep])

theorem cca_combine_dec_replay {k : ℕ} (encrypt : Ω → ℕ → M → C)
    (decrypt : Ω → List M → C → Option M) (table : Option (List (M × C))) (ω : Ω)
    (known : List M) (r : (Fin k → M) × ℕ) (c : C) {m : M}
    (hr : AE.replay (table.getD []) c = some m) :
    (AE.CCA.body M C).combine (parallelStep (oracleStep encrypt decrypt) (sourceStep (AE.CCA.law1 M C)))
        (AE.CCA.bound_spec M C) (table, ((ω, known), r)) .dec c =
      ((some (table.getD []), ((ω, known), r)), some m) :=
  Program.combine_eq_of_invoke _ _ (n := 0) (by
    cases table <;> simp_all [Program.invoke, AE.CCA.body, returnProg])

theorem cca_combine_dec_fresh {k : ℕ} (encrypt : Ω → ℕ → M → C)
    (decrypt : Ω → List M → C → Option M) (table : Option (List (M × C))) (ω : Ω)
    (known : List M) (r : (Fin k → M) × ℕ) (c : C) (hr : AE.replay (table.getD []) c = none) :
    (AE.CCA.body M C).combine (parallelStep (oracleStep encrypt decrypt) (sourceStep (AE.CCA.law1 M C)))
        (AE.CCA.bound_spec M C) (table, ((ω, known), r)) .dec c =
      ((some (table.getD []), ((ω, known), r)), decrypt ω known c) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    cases table <;> simp_all [Program.invoke, AE.CCA.body, callProg, returnProg, oracleStep,
      parallelStep])

/-- **The random-message transformation on an oracle** encrypts the replacement messages, and
decrypts by replay of its own encryptions, otherwise by the oracle on the replacement
messages. -/
theorem cca_bisim {k : ℕ} (encrypt : Ω → ℕ → M → C) (decrypt : Ω → List M → C → Option M) :
    IsBisim ((AE.CCA.body M C).combine
        (parallelStep (oracleStep encrypt decrypt) (sourceStep (AE.CCA.law1 M C)))
        (AE.CCA.bound_spec M C))
      (oracleStep (replacedEncrypt (k := k) (AE.CCA.law1 M C) encrypt)
        (ccaDecrypt (AE.CCA.law1 M C) encrypt decrypt))
      (fun a a' => a.2.1.1 = a'.1.1 ∧ a.2.2.1 = a'.1.2 ∧ a.2.2.2 = a'.2.length ∧
        a.2.1.2 = replacements (AE.CCA.law1 M C) a'.1.2 a'.2.length ∧
        a.1.getD [] = a'.2.zip (replacedCiphertexts (AE.CCA.law1 M C) encrypt a'.1.1 a'.1.2
          a'.2.length)) := by
  rintro ⟨table, ⟨ω, inner⟩, t, n⟩ ⟨⟨ω', t'⟩, known⟩ (_ | _) x ⟨h₁, h₂, h₃, h₄, h₅⟩ <;>
    dsimp only at h₁ h₂ h₃ h₄ h₅ <;> subst h₁ h₂ h₃ h₄
  · rw [cca_combine_enc]
    have hl : (replacements (AE.CCA.law1 M C) t known.length).length = known.length := by
      simp [replacements]
    refine ⟨by simp [oracleStep, replacedEncrypt, hl], rfl, rfl, by simp [oracleStep], ?_, ?_⟩
    · simp [replacements, List.range_succ, oracleStep]
    · simp only [oracleStep, replacedEncrypt, h₅, Option.getD_some, List.length_append,
        List.length_singleton, replacedCiphertexts, List.range_succ, List.map_append,
        List.map_singleton]
      rw [List.zip_append (by simp)]
      simp [hl]
  · cases hr : AE.replay (table.getD []) x with
    | some m =>
      rw [cca_combine_dec_replay _ _ _ _ _ _ _ hr]
      simp [oracleStep, ccaDecrypt, ← h₅, hr]
    | none =>
      rw [cca_combine_dec_fresh _ _ _ _ _ _ _ hr]
      simp [oracleStep, ccaDecrypt, ← h₅, hr]

theorem aeIdeal_combine_enc {k : ℕ} (encrypt : Ω → ℕ → M → C)
    (table : Option (List (M × C))) (ω : Ω) (known : List M) (t : Fin k → M) (n : ℕ) (m : M) :
    (AE.Ideal.body M C).combine
        (parallelStep (encryptionStep encrypt) (sourceStep (AE.Ideal.law1 M C)))
        (AE.Ideal.bound_spec M C) (table, ((ω, known), (t, n))) .enc m =
      ((some (table.getD [] ++ [(m, encrypt ω known.length (entry (AE.Ideal.law1 M C) t n))]),
          ((ω, known ++ [entry (AE.Ideal.law1 M C) t n]), (t, n + 1))),
        encrypt ω known.length (entry (AE.Ideal.law1 M C) t n)) :=
  Program.combine_eq_of_invoke _ _ (n := 2) (by
    cases table <;> simp [Program.invoke, AE.Ideal.body, callProg, returnProg, encryptionStep,
      parallelStep, entry, sourceStep])

theorem aeIdeal_combine_dec {k : ℕ} (encrypt : Ω → ℕ → M → C)
    (table : Option (List (M × C))) (ω : Ω) (known : List M) (r : (Fin k → M) × ℕ) (c : C) :
    (AE.Ideal.body M C).combine
        (parallelStep (encryptionStep encrypt) (sourceStep (AE.Ideal.law1 M C)))
        (AE.Ideal.bound_spec M C) (table, ((ω, known), r)) .dec c =
      ((some (table.getD []), ((ω, known), r)), AE.replay (table.getD []) c) :=
  Program.combine_eq_of_invoke _ _ (n := 0) (by
    cases table <;> simp [Program.invoke, AE.Ideal.body, returnProg, AE.replay])

/-- **The ideal transformation on an encryption oracle** encrypts the replacement messages, and
decrypts only by replay of its own encryptions. -/
theorem aeIdeal_bisim {k : ℕ} (encrypt : Ω → ℕ → M → C) :
    IsBisim ((AE.Ideal.body M C).combine
        (parallelStep (encryptionStep encrypt) (sourceStep (AE.Ideal.law1 M C)))
        (AE.Ideal.bound_spec M C))
      (oracleStep (replacedEncrypt (k := k) (AE.Ideal.law1 M C) encrypt)
        (idealDecrypt (AE.Ideal.law1 M C) encrypt))
      (fun a a' => a.2.1.1 = a'.1.1 ∧ a.2.2.1 = a'.1.2 ∧ a.2.2.2 = a'.2.length ∧
        a.2.1.2 = replacements (AE.Ideal.law1 M C) a'.1.2 a'.2.length ∧
        a.1.getD [] = a'.2.zip (replacedCiphertexts (AE.Ideal.law1 M C) encrypt a'.1.1 a'.1.2
          a'.2.length)) := by
  rintro ⟨table, ⟨ω, inner⟩, t, n⟩ ⟨⟨ω', t'⟩, known⟩ (_ | _) x ⟨h₁, h₂, h₃, h₄, h₅⟩ <;>
    dsimp only at h₁ h₂ h₃ h₄ h₅ <;> subst h₁ h₂ h₃ h₄
  · rw [aeIdeal_combine_enc]
    have hl : (replacements (AE.Ideal.law1 M C) t known.length).length = known.length := by
      simp [replacements]
    refine ⟨by simp [oracleStep, replacedEncrypt, hl], rfl, rfl, by simp [oracleStep], ?_, ?_⟩
    · simp [replacements, List.range_succ, oracleStep]
    · simp only [oracleStep, replacedEncrypt, h₅, Option.getD_some, List.length_append,
        List.length_singleton, replacedCiphertexts, List.range_succ, List.map_append,
        List.map_singleton]
      rw [List.zip_append (by simp)]
      simp [hl]
  · rw [aeIdeal_combine_dec]
    simp [oracleStep, idealDecrypt, ← h₅]

end Replacement

section Systems

variable {K : Type} [Fintype K] [DecidableEq K] [DecidableEq M] (scheme : SymmetricEncryption K M C)

/-- The key of the real system: the first entry of its key table. -/
noncomputable def realKey {k : ℕ} (tK : Fin k → K) : K := entry (AE.Real.law1 scheme) tK 0

/-- The real system's automaton: its program against its key and encryption sources. -/
noncomputable abbrev realStep (k : ℕ) :=
  (AE.Real.body scheme).combine (parallelStep (sourceStep (q := k) (AE.Real.law1 scheme))
    (sourceStep (q := k) (AE.Real.law2 scheme))) (AE.Real.bound_spec scheme)

theorem real_combine_enc_first {k : ℕ} (tK : Fin k → K) (tE : Fin k → (K × M → C)) (nE : ℕ)
    (m : M) :
    realStep scheme k (none, ((tK, 0), (tE, nE))) .enc m =
      ((some (realKey scheme tK), ((tK, 1), (tE, nE + 1))),
        entry (AE.Real.law2 scheme) tE nE (realKey scheme tK, m)) :=
  Program.combine_eq_of_invoke _ _ (n := 2) (by
    simp [Program.invoke, AE.Real.body, callProg, returnProg, parallelStep, sourceStep, entry,
      realKey])

theorem real_combine_enc_later {k : ℕ} (key : K) (tK : Fin k → K) (nK : ℕ)
    (tE : Fin k → (K × M → C)) (nE : ℕ) (m : M) :
    realStep scheme k (some key, ((tK, nK), (tE, nE))) .enc m =
      ((some key, ((tK, nK), (tE, nE + 1))), entry (AE.Real.law2 scheme) tE nE (key, m)) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    simp [Program.invoke, AE.Real.body, callProg, returnProg, parallelStep, sourceStep, entry])

theorem real_combine_dec_first {k : ℕ} (tK : Fin k → K) (r : (Fin k → (K × M → C)) × ℕ)
    (c : C) :
    realStep scheme k (none, ((tK, 0), r)) .dec c =
      ((some (realKey scheme tK), ((tK, 1), r)), scheme.dec (realKey scheme tK) c) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    simp [Program.invoke, AE.Real.body, callProg, returnProg, parallelStep, sourceStep, entry,
      realKey])

theorem real_combine_dec_later {k : ℕ} (key : K) (r : ((Fin k → K) × ℕ) ×
    ((Fin k → (K × M → C)) × ℕ)) (c : C) :
    realStep scheme k (some key, r) .dec c = ((some key, r), scheme.dec key c) :=
  Program.combine_eq_of_invoke _ _ (n := 0) (by simp [Program.invoke, AE.Real.body, returnProg])

/-- The real encryption: the `i`-th encryption reads entry `i` of the encryption table, under
the key. -/
noncomputable def realEncrypt {k : ℕ} : (Fin k → K) × (Fin k → (K × M → C)) → ℕ → M → C :=
  fun ω i m => entry (AE.Real.law2 scheme) ω.2 i (realKey scheme ω.1, m)

/-- The real decryption, under the key. -/
noncomputable def realDecrypt {k : ℕ} :
    (Fin k → K) × (Fin k → (K × M → C)) → List M → C → Option M :=
  fun ω _ c => scheme.dec (realKey scheme ω.1) c

/-- **The real system is an oracle**: the `i`-th encryption reads entry `i` of the encryption
table under the key, and decryption decrypts under the key. -/
theorem real_bisim {k : ℕ} :
    IsBisim (realStep scheme k (M := M) (C := C))
      (oracleStep (realEncrypt scheme) (realDecrypt scheme))
      (fun a a' => a.2.1.1 = a'.1.1 ∧ a.2.2.1 = a'.1.2 ∧ a.2.2.2 = a'.2.length ∧
        (a.1 = none ∧ a.2.1.2 = 0 ∨ a.1 = some (realKey scheme a'.1.1) ∧ a.2.1.2 = 1)) := by
  rintro ⟨sR, ⟨tK, nK⟩, tE, nE⟩ ⟨⟨tK', tE'⟩, known⟩ (_ | _) x ⟨h₁, h₂, h₃, h₄⟩ <;>
    dsimp only at h₁ h₂ h₃ h₄ <;> subst h₁ h₂ h₃ <;>
    rcases h₄ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [real_combine_enc_first]
    simp [oracleStep, realEncrypt]
  · rw [real_combine_enc_later]
    simp [oracleStep, realEncrypt]
  · rw [real_combine_dec_first]
    simp [oracleStep, realDecrypt]
  · rw [real_combine_dec_later]
    simp [oracleStep, realDecrypt]

omit [Fintype K] [Fintype M] [Fintype C] in
theorem encryptionReal_law1 : Encryption.Real.law1 scheme = AE.Real.law1 scheme := rfl

omit [Fintype C] in
theorem encryptionReal_law2 : Encryption.Real.law2 scheme = AE.Real.law2 scheme := rfl

/-- The real encryption system's automaton: its program against its key and encryption
sources. -/
noncomputable abbrev encryptionRealStep (k : ℕ) :=
  (Encryption.Real.body scheme).combine (parallelStep
    (sourceStep (q := k) (Encryption.Real.law1 scheme))
    (sourceStep (q := k) (Encryption.Real.law2 scheme))) (Encryption.Real.bound_spec scheme)

theorem encryptionReal_combine_first {k : ℕ} (tK : Fin k → K) (tE : Fin k → (K × M → C))
    (nE : ℕ) (m : M) :
    encryptionRealStep scheme k (none, ((tK, 0), (tE, nE))) .enc m =
      ((some (realKey scheme tK), ((tK, 1), (tE, nE + 1))),
        entry (AE.Real.law2 scheme) tE nE (realKey scheme tK, m)) :=
  Program.combine_eq_of_invoke _ _ (n := 2) (by
    simp [Program.invoke, Encryption.Real.body, callProg, returnProg, parallelStep, sourceStep,
      entry, realKey, encryptionReal_law1, encryptionReal_law2])

theorem encryptionReal_combine_later {k : ℕ} (key : K) (tK : Fin k → K) (nK : ℕ)
    (tE : Fin k → (K × M → C)) (nE : ℕ) (m : M) :
    encryptionRealStep scheme k (some key, ((tK, nK), (tE, nE))) .enc m =
      ((some key, ((tK, nK), (tE, nE + 1))), entry (AE.Real.law2 scheme) tE nE (key, m)) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    simp [Program.invoke, Encryption.Real.body, callProg, returnProg, parallelStep, sourceStep,
      entry, encryptionReal_law2])

/-- **The real encryption system is an encryption oracle**: the `i`-th encryption reads entry `i`
of the encryption table under the key. -/
theorem encryptionReal_bisim {k : ℕ} :
    IsBisim (encryptionRealStep scheme k (M := M) (C := C))
      (encryptionStep (realEncrypt scheme))
      (fun a a' => a.2.1.1 = a'.1.1 ∧ a.2.2.1 = a'.1.2 ∧ a.2.2.2 = a'.2.length ∧
        (a.1 = none ∧ a.2.1.2 = 0 ∨ a.1 = some (realKey scheme a'.1.1) ∧ a.2.1.2 = 1)) := by
  rintro ⟨sR, ⟨tK, nK⟩, tE, nE⟩ ⟨⟨tK', tE'⟩, known⟩ (_ | _) x ⟨h₁, h₂, h₃, h₄⟩
  dsimp only at h₁ h₂ h₃ h₄
  subst h₁ h₂ h₃
  rcases h₄ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [encryptionReal_combine_first]
    simp [encryptionStep, realEncrypt]
  · rw [encryptionReal_combine_later]
    simp [encryptionStep, realEncrypt]

end Systems

/-- **Oracles that agree on the first `n` encryptions** have the same system on the histories of
at most `n` encryptions. -/
theorem oracle_system_congr {Ω' : Type} {encrypt : Ω → ℕ → M → C}
    {decrypt : Ω → List M → C → Option M} {encrypt' : Ω' → ℕ → M → C}
    {decrypt' : Ω' → List M → C → Option M} {ω : Ω} {ω' : Ω'} {n : ℕ}
    (henc : ∀ i < n, ∀ m, encrypt ω i m = encrypt' ω' i m)
    (hdec : ∀ known : List M, known.length ≤ n → ∀ c, decrypt ω known c = decrypt' ω' known c)
    (h : List (Σ p, AE.Input M C p)) (hn : (messages h).length ≤ n) :
    automatonSystem (oracleStep encrypt decrypt) (ω, []) h =
      automatonSystem (oracleStep encrypt' decrypt') (ω', []) h := by
  rcases List.eq_nil_or_concat h with rfl | ⟨h, ⟨p, x⟩, rfl⟩
  · rfl
  · rw [List.concat_eq_append] at hn ⊢
    rw [automatonSystem_snoc, automatonSystem_snoc, stateAfter_oracleStep, stateAfter_oracleStep]
    cases p with
    | enc =>
      simp only [messages_append, messages_enc, List.length_append, List.length_singleton] at hn
      simp [oracleStep, henc (messages h).length (by omega)]
    | dec =>
      simp only [messages_append, messages_dec, List.append_nil] at hn
      simp [oracleStep, hdec _ hn]

end AuthenticatedEncryption
