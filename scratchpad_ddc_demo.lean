/-
DDC ergonomics demonstration, end to end, against the real repo:

1. `ConverterImpl` / `ConverterImpl.engine` — the authoring combinator: a Mealy-style
   per-event program becomes an engine (a plain DDS on the sum alphabet),
   with dom/output receipts proven once.
2. `encImpl` — a genuinely stateful, adaptive TWO-call converter (the
   §3 example of the converter-theory doc): on message `m`, get the key,
   send `m ⊕ k`, deliver the ciphertext.  Four lines to author.
3. `encChan_eq` — attach it to a key/channel resource and prove the CLOSED
   FORM: the attached system IS `functionEvaluator (fun m => xor m k)`.
4. `notImpl` + the composite: attach a second (one-call) converter on top
   and prove the composed closed form — attachment composes by applying
   `connect` twice, no cascade object needed.
-/
import RandomSystems.Converter.ConverterImpl

namespace ScratchDemo

open RandomSystems System

noncomputable section

open Classical

/-! ## 1. The authoring combinator -/

/-! ## 2. The two-call encryptor -/

/-- `getKey` / `send c`: fixed-key resource with an echoing channel. -/
def keyChan (k : Bool) : DDS (Unit ⊕ Bool) Bool :=
  functionEvaluator (Sum.elim (fun _ => k) id)

@[simp] theorem mem_dom_keyChan (k : Bool) (l : List (Unit ⊕ Bool)) :
    l ∈ dom (keyChan k) ↔ l ≠ [] :=
  Iff.rfl

inductive EncSt | idle | wait1 (m : Bool) | wait2
open EncSt

/-- The encryptor: on message `m` — ask for the key, send `m ⊕ k`, deliver
the ciphertext.  Adaptive second call, state across events. -/
def encImpl : ConverterImpl EncSt Bool Bool Bool (Unit ⊕ Bool) where
  init := idle
  onQuery := fun _ m => Part.some (wait1 m, Sum.inr (Sum.inl ()))
  onReply := fun s y => Part.some (match s with
    | wait1 m => (wait2, Sum.inr (Sum.inr (xor m y)))
    | _ => (idle, Sum.inl y))

theorem htot_enc : ∀ s e, (encImpl.step s e).Dom := by
  intro s e
  cases e <;> trivial

/-- One round resolves in three interpreter steps, from any reachable
(idle) state, and returns to idle. -/
theorem serve_enc (k : Bool) (n : ℕ) (eh : List (Bool ⊕ Bool))
    (rh : List (Unit ⊕ Bool))
    (hst : encImpl.state eh = Part.some idle) (m : Bool) :
    Connect.serve encImpl.engine (keyChan k) (n + 3)
        (eh ++ [Sum.inl m], rh) =
      Part.some (xor m k,
        (eh ++ [Sum.inl m, Sum.inr k, Sum.inr (xor m k)],
          rh ++ [Sum.inl (), Sum.inr (xor m k)])) := by
  have hok : eh = [] ∨ eh ∈ dom encImpl.engine := by
    rcases List.eq_nil_or_concat eh with rfl | ⟨_, _, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (ConverterImpl.mem_dom_engine_of_total _ htot_enc
        (by simp))
  rw [ConverterImpl.serve_engine _ _ _ _ _ _ hok, hst]
  simp [encImpl, keyChan]

/-- The round state-invariant: the encryptor returns to idle. -/
theorem state_enc_round (eh : List (Bool ⊕ Bool)) (m k c : Bool)
    (hst : encImpl.state eh = Part.some idle) :
    encImpl.state (eh ++ [Sum.inl m, Sum.inr k, Sum.inr c]) =
      Part.some idle := by
  rw [show eh ++ [Sum.inl m, Sum.inr k, Sum.inr c] =
      ((eh ++ [Sum.inl m]) ++ [Sum.inr k]) ++ [Sum.inr c] by simp,
    ConverterImpl.state_append, ConverterImpl.state_append,
    ConverterImpl.state_append, hst]
  simp [encImpl, ConverterImpl.step]

/-- Whole histories resolve at fuel 3, answering `m ⊕ k` to the last
message. -/
theorem runAux_enc (k : Bool) :
    ∀ (us : List Bool) (h : us ≠ []) (eh : List (Bool ⊕ Bool))
      (rh : List (Unit ⊕ Bool)),
      encImpl.state eh = Part.some idle →
      ∃ eh' rh', Connect.runAux encImpl.engine (keyChan k) 3 us (eh, rh) =
          Part.some (xor (us.getLast h) k, (eh', rh')) ∧
        encImpl.state eh' = Part.some idle := by
  intro us
  induction us with
  | nil => exact fun h => absurd rfl h
  | cons u t ih =>
      intro h eh rh hst
      cases t with
      | nil =>
          refine ⟨eh ++ [Sum.inl u, Sum.inr k, Sum.inr (xor u k)],
            rh ++ [Sum.inl (), Sum.inr (xor u k)], ?_,
            state_enc_round eh u k (xor u k) hst⟩
          rw [Connect.runAux_singleton, serve_enc k 0 eh rh hst u]
          rfl
      | cons u' t' =>
          obtain ⟨eh', rh', heq, hst'⟩ := ih (by simp)
            (eh ++ [Sum.inl u, Sum.inr k, Sum.inr (xor u k)])
            (rh ++ [Sum.inl (), Sum.inr (xor u k)])
            (state_enc_round eh u k (xor u k) hst)
          refine ⟨eh', rh', ?_, hst'⟩
          rw [Connect.runAux_cons_cons, serve_enc k 0 eh rh hst u,
            Part.bind_some, heq]
          rfl

/-- **The closed form**: the attached system IS the xor evaluator — a
DDS-level equality, kernel-checked. -/
theorem encChan_eq (k : Bool) :
    connect encImpl.engine (keyChan k) =
      functionEvaluator (fun m => xor m k) := by
  apply Subtype.ext
  funext us
  refine Part.ext' ?_ ?_
  · constructor
    · rintro ⟨n, hn⟩
      show us ≠ []
      rintro rfl
      exact hn.elim
    · intro h
      obtain ⟨eh', rh', heq, -⟩ := runAux_enc k us h [] [] rfl
      exact ⟨3, by rw [heq]; trivial⟩
  · intro h₁ h₂
    have hne : us ≠ [] := h₂
    obtain ⟨eh', rh', heq, -⟩ := runAux_enc k us hne [] [] rfl
    have h3 : (Connect.runAux encImpl.engine (keyChan k) 3 us
        ([], [])).Dom := by rw [heq]; trivial
    have hmax : Connect.runAux encImpl.engine (keyChan k) (Nat.find h₁) us
        ([], []) = Connect.runAux encImpl.engine (keyChan k) 3 us
        ([], []) := by
      rw [← Connect.runAux_mono (le_max_left (Nat.find h₁) 3)
        (Nat.find_spec h₁),
        Connect.runAux_mono (le_max_right (Nat.find h₁) 3) h3]
    show ((Connect.runAux encImpl.engine (keyChan k) (Nat.find h₁) us
      ([], [])).get (Nat.find_spec h₁)).1 = _
    rw [Part.get_eq_of_mem (by rw [hmax, heq]; exact Part.mem_some _)
      (Nat.find_spec h₁)]
    rfl

/-! ## 3. Composition: a second converter on top -/

/-- The one-call pre-processor: negate the message, relay the answer. -/
def notImpl : ConverterImpl Unit Bool Bool Bool Bool where
  init := ()
  onQuery := fun _ m => Part.some ((), Sum.inr (!m))
  onReply := fun _ c => Part.some ((), Sum.inl c)

theorem htot_not : ∀ s e, (notImpl.step s e).Dom := by
  intro s e
  cases e <;> trivial

theorem serve_not (g : Bool → Bool) (n : ℕ) (eh : List (Bool ⊕ Bool))
    (rh : List Bool) (m : Bool) :
    Connect.serve notImpl.engine (functionEvaluator g) (n + 2)
        (eh ++ [Sum.inl m], rh) =
      Part.some (g (!m),
        (eh ++ [Sum.inl m, Sum.inr (g (!m))], rh ++ [!m])) := by
  have hok : eh = [] ∨ eh ∈ dom notImpl.engine := by
    rcases List.eq_nil_or_concat eh with rfl | ⟨_, _, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (ConverterImpl.mem_dom_engine_of_total _ htot_not
        (by simp))
  have hst : notImpl.state eh = Part.some () :=
    Part.eq_some_iff.mpr
      ⟨ConverterImpl.state_dom_of_total _ htot_not eh, rfl⟩
  rw [ConverterImpl.serve_engine _ _ _ _ _ _ hok, hst]
  simp [notImpl]

theorem runAux_not (g : Bool → Bool) :
    ∀ (us : List Bool) (h : us ≠ []) (eh : List (Bool ⊕ Bool))
      (rh : List Bool),
      ∃ eh' rh', Connect.runAux notImpl.engine (functionEvaluator g) 2 us
        (eh, rh) = Part.some (g (!(us.getLast h)), (eh', rh')) := by
  intro us
  induction us with
  | nil => exact fun h => absurd rfl h
  | cons u t ih =>
      intro h eh rh
      cases t with
      | nil =>
          refine ⟨eh ++ [Sum.inl u, Sum.inr (g (!u))], rh ++ [!u], ?_⟩
          rw [Connect.runAux_singleton, serve_not g 0 eh rh u]
          rfl
      | cons u' t' =>
          obtain ⟨eh', rh', heq⟩ := ih (by simp)
            (eh ++ [Sum.inl u, Sum.inr (g (!u))]) (rh ++ [!u])
          refine ⟨eh', rh', ?_⟩
          rw [Connect.runAux_cons_cons, serve_not g 0 eh rh u,
            Part.bind_some, heq]
          rfl

theorem connect_not (g : Bool → Bool) :
    connect notImpl.engine (functionEvaluator g) =
      functionEvaluator (fun m => g (!m)) := by
  apply Subtype.ext
  funext us
  refine Part.ext' ?_ ?_
  · constructor
    · rintro ⟨n, hn⟩
      show us ≠ []
      rintro rfl
      exact hn.elim
    · intro h
      obtain ⟨eh', rh', heq⟩ := runAux_not g us h [] []
      exact ⟨2, by rw [heq]; trivial⟩
  · intro h₁ h₂
    have hne : us ≠ [] := h₂
    obtain ⟨eh', rh', heq⟩ := runAux_not g us hne [] []
    have h2 : (Connect.runAux notImpl.engine (functionEvaluator g) 2 us
        ([], [])).Dom := by rw [heq]; trivial
    have hmax : Connect.runAux notImpl.engine (functionEvaluator g)
        (Nat.find h₁) us ([], []) =
        Connect.runAux notImpl.engine (functionEvaluator g) 2 us
        ([], []) := by
      rw [← Connect.runAux_mono (le_max_left (Nat.find h₁) 2)
        (Nat.find_spec h₁),
        Connect.runAux_mono (le_max_right (Nat.find h₁) 2) h2]
    show ((Connect.runAux notImpl.engine (functionEvaluator g)
      (Nat.find h₁) us ([], [])).get (Nat.find_spec h₁)).1 = _
    rw [Part.get_eq_of_mem (by rw [hmax, heq]; exact Part.mem_some _)
      (Nat.find_spec h₁)]
    rfl

/-- **Attachment composes by attaching twice** — no cascade object, no
new machinery: the composed closed form, kernel-checked. -/
theorem composed (k : Bool) :
    connect notImpl.engine (connect encImpl.engine (keyChan k)) =
      functionEvaluator (fun m => xor (!m) k) := by
  rw [encChan_eq, connect_not]

end

end ScratchDemo
