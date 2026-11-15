module

public import RandomSystems.Typed.QueryRouting

/-!
# Input-dependent routing regression

Routing on one outside port `⋆` with queries `(b,x) ∈ Bool²` to two inside ports `j ∈ Bool`.
The value `b` selects the inside port and `x` becomes the inside query, a value-dependent choice
that no renaming of labels expresses.

```text
                ┌──────────────────────┐
  ⋆((b,x))  ──► │ (j,x) = (b,x)        │ ──► b(x)
  ⋆ ⇒ y'    ◄── │ y' = answer u (b,y)  │ ◄── b ⇒ y
                └──────────────────────┘
```

* A writer and a reader share a single Boolean register. A router complements the writer's
  acknowledgement, and the reader observes exactly the written bit.
* The identity oracle `f_j(x) = x` checks that the payload `x` is forwarded.
* The port-returning oracle `f_j(x) = j` checks that the selected label is `b`.
* Reply alphabets `Y_false = Unit`, `Y_true = Bool` check heterogeneous replies, with an answer
  map that uses the retained outside input on the `Unit` port.
* The unrestricted domains `F = E = True`, which contain `[]`, check the domain theorem under
  nonempty-prefix closure alone.
* Encoding `x` as `(true,x)` meets a restricted inside domain; projecting a pair reply to its
  second coordinate gives the functional and memoryless contracts directly.
-/

@[expose] public section

namespace SystemAlgebra.Tests.QueryRouting

/-- Outside interface: one port `⋆`, queries `(b,x) ∈ Bool²`, and Boolean replies.
Its domain is `F = {[(⋆,(b,x))] | b,x ∈ Bool}`: one query. -/
def outside : Interface := Interface.queryBudget Unit (fun _ => Bool × Bool) (fun _ => Bool) 1

/-- Inside interface: ports `j ∈ Bool` with Boolean queries and replies.
Its domain is `E = {[(j,x)] | j,x ∈ Bool}`: one query at either port. -/
def inside : Interface := Interface.queryBudget Bool (fun _ => Bool) (fun _ => Bool) 1

/-- `request(⋆,(b,x)) = (b,x)`: the selector `b` becomes the inside port label. -/
def request (u : Σ o, outside.X o) : Σ j, inside.X j := ⟨u.2.1, u.2.2⟩

/-- `answer(u,(j,y)) = y`: forward the inside Boolean to the original outside port. -/
def answer (u : Σ o, outside.X o) (r : Σ j, inside.Y j) : outside.Y u.1 := r.2

/-- The map-domain condition `F us → E (us.map request)`: the value-dependent request sends the
one-query outside domain into the one-query inside domain. -/
lemma request_domain (us : List (Σ o, outside.X o)) (hu : outside.domain us) :
    inside.domain (us.map request) := by
  -- Mapping preserves both nonemptiness and the one-query bound.
  exact ⟨fun he => hu.1 (List.map_eq_nil_iff.mp he),
    (List.length_map request).trans_le hu.2⟩

/-- The router is a DDC from `E` to `F` with one inside query per invocation. -/
lemma certified : IsDDCFrom inside.domain outside.domain 1
    (routingConverter request answer outside.domain) :=
  routingConverter_isDDCFrom request answer outside.nonempty_prefix.2 request_domain

/-- With `f_j(x) = x`, routing returns `g(b,x) = x` at the outside port `⋆`. -/
example : TypedConverter.ofDDC (routingConverter request answer outside.domain) certified •
    TypedSystem.ofFunction (A := inside) (fun (_ : Bool) (x : Bool) => x) =
    TypedSystem.ofFunction (A := outside) (fun (_ : Unit) (u : Bool × Bool) => u.2) := by
  -- Substituting f_j(x) = x in the routing equation gives g(b,x) = x.
  exact TypedConverter.ofDDC_routingConverter_smul_ofFunction request answer certified
    (fun (_ : Bool) (x : Bool) => x)

/-- With `f_j(x) = j`, routing returns `g(b,x) = b`. A router querying a constant port `j₀`
would return `j₀` and fail this law. -/
example : TypedConverter.ofDDC (routingConverter request answer outside.domain) certified •
    TypedSystem.ofFunction (A := inside) (fun (j : Bool) (_ : Bool) => j) =
    TypedSystem.ofFunction (A := outside) (fun (_ : Unit) (u : Bool × Bool) => u.1) := by
  -- The returned inside label exposes the selector used by request.
  exact TypedConverter.ofDDC_routingConverter_smul_ofFunction request answer certified
    (fun (j : Bool) (_ : Bool) => j)

/-- Inside ports and queries are Boolean, with `Y_false = Unit` and `Y_true = Bool`.
The domain remains `E = {[(j,x)] | j,x ∈ Bool}`, so the same request map is admissible. -/
def heterogeneousInside : Interface :=
  -- Each port uses the usual finite enumeration of its reply alphabet.
  letI (j : Bool) : Fintype (if j then Bool else Unit) := by
    cases j
    · exact inferInstanceAs (Fintype Unit)
    · exact inferInstanceAs (Fintype Bool)
  Interface.queryBudget Bool (fun _ => Bool) (fun j => if j then Bool else Unit) 1

/-- `f_false(x) = ()` and `f_true(x) = x`: only port `true` returns a Boolean. -/
def heterogeneousOracle : ∀ j, heterogeneousInside.X j → heterogeneousInside.Y j
  | false, _ => ()
  | true, x => x

/-- `answer((⋆,(b,x)),(false,())) = x` and `answer((⋆,(b,x)),(true,y)) = !y`.
The `Unit` reply carries no data, so on port `false` the answer reads the retained input. -/
def heterogeneousAnswer (u : Σ o, outside.X o)
    (r : Σ j, heterogeneousInside.Y j) : outside.Y u.1 :=
  match r with
  | ⟨false, _⟩ => u.2.2
  | ⟨true, y⟩ => !y

/-- The domains do not involve reply alphabets, so `request_domain` certifies this router too. -/
lemma heterogeneous_certified : IsDDCFrom heterogeneousInside.domain outside.domain 1
    (routingConverter request heterogeneousAnswer outside.domain) :=
  routingConverter_isDDCFrom request heterogeneousAnswer outside.nonempty_prefix.2 request_domain

/-- The outside function is `g(false,x) = x` and `g(true,x) = !x`. It depends on the selected
port, on the reply of its alphabet, and on the retained input. -/
example : TypedConverter.ofDDC (A := outside) (B := heterogeneousInside)
    (routingConverter request heterogeneousAnswer outside.domain) heterogeneous_certified •
    TypedSystem.ofFunction (A := heterogeneousInside) heterogeneousOracle =
    TypedSystem.ofFunction (A := outside)
      (fun (_ : Unit) (u : Bool × Bool) => if u.1 then !u.2 else u.2) := by
  -- The routing law gives `g(b,x) = heterogeneousAnswer (⋆,(b,x)) (b, f_b(x))`.
  refine (TypedConverter.ofDDC_routingConverter_smul_ofFunction
    (A := outside) (B := heterogeneousInside)
    request heterogeneousAnswer heterogeneous_certified heterogeneousOracle).trans ?_
  congr 1
  funext o u
  -- Case on the selected port `b`; each case is the corresponding equation.
  obtain ⟨b, x⟩ := u
  cases b <;> rfl

/-- With `F = E = True`, which contains `[]`, the router is a DDC from `E` to `F`: the domain
theorem needs only closure of `F` under nonempty prefixes. -/
example : IsDDCFrom (fun _ => True) (fun _ => True) 1
    (routingConverter request answer (fun _ => True)) := by
  apply routingConverter_isDDCFrom request answer
  -- `F = True` is closed under nonempty prefixes.
  · intro p h _ _ _
    trivial
  -- `E = True` holds at every request image `us.map request`.
  · intro us _
    trivial

open Probability.Distribution

/-- One Boolean query and reply port, usable at most `q` times. -/
abbrev bits (q : ℕ) : Interface :=
  Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) q

/-- Pair-valued queries and replies on nonempty histories of at most `q` queries, all tagged
`true` in the first coordinate. The reply's second coordinate is the payload. -/
abbrev encodedPairs (q : ℕ) : Interface :=
  (Interface.queryBudget Unit (fun _ => Bool × Bool) (fun _ => Bool × Bool) q).restrict
    (fun xs => ∀ x ∈ xs, x.2.1 = true)
    (fun _ _ hp hd x hx => hd x (hp.subset hx))

/-- `x ↦ (true,x)` sends the outside query to the encoded inside domain. -/
def encode (x : Σ _ : Unit, Bool) : Σ _ : Unit, Bool × Bool := ⟨(), (true, x.2)⟩

/-- The encoding preserves nonemptiness and length, and sets every domain tag to `true`. -/
lemma encode_domain (q : ℕ) (xs : List (Σ _ : Unit, Bool)) (hx : (bits q).domain xs) :
    (encodedPairs q).domain (xs.map encode) := by
  refine ⟨⟨fun he => hx.1 (List.map_eq_nil_iff.mp he),
    (List.length_map encode).trans_le hx.2⟩, ?_⟩
  intro y hy
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
  rfl

/-- The inside domain rejects a false tag even though the query has the right type. -/
example (q : ℕ) : ¬ (encodedPairs q).domain [⟨(), (false, false)⟩] := by
  intro hd
  have hf := hd.2 ⟨(), (false, false)⟩ (List.mem_singleton_self _)
  cases hf

/-- Input encoding followed by reply projection needs only its history-domain certificate. -/
example (q : ℕ) (f : Bool × Bool → Bool × Bool) :
    TypedConverter.routing (A := bits q) (B := encodedPairs q)
        encode (fun _ r => r.2.2) (encode_domain q) •
      TypedSystem.ofFunction (A := encodedPairs q) (fun _ => f) =
        TypedSystem.ofFunction (A := bits q) (fun _ x => (f (true, x)).2) :=
  TypedConverter.routing_smul_ofFunction (A := bits q) (B := encodedPairs q)
    encode (fun _ r => r.2.2) (encode_domain q) (fun _ => f)

/-- Fresh pair replies remain fresh after projecting the payload; no table is retained. -/
example (q : ℕ) (ν : Bool × Bool → ProbDist (Bool × Bool)) :
    TypedConverter.routing (A := bits q) (B := encodedPairs q)
        encode (fun _ r => r.2.2) (encode_domain q) •
      TypedSystem.ofMemoryless (encodedPairs q) (fun _ => ν) =
        TypedSystem.ofMemoryless (bits q) (fun _ x => ProbDist.map Prod.snd (ν (true, x))) :=
  TypedConverter.routing_smul_ofMemoryless (A := bits q) (B := encodedPairs q)
    encode (fun _ r => r.2.2)
    (encode_domain q) (fun _ => ν)

/-- At the false port the reply is unit; at the true port negate the Boolean reply. -/
def answerAt : (u : Σ o, outside.X o) → heterogeneousInside.Y (request u).1 → outside.Y u.1
  | ⟨_, false, x⟩, _ => x
  | ⟨_, true, _⟩, y => !y

example : TypedConverter.routingAt (A := outside) (B := heterogeneousInside)
    request answerAt request_domain • TypedSystem.ofFunction heterogeneousOracle =
      TypedSystem.ofFunction (fun o x => answerAt ⟨o, x⟩ (heterogeneousOracle x.1 x.2)) :=
  TypedConverter.routingAt_smul_ofFunction _ _ _ _

-- Routing to the restricted oracle still requires the tag certificate.
example (q : ℕ) (f : Bool × Bool → Bool × Bool) :
    TypedConverter.routingAt (A := bits q) (B := encodedPairs q)
      encode (fun _ y => y.2) (encode_domain q) •
      TypedSystem.ofFunction (A := encodedPairs q) (fun _ => f) =
    TypedSystem.ofFunction (A := bits q) (fun _ x => (f (true, x)).2) :=
  TypedConverter.routingAt_smul_ofFunction _ _ _ _

/-- Each selected port draws from its own reply alphabet before the outside translation. -/
example (ν : ∀ j, heterogeneousInside.X j → ProbDist (heterogeneousInside.Y j)) :
    TypedConverter.routingAt (A := outside) (B := heterogeneousInside)
        request answerAt request_domain • TypedSystem.ofMemoryless heterogeneousInside ν =
      TypedSystem.ofMemoryless outside (fun o x => (ν x.1 x.2).map (answerAt ⟨o, x⟩)) :=
  TypedConverter.routingAt_smul_ofMemoryless _ _ _ _

/-! ## A writer and a reader sharing one register -/

/-- Two ports, each admitting one Boolean query. -/
abbrev registerPorts := (bits 1).tensor (bits 1)

/-- The writer stores and acknowledges `b`; the reader returns the current register. -/
def registerStep : Bool → (i : registerPorts.I) → registerPorts.X i → Bool × registerPorts.Y i
  | _, .inl _, b => (b, b)
  | r, .inr _, _ => (r, r)

/-- Complement the writer's acknowledgement and pass the reader's reply through. -/
def registerAnswer : (u : Σ i, registerPorts.X i) → registerPorts.Y u.1 → registerPorts.Y u.1
  | ⟨.inl _, _⟩, y => !y
  | ⟨.inr _, _⟩, y => y

/-- Both ports forward their input unchanged, so the one-query-per-port domain is preserved. -/
noncomputable def registerRouter : TypedConverter registerPorts registerPorts :=
  TypedConverter.routingAt id registerAnswer (fun xs hx => by simpa only [List.map_id] using hx)

/-- Writing `b` returns `!b`. The other caller then reads `b`, even if the initial bit differs.
The probability includes both exchanges on the router's declared domain. -/
lemma register_write_read_mass (initial b read : Bool) :
    (registerRouter • TypedSystem.ofProbAutomaton registerPorts
      (ProbStep.ofDeterministic registerStep) (ProbDist.single initial)).1
        [(⟨.inl (), b⟩, ⟨.inl (), !b⟩), (⟨.inr (), false⟩, ⟨.inr (), read⟩)] =
      if read = b then 1 else 0 := by
  -- The stateful attachment law translates the reply while retaining the register update.
  rw [registerRouter, TypedConverter.routingAt_smul_ofProbAutomaton]
  simp only [id_eq]
  let δ (r : Bool) (i : registerPorts.I) (x : registerPorts.X i) :=
    ((registerStep r i x).1, registerAnswer ⟨i, x⟩ (registerStep r i x).2)
  have hstep : ∀ r i x, ((ProbStep.ofDeterministic registerStep) r i x).map
      (fun p => (p.1, registerAnswer ⟨i, x⟩ p.2)) = ProbStep.ofDeterministic δ r i x :=
    fun _ _ _ => Subtype.ext (fTransform_single _ _ _)
  rw [show (fun r i x => _) = ProbStep.ofDeterministic δ from funext₃ hstep,
    TypedSystem.ofProbAutomaton_ofDeterministic, TypedSystem.ofAutomaton_mass]
  -- The point initial law gives mass one exactly when both prescribed replies occur.
  rw [ProbDist.single, mass_single]
  congr 1
  apply propext
  let w : Σ i, registerPorts.X i := ⟨.inl (), b⟩
  let q : Σ i, registerPorts.X i := ⟨.inr (), false⟩
  change Replies (filterDom _ (automatonSystem δ initial)) [w, q] _ ↔ read = b
  have legal : registerPorts.domain [w, q] := by
    -- Each port receives exactly one call.
    simp [registerPorts, Interface.tensor, Interface.parallelDomain, parallelInputs, w, q,
      bits, Interface.queryBudget, sumAlphabet, restrict_cons_self, restrict_cons_ne]
  rw [replies_filterDom_iff registerPorts.nonempty_prefix.2 _ (fun _ => legal)]
  -- The write reaches state b, so the read reply is precisely b.
  change Replies (automatonSystem δ initial) ([w] ++ [q]) ([⟨.inl (), !b⟩] ++ [⟨.inr (), read⟩]) ↔ _
  rw [replies_snoc, automatonSystem_snoc]
  have hw : Replies (automatonSystem δ initial) [w] [⟨.inl (), !b⟩] :=
    (replies_snoc (xs := []) (ys := [])).mpr ⟨replies_nil _, rfl⟩
  simp only [hw, true_and, Part.some_inj]
  exact ⟨fun h => (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm, fun h => h ▸ rfl⟩

#print axioms register_write_read_mass
#print axioms TypedConverter.routingAt_smul_ofProbAutomaton

#print axioms TypedConverter.routingAt_smul_ofMemoryless
#print axioms TypedConverter.routingAt_smul_ofFunction
#print axioms routingConverter_query_count
#print axioms routingConverter_eq_ofProgramOn
#print axioms TypedConverter.routing_smul_ofFunction
#print axioms TypedConverter.routing_smul_ofMemoryless

end SystemAlgebra.Tests.QueryRouting
