module

public import RandomSystems.Converter.ConverterAttachment

/-!
# Interfaces, typed systems and typed converters

`Interface` packages ports `I`, query/reply alphabets `X i`, `Y i`, and a bounded input-history
domain `D = domain`. A `TypedSystem A` is a cumulative behavior on that domain, replying at
the queried port. `TypedConverter A B` carries a PDC behavior from inside domain `B` to outside
domain `A`; `α • R` (`TypedConverter.attach`) sends `R : TypedSystem B` to `TypedSystem A`.
The carriers are indexed by finite interfaces, using the systems and converters of
[2, Definitions 2.2.1–2.2.2, pp. 16–18] and [3, Definitions 3.8–3.9, p. 62; Definition 3.17, p. 64].

`Interface.queryBudget` and `Interface.portBudget` admit total and per-port query bounds.
`Interface.queryBudget_domain_map` transfers one-query maps when `A.bound ≤ q`;
`Interface.queryBudget_inputDomain_iff` reduces next-query admission to a length inequality.
`TypedSystem.ofPDS` presents a sampled deterministic system; `TypedSystem.exists_ofPDS` gives
such a presentation for every typed behavior.

`TypedConverter.ofDDC_eq_comp` turns raw equality with a trimmed serial DDC into equality of
typed converters, independently of their certified bounds. `TypedConverter.identity_attach`
and `TypedConverter.comp_smul` lift the PDC attachment laws; the latter is the serial law of
[1, §3.3, p. 7].

## References

1. U. Maurer and R. Renner. *From Indifferentiability to Constructive Cryptography (and Back)*.
   TCC 2016-B. Cryptology ePrint Archive, Paper 2016/903, 2016.
2. D. Jost. *On Generalizations of Composable Security*. Doctoral thesis,
   Diss. ETH No. 26723, ETH Zurich, 2020.
3. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

@[expose] public section

namespace SystemAlgebra

/-- `A = (I, X, Y, D)` indexes systems on finite ports and alphabets with bounded domain `D`. -/
structure Interface where
  /-- `I` indexes the ports exposed to the caller. -/
  I : Type
  /-- `X i` is the query type at port `i : I`. -/
  X : I → Type
  /-- `Y i` is the reply type at port `i : I`. -/
  Y : I → Type
  [instFintypeI : Fintype I]
  [instFintypeX : ∀ i, Fintype (X i)]
  [instFintypeY : ∀ i, Fintype (Y i)]
  /-- `domain xs` admits the complete list `xs` of port-tagged inputs. -/
  domain : List (Σ i, X i) → Prop
  /-- `domain` excludes `[]` and admits each nonempty prefix of an admitted history. -/
  nonempty_prefix : ¬ domain [] ∧ ∀ {p h}, p <+: h → p ≠ [] → domain h → domain p
  /-- `bound` is a uniform upper bound on the number of admitted queries. -/
  bound : ℕ
  /-- `length_le` states `h.length ≤ bound` whenever `domain h`. -/
  length_le : ∀ h, domain h → h.length ≤ bound

attribute [instance] Interface.instFintypeI Interface.instFintypeX Interface.instFintypeY

namespace Interface

/-- `D = {h | h ≠ [] ∧ h.length ≤ q}` admits at most `q` queries in total. -/
abbrev queryBudget
    -- `I` indexes finite ports; `X i`, `Y i` carry their finite query and reply alphabets.
    (I : Type) [Fintype I] (X Y : I → Type) [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    -- `q` bounds the total length of an admitted input history.
    (q : ℕ) : Interface where
  I := I
  X := X
  Y := Y
  domain h := h ≠ [] ∧ h.length ≤ q
  nonempty_prefix := ⟨fun h => h.1 rfl, fun hp hne hd => ⟨hne, hp.length_le.trans hd.2⟩⟩
  bound := q
  length_le _ hd := hd.2

/-- A one-query map sends each history of `A` into a query-budget interface when its whole
history bound fits inside `q`. For a tagged caller family, this checks the sum of caller bounds. -/
lemma queryBudget_domain_map
    -- `A` is the outside interface, including its complete history bound `A.bound`.
    {A : Interface}
    -- `I`, `X`, `Y` give the inside ports, queries, and replies.
    {I : Type} [Fintype I] {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    -- `request` makes one inside query for each outside input; `q` bounds their combined count.
    (request : (Σ o, A.X o) → Σ i, X i) {q : ℕ} (hq : A.bound ≤ q)
    -- `hx` admits the complete outside history `xs`, including all callers.
    {xs : List (Σ o, A.X o)} (hx : A.domain xs) :
    (queryBudget I X Y q).domain (xs.map request) := by
  refine ⟨fun he => A.nonempty_prefix.1 (List.map_eq_nil_iff.mp he ▸ hx), ?_⟩
  -- Each outside input contributes one query, so mapping preserves the aggregate length.
  exact (List.length_map request).trans_le ((A.length_le xs hx).trans hq)

/-- `D = {h | h ≠ [] ∧ ∀ i, (restrict i h).length ≤ q i}` bounds each port separately. -/
abbrev portBudget
    -- `I` indexes finite ports; `X i`, `Y i` carry their finite query and reply alphabets.
    (I : Type) [Fintype I] (X Y : I → Type) [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    -- `q i` bounds the number of inputs sent to port `i`.
    (q : I → ℕ) : Interface where
  I := I
  X := X
  Y := Y
  domain h := h ≠ [] ∧ ∀ i, (restrict i h).length ≤ q i
  nonempty_prefix := ⟨fun h => h.1 rfl, fun hp hne hd =>
    ⟨hne, fun i => (restrict_prefix i hp).length_le.trans (hd.2 i)⟩⟩
  bound := ∑ i, q i
  length_le h hd := (length_eq_sum_restrict h).trans_le (Finset.sum_le_sum fun i _ => hd.2 i)

/-- `A.inputDomain h x = A.domain (h.map Prod.fst ++ [x])`: admit input `x` after transcript `h`. -/
abbrev inputDomain (A : Interface) : Domain (Σ i, A.X i) (Σ i, A.Y i) :=
  Domain.ofInputs A.domain A.bound A.length_le

/-- For `queryBudget I X Y q`, `inputDomain h x ↔ h.length < q`. -/
lemma queryBudget_inputDomain_iff
    -- `I`, `X`, `Y` give the ports, queries and replies; `q` bounds the complete input history.
    {I : Type} [Fintype I] {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    {q : ℕ}
    -- `h` is the past transcript; `x` is the next port-tagged input.
    {h : List ((Σ i, X i) × (Σ i, Y i))} {x : Σ i, X i} :
    (queryBudget I X Y q).inputDomain h x ↔ h.length < q := by
  -- The new input makes the history nonempty and increases its length by one.
  change (h.map Prod.fst ++ [x] ≠ [] ∧ (h.map Prod.fst ++ [x]).length ≤ q) ↔ _
  have hne : h.map Prod.fst ++ [x] ≠ [] :=
    List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
  constructor
  · intro hd
    simpa only [List.length_append, List.length_map, List.length_singleton,
      Nat.add_one_le_iff] using hd.2
  · intro hl
    refine ⟨hne, ?_⟩
    simpa only [List.length_append, List.length_map, List.length_singleton,
      Nat.add_one_le_iff] using hl

end Interface

/-- Typed systems on `A`: random systems over its domain replying at the queried interface. -/
def TypedSystem (A : Interface) :=
  {R : RandomSystem (Σ i, A.X i) (Σ i, A.Y i) A.inputDomain // R.RepliesAtQueriedInterface}

/-- The behavior of a PDS of deterministic systems with domain `A.domain`. -/
noncomputable def TypedSystem.ofPDS {A : Interface}
    (P : Probability.Distribution.ProbDist {s : InterfaceSystem A.I A.X A.Y //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ A.domain h}) : TypedSystem A :=
  ⟨RandomSystem.ofPDS P.1 P.2 (fun s _ _ _ _ => s.2.2.2 _),
    RandomSystem.ofPDS_repliesAtQueriedInterface P⟩

/-- Every typed system is the behavior of a PDS of deterministic systems. -/
lemma TypedSystem.exists_ofPDS {A : Interface} (R : TypedSystem A) :
    ∃ Q : Probability.Distribution.ProbDist {s : InterfaceSystem A.I A.X A.Y //
      IsDDS s ∧ SystemAlgebra.RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ A.domain h},
      TypedSystem.ofPDS Q = R := by
  obtain ⟨Q, hQ⟩ := RandomSystem.exists_resource_presentation A.nonempty_prefix R.1 R.2
  exact ⟨Q, Subtype.ext (RandomSystem.ext hQ)⟩

/-- A deterministic system, as its point distribution. -/
noncomputable def TypedSystem.ofDeterministic {A : Interface} (s : InterfaceSystem A.I A.X A.Y)
    (hs : IsDDS s ∧ SystemAlgebra.RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ A.domain h) :
    TypedSystem A :=
  TypedSystem.ofPDS ⟨Finsupp.single ⟨s, hs⟩ 1, Probability.Distribution.isProbDist_single _⟩

open Classical in
/-- A deterministic presentation gives mass one to its reply transcripts and zero elsewhere. -/
lemma TypedSystem.ofDeterministic_mass
    -- `s` is the deterministic system on interface `A`, certified by `hs` on exactly its domain.
    {A : Interface} (s : InterfaceSystem A.I A.X A.Y)
    (hs : IsDDS s ∧ SystemAlgebra.RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ A.domain h)
    -- `h` is the query/reply transcript whose cumulative probability is tested.
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i))) :
    (TypedSystem.ofDeterministic s hs).1 h =
      if Replies s (h.map Prod.fst) (h.map Prod.snd) then 1 else 0 := by
  simp [TypedSystem.ofDeterministic, TypedSystem.ofPDS, RandomSystem.ofPDS, behaviorMass,
    Probability.Distribution.mass, Finsupp.sum]

/-- Typed converters from `A` to `B`: behaviors of PDCs from `B`'s domain (inside) to `A`'s
domain (outside). -/
@[instance_reducible] def TypedConverter (A B : Interface) :=
  PDCBehavior A.I B.I A.X A.Y B.X B.Y B.domain B.bound B.length_le A.domain A.bound A.length_le

namespace TypedConverter

/-- Serial composition of typed converters: the composition of their PDC behaviors, `α` outside
and `β` inside. -/
noncomputable def comp {A B C : Interface} (α : TypedConverter A B) (β : TypedConverter B C) :
    TypedConverter A C :=
  PDCBehavior.comp α β

/-- The identity typed converter: the identity PDC behavior on `A`'s domain. -/
protected noncomputable def id (A : Interface) : TypedConverter A A :=
  PDCBehavior.id A.nonempty_prefix

/-- The typed converter of a DDC from `B`'s domain to `A`'s domain. -/
noncomputable def ofDDC {A B : Interface} (α : InsideOutsideSystem A.I B.I A.X A.Y B.X B.Y)
    {b : ℕ} (hα : IsDDCFrom B.domain A.domain b α) : TypedConverter A B :=
  PDCBehavior.ofDDC α hα

/-- The typed converter of a DDC gives probability one to its transcripts and zero to all
others. -/
lemma ofDDC_apply {A B : Interface} (α : InsideOutsideSystem A.I B.I A.X A.Y B.X B.Y)
    {b : ℕ} (hα : IsDDCFrom B.domain A.domain b α)
    (t : List ((Σ l, twoFam A.X B.Y l) × (Σ l, twoFam A.Y B.X l))) :
    (ofDDC α hα).1 t = open Classical in
      if Replies α (t.map Prod.fst) (t.map Prod.snd) then 1 else 0 :=
  PDCBehavior.ofDDC_apply α hα t

/-- If `γ = trim (serialM α β)`, its typed behavior is `comp (ofDDC α hα) (ofDDC β hβ)`.
The certified bound `c` may differ from the product bound `b * a` of `IsDDCFrom.comp`.
Each bound limits consecutive inside outputs [2, Definition 2.2.2, pp. 17–18].

```text
    A ┌───┐ B ┌───┐ C             A ┌────────────────────────┐ C
  ────┤ α ├───┤ β ├────    =    ────┤ γ = trim (serialM α β) ├────
      └───┘   └───┘                 └────────────────────────┘
```
-/
lemma ofDDC_eq_comp
    -- `A`, `B`, `C` are the outside, intermediate and inside interfaces.
    {A B C : Interface}
    -- `α` is outside, `β` inside, and `γ` their complete direct DDC presentation.
    {α : InsideOutsideSystem A.I B.I A.X A.Y B.X B.Y}
    {β : InsideOutsideSystem B.I C.I B.X B.Y C.X C.Y}
    {γ : InsideOutsideSystem A.I C.I A.X A.Y C.X C.Y}
    -- `a`, `b`, `c` bound consecutive inside calls in `α`, `β`, `γ`, respectively.
    {a b c : Nat}
    -- `hα`, `hβ`, `hγ` certify DDC behavior and preservation of their declared domains.
    (hα : IsDDCFrom B.domain A.domain a α) (hβ : IsDDCFrom C.domain B.domain b β)
    (hγ : IsDDCFrom C.domain A.domain c γ)
    -- `he` identifies the complete trimmed DDC, including its off-tree values.
    (he : γ = trim (serialM α β)) :
    ofDDC γ hγ = comp (ofDDC α hα) (ofDDC β hβ) := by
  -- `PDCBehavior.comp_ofDDC`: the composition is `ofDDC (trim (serialM α β))` with bound `b * a`.
  change PDCBehavior.ofDDC γ hγ =
    PDCBehavior.comp (PDCBehavior.ofDDC α hα) (PDCBehavior.ofDDC β hβ)
  rw [PDCBehavior.comp_ofDDC]
  subst γ
  -- The behavior of a DDC depends on its replies, not on the chosen certificate.
  apply PDCBehavior.ext
  intro t
  simp only [PDCBehavior.ofDDC_apply]

/-- Attachment of a typed converter to a typed system. -/
noncomputable def attach {A B : Interface} (α : TypedConverter A B) (R : TypedSystem B) :
    TypedSystem A :=
  ⟨PDCBehavior.attach B.nonempty_prefix A.nonempty_prefix α R.1 R.2,
    PDCBehavior.attach_repliesAtQueriedInterface _ _ α R.1 R.2⟩

/-- The action of a typed converter on a typed system is attachment. -/
noncomputable instance {A B : Interface} :
    HSMul (TypedConverter A B) (TypedSystem B) (TypedSystem A) :=
  ⟨attach⟩

/-- `(α • R).1` attaches the PDC behavior `α` to the cumulative behavior `R.1`. -/
lemma smul_val {A B : Interface} (α : TypedConverter A B) (R : TypedSystem B) :
    (α • R).1 = PDCBehavior.attach B.nonempty_prefix A.nonempty_prefix α R.1 R.2 := rfl

/-- **Attaching the identity** leaves a typed system unchanged. -/
lemma identity_attach {A : Interface} (R : TypedSystem A) :
    (TypedConverter.id A • R : TypedSystem A) = R :=
  Subtype.ext (PDCBehavior.attach_id A.nonempty_prefix R.1 R.2)

/-- Attach the inner converter first: `comp α β • R = α • (β • R)`.
[1, §3.3, p. 7]: “(β ∘ α)ⁱR = βⁱ(αⁱR)”, where the source's `β`, `α` are `α`, `β` here. -/
theorem comp_smul
    -- `A`, `B`, `C` are the outside, intermediate and inside interfaces.
    {A B C : Interface}
    -- `α` is the outside converter and `β` the inside converter, attached to system `R` on `C`.
    (α : TypedConverter A B) (β : TypedConverter B C) (R : TypedSystem C) :
    comp α β • R = α • (β • R) :=
  Subtype.ext (PDCBehavior.attach_comp C.nonempty_prefix A.nonempty_prefix B.nonempty_prefix
    α β R.1 R.2)

end TypedConverter

end SystemAlgebra
