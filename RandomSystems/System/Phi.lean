/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.Connect

/-!
# Φ: the universe of all systems

MauRen16 §2.3 works over "a universe `Φ` of objects"; specifications are
its subsets.  Here Φ is **one type** of systems over the universal
alphabet:

```
Uni := Σ X : Type u, X          Φ := PDS Uni Uni
```

A query carries its type — there are no untyped values anywhere — and an
element's signature is not data on it: `support` derives the queries it
answers, and "speaks `(X, Y)`" is membership in the specification
`TypedAt X Y`.  The union `typed = ⋃ X Y, TypedAt X Y` is the literal
set-of-all-`PDS X Y`; its elements are bare behaviors, their alphabets
views — which is what MauRen16's Φ is in set theory, where an untagged
union forgets intended signatures and keeps supports.

Typed systems arrive by the canonical on-ramp `ofTyped` (a value `x : X`
enters as `⟨X, x⟩`; nothing is encoded, nothing is chosen), hidden behind a
coercion at use sites — the `ℕ ⊆ ℝ` discipline.  A foreign query is out of
domain: partiality by undefinedness, no error element.

Resources, converters, and environments are all elements of Φ, roles
positional (CR18 Def 3.8; LiuZhang §3.3.3; Jost §2.2: converters are
systems).  The converter monoid Σ is derived from Φ by `connect`, in the
attachment modules.
-/

namespace RandomSystems

open Probability (Distribution)

noncomputable section

open Classical

universe u v w

/-- The universal alphabet: every `u`-typed value, addressed by its type.
Jost fixes one countable alphabet 𝒳 and addresses interfaces inside it;
this is the same move at the canonical alphabet of all typed values, so
nothing is left out and no encoding is chosen. -/
def Uni : Type (u + 1) := Σ X : Type u, X

/-- MauRen16 §2.3's Φ: the set of all probabilistic discrete systems, as
one type.  Resources, converters, and environments alike; a specification
is a `Set Phi`. -/
def Phi : Type (u + 1) := PDS Uni.{u} Uni.{u}

namespace System

/-- The queries a system can ever answer: its interface set, derived from
behavior rather than carried as data. -/
def support {X : Type v} {Y : Type w} (S : DDS X Y) : Set X :=
  {q | ∃ l ∈ dom S, q ∈ l}

/-- The canonical inclusion of a typed value: itself, with its type as
address.  A named constant so every elaboration is the same term (the
ascription `(⟨X, x⟩ : Uni)` elaborates inconsistently). -/
def encode (X : Type u) (x : X) : Uni.{u} := ⟨X, x⟩

/-- Decode a universal query at alphabet `X`: defined exactly on `X`'s
copy.  The one site where a type equality lives. -/
def decode (X : Type u) (q : Uni.{u}) : Part X :=
  ⟨q.1 = X, fun h => h ▸ q.2⟩

@[simp] theorem decode_encode (X : Type u) (x : X) :
    decode X (encode X x) = Part.some x := by
  refine Part.eq_some_iff.mpr ?_
  exact ⟨rfl, rfl⟩

/-- Decode a history entrywise. -/
def decodeList (X : Type u) : List Uni.{u} → Part (List X)
  | [] => Part.some []
  | q :: t => (decode X q).bind fun x => (decodeList X t).map (x :: ·)

/-- A defined decoding certifies every entry's address. -/
theorem decodeList_dom_mem {X : Type u} :
    ∀ {l : List Uni.{u}}, (decodeList X l).Dom → ∀ q ∈ l, q.1 = X := by
  intro l
  induction l with
  | nil =>
      intro _ q hq
      exact absurd hq (List.not_mem_nil)
  | cons a t ih =>
      intro h q hq
      obtain ⟨ha, hrest⟩ := Part.bind_dom.mp h
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact ha
      · exact ih hrest q hq'

/-- The canonical typed on-ramp, raw: decode every query at `X`, run the
system, re-encode the answer at `Y`.  Foreign queries are out of domain. -/
def ofTypedRaw {X Y : Type u} (S : DDS X Y) : Raw Uni.{u} Uni.{u} :=
  fun l => ((decodeList X l).bind fun lx => S.1 lx).map
    fun y => (⟨Y, y⟩ : Uni.{u})

/-- The canonical typed on-ramp: every `S : DDS X Y` as a system over the
universal alphabet.  A value enters as itself with its type as address —
nothing is encoded, nothing is chosen. -/
def ofTyped {X Y : Type u} (S : DDS X Y) : DDS Uni.{u} Uni.{u} :=
  validate (ofTypedRaw S)

/-- **The signature receipt**: an on-ramped system's support lies in its
own alphabet's copy — the signature recovered as a theorem about the
element. -/
theorem support_ofTyped {X Y : Type u} (S : DDS X Y) :
    support (ofTyped S) ⊆ {q | q.1 = X} := by
  rintro q ⟨l, hl, hq⟩
  have hraw : (ofTypedRaw S l).Dom := hl.2 l (List.prefix_refl _) hl.1
  obtain ⟨hdec, -⟩ := hraw
  exact decodeList_dom_mem hdec q hq

/-! ### The inclusion round trip

An included resource, interrogated on its own alphabet's copy, is
indistinguishable from the typed system: decoding inverts the inclusion,
prefixes of included histories are included prefixes, and the domain and
outputs transfer exactly. -/

/-- Decoding an included history recovers it. -/
theorem decodeList_encode (X : Type u) (l : List X) :
    decodeList X (l.map (encode X)) = Part.some l := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      show ((decode X (encode X x)).bind fun x' =>
        (decodeList X (t.map (encode X))).map (x' :: ·)) = _
      rw [ih, decode_encode]
      simp [Part.bind_some]

/-- A prefix of an included history is an included prefix. -/
theorem prefix_map_encode {X : Type u} :
    ∀ {l : List X} {l' : List Uni.{u}},
      l' <+: l.map (encode X) →
      ∃ l₀ : List X, l₀ <+: l ∧ l' = l₀.map (encode X) := by
  intro l
  induction l with
  | nil =>
      intro l' h
      exact ⟨[], List.prefix_refl _, List.prefix_nil.mp h⟩
  | cons x t ih =>
      intro l' h
      cases l' with
      | nil => exact ⟨[], List.nil_prefix, rfl⟩
      | cons e l'' =>
          rw [List.map_cons, List.cons_prefix_cons] at h
          obtain ⟨rfl, h'⟩ := h
          obtain ⟨l₀, hpre, rfl⟩ := ih h'
          exact ⟨x :: l₀, List.cons_prefix_cons.mpr ⟨rfl, hpre⟩, rfl⟩

/-- The included resource accepts an included history iff the typed system
accepts it. -/
theorem mem_dom_ofTyped_encode {X Y : Type u} {S : DDS X Y} {l : List X}
    (hne : l ≠ []) :
    (l.map (encode X)) ∈ dom (ofTyped S) ↔ l ∈ dom S := by
  constructor
  · intro h
    have hraw : (ofTypedRaw S (l.map (encode X))).Dom :=
      h.2 _ (List.prefix_refl _) h.1
    obtain ⟨hdec, hS⟩ := hraw
    have hget : (decodeList X (l.map (encode X))).get hdec = l :=
      Part.get_eq_of_mem (by rw [decodeList_encode]; exact Part.mem_some _)
        hdec
    have hS' : (S.1 ((decodeList X (l.map (encode X))).get hdec)).Dom := hS
    rw [hget] at hS'
    exact hS'
  · intro hS
    refine ⟨fun hc => hne (List.map_eq_nil_iff.mp hc), ?_⟩
    intro l' hl' hne'
    obtain ⟨l₀, hpre, rfl⟩ := prefix_map_encode hl'
    have hl₀ne : l₀ ≠ [] := fun hc => hne' (by rw [hc]; rfl)
    have hcompute : ofTypedRaw S (l₀.map (encode X)) =
        (S.1 l₀).map (encode Y) := by
      show ((decodeList X _).bind fun lx => S.1 lx).map _ = _
      rw [decodeList_encode, Part.bind_some]
      rfl
    rw [hcompute]
    exact prefix_closed S hpre hl₀ne hS

/-- The included resource's output at an included history: the typed
output, included. -/
theorem output_ofTyped_encode {X Y : Type u} {S : DDS X Y} {l : List X}
    (hS : l ∈ dom S) (h : (l.map (encode X)) ∈ dom (ofTyped S)) :
    output (ofTyped S) (l.map (encode X)) h =
      encode Y (output S l hS) := by
  apply output_validate_of_eq_some
  rw [show ofTypedRaw S (l.map (encode X)) =
      (S.1 l).map (encode Y) by
    show ((decodeList X _).bind fun lx => S.1 lx).map _ = _
    rw [decodeList_encode, Part.bind_some]
    rfl]
  exact Part.eq_some_iff.mpr (Part.mem_map _ (Part.get_mem hS))

/-- The inclusion is injective. -/
theorem encode_injective (X : Type u) :
    Function.Injective (encode X) := by
  intro a b h
  have := congrArg (decode X) h
  rw [decode_encode, decode_encode] at this
  exact Part.some_inj.mp this

/-- Decoding recovers the included value. -/
theorem encode_decode {Y : Type u} (q : Uni.{u})
    (h : (decode Y q).Dom) : encode Y ((decode Y q).get h) = q := by
  obtain ⟨Q, v⟩ := q
  cases h
  rfl

/-- A decodable history is an included history. -/
theorem decodeList_mem_eq {X : Type u} :
    ∀ {l : List Uni.{u}} {lx : List X},
      lx ∈ decodeList X l → l = lx.map (encode X) := by
  intro l
  induction l with
  | nil =>
      intro lx h
      have : lx = [] := Part.mem_some_iff.mp h
      rw [this]
      rfl
  | cons q t ih =>
      intro lx h
      obtain ⟨x, hx, hmem⟩ := Part.mem_bind_iff.mp h
      obtain ⟨tx, htx, rfl⟩ := (Part.mem_map_iff _).mp hmem
      have hq : q = encode X x := by
        obtain ⟨hd, hget⟩ := hx
        rw [← hget]
        exact (encode_decode q hd).symm
      rw [List.map_cons, ← ih htx, ← hq]

/-- A universal resource viewed at a typed signature: query through the
inclusion, decode the answers.  Dual to `ofTyped`; the inclusion is a
section of it. -/
def toTypedRaw (X Y : Type u) (R : DDS Uni.{u} Uni.{u}) : Raw X Y :=
  fun l => (R.1 (l.map (encode X))).bind (decode Y)

def toTyped (X Y : Type u) (R : DDS Uni.{u} Uni.{u}) : DDS X Y :=
  validate (toTypedRaw X Y R)

/-- Blocking commutes with the inclusion: silencing queries of an
included resource is including it with the decoded queries silenced. -/
theorem blockSet_ofTyped {X Y : Type u} (Q : Set Uni.{u}) (S : DDS X Y) :
    blockSet Q (ofTyped S) = ofTyped (blockSet (encode X ⁻¹' Q) S) := by
  apply Subtype.ext
  funext l
  refine Part.ext' ?_ (fun _ _ => rfl)
  constructor
  · rintro ⟨⟨hne, hall⟩, havoid⟩
    refine ⟨hne, fun l' hl' hne' => ?_⟩
    obtain ⟨hdec, hS⟩ := hall l' hl' hne'
    refine ⟨hdec, hS, ?_⟩
    intro x hx
    have heq : l' = ((decodeList X l').get hdec).map (encode X) :=
      decodeList_mem_eq (Part.get_mem hdec)
    have hmem : encode X x ∈ l' := by
      rw [heq]
      exact List.mem_map_of_mem hx
    exact havoid (encode X x) (hl'.subset hmem)
  · rintro ⟨hne, hall⟩
    have hfull := hall l (List.prefix_refl _) hne
    obtain ⟨hdec, hS, hav⟩ := hfull
    refine ⟨⟨hne, fun l' hl' hne' => ?_⟩, ?_⟩
    · obtain ⟨hdec', hS', -⟩ := hall l' hl' hne'
      exact ⟨hdec', hS'⟩
    · intro q hq
      have heq : l = ((decodeList X l).get hdec).map (encode X) :=
        decodeList_mem_eq (Part.get_mem hdec)
      rw [heq] at hq
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
      exact hav x hx

/-- Blocking commutes with the typed view. -/
theorem toTyped_blockSet {X Y : Type u} (Q : Set Uni.{u})
    (R : DDS Uni.{u} Uni.{u}) :
    toTyped X Y (blockSet Q R) =
      blockSet (encode X ⁻¹' Q) (toTyped X Y R) := by
  apply Subtype.ext
  funext lx
  refine Part.ext' ?_ (fun _ _ => rfl)
  constructor
  · rintro ⟨hne, hall⟩
    have hfull := hall lx (List.prefix_refl _) hne
    obtain ⟨⟨hR, hav⟩, hdec⟩ := hfull
    refine ⟨⟨hne, fun lx' hl' hne' => ?_⟩, ?_⟩
    · obtain ⟨⟨hR', hav'⟩, hdec'⟩ := hall lx' hl' hne'
      exact ⟨hR', hdec'⟩
    · intro x hx
      exact hav (encode X x) (List.mem_map_of_mem hx)
  · rintro ⟨⟨hne, hall⟩, havoid⟩
    refine ⟨hne, fun lx' hl' hne' => ?_⟩
    obtain ⟨hR', hdec'⟩ := hall lx' hl' hne'
    refine ⟨⟨hR', ?_⟩, hdec'⟩
    intro q hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
    exact havoid x (hl'.subset hx)

/-- **The preimage of an interface set's included queries** is the tag
cylinder — the inclusion transfer that carries a splitting of `Uni` back
to a splitting of the tagged alphabet. -/
theorem encode_preimage_tags {P A : Type u} (Z : Set P) :
    encode (P × A) ⁻¹'
        {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A, q = encode (P × A) (p, a)} =
      {p : P × A | p.1 ∈ Z} := by
  ext ⟨p, a⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨p', hp', a', heq⟩
    have hfst : p = p' := congrArg Prod.fst (encode_injective (P × A) heq)
    rw [hfst]
    exact hp'
  · intro hp
    exact ⟨p, hp, a, rfl⟩

end System

/-- The canonical typed on-ramp at the probabilistic level. -/
def ofTyped {X Y : Type u} : PDS X Y → Phi.{u} :=
  Distribution.fTransform System.ofTyped

/-- Typed systems coerce into Φ silently — the `ℕ ⊆ ℝ` discipline. -/
instance {X Y : Type u} : CoeTC (PDS X Y) Phi.{u} :=
  ⟨ofTyped⟩

/-- "Speaks `(X, Y)`" is a specification, not data on the element. -/
def TypedAt (X Y : Type u) : Set Phi.{u} :=
  Set.range (ofTyped (X := X) (Y := Y))

theorem ofTyped_mem_typedAt {X Y : Type u} (S : PDS X Y) :
    ofTyped S ∈ TypedAt X Y :=
  ⟨S, rfl⟩

/-- The literal union of all `PDS X Y`, for all `X Y` — MauRen16's Φ as
written on paper. -/
def typed : Set Phi.{u} :=
  ⋃ (X : Type u) (Y : Type u), TypedAt X Y

theorem ofTyped_mem_typed {X Y : Type u} (S : PDS X Y) :
    ofTyped S ∈ typed.{u} :=
  Set.mem_iUnion.mpr ⟨X, Set.mem_iUnion.mpr ⟨Y, ofTyped_mem_typedAt S⟩⟩

/-- The interface set of a resource: the union of its behaviors'
supports. -/
def support (R : Phi.{u}) : Set Uni.{u} :=
  ⋃ S ∈ R.support, System.support S

end

/-! ## Parallel composition of laws (MauRen16 §2.1; Jost §2.2.2)

The independent product of component laws pushed along the deterministic
parallel composition; consumed by `System/Parallel.lean`. -/

namespace PDS

noncomputable section

open Probability (Distribution)

universe u v

/-- The alphabet family of a two-component parallel composition. -/
abbrev parAlphabet (A B : Type u) : Fin 2 → Type u := ![A, B]

/-- The law of `[R, S]`: the independent product of the component laws,
pushed forward along the deterministic parallel composition. -/
noncomputable def parLaw {X X' : Type u} {Y Y' : Type v} (S : PDS X Y)
    (T : PDS X' Y') :
    PDS (Sigma (parAlphabet X X')) (Sigma (parAlphabet Y Y')) :=
  Distribution.fTransform
    (fun p : System.DDS X Y × System.DDS X' Y' =>
      System.parallel (Xs := parAlphabet X X') (Ys := parAlphabet Y Y')
        (Fin.cases p.1 (Fin.cases p.2 (fun i => i.elim0))))
    (Distribution.prod S T)

end

end PDS

end RandomSystems
