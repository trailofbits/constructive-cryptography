module

public import RandomSystems.Typed.DSL.Converters
public import ConstructiveCryptography.Notation

/-!
# Program comparison by retained state

`listProgram` records queries; `mappedListProgram` records their parity bits. A non-injective
state map gives equal converters with different certificates. Equal parity images also give a
many-to-many relation between lists. The forwarding bodies `pairStateProgram` and
`unitStateProgram` test the universal relation and replacement under parallel attachment.
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.ProgramConverterBisimulation

open CategoryTheory CategoryTheory.MonoidalCategory
open SystemAlgebra
open scoped SystemAlgebra

/-- One-port interface with `Fin 4` queries, `Bool` replies, and budget `2`. -/
abbrev SmallPort : Interface :=
  Interface.queryBudget Unit (fun _ => Fin 4) (fun _ => Bool) 2

/-- Non-injective tag map collapsing `Fin 4` to its parity bit. -/
def parity (x : Fin 4) : Bool := x.val % 2 == 0

/-- Program keeping the raw list of `Fin 4` queries; each invocation forwards `u` inside once
and replies with whether `parity u` has been seen among recorded tags or the inside reply holds. -/
def listProgram :
    Program (List (Fin 4)) SmallPort.I SmallPort.I SmallPort.X SmallPort.Y
      SmallPort.X SmallPort.Y
  | _, (), u, [] => .inr ⟨(), u⟩
  | s, (), u, (_, ⟨(), y⟩) :: _ => .inl (u :: s, y || (s.map parity).contains (parity u))

/-- Keep parity bits, query `u` once, then return `y || s.contains (parity u)`. -/
def mappedListProgram :
    Program (List Bool) SmallPort.I SmallPort.I SmallPort.X SmallPort.Y
      SmallPort.X SmallPort.Y
  | _, (), u, [] => .inr ⟨(), u⟩
  | s, (), u, (_, ⟨(), y⟩) :: _ => .inl (parity u :: s, y || s.contains (parity u))

lemma listProgram_bounded (b : ℕ) (hb : 1 ≤ b) : listProgram.Bounded b := by
  intro s o u h q _ hq
  rcases h with _ | ⟨⟨_, ⟨_, _⟩⟩, _⟩
  · simp; omega
  · simp [listProgram] at hq

lemma mappedListProgram_bounded (b : ℕ) (hb : 1 ≤ b) : mappedListProgram.Bounded b := by
  intro s o u h q _ hq
  rcases h with _ | ⟨⟨_, ⟨_, _⟩⟩, _⟩
  · simp; omega
  · simp [mappedListProgram] at hq

lemma listProgram_isDDCFrom (s : List (Fin 4)) :
    IsDDCFrom SmallPort.domain SmallPort.domain 1
      (DDC.ofProgramOn s listProgram SmallPort.domain) :=
  DDC.ofProgramOn_isDDCFrom (listProgram_bounded 1 le_rfl) SmallPort.nonempty_prefix.2
    fun h hr hF => by
      by_cases hne : insideQueries (h.map Prod.snd) = []
      · exact Or.inl hne
      · refine Or.inr ⟨hne, ?_⟩
        simpa using DDC.insideQueries_length_le_of_budget
          (listProgram_bounded 1 le_rfl) SmallPort.length_le hr hF

lemma mappedListProgram_isDDCFrom (t : List Bool) :
    IsDDCFrom SmallPort.domain SmallPort.domain 2
      (DDC.ofProgramOn t mappedListProgram SmallPort.domain) :=
  DDC.ofProgramOn_isDDCFrom (mappedListProgram_bounded 2 (by omega)) SmallPort.nonempty_prefix.2
    fun h hr hF => by
      by_cases hne : insideQueries (h.map Prod.snd) = []
      · exact Or.inl hne
      · refine Or.inr ⟨hne, ?_⟩
        simpa using DDC.insideQueries_length_le_of_budget
          (mappedListProgram_bounded 1 le_rfl) SmallPort.length_le hr hF

/-- The list program and mapped-list program define one typed converter, even with distinct
certificates (`1` vs `2`). -/
lemma listProgram_eq_mappedListProgram (s : List (Fin 4)) :
    TypedConverter.ofDDC (DDC.ofProgramOn s listProgram SmallPort.domain)
        (listProgram_isDDCFrom s) =
      TypedConverter.ofDDC (DDC.ofProgramOn (s.map parity) mappedListProgram SmallPort.domain)
        (mappedListProgram_isDDCFrom (s.map parity)) := by
  refine TypedConverter.ofDDC_ofProgramOn_eq_of_stateMap listProgram mappedListProgram
    (List.map parity) ?_ _ _
  intro σ o u h
  rcases o with ⟨⟩
  rcases h with _ | ⟨⟨_, ⟨⟨⟩, y⟩⟩, _⟩ <;> rfl

/-- Different lists with equal parity images form a many-to-many state relation. -/
example : DDC.ofProgram [(0 : Fin 4)] listProgram =
    DDC.ofProgram [(2 : Fin 4)] listProgram := by
  apply DDC.ofProgram_eq_of_stateRel listProgram listProgram
    (fun s t => s.map parity = t.map parity) ?_ (by rfl)
  intro s t o u h related
  rcases o with ⟨⟩
  rcases h with _ | ⟨⟨_, ⟨⟨⟩, y⟩⟩, _⟩
  · exact Sum.LiftRel.inr rfl
  · apply Sum.LiftRel.inl
    exact ⟨congrArg (List.cons (parity u)) related,
      congrArg (fun tags => y || tags.contains (parity u)) related⟩

/-- A prior query of the same parity changes the reply even when the inside answer is false. -/
example : listProgram [0] () 2 [(⟨(), 2⟩, ⟨(), false⟩)] = .inl ([2, 0], true) := by
  rfl

/-- Forwarding program with state `Unit × Unit`. -/
def pairStateProgram :
    Program (Unit × Unit) SmallPort.I SmallPort.I SmallPort.X SmallPort.Y
      SmallPort.X SmallPort.Y
  | _, (), u, [] => .inr ⟨(), u⟩
  | _, (), _, (_, ⟨(), y⟩) :: _ => .inl (((), ()), y)

/-- Forwarding program with state `Unit` and the same body. -/
def unitStateProgram :
    Program Unit SmallPort.I SmallPort.I SmallPort.X SmallPort.Y
      SmallPort.X SmallPort.Y
  | _, (), u, [] => .inr ⟨(), u⟩
  | _, (), _, (_, ⟨(), y⟩) :: _ => .inl ((), y)

lemma pairStateProgram_isDDCFrom :
    IsDDCFrom SmallPort.domain SmallPort.domain 1
      (DDC.ofProgramOn ((), ()) pairStateProgram SmallPort.domain) := by
  have hb : pairStateProgram.Bounded 1 := by
    intro s o u h q _ hq
    rcases h with _ | ⟨⟨_, ⟨_, _⟩⟩, _⟩
    · simp
    · simp [pairStateProgram] at hq
  exact DDC.ofProgramOn_isDDCFrom hb SmallPort.nonempty_prefix.2 fun h hr hF => by
    by_cases hne : insideQueries (h.map Prod.snd) = []
    · exact Or.inl hne
    · refine Or.inr ⟨hne, ?_⟩
      simpa using DDC.insideQueries_length_le_of_budget hb SmallPort.length_le hr hF

lemma unitStateProgram_isDDCFrom :
    IsDDCFrom SmallPort.domain SmallPort.domain 1
      (DDC.ofProgramOn () unitStateProgram SmallPort.domain) := by
  have hb : unitStateProgram.Bounded 1 := by
    intro s o u h q _ hq
    rcases h with _ | ⟨⟨_, ⟨_, _⟩⟩, _⟩
    · simp
    · simp [unitStateProgram] at hq
  exact DDC.ofProgramOn_isDDCFrom hb SmallPort.nonempty_prefix.2 fun h hr hF => by
    by_cases hne : insideQueries (h.map Prod.snd) = []
    · exact Or.inl hne
    · refine Or.inr ⟨hne, ?_⟩
      simpa using DDC.insideQueries_length_le_of_budget hb SmallPort.length_le hr hF

/-- `Unit × Unit` and `Unit` programs with identical bodies define one typed converter along the
universal relation. -/
lemma pairStateProgram_eq_unitStateProgram :
    TypedConverter.ofDDC (DDC.ofProgramOn ((), ()) pairStateProgram SmallPort.domain)
        pairStateProgram_isDDCFrom =
      TypedConverter.ofDDC (DDC.ofProgramOn () unitStateProgram SmallPort.domain)
        unitStateProgram_isDDCFrom := by
  refine TypedConverter.ofDDC_ofProgramOn_eq_of_stateRel pairStateProgram unitStateProgram
    (fun _ _ => True) ?_ trivial _ _
  intro σ τ o u h _
  rcases o with ⟨⟩
  rcases h with _ | ⟨⟨_, ⟨⟨⟩, y⟩⟩, _⟩
  · exact Sum.LiftRel.inr rfl
  · exact Sum.LiftRel.inl ⟨trivial, rfl⟩

/-- `cc_normalize` composes cleanly with state-map and state-relation equalities in context. -/
example {C : Interface} (R : TypedSystem SmallPort) (S : TypedSystem C) :
    ((TypedConverter.ofDDC (DDC.ofProgramOn ((), ()) pairStateProgram SmallPort.domain)
        pairStateProgram_isDDCFrom : SmallPort ⟶ SmallPort) ⊗ₘ 𝟙 C) • (R ∥ S) =
      (TypedConverter.ofDDC (DDC.ofProgramOn () unitStateProgram SmallPort.domain)
        unitStateProgram_isDDCFrom • R) ∥ S := by
  rw [pairStateProgram_eq_unitStateProgram]
  cc_normalize

#print axioms Program.emit_stateMap
#print axioms Program.step_stateMap
#print axioms Program.after_stateMap
#print axioms DDC.ofProgram_eq_of_stateMap
#print axioms DDC.ofProgramOn_eq_of_stateMap
#print axioms TypedConverter.ofDDC_ofProgramOn_eq_of_stateMap
#print axioms DDC.ofProgram_eq_of_stateRel
#print axioms DDC.ofProgramOn_eq_of_stateRel
#print axioms TypedConverter.ofDDC_ofProgramOn_eq_of_stateRel

end Tests.ProgramConverterBisimulation
