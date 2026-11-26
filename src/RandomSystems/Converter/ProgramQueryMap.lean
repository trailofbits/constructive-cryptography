module

public import RandomSystems.Converter.Program
public import RandomSystems.DDC.DDCRelabel

/-!
# Mapping a program's inside queries

`Program.Mode.mapQueries` maps the completed exchange queries and pending query in one
invocation. The outside query, retained state, and inside replies stay unchanged.
`DDC.ofProgramOn_relabel_of_queryMap` transports a body equation to the complete converter
function on its original outside domain, using the shared compiler transport law.
-/

@[expose] public section

namespace SystemAlgebra

variable {S O J : Type} {U V : O → Type} {X X' Y : J → Type}

/-- Map each recorded and pending inside query by `f`, retaining its replies and outside input. -/
def Program.Mode.mapQueries
    (f : (Σ j, X j) → (Σ j, X' j)) :
    Program.Mode S O J U X Y → Program.Mode S O J U X' Y
  | .idle s => .idle s
  | .busy o s u h q => .busy o s u (h.map (Prod.map f id)) (f q)

/-- A body equation transports the emitted message and the resulting invocation. -/
lemma Program.emit_queryMap
    {P : Program S O J U V X Y} {Q : Program S O J U V X' Y}
    -- `f` maps inside query messages; the body equation retains states and final replies.
    (f : (Σ j, X j) → (Σ j, X' j))
    (bodyMap : ∀ s o u h, Sum.map id f (P s o u h) =
      Q s o u (h.map (Prod.map f id)))
    (s : S) (o : O) (u : U o) (h : List ((Σ j, X j) × (Σ j, Y j))) :
    Prod.map (Program.Mode.mapQueries f) (insideMap f) (P.emit s o u h) =
      Q.emit s o u (h.map (Prod.map f id)) := by
  have he := bodyMap s o u h
  unfold Program.emit
  rcases hp : P s o u h with ⟨s', v⟩ | q
  · simp only [hp, Sum.map_inl, id_eq] at he
    rw [← he]
    rfl
  · simp only [hp, Sum.map_inr] at he
    rw [← he]
    rfl

/-- Preserving query labels makes the two programs accept exactly the same next inputs. -/
lemma Program.step_queryMap
    {P : Program S O J U V X Y} {Q : Program S O J U V X' Y}
    (f : (Σ j, X j) → (Σ j, X' j))
    -- `labels` retains the port awaited by each pending query; `f` need not be injective.
    (labels : ∀ q, (f q).1 = q.1)
    (bodyMap : ∀ s o u h, Sum.map id f (P s o u h) =
      Q s o u (h.map (Prod.map f id)))
    (m : Program.Mode S O J U X Y) (x : Σ l, twoFam U Y l) :
    (P.step m x).map (Prod.map (Program.Mode.mapQueries f) (insideMap f)) =
      Q.step (m.mapQueries f) x := by
  classical
  rcases m with s | ⟨o, s, u, h, q⟩ <;> rcases x with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, v⟩
  · simpa only [Program.step, Program.Mode.mapQueries, Option.map_some, List.map_nil] using
      congrArg some (Program.emit_queryMap f bodyMap s j v [])
  · rfl
  · rfl
  · change (if j = q.1 then some (P.emit s o u (h ++ [(q, ⟨j, v⟩)])) else none).map
        (Prod.map (Program.Mode.mapQueries f) (insideMap f)) =
      if j = (f q).1 then
        some (Q.emit s o u (h.map (Prod.map f id) ++ [(f q, ⟨j, v⟩)])) else none
    rw [labels q]
    by_cases hj : j = q.1
    · rw [ite_eq_left hj, ite_eq_left hj, Option.map_some]
      have history : (h ++ [(q, (⟨j, v⟩ : Σ j, Y j))]).map (Prod.map f id) =
          h.map (Prod.map f id) ++ [(f q, ⟨j, v⟩)] := by
        rw [List.map_append, List.map_singleton]
        rfl
      have mapped := Program.emit_queryMap f bodyMap s o u (h ++ [(q, ⟨j, v⟩)])
      rw [history] at mapped
      exact congrArg some mapped
    · rw [ite_eq_right hj, ite_eq_right hj, Option.map_none]

/-- A body-preserving query map relabels the converter on the same outside domain `F`. -/
lemma DDC.ofProgramOn_relabel_of_queryMap
    (P : Program S O J U V X Y) (Q : Program S O J U V X' Y)
    -- `f` changes only inside query values, retaining their labels and every input type.
    (f : (Σ j, X j) → (Σ j, X' j)) (labels : ∀ q, (f q).1 = q.1)
    (bodyMap : ∀ s o u h, Sum.map id f (P s o u h) =
      Q s o u (h.map (Prod.map f id)))
    -- `s` is the shared initial state; `F` admits the same outside query histories.
    (s : S) (F : List (Σ o, U o) → Prop) :
    DDC.ofProgramOn s Q F = relabel (DDC.ofProgramOn s P F) id (insideMap f) :=
  DDC.ofProgramOn_relabel_of_stepMap P Q (Program.Mode.mapQueries f) (insideMap f)
    (Program.step_queryMap f labels bodyMap) s s rfl F

end SystemAlgebra
