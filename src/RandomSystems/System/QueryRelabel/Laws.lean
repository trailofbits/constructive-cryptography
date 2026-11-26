module

public import RandomSystems.System.QueryRelabel
public import RandomSystems.System.Distinguisher

/-!
# Laws of query relabeling

`envOf_relabelQueries` maps the caller's next resource query;
`IsDDD.relabelQueries` preserves its interaction discipline.
`ddeOf_relabelQueries` maps its query strategy; `ddeOf_relabelQueries_map_decode`
recovers that strategy when decoding is inverse on the queries it can propose.
`queryBounded_ddeOf_relabelQueries_iff` preserves every stopping horizon.
These laws combine with `System.tr_relabel_input` to transport completed observations.
-/

@[expose] public section

namespace SystemAlgebra

variable
  -- `I` labels resource ports; `X i` and `X' i` carry the source and coded queries.
  -- `Y i` carries the replies, which query relabeling leaves unchanged.
  {I : Type} {X X' Y : I → Type}

/-- The query function of `D.relabelQueries code` is the pointwise image of `envOf D`. -/
lemma envOf_relabelQueries
    -- `D` is the source caller; `code i` changes query values at port `i`.
    (D : DDD I X Y) (code : ∀ i, X i → X' i)
    -- `ys` is the received reply history at which the next query is observed.
    (ys : List (Σ i, Y i)) :
    envOf (DDD.relabelQueries D code) ys =
      (envOf D ys).map (fun x => ⟨x.1, code x.1 x.2⟩) := by
  unfold DDD.relabelQueries
  simp only [envOf, relabel, List.map_id, Part.bind_map, Part.map_bind]
  congr 1
  funext o
  obtain ⟨_ | _ | i, value⟩ := o
  · exact value.elim
  · exact (Part.map_none _).symm
  · rfl

/-- Relabeling resource queries preserves the distinguisher discipline. -/
lemma IsDDD.relabelQueries
    -- `valid` certifies the source caller `D`'s bounded interaction discipline.
    {D : DDD I X Y} (valid : IsDDD D)
    -- `code` changes query values while keeping their resource port.
    (code : ∀ i, X i → X' i) : IsDDD (DDD.relabelQueries D code) := by
  apply valid.relabel id _ (Equiv.refl I)
  · rintro ⟨p, x⟩
    cases p <;> rfl
  · rintro ⟨p, x⟩
    cases p with
    | start => exact x.elim
    | dec => rfl
    | res i => rfl

/-- Trimming and query relabeling induce the same mapped strategy. -/
lemma ddeOf_relabelQueries
    -- `valid` supplies the query environment of the source caller `D`.
    {D : DDD I X Y} (valid : IsDDD D)
    -- `code` maps each query at its own port; `ys` is the received reply history.
    (code : ∀ i, X i → X' i) (ys : List (Σ i, Y i)) :
    (ddeOf (IsDDD.relabelQueries valid code)).1 ys =
      ((ddeOf valid).1 ys).map (fun x => ⟨x.1, code x.1 x.2⟩) := by
  change envOf (trim (DDD.relabelQueries D code)) ys = _
  rw [show trim (DDD.relabelQueries D code) = DDD.relabelQueries (trim D) code from
    trim_relabel D id _]
  exact envOf_relabelQueries (trim D) code ys

/-- Query relabeling preserves each stopping bound, including bound zero. -/
lemma queryBounded_ddeOf_relabelQueries_iff
    -- `valid` supplies the source caller's query environment; `code` changes only its queries.
    {D : DDD I X Y} (valid : IsDDD D) (code : ∀ i, X i → X' i)
    -- `n` is the same maximum number of queries before and after recoding.
    (n : ℕ) :
    QueryBounded n (ddeOf (IsDDD.relabelQueries valid code)) ↔
      QueryBounded n (ddeOf valid) := by
  have domains (ys : List (Σ i, Y i)) :
      ((ddeOf (IsDDD.relabelQueries valid code)).1 ys).Dom ↔
        ((ddeOf valid).1 ys).Dom := by
    rw [ddeOf_relabelQueries, Part.map_Dom]
  exact ⟨fun bounded ys h => bounded ys ((domains ys).mpr h),
    fun bounded ys h => bounded ys ((domains ys).mp h)⟩

/-- A decoder need undo the code only on queries the original strategy can propose. -/
lemma ddeOf_relabelQueries_map_decode
    -- `valid` supplies the source caller `D`'s query environment.
    {D : DDD I X Y} (valid : IsDDD D)
    -- `code` and `decode` translate query values without changing their ports.
    (code : ∀ i, X i → X' i) (decode : ∀ i, X' i → X i)
    -- `supported` puts every proposed query in `K`; `inverse` recovers values there.
    (K : Set (Σ i, X i))
    (supported : ∀ ys x, x ∈ (ddeOf valid).1 ys → x ∈ K)
    (inverse : ∀ x ∈ K, decode x.1 (code x.1 x.2) = x.2)
    -- `ys` is any reply history, including one where the caller has stopped.
    (ys : List (Σ i, Y i)) :
    ((ddeOf (IsDDD.relabelQueries valid code)).1 ys).map
      (fun x => ⟨x.1, decode x.1 x.2⟩) = (ddeOf valid).1 ys := by
  rw [ddeOf_relabelQueries, Part.map_map]
  · refine Part.ext' Iff.rfl ?_
    intro _ defined
    let x := ((ddeOf valid).1 ys).get defined
    exact congrArg (Sigma.mk x.1) (inverse x (supported ys x (Part.get_mem defined)))

end SystemAlgebra
