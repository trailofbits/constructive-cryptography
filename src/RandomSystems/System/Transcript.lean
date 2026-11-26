module

public import RandomSystems.System.Basic

/-!
# Deterministic interaction transcripts

`System.tr s σ n` records at most `n` query–reply pairs, ending when either partial
participant stops. `System.tr_relabel` transports this interaction through arbitrary query
and reply maps; its input and output corollaries share the same proof.

## References

1. D. Lanzenberger and U. Maurer. *Coupling of Random Systems*. TCC 2020.
   Cryptology ePrint Archive, Paper 2020/1187.
-/

@[expose] public section

namespace SystemAlgebra.System

variable {A B : Type}

open Classical in
/-- **The transcript** of the deterministic system `s` with the strategy `σ` within `n` rounds
[1, Definition 7, p. 12]: "the sequence of pairs (x₁, y₁), (x₂, y₂),
…, (x_l, y_l), defined for i ≥ 1 by xᵢ = e(y₁, …, yᵢ₋₁) and yᵢ = s(x₁, …, xᵢ)", and "If
e(y₁, …, yᵢ₋₁) is undefined (the environment stops), the transcript ends and has length
l = i − 1." It also ends after `n` rounds, and when `s` does not answer the query, which a
compatible strategy never asks. -/
noncomputable def tr (s : System A B) (σ : List B →. A) : ℕ → List (A × B)
  | 0 => []
  | n + 1 =>
    -- The transcript `h` of the first `n` rounds, extended by the query `x` of `σ` and the
    -- reply of `s` to it, if both are defined.
    let h := tr s σ n
    if hx : (σ (h.map Prod.snd)).Dom then
      let x := (σ (h.map Prod.snd)).get hx
      if hy : (s (h.map Prod.fst ++ [x])).Dom then h ++ [(x, (s (h.map Prod.fst ++ [x])).get hy)]
      else h
    else h

/-- Relabeling queries and replies preserves the interaction in their common alphabets. -/
lemma tr_relabel
    -- `f` interprets outside queries in `A`; `g` exposes inside replies in `B'`.
    {A' B' : Type} (s : System A B) (f : A' → A) (g : B → B')
    -- `σ` chooses outside queries from exposed replies; `n` bounds completed rounds.
    (σ : List B' →. A') (n : ℕ) :
    ((relabel s f g).tr σ n).map (Prod.map f id) =
      (s.tr (fun ys => (σ (ys.map g)).map f) n).map (Prod.map id g) := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    -- The previous transcript equation identifies the queries and the caller's reply history.
    have queries := congrArg (List.map Prod.fst) ih
    have replies := congrArg (List.map Prod.snd) ih
    simp only [List.map_map, Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq]
      at queries replies
    -- Both sides ask the same interpreted query and stop on the same undefined reply.
    simp only [tr, relabel, List.map_append, List.map_singleton, List.map_map,
      Function.comp_def, Part.map, queries, replies]
    split_ifs <;>
      simp only [List.map_append, List.map_singleton, Prod.map_apply, id_eq, ih] <;> rfl

/-- Relabeling replies commutes with interaction: the strategy sees the mapped replies,
and the transcript keeps each original query paired with its mapped answer. -/
lemma tr_relabel_output
    -- `s` accepts queries in `A` and returns partial replies in `B`; `f` maps them to `C`.
    {C : Type} (s : System A B) (f : B → C)
    -- `σ` chooses queries from mapped reply histories; `n` is the observation horizon.
    (σ : List C →. A) (n : ℕ) :
    (relabel s id f).tr σ n =
      (s.tr (fun ys => σ (ys.map f)) n).map (Prod.map id f) := by
  simpa only [Prod.map_id, List.map_id, Part.map_id' (f := id) (fun _ => rfl)] using
    tr_relabel s id f σ n

/-- Mapping the caller's queries gives the same transcript as relabeling the resource inputs. -/
lemma tr_relabel_input
    -- `f` maps outside queries to the resource's input alphabet `A`.
    {A' : Type} (s : System A B) (f : A' → A)
    -- `σ` receives the unchanged replies in `B`; `n` is the observation horizon.
    (σ : List B →. A') (n : ℕ) :
    ((relabel s f id).tr σ n).map (Prod.map f id) =
      s.tr (fun ys => (σ ys).map f) n := by
  simpa only [Prod.map_id, List.map_id] using tr_relabel s f id σ n

end SystemAlgebra.System
