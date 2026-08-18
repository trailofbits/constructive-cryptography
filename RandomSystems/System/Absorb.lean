/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.ConnectPhi
import RandomSystems.System.Environment
import RandomSystems.System.FullyDefined

/-!
# Absorption: the converters an environment can run itself

MauRen16 **§4.3**'s vocabulary — "a polynomial-time converter can be absorbed
into a poly-time distinguisher without leaving the distinguisher class, i.e.,
the metric is non-expanding".  The property absorption certifies is therefore
MauRen16 **Definition 2**, not Lemma 2 (which consumes it).  A converter is
**absorbed** by the
environment when everything the environment learns by interacting with the
converted system it could have learnt by interacting with the bare system
under a different strategy.  Absorption is what makes the distinguishing
metric a *pseudometric on the quotient by converters*, and it is stated here
at the fully defined advantage of Ruling R4 (`PDS.advFullyDefined`).

The layering is deliberate:

* `nonexpandingConverters` — the endomorphisms of Φ that never help, as a
  submonoid.  Composition chains the inequalities; that is the whole content
  of the algebraic step, and it is proved once.
* `PDS.advFullyDefined_fTransform_le` — the **pushforward reduction**: the
  single lemma that separates the metric plumbing (data processing, suprema)
  from the interpreter work.  Its hypothesis is purely combinatorial: every
  outer interaction, at every length, is a *fixed* post-processing of some
  inner interaction, uniformly in the deterministic system.
* the individual generator families, each discharging that hypothesis by a
  re-simulation argument.

Only the first two are carrier-independent; everything below them is about a
specific way of building a system from a system.
-/

namespace RandomSystems

noncomputable section

open Probability (Distribution statDist)

open scoped ENNReal

universe u

/-- **The converters that never help a distinguisher**: the nonexpanding
endomorphisms of Φ for the fully defined advantage.  A submonoid by
definition — composition chains the inequalities, and the identity is
reflexivity.

This is the target specification of the whole module: every statement below
is a membership proof, and the closure theorem is the assembly. -/
def nonexpandingConverters : Submonoid (Function.End Phi.{u}) where
  carrier := {σ | ∀ RL SL : Phi.{u},
    PDS.advFullyDefined (σ RL) (σ SL) ≤ PDS.advFullyDefined RL SL}
  one_mem' := fun _ _ => le_rfl
  mul_mem' := fun {_ τ} hσ hτ RL SL =>
    le_trans (hσ (τ RL) (τ SL)) (hτ RL SL)

@[simp]
theorem mem_nonexpandingConverters {σ : Function.End Phi.{u}} :
    σ ∈ nonexpandingConverters.{u} ↔
      ∀ RL SL : Phi.{u},
        PDS.advFullyDefined (σ RL) (σ SL) ≤ PDS.advFullyDefined RL SL :=
  Iff.rfl

namespace PDS

/-! ## The pushforward reduction

The one lemma that separates metric plumbing from interpreter work.  Read the
hypothesis as: *the environment `e`, run for `n` rounds against the
transformed system, is a fixed post-processing `p` of the environment `e'`
run for `m` rounds against the original system* — and the choice of
`(e', m, p)` may depend on `(e, n)` but **not** on the deterministic system.
That is exactly what "the environment absorbs the converter" means, and it is
strictly stronger than the metric conclusion: it says the outer view is a
function of an inner view, not merely that it is no easier to distinguish
with. -/

theorem advFullyDefined_fTransform_le
    {X : Type*} {Y : Type*} {X' : Type*} {Y' : Type*}
    (g : System.DDS X Y → System.DDS X' Y') (RL SL : PDS X Y)
    (h : ∀ (e : System.DDE.Total Y' X') (n : ℕ),
      ∃ (e' : System.DDE.Total Y X) (m : ℕ)
        (p : List (X × Option Y) → List (X' × Option Y')),
        ∀ s : System.DDS X Y,
          System.DDE.Total.transcript (g s) e n =
            p (System.DDE.Total.transcript s e' m)) :
    advFullyDefined (Distribution.fTransform g RL)
        (Distribution.fTransform g SL) ≤
      advFullyDefined RL SL := by
  refine iSup_le fun e => iSup_le fun n => ?_
  obtain ⟨e', m, p, hp⟩ := h e n
  have key : ∀ L : PDS X Y,
      trLawFullyDefined e n (Distribution.fTransform g L) =
        Distribution.fTransform p (trLawFullyDefined e' m L) := by
    intro L
    show Distribution.fTransform _ (Distribution.fTransform g L) =
      Distribution.fTransform p (Distribution.fTransform _ L)
    rw [Distribution.fTransform_fTransform, Distribution.fTransform_fTransform]
    exact congrFun (congrArg Distribution.fTransform (funext hp)) L
  rw [key RL, key SL]
  calc
    ENNReal.ofReal
        (statDist (Distribution.fTransform p (trLawFullyDefined e' m RL))
          (Distribution.fTransform p (trLawFullyDefined e' m SL)))
        ≤ ENNReal.ofReal
            (statDist (trLawFullyDefined e' m RL)
              (trLawFullyDefined e' m SL)) :=
          ENNReal.ofReal_le_ofReal
            (Probability.statDist_fTransform_le _ _ p)
    _ ≤ advFullyDefined RL SL := le_iSup_of_le e' (le_iSup_of_le m le_rfl)

/-- The reduction in the other direction, for the *inclusions*: if every inner
interaction is a fixed post-processing of some outer one — again uniformly in
the deterministic system — then the construction loses nothing either, and the
two advantages are equal.  Same proof as above with the roles of the two
interactions exchanged; it is a separate statement because it is a separate
hypothesis, and only a construction that is a genuine inclusion satisfies
both. -/
theorem advFullyDefined_le_fTransform
    {X : Type*} {Y : Type*} {X' : Type*} {Y' : Type*}
    (g : System.DDS X Y → System.DDS X' Y') (RL SL : PDS X Y)
    (h : ∀ (e' : System.DDE.Total Y X) (m : ℕ),
      ∃ (e : System.DDE.Total Y' X') (n : ℕ)
        (q : List (X' × Option Y') → List (X × Option Y)),
        ∀ s : System.DDS X Y,
          System.DDE.Total.transcript s e' m =
            q (System.DDE.Total.transcript (g s) e n)) :
    advFullyDefined RL SL ≤
      advFullyDefined (Distribution.fTransform g RL)
        (Distribution.fTransform g SL) := by
  refine iSup_le fun e' => iSup_le fun m => ?_
  obtain ⟨e, n, q, hq⟩ := h e' m
  have key : ∀ L : PDS X Y,
      trLawFullyDefined e' m L =
        Distribution.fTransform q
          (trLawFullyDefined e n (Distribution.fTransform g L)) := by
    intro L
    show Distribution.fTransform _ L =
      Distribution.fTransform q
        (Distribution.fTransform _ (Distribution.fTransform g L))
    rw [Distribution.fTransform_fTransform, Distribution.fTransform_fTransform]
    exact congrFun (congrArg Distribution.fTransform (funext hq)) L
  rw [key RL, key SL]
  calc
    ENNReal.ofReal
        (statDist
          (Distribution.fTransform q
            (trLawFullyDefined e n (Distribution.fTransform g RL)))
          (Distribution.fTransform q
            (trLawFullyDefined e n (Distribution.fTransform g SL))))
        ≤ ENNReal.ofReal
            (statDist (trLawFullyDefined e n (Distribution.fTransform g RL))
              (trLawFullyDefined e n (Distribution.fTransform g SL))) :=
          ENNReal.ofReal_le_ofReal
            (Probability.statDist_fTransform_le _ _ q)
    _ ≤ advFullyDefined (Distribution.fTransform g RL)
          (Distribution.fTransform g SL) :=
        le_iSup_of_le e (le_iSup_of_le n le_rfl)

end PDS

namespace System

/-! ## The completion's answer, and the blocked system's

A blocked query is refused outright and, by CR18's deletion convention, leaves
the system untouched: the blocked system's kept history is the unblocked
system's kept history of the *surviving* queries (`keptPrefix_blockSet`).  Read
at a single query, that is the pair of equations below, and they are the whole
input the absorption receipt needs — the replay itself is the general one
(`exists_absorb_relay`). -/

section Block

open Classical

universe w₁ w₂

variable {X : Type w₁} {Y : Type w₂}

/-! ### The completion's answer, as a total function

`S⊥` is defined on every nonempty history, so its answer to a query after a
history carries no side condition.  Naming it (coinage: CR18 Def 3.3 gives
the object, not the name) removes the dependent domain proof from every
transcript equation below — which is what makes the transcript rewritable at
all. -/

/-- The answer `S⊥` gives to the query `x` after the history `l`. -/
def answer (S : DDS X Y) (l : List X) (x : X) : Option Y :=
  output S⊥ (l ++ [x]) (by simp [fullyDefined, dom])

/-- CR18 Definition 3.3, computed: the completion answers from the kept
prefix, and refuses exactly where the original system is undefined. -/
theorem answer_eq (S : DDS X Y) (l : List X) (x : X) :
    answer S l x =
      if h : keptPrefix S l ++ [x] ∈ dom S then
        some (output S (keptPrefix S l ++ [x]) h)
      else none :=
  output_fullyDefined_append S l x _

/-- A blocked query is refused: the completion answers `⊥`, and by
`keptPrefix_blockSet` the refusal is deleted, so the inner system is never
consulted. -/
theorem answer_blockSet_mem (Q : Set X) (S : DDS X Y) (l : List X) (x : X)
    (hx : x ∈ Q) : answer (blockSet Q S) l x = none := by
  rw [answer_eq]
  refine dif_neg fun hc => ?_
  exact ((mem_dom_blockSet Q S _).mp hc).2 x (by simp) hx

/-- A surviving query is answered exactly as the unblocked system answers it
on the sub-history of surviving queries. -/
theorem answer_blockSet_not_mem (Q : Set X) (S : DDS X Y) (l : List X)
    (x : X) (hx : x ∉ Q) :
    answer (blockSet Q S) l x = answer S (historyAt Qᶜ l) x := by
  rw [answer_eq, answer_eq]
  have havoid : ∀ q ∈ keptPrefix (blockSet Q S) l, q ∉ Q := by
    rcases keptPrefix_mem_or (blockSet Q S) l with hd | he
    · exact ((mem_dom_blockSet Q S _).mp hd).2
    · rw [he]
      exact fun q hq => absurd hq (by simp)
  have hkept := keptPrefix_blockSet Q S l
  have hiff : keptPrefix (blockSet Q S) l ++ [x] ∈ dom (blockSet Q S) ↔
      keptPrefix S (historyAt Qᶜ l) ++ [x] ∈ dom S := by
    rw [mem_dom_blockSet, hkept]
    refine and_iff_left fun q hq => ?_
    rcases List.mem_append.mp hq with hq' | hq'
    · rw [← hkept] at hq'
      exact havoid q hq'
    · rw [List.mem_singleton.mp hq']
      exact hx
  by_cases hd : keptPrefix (blockSet Q S) l ++ [x] ∈ dom (blockSet Q S)
  · rw [dif_pos hd, dif_pos (hiff.mp hd)]
    exact congrArg some ((output_blockSet Q S _ hd).trans
      (output_congr S (by rw [hkept]) hd.1 (hiff.mp hd)))
  · rw [dif_neg hd, dif_neg fun hc => hd (hiff.mpr hc)]

/-! ### Transcripts, unfolded and monotone

(General; the relay machinery below and the block/par instances all consume
these three.) -/

theorem transcriptInputs_concat (t : List (X × Option Y)) (p : X × Option Y) :
    (t ++ [p])↓ₓ = t↓ₓ ++ [p.1] := by
  simp [transcriptInputs]

theorem transcriptOutputs_concat (t : List (X × Option Y))
    (p : X × Option Y) : (t ++ [p])↓ᵧ = t↓ᵧ ++ [p.2] := by
  simp [transcriptOutputs]

/-- A round in which the environment stops leaves the transcript alone. -/
theorem DDE.Total.transcript_succ_of_stop (s : DDS X Y) (e : DDE.Total Y X)
    {n : ℕ} (h : e (transcript s e n)↓ᵧ = none) :
    transcript s e (n + 1) = transcript s e n := by
  simp only [DDE.Total.transcript, h]

/-- A round in which the environment queries appends the query together with
the completion's answer. -/
theorem DDE.Total.transcript_succ_of_query (s : DDS X Y) (e : DDE.Total Y X)
    {n : ℕ} {x : X} (h : e (transcript s e n)↓ᵧ = some x) :
    transcript s e (n + 1) =
      transcript s e n ++ [(x, answer s (transcript s e n)↓ₓ x)] := by
  simp only [DDE.Total.transcript, h]
  rfl

/-- The transcript at length `n` is a prefix of the transcript at length
`n + 1`: a round either appends one entry or stalls. -/
theorem DDE.Total.transcript_prefix_succ (s : DDS X Y) (e : DDE.Total Y X)
    (n : ℕ) : transcript s e n <+: transcript s e (n + 1) := by
  rcases hx : e (transcript s e n)↓ᵧ with _ | x
  · rw [DDE.Total.transcript_succ_of_stop s e hx]
  · rw [DDE.Total.transcript_succ_of_query s e hx]
    exact List.prefix_append _ _

/-- Transcripts are monotone in the interaction length. -/
theorem DDE.Total.transcript_prefix (s : DDS X Y) (e : DDE.Total Y X)
    {n m : ℕ} (h : n ≤ m) : transcript s e n <+: transcript s e m := by
  induction m, h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ m _ ih => exact ih.trans (DDE.Total.transcript_prefix_succ s e m)

end Block

/-! ## Relays absorb into the environment

The pattern shared by every construction whose outer round costs **at most one
inner query**: an outer query either is answered by the construction itself,
with no inner traffic, or is relayed — as one inner query, whose answer is
translated back.  Blocking, a parallel frame, the typed inclusion and a
relabelling are all of this shape, and each one's absorption receipt is this
module's `exists_absorb_relay` at its own three data:

* `rel : X' → Option X` — the inner query an outer query is relayed as, `none`
  where the construction answers alone.  The inner system's history is then
  `L.filterMap rel`, the relayed sub-history of the outer one.
* `self : List X' → X' → Option Y'` — the answer computed without the resource.
* `post : Option Y → Option Y'` — the translation of a relayed answer.

Soundness is not an accident of the proof: an unrelayed round carries no
information about the resource, and a relayed one is a single query, so a
refusal never follows inner traffic *within* a round — the criterion the B4
counterexample turns on.  Engines are the other case, and they need their own
machinery (`System.exists_absorb_connectFully`, B4-RESUME).

The replay is the whole construction.  It is a fold over the outer rounds whose
state is the outer transcript built so far together with the inner answers not
yet consumed; it stalls exactly when it needs an answer it has not been given,
and that stall is what the inner environment reports as its next query. -/

section Relay

open Classical

universe w₁ w₂ w₃ w₄

variable {X : Type w₁} {Y : Type w₂} {X' : Type w₃} {Y' : Type w₄}

/-- One round of the replay of an outer interaction with a relay: the outer
environment moves on the outer transcript built so far; an unrelayed query is
answered on the spot, a relayed query consumes the next inner answer, and if
there is none the replay stalls. -/
def relayReplayStep (rel : X' → Option X) (self : List X' → X' → Option Y')
    (post : Option Y → Option Y') (e : DDE.Total Y' X')
    (st : List (X' × Option Y') × List (Option Y)) :
    List (X' × Option Y') × List (Option Y) :=
  match e st.1↓ᵧ with
  | none => st
  | some x' =>
      match rel x' with
      | none => (st.1 ++ [(x', self st.1↓ₓ x')], st.2)
      | some _ =>
          match st.2 with
          | [] => st
          | y :: ys => (st.1 ++ [(x', post y)], ys)

theorem relayReplayStep_stop (rel : X' → Option X)
    (self : List X' → X' → Option Y') (post : Option Y → Option Y')
    (e : DDE.Total Y' X') {st : List (X' × Option Y') × List (Option Y)}
    (h : e st.1↓ᵧ = none) : relayReplayStep rel self post e st = st := by
  simp [relayReplayStep, h]

theorem relayReplayStep_self (rel : X' → Option X)
    (self : List X' → X' → Option Y') (post : Option Y → Option Y')
    (e : DDE.Total Y' X') {st : List (X' × Option Y') × List (Option Y)}
    {x' : X'} (h : e st.1↓ᵧ = some x') (hx : rel x' = none) :
    relayReplayStep rel self post e st =
      (st.1 ++ [(x', self st.1↓ₓ x')], st.2) := by
  simp [relayReplayStep, h, hx]

theorem relayReplayStep_stuck (rel : X' → Option X)
    (self : List X' → X' → Option Y') (post : Option Y → Option Y')
    (e : DDE.Total Y' X') {st : List (X' × Option Y') × List (Option Y)}
    {x' : X'} {x : X} (h : e st.1↓ᵧ = some x') (hx : rel x' = some x)
    (hst : st.2 = []) : relayReplayStep rel self post e st = st := by
  rcases st with ⟨o, ys⟩
  simp only at hst
  subst hst
  simp [relayReplayStep, h, hx]

theorem relayReplayStep_serve (rel : X' → Option X)
    (self : List X' → X' → Option Y') (post : Option Y → Option Y')
    (e : DDE.Total Y' X') (o : List (X' × Option Y')) (y : Option Y)
    (ys : List (Option Y)) {x' : X'} {x : X} (h : e o↓ᵧ = some x')
    (hx : rel x' = some x) :
    relayReplayStep rel self post e (o, y :: ys) = (o ++ [(x', post y)], ys) := by
  simp [relayReplayStep, h, hx]

/-- The replay of the first `k` outer rounds against a given list of inner
answers. -/
def relayReplay (rel : X' → Option X) (self : List X' → X' → Option Y')
    (post : Option Y → Option Y') (e : DDE.Total Y' X') (ys : List (Option Y)) :
    ℕ → List (X' × Option Y') × List (Option Y)
  | 0 => ([], ys)
  | k + 1 => relayReplayStep rel self post e (relayReplay rel self post e ys k)

@[simp]
theorem relayReplay_zero (rel : X' → Option X)
    (self : List X' → X' → Option Y') (post : Option Y → Option Y')
    (e : DDE.Total Y' X') (ys : List (Option Y)) :
    relayReplay rel self post e ys 0 = ([], ys) :=
  rfl

theorem relayReplay_succ (rel : X' → Option X)
    (self : List X' → X' → Option Y') (post : Option Y → Option Y')
    (e : DDE.Total Y' X') (ys : List (Option Y)) (k : ℕ) :
    relayReplay rel self post e ys (k + 1) =
      relayReplayStep rel self post e (relayReplay rel self post e ys k) :=
  rfl

/-- A stalled replay stays stalled: once the state is a fixed point of the
round, more rounds change nothing. -/
theorem relayReplay_of_fixed (rel : X' → Option X)
    (self : List X' → X' → Option Y') (post : Option Y → Option Y')
    (e : DDE.Total Y' X') (ys : List (Option Y)) {k : ℕ}
    (hfix : relayReplayStep rel self post e (relayReplay rel self post e ys k) =
      relayReplay rel self post e ys k) :
    ∀ i, k ≤ i → relayReplay rel self post e ys i =
      relayReplay rel self post e ys k := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => rfl
  | succ i _ ih => rw [relayReplay_succ, ih, hfix]

/-- The query the replay is waiting for: `some x` exactly when the outer
environment's next move is a relayed query and no inner answer is left.  It
does not consult the construction's own answers — those never stall. -/
def relayNeed (rel : X' → Option X) (e : DDE.Total Y' X')
    (st : List (X' × Option Y') × List (Option Y)) : Option X :=
  match e st.1↓ᵧ with
  | none => none
  | some x' =>
      match rel x' with
      | none => none
      | some x =>
          match st.2 with
          | [] => some x
          | _ :: _ => none

theorem relayNeed_stuck (rel : X' → Option X) (e : DDE.Total Y' X')
    (o : List (X' × Option Y')) {x' : X'} {x : X} (h : e o↓ᵧ = some x')
    (hx : rel x' = some x) :
    relayNeed rel e (o, ([] : List (Option Y))) = some x := by
  simp [relayNeed, h, hx]

/-- **The absorbed environment**: the inner environment that replays the outer
interaction for `n` rounds and asks exactly the query the replay is waiting
for.  It depends on the outer environment, the length and the relay's data —
never on the system, which is what makes the reduction a reduction. -/
def absorbRelay (rel : X' → Option X) (self : List X' → X' → Option Y')
    (post : Option Y → Option Y') (e : DDE.Total Y' X') (n : ℕ) :
    DDE.Total Y X :=
  fun ys => relayNeed rel e (relayReplay rel self post e ys n)

/-- **The replay invariant.**  After `k` outer rounds the replay has rebuilt
the outer transcript exactly and consumed exactly the answers of the first `j`
inner rounds — the `j` inner queries being the relayed outer queries, in order,
which is the inner system's own history.  The quantifier over the unconsumed
tail `zs` is what makes the invariant usable both at the truncated answer list
(what the inner environment sees when it is asked for its next query) and at
the full one (what the reconstruction map sees). -/
theorem relayReplay_invariant (rel : X' → Option X)
    (self : List X' → X' → Option Y') (post : Option Y → Option Y')
    (g : DDS X Y → DDS X' Y')
    (hself : ∀ (s : DDS X Y) (L : List X') (x' : X'), rel x' = none →
      answer (g s) L x' = self L x')
    (hrel : ∀ (s : DDS X Y) (L : List X') (x' : X') (x : X), rel x' = some x →
      answer (g s) L x' = post (answer s (L.filterMap rel) x))
    (e : DDE.Total Y' X') (n : ℕ) (s : DDS X Y) :
    ∀ k ≤ n, ∃ j ≤ k,
      (DDE.Total.transcript s (absorbRelay rel self post e n) j)↓ₓ =
        (DDE.Total.transcript (g s) e k)↓ₓ.filterMap rel ∧
      ∀ zs : List (Option Y),
        relayReplay rel self post e
            ((DDE.Total.transcript s (absorbRelay rel self post e n) j)↓ᵧ ++ zs)
            k =
          (DDE.Total.transcript (g s) e k, zs) := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨0, le_rfl, rfl, fun _ => rfl⟩
  | succ k ih =>
      intro hk
      obtain ⟨j, hjk, hinputs, hreplay⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨o, ho⟩ : ∃ o, DDE.Total.transcript (g s) e k = o := ⟨_, rfl⟩
      obtain ⟨T, hT⟩ :
          ∃ T, DDE.Total.transcript s (absorbRelay rel self post e n) j = T :=
        ⟨_, rfl⟩
      rw [ho] at hinputs hreplay
      rw [hT] at hinputs hreplay
      rcases hx : e o↓ᵧ with _ | x'
      · -- the outer environment stops: nothing moves on either side
        have houter : DDE.Total.transcript (g s) e (k + 1) = o := by
          rw [DDE.Total.transcript_succ_of_stop (g s) e (n := k)
            (by rw [ho]; exact hx), ho]
        exact ⟨j, hjk.trans (Nat.le_succ k), by rw [hT, houter]; exact hinputs,
          fun zs => by
            rw [hT, relayReplay_succ, hreplay zs,
              relayReplayStep_stop rel self post e (st := (o, zs)) hx, houter]⟩
      · rcases hrx : rel x' with _ | x
        · -- the construction answers by itself: no inner traffic
          have houter : DDE.Total.transcript (g s) e (k + 1) =
              o ++ [(x', self o↓ₓ x')] := by
            rw [DDE.Total.transcript_succ_of_query (g s) e (n := k) (x := x')
              (by rw [ho]; exact hx), ho, hself s o↓ₓ x' hrx]
          refine ⟨j, hjk.trans (Nat.le_succ k), ?_, fun zs => ?_⟩
          · rw [hT, houter, transcriptInputs_concat, List.filterMap_append]
            simp [hrx, hinputs]
          · rw [hT, relayReplay_succ, hreplay zs,
              relayReplayStep_self rel self post e (st := (o, zs)) hx hrx,
              houter]
        · -- a relayed query: one inner round answers it
          have hstuck : relayReplay rel self post e T↓ᵧ n = (o, []) := by
            have hk0 : relayReplay rel self post e T↓ᵧ k = (o, []) := by
              have := hreplay []
              rwa [List.append_nil] at this
            have hfix : relayReplayStep rel self post e
                (relayReplay rel self post e T↓ᵧ k) =
                  relayReplay rel self post e T↓ᵧ k := by
              rw [hk0]
              exact relayReplayStep_stuck rel self post e (st := (o, []))
                hx hrx rfl
            rw [relayReplay_of_fixed rel self post e T↓ᵧ hfix n
              (le_trans (Nat.le_succ k) hk), hk0]
          have hneed : absorbRelay rel self post e n T↓ᵧ = some x := by
            show relayNeed rel e (relayReplay rel self post e T↓ᵧ n) = some x
            rw [hstuck]
            exact relayNeed_stuck rel e o hx hrx
          have hinner : DDE.Total.transcript s (absorbRelay rel self post e n)
              (j + 1) = T ++ [(x, answer s T↓ₓ x)] := by
            rw [DDE.Total.transcript_succ_of_query s
              (absorbRelay rel self post e n) (n := j) (x := x)
              (by rw [hT]; exact hneed), hT]
          have hans : answer (g s) o↓ₓ x' = post (answer s T↓ₓ x) := by
            rw [hrel s o↓ₓ x' x hrx, hinputs]
          have houter : DDE.Total.transcript (g s) e (k + 1) =
              o ++ [(x', post (answer s T↓ₓ x))] := by
            rw [DDE.Total.transcript_succ_of_query (g s) e (n := k) (x := x')
              (by rw [ho]; exact hx), ho, hans]
          refine ⟨j + 1, Nat.succ_le_succ hjk, ?_, fun zs => ?_⟩
          · rw [hinner, houter, transcriptInputs_concat,
              transcriptInputs_concat, List.filterMap_append]
            simp [hrx, hinputs]
          · rw [hinner, transcriptOutputs_concat, List.append_assoc,
              List.singleton_append, relayReplay_succ, hreplay _,
              relayReplayStep_serve rel self post e o _ zs hx hrx, houter]

/-- **Relays absorb**: every interaction with a relaying construction is a
fixed post-processing of an interaction with the bare system, uniformly in the
system.  The hypothesis is the whole content — the construction's answer to an
outer query is either computed without the resource, or is the resource's own
answer to the relayed query at the relayed sub-history. -/
theorem exists_absorb_relay (rel : X' → Option X)
    (self : List X' → X' → Option Y') (post : Option Y → Option Y')
    (g : DDS X Y → DDS X' Y')
    (hself : ∀ (s : DDS X Y) (L : List X') (x' : X'), rel x' = none →
      answer (g s) L x' = self L x')
    (hrel : ∀ (s : DDS X Y) (L : List X') (x' : X') (x : X), rel x' = some x →
      answer (g s) L x' = post (answer s (L.filterMap rel) x))
    (e : DDE.Total Y' X') (n : ℕ) :
    ∃ (e' : DDE.Total Y X) (m : ℕ)
      (p : List (X × Option Y) → List (X' × Option Y')),
      ∀ s : DDS X Y,
        DDE.Total.transcript (g s) e n = p (DDE.Total.transcript s e' m) := by
  refine ⟨absorbRelay rel self post e n, n,
    fun T => (relayReplay rel self post e T↓ᵧ n).1, fun s => ?_⟩
  obtain ⟨j, hjn, -, hreplay⟩ :=
    relayReplay_invariant rel self post g hself hrel e n s n le_rfl
  obtain ⟨zs, hzs⟩ :
      ∃ zs, (DDE.Total.transcript s (absorbRelay rel self post e n) j)↓ᵧ ++ zs =
        (DDE.Total.transcript s (absorbRelay rel self post e n) n)↓ᵧ := by
    obtain ⟨w, hw⟩ :=
      DDE.Total.transcript_prefix s (absorbRelay rel self post e n) hjn
    exact ⟨w↓ᵧ, by simp only [transcriptOutputs, ← List.map_append, hw]⟩
  show DDE.Total.transcript (g s) e n =
    (relayReplay rel self post e
      (DDE.Total.transcript s (absorbRelay rel self post e n) n)↓ᵧ n).1
  rw [← hzs, hreplay zs]

/-- The relayed sub-history of a splitting is the component's sub-history: the
`filterMap` the relay machinery projects with is `historyAt` at the relay
`fun q => if q ∈ c then some q else none`. -/
theorem filterMap_relay_eq_historyAt {Z : Type w₁} (c : Set Z) (l : List Z) :
    l.filterMap (fun q => if q ∈ c then some q else none) = historyAt c l := by
  induction l with
  | nil => rfl
  | cons q t ih =>
      by_cases hq : q ∈ c <;> simp [historyAt, hq, ih]

/-! ### Relabelling is the pointwise relay

A relabelling has no state and no queries of its own, so every outer query is
relayed — as its translation — and every answer comes back translated.  The
kept prefixes correspond pointwise (`keptPrefix_relabel`), which is why the
refusal correspondence needs no window. -/

/-- The completion of a relabelled system answers the translated query at the
translated history, and translates the answer back. -/
theorem answer_relabel (f : X' → X) (g : Y → Y') (S : DDS X Y) (l : List X')
    (x : X') :
    answer (relabel f g S) l x = (answer S (l.map f) (f x)).map g := by
  have hmap : (keptPrefix (relabel f g S) l ++ [x]).map f =
      keptPrefix S (l.map f) ++ [f x] := by
    rw [List.map_append, keptPrefix_relabel]
    simp
  have hiff : keptPrefix (relabel f g S) l ++ [x] ∈ dom (relabel f g S) ↔
      keptPrefix S (l.map f) ++ [f x] ∈ dom S := by
    rw [mem_dom_relabel, hmap]
  rw [answer_eq, answer_eq]
  by_cases hd : keptPrefix (relabel f g S) l ++ [x] ∈ dom (relabel f g S)
  · rw [dif_pos hd, dif_pos (hiff.mp hd), Option.map_some,
      output_relabel f g S _ hd]
    exact congrArg (some ∘ g)
      (output_congr S hmap hd (hiff.mp hd))
  · rw [dif_neg hd, dif_neg fun hc => hd (hiff.mpr hc), Option.map_none]

/-- **Relabellings absorb**: every interaction with a relabelled system is a
fixed post-processing of an interaction with the original.  The relay is the
translation itself — no query is answered without the resource, and no window
is needed. -/
theorem exists_absorb_relabel (f : X' → X) (g : Y → Y') (e : DDE.Total Y' X')
    (n : ℕ) :
    ∃ (e' : DDE.Total Y X) (m : ℕ)
      (p : List (X × Option Y) → List (X' × Option Y')),
      ∀ s : DDS X Y,
        DDE.Total.transcript (relabel f g s) e n =
          p (DDE.Total.transcript s e' m) :=
  exists_absorb_relay (fun x' => some (f x')) (fun _ _ => none) (Option.map g)
    (relabel f g)
    (fun _ _ _ hx' => absurd hx' (by simp))
    (fun s L x' x hx' => by
      injection hx' with hxx
      subst hxx
      rw [show L.filterMap (fun x' => some (f x')) = L.map f by
        induction L with
        | nil => rfl
        | cons a t ih => simp [ih]]
      rw [answer_relabel])
    e n

/-- The same, for a relay that *silences* `c`: the surviving sub-history. -/
theorem filterMap_relay_eq_historyAt_compl {Z : Type w₁} (c : Set Z)
    (l : List Z) :
    l.filterMap (fun q => if q ∈ c then none else some q) = historyAt cᶜ l := by
  induction l with
  | nil => rfl
  | cons q t ih =>
      by_cases hq : q ∈ c <;> simp [historyAt, hq, ih]

end Relay

section BlockAbsorb

open Classical

universe w₁ w₂

variable {X : Type w₁} {Y : Type w₂}

/-- **Blocks absorb**: every interaction with a blocked system is a fixed
post-processing of an interaction with the bare system.

The relay is "refuse the blocked queries, relay the rest unchanged".  A blocked
query is answered `⊥` *without touching the inner system* — that is
`answer_blockSet_mem`, on the crux `keptPrefix_blockSet` — and a surviving one
is answered by the bare system at the surviving sub-history
(`answer_blockSet_not_mem`), which is exactly the relayed sub-history the
replay projects with (`filterMap_relay_eq_historyAt`). -/
theorem exists_absorb_blockSet (Q : Set X) (e : DDE.Total Y X) (n : ℕ) :
    ∃ (e' : DDE.Total Y X) (m : ℕ)
      (p : List (X × Option Y) → List (X × Option Y)),
      ∀ s : DDS X Y,
        DDE.Total.transcript (blockSet Q s) e n =
          p (DDE.Total.transcript s e' m) :=
  exists_absorb_relay (fun q => if q ∈ Q then none else some q)
    (fun _ _ => none) id (blockSet Q)
    (fun s L x' hx' => by
      by_cases h : x' ∈ Q
      · exact answer_blockSet_mem Q s L x' h
      · simp only [if_neg h] at hx'
        exact absurd hx' (by simp))
    (fun s L x' x hx' => by
      by_cases h : x' ∈ Q
      · simp only [if_pos h] at hx'
        exact absurd hx' (by simp)
      · simp only [if_neg h] at hx'
        injection hx' with hxx
        subst hxx
        rw [answer_blockSet_not_mem Q s L x' h,
          filterMap_relay_eq_historyAt_compl]
        rfl)
    e n

/-- **The tagged block absorbs** (A7): the interface-set block is the query-set
block at the tag cylinder (`block_eq_blockSet`, definitional), so its receipt is
`exists_absorb_blockSet` there.  The `s⊥`-receipt of the same row is
`fullyDefined_block`. -/
theorem exists_absorb_block {P : Type w₁} {A : Type w₁} {B : Type w₂}
    (Z : Set P) (e : DDE.Total B (P × A)) (n : ℕ) :
    ∃ (e' : DDE.Total B (P × A)) (m : ℕ)
      (p : List ((P × A) × Option B) → List ((P × A) × Option B)),
      ∀ s : Resource P A B,
        DDE.Total.transcript (block Z s) e n =
          p (DDE.Total.transcript s e' m) :=
  exists_absorb_blockSet {p : P × A | p.1 ∈ Z} e n

end BlockAbsorb

/-! ## The parallel partner absorbs into the environment

`par c s t` offers the inner system `s` on the queries in `c` and the fixed
partner `t` on the rest, each component seeing only its own sub-history
(`historyAt`).  So an environment interacting with the composite can be run
by an environment interacting with `s` alone: replay the outer interaction,
answer every `cᶜ`-owned query on the spot with `System.answer t` at the
partner's projected sub-history, and consume one inner answer per `c`-owned
query.

This is `exists_absorb_blockSet` with the silent partner replaced by an
arbitrary one — literally the same relay, with the partner's answer *computed*
instead of being known to be `⊥`.

Soundness is not an accident of the proof: a round of `par` is one query to
one component, so a refusal never follows inner traffic within a round, which
is exactly the criterion isolated at the end of this module. -/

section Par

open Classical

universe w₃ w₄

variable {X : Type w₃} {Y : Type w₄}

/-! ### The completion answers component by component

`fullyDefined_par` says `(par c R S)⊥ = par c R⊥ S⊥`; read at a single query
that is the statement that the composite's answer *is* the owning component's
answer, at the component's own projected kept history. -/

/-- A query owned by the left component is answered by that component, on its
own sub-history. -/
theorem answer_par_mem (c : Set X) (R S : DDS X Y) (l : List X) (x : X)
    (hx : x ∈ c) : answer (par c R S) l x = answer R (historyAt c l) x := by
  rw [answer_eq, answer_eq]
  obtain ⟨ihR, ihS⟩ := keptPrefix_par_proj c R S l
  have hinv := (keptPrefix_mem_or (par c R S) l).symm
  have hiff : keptPrefix (par c R S) l ++ [x] ∈ dom (par c R S) ↔
      keptPrefix R (historyAt c l) ++ [x] ∈ dom R := by
    rw [mem_dom_par_concat_mem c R S hx hinv, ihR, ihS]
    exact and_iff_left (keptPrefix_mem_or S (historyAt cᶜ l)).symm
  by_cases hd : keptPrefix (par c R S) l ++ [x] ∈ dom (par c R S)
  · have hR' : historyAt c (keptPrefix (par c R S) l) ++ [x] ∈ dom R := by
      rw [ihR]; exact hiff.mp hd
    rw [dif_pos hd, dif_pos (hiff.mp hd)]
    exact congrArg some ((output_par_mem c R S _ x hx hd hR').trans
      (output_congr R (by rw [ihR]) hR' (hiff.mp hd)))
  · rw [dif_neg hd, dif_neg fun hc => hd (hiff.mpr hc)]

/-- A query owned by the right component is answered by that component, on its
own sub-history. -/
theorem answer_par_not_mem (c : Set X) (R S : DDS X Y) (l : List X) (x : X)
    (hx : x ∉ c) : answer (par c R S) l x = answer S (historyAt cᶜ l) x := by
  rw [answer_eq, answer_eq]
  obtain ⟨ihR, ihS⟩ := keptPrefix_par_proj c R S l
  have hinv := (keptPrefix_mem_or (par c R S) l).symm
  have hiff : keptPrefix (par c R S) l ++ [x] ∈ dom (par c R S) ↔
      keptPrefix S (historyAt cᶜ l) ++ [x] ∈ dom S := by
    rw [mem_dom_par_concat_not_mem c R S hx hinv, ihR, ihS]
    exact and_iff_right (keptPrefix_mem_or R (historyAt c l)).symm
  by_cases hd : keptPrefix (par c R S) l ++ [x] ∈ dom (par c R S)
  · have hS' : historyAt cᶜ (keptPrefix (par c R S) l) ++ [x] ∈ dom S := by
      rw [ihS]; exact hiff.mp hd
    rw [dif_pos hd, dif_pos (hiff.mp hd)]
    exact congrArg some ((output_par_not_mem c R S _ x hx hd hS').trans
      (output_congr S (by rw [ihS]) hS' (hiff.mp hd)))
  · rw [dif_neg hd, dif_neg fun hc => hd (hiff.mpr hc)]

/-- **The parallel partner absorbs**: every interaction with `par c s t` is a
fixed post-processing of an interaction with `s` alone, uniformly in `s`.

This is `exists_absorb_blockSet` with the silent partner replaced by an
arbitrary one, and both are the same relay: the delta is that the partner's
answer is *computed* (`answer t` at the partner's projected sub-history)
instead of being known to be `⊥`. -/
theorem exists_absorb_par (c : Set X) (t : DDS X Y) (e : DDE.Total Y X)
    (n : ℕ) :
    ∃ (e' : DDE.Total Y X) (m : ℕ)
      (p : List (X × Option Y) → List (X × Option Y)),
      ∀ s : DDS X Y,
        DDE.Total.transcript (par c s t) e n =
          p (DDE.Total.transcript s e' m) :=
  exists_absorb_relay (fun q => if q ∈ c then some q else none)
    (fun L x => answer t (historyAt cᶜ L) x) id (fun s => par c s t)
    (fun s L x' hx' => by
      by_cases h : x' ∈ c
      · simp only [if_pos h] at hx'
        exact absurd hx' (by simp)
      · exact answer_par_not_mem c s t L x' h)
    (fun s L x' x hx' => by
      by_cases h : x' ∈ c
      · simp only [if_pos h] at hx'
        injection hx' with hxx
        subst hxx
        rw [answer_par_mem c s t L x' h, filterMap_relay_eq_historyAt]
        rfl
      · simp only [if_neg h] at hx'
        exact absurd hx' (by simp))
    e n
end Par

/-! ## The typed inclusion absorbs, in both directions

`ofTyped S` is the typed system `S` read on the universal alphabet: a query
that does not decode at `X` is out of domain, and one that does is answered by
`S`, its answer re-encoded at `Y`.  Both halves of the isometry are here.

*Outwards* (`exists_absorb_ofTyped`): an environment on the included system is
run by a typed environment.  The included system **refuses an undecodable query
before any inner traffic** — decoding is a domain condition on the history, not
a step of the interaction — so the relay of the previous section applies with
`decodeOption` as the relay itself.  This is the row the LEDGER predicted
provable ("refusal-first"), and that is exactly why.

*Inwards* (`exists_absorb_ofTyped_typed`): a typed environment is run by an
outer environment, which encodes its queries and decodes its answers.  Nothing
is refused on the way in, so this direction needs no replay at all — the outer
transcript *is* the typed transcript, entry by entry, under the inclusion. -/

section TypedInclusion

open Classical

universe u₀

variable {X : Type u₀} {Y : Type u₀}

/-- **Decoding as a total function**: `some x` exactly on `X`'s copy of the
universal alphabet, `none` off it.  The `Option`-valued form of `decode`, as
`answer` is the total form of `output` — a single named term, so that every use
site elaborates the same decidability instance. -/
def decodeOption (q : Uni.{u₀}) : Option X :=
  (decode X q).toOption

@[simp]
theorem decodeOption_encode (x : X) :
    decodeOption (encode X x) = some x := by
  rw [decodeOption, decode_encode]
  simp [Part.toOption]

/-- Decoding an included history recovers it, entrywise. -/
theorem filterMap_decodeOption_map_encode (l : List X) :
    List.filterMap decodeOption (l.map (encode X)) = l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem decodeOption_eq_some_iff {q : Uni.{u₀}} {x : X} :
    decodeOption q = some x ↔ q = encode X x := by
  constructor
  · intro h
    by_cases hd : (decode X q).Dom
    · rw [decodeOption, Part.toOption, dif_pos hd] at h
      rw [← encode_decode q hd, Option.some_inj.mp h]
    · rw [decodeOption, Part.toOption, dif_neg hd] at h
      exact absurd h (by simp)
  · rintro rfl
    exact decodeOption_encode x

theorem tag_of_decodeOption_eq_some {q : Uni.{u₀}} {x : X}
    (h : decodeOption q = some x) : q.1 = X := by
  rw [decodeOption_eq_some_iff.mp h]
  rfl

/-- An undecodable query is refused, and the refusal is a condition on the
*history*: it precedes every step of the interaction. -/
theorem not_mem_dom_ofTyped_of_decodeOption_none {S : DDS X Y}
    {l : List Uni.{u₀}} {q : Uni.{u₀}} (hq : decodeOption (X := X) q = none) :
    l ++ [q] ∉ dom (ofTyped S) := by
  intro hd
  have hraw : (ofTypedRaw S (l ++ [q])).Dom :=
    hd.2 _ (List.prefix_refl _) hd.1
  obtain ⟨hdec, -⟩ := hraw
  have htag : q.1 = X := decodeList_dom_mem hdec q (by simp)
  have : decodeOption (X := X) q = some (htag ▸ q.2) := by
    rw [decodeOption_eq_some_iff]
    obtain ⟨Q, v⟩ := q
    cases htag
    rfl
  rw [hq] at this
  exact absurd this (by simp)

/-- **The inclusion crux**: the included system's kept prefix is the typed
system's kept prefix of the decodable sub-history, included.  Undecodable
queries never enter it — they are refused outright, as blocked queries are. -/
theorem keptPrefix_ofTyped (S : DDS X Y) (l : List Uni.{u₀}) :
    keptPrefix (ofTyped S) l =
      (keptPrefix S (l.filterMap decodeOption)).map (encode X) := by
  induction l using List.reverseRecOn with
  | nil => simp [keptPrefix]
  | append_singleton l q ih =>
      rw [keptPrefix_append_singleton, List.filterMap_append]
      rcases hq : decodeOption (X := X) q with _ | x
      · rw [if_neg (by rw [ih]; exact not_mem_dom_ofTyped_of_decodeOption_none hq),
          ih]
        simp [hq]
      · have hqe : q = encode X x := decodeOption_eq_some_iff.mp hq
        have hcat : keptPrefix (ofTyped S) l ++ [q] =
            (keptPrefix S (l.filterMap decodeOption) ++ [x]).map (encode X) := by
          rw [ih, hqe, List.map_append]
          rfl
        have hiff : keptPrefix (ofTyped S) l ++ [q] ∈ dom (ofTyped S) ↔
            keptPrefix S (l.filterMap decodeOption) ++ [x] ∈ dom S := by
          rw [hcat]
          exact mem_dom_ofTyped_encode (by simp)
        rw [show ([q].filterMap decodeOption) = [x] by simp [hq],
          keptPrefix_append_singleton]
        by_cases hd : keptPrefix (ofTyped S) l ++ [q] ∈ dom (ofTyped S)
        · rw [if_pos hd, if_pos (hiff.mp hd), ← hcat]
        · rw [if_neg hd, if_neg fun hc => hd (hiff.mpr hc), ih]

/-- An undecodable query is answered `⊥`, with no inner traffic. -/
theorem answer_ofTyped_none (S : DDS X Y) (l : List Uni.{u₀}) {q : Uni.{u₀}}
    (hq : decodeOption (X := X) q = none) : answer (ofTyped S) l q = none := by
  rw [answer_eq]
  exact dif_neg (not_mem_dom_ofTyped_of_decodeOption_none hq)

/-- A decodable query is answered by the typed system at the decoded
sub-history, its answer re-encoded. -/
theorem answer_ofTyped_some (S : DDS X Y) (l : List Uni.{u₀}) {q : Uni.{u₀}}
    {x : X} (hq : decodeOption q = some x) :
    answer (ofTyped S) l q =
      (answer S (l.filterMap decodeOption) x).map (encode Y) := by
  have hcat : keptPrefix (ofTyped S) l ++ [q] =
      (keptPrefix S (l.filterMap decodeOption) ++ [x]).map (encode X) := by
    rw [keptPrefix_ofTyped, decodeOption_eq_some_iff.mp hq, List.map_append]
    rfl
  have hiff : keptPrefix (ofTyped S) l ++ [q] ∈ dom (ofTyped S) ↔
      keptPrefix S (l.filterMap decodeOption) ++ [x] ∈ dom S := by
    rw [hcat]
    exact mem_dom_ofTyped_encode (by simp)
  rw [answer_eq, answer_eq]
  by_cases hd : keptPrefix (ofTyped S) l ++ [q] ∈ dom (ofTyped S)
  · rw [dif_pos hd, dif_pos (hiff.mp hd), Option.map_some]
    refine congrArg some ?_
    rw [output_congr (ofTyped S) hcat hd (hcat ▸ hd),
      output_ofTyped_encode (hiff.mp hd) (hcat ▸ hd)]
  · rw [dif_neg hd, dif_neg fun hc => hd (hiff.mpr hc), Option.map_none]

/-- **The typed inclusion absorbs outwards**: every interaction with the
included system is a fixed post-processing of an interaction with the typed
system.  The relay is `decodeOption` — an undecodable query is refused before
any inner traffic, a decodable one is relayed and its answer re-encoded. -/
theorem exists_absorb_ofTyped (e : DDE.Total Uni.{u₀} Uni.{u₀}) (n : ℕ) :
    ∃ (e' : DDE.Total Y X) (m : ℕ)
      (p : List (X × Option Y) → List (Uni.{u₀} × Option Uni.{u₀})),
      ∀ s : DDS X Y,
        DDE.Total.transcript (ofTyped s) e n =
          p (DDE.Total.transcript s e' m) :=
  exists_absorb_relay decodeOption (fun _ _ => none) (Option.map (encode Y))
    ofTyped
    (fun s L _ hq => answer_ofTyped_none s L hq)
    (fun s L _ _ hq => answer_ofTyped_some s L hq)
    e n

/-! ### Inwards: the typed environment, encoded

No replay: the outer environment encodes each query the typed one makes and
decodes the answers it gets, and the outer transcript is the typed transcript
entry by entry under the inclusion. -/

/-- One transcript entry, included. -/
def encodeEntry (p : X × Option Y) : Uni.{u₀} × Option Uni.{u₀} :=
  (encode X p.1, p.2.map (encode Y))

/-- **The encoding environment**: it decodes the answers it has seen, asks what
the typed environment would ask, and encodes that query. -/
def encodeEnv (e' : DDE.Total Y X) : DDE.Total Uni.{u₀} Uni.{u₀} :=
  fun os => (e' (os.map fun o => o.bind decodeOption)).map (encode X)

theorem decodeOption_bind_map_encode (o : Option Y) :
    (o.map (encode Y)).bind decodeOption = o := by
  cases o with
  | none => rfl
  | some y => simp

/-- The included interaction is the typed interaction, entry by entry. -/
theorem transcript_ofTyped_encodeEnv (s : DDS X Y) (e' : DDE.Total Y X)
    (k : ℕ) :
    DDE.Total.transcript (ofTyped s) (encodeEnv e') k =
      (DDE.Total.transcript s e' k).map encodeEntry := by
  induction k with
  | zero => rfl
  | succ k ih =>
      obtain ⟨t, ht⟩ : ∃ t, DDE.Total.transcript s e' k = t := ⟨_, rfl⟩
      rw [ht] at ih
      have houts : (DDE.Total.transcript (ofTyped s) (encodeEnv e') k)↓ᵧ.map
          (fun o => o.bind decodeOption) = t↓ᵧ := by
        rw [ih]
        simp only [transcriptOutputs, List.map_map, Function.comp_def,
          encodeEntry, decodeOption_bind_map_encode]
      have hmove : encodeEnv e'
          (DDE.Total.transcript (ofTyped s) (encodeEnv e') k)↓ᵧ =
            (e' t↓ᵧ).map (encode X) := by
        rw [encodeEnv, houts]
      have hinputs : List.filterMap decodeOption
          (List.map (encodeEntry (X := X) (Y := Y)) t)↓ₓ = t↓ₓ := by
        rw [show (List.map (encodeEntry (X := X) (Y := Y)) t)↓ₓ =
            t↓ₓ.map (encode X) by
          simp [transcriptInputs, encodeEntry, List.map_map, Function.comp_def],
          filterMap_decodeOption_map_encode]
      rcases hx : e' t↓ᵧ with _ | x
      · rw [DDE.Total.transcript_succ_of_stop _ _ (by rw [hmove, hx]; rfl),
          DDE.Total.transcript_succ_of_stop _ _ (by rw [ht]; exact hx), ht, ih]
      · rw [DDE.Total.transcript_succ_of_query _ _ (x := encode X x)
            (by rw [hmove, hx]; rfl),
          DDE.Total.transcript_succ_of_query _ _ (x := x)
            (by rw [ht]; exact hx), ht, ih,
          answer_ofTyped_some s _ (decodeOption_encode x), hinputs]
        simp [encodeEntry]

/-- **The typed inclusion absorbs inwards**: every interaction with the typed
system is a fixed post-processing of an interaction with the included one. -/
theorem exists_absorb_ofTyped_typed (e' : DDE.Total Y X) (m : ℕ) :
    ∃ (e : DDE.Total Uni.{u₀} Uni.{u₀}) (n : ℕ)
      (q : List (Uni.{u₀} × Option Uni.{u₀}) → List (X × Option Y)),
      ∀ s : DDS X Y,
        DDE.Total.transcript s e' m =
          q (DDE.Total.transcript (ofTyped s) e n) := by
  refine ⟨encodeEnv e', m,
    fun T => T.filterMap fun p =>
      (decodeOption p.1).map fun x => (x, p.2.bind decodeOption), fun s => ?_⟩
  rw [transcript_ofTyped_encodeEnv]
  show _ = List.filterMap _ (List.map encodeEntry _)
  rw [List.filterMap_map,
    show ((fun p : Uni.{u₀} × Option Uni.{u₀} =>
        (decodeOption p.1).map fun x => (x, p.2.bind decodeOption)) ∘
      (encodeEntry : X × Option Y → Uni.{u₀} × Option Uni.{u₀})) =
        fun p => some p by
      funext p
      simp [encodeEntry, decodeOption_bind_map_encode]]
  exact List.filterMap_some.symm

end TypedInclusion

end System

/-! ## Blocking is nonexpanding

The Φ-level generator `block Q` is the pushforward of `System.blockSet Q`,
so the reduction applies verbatim. -/

/-- **MauRen16 §3.4's `⊣` never helps a distinguisher.**  Whatever an
environment learns from a blocked system it learns from the bare system by
running the block itself: blocked queries are refused with no inner traffic,
surviving queries are relayed one for one. -/
theorem block_mem_nonexpandingConverters (Q : Set Uni.{u}) :
    block Q ∈ nonexpandingConverters.{u} := fun RL SL =>
  PDS.advFullyDefined_fTransform_le (System.blockSet Q) RL SL
    fun e n => System.exists_absorb_blockSet Q e n

/-! ## The typed inclusion is an isometry

Both directions of A7's inclusion row, assembled: outwards by the relay
(`System.exists_absorb_ofTyped`), inwards by the encoding environment
(`System.exists_absorb_ofTyped_typed`).  Equality, not merely `≤`: including a
typed system into Φ neither hides nor creates distinguishing power, so the
`ℕ ⊆ ℝ` discipline of `Phi.lean` is metrically honest — a typed statement and
its included form say the same thing. -/

/-- **The typed inclusion is an isometry for `Adv⊥`** (A7): the advantage
against included systems is the advantage against the typed ones.  `≤` is the
outward absorption (an undecodable query is refused before any traffic, a
decodable one is relayed), `≥` is the inward one (the outer environment encodes
what the typed environment asks and decodes what it gets). -/
theorem PDS.advFullyDefined_ofTyped {X : Type u} {Y : Type u} (RL SL : PDS X Y) :
    PDS.advFullyDefined (RandomSystems.ofTyped RL) (RandomSystems.ofTyped SL) =
      PDS.advFullyDefined RL SL :=
  le_antisymm
    (PDS.advFullyDefined_fTransform_le System.ofTyped RL SL
      fun e n => System.exists_absorb_ofTyped e n)
    (PDS.advFullyDefined_le_fTransform System.ofTyped RL SL
      fun e' m => System.exists_absorb_ofTyped_typed e' m)

/-! ## Relabelling is nonexpanding

Stated twice, because the two statements say different things.  At arbitrary
alphabets a relabelling is not an endomorphism of anything — it is a map
`PDS X Y → PDS X' Y'` — and the honest statement is the bound; at the universal
alphabet the alphabets coincide and the bound *is* a membership in
`nonexpandingConverters`. -/

/-- **A relabelling never helps a distinguisher** (A7), at arbitrary alphabets:
what an environment learns from the relabelled system it learns from the
original by translating its own queries and the answers it gets. -/
theorem PDS.advFullyDefined_relabelLaw_le {X : Type*} {Y : Type*} {X' : Type*}
    {Y' : Type*} (f : X' → X) (g : Y → Y') (RL SL : PDS X Y) :
    PDS.advFullyDefined (PDS.relabelLaw f g RL) (PDS.relabelLaw f g SL) ≤
      PDS.advFullyDefined RL SL :=
  PDS.advFullyDefined_fTransform_le (System.relabel f g) RL SL
    fun e n => System.exists_absorb_relabel f g e n

/-- **A relabelling of the universal alphabet is a nonexpanding converter**:
at `Uni` the relabelling is an endomorphism of Φ, so the bound above is a
membership.  (LiuZhang §3.3.3's second trivial converter, joining `block`.) -/
theorem relabelLaw_mem_nonexpandingConverters (f g : Uni.{u} → Uni.{u}) :
    (PDS.relabelLaw f g : Function.End Phi.{u}) ∈ nonexpandingConverters.{u} :=
  fun RL SL => PDS.advFullyDefined_relabelLaw_le f g RL SL

/-- Φ read as what it is: a law over deterministic systems.  `Phi` is a
`def`, so the `Finsupp` module structure does not reach it by instance
search; this is the one-line re-typing that lets a mixture be written down.
(Coinage.) -/
def ofPhi (L : Phi.{u}) : PDS Uni.{u} Uni.{u} := L

/-- **Mixtures of nonexpanding converters are nonexpanding**, at
subprobability weights.

This is the step that reduces a *probabilistic* converter to its
deterministic support: `connectPhi EL` is the `EL`-weighted mixture of the
`attach E` over `EL`'s support, so the moment a deterministic family is known
nonexpanding, every mixture of it is too — the mixture argument does not care
what the family does.  The endomorphism is taken as given together with its
decomposition (`hπ`) rather than built here, which is the shape a caller
actually has.

Non-negativity is the honest hypothesis, and it is where the signed carrier
bites: the estimate is convexity of `δ` (`statDist_sum_le`), which a negative
weight destroys.  The budget `∑ w ≤ 1` is what turns the weighted average
into a bound by the same constant.

The engine family is not an instance of this today — see the scope note at
the end of this file: `attach E` is refuted for the current composite, so the
missing input is the deterministic case, not the mixture argument. -/
theorem mem_nonexpandingConverters_of_sum {ι : Type*} (t : Finset ι)
    (w : ι → ℝ) (σ : ι → Function.End Phi.{u}) (π : Function.End Phi.{u})
    (hw : ∀ i ∈ t, 0 ≤ w i) (hsum : ∑ i ∈ t, w i ≤ 1)
    (hσ : ∀ i ∈ t, σ i ∈ nonexpandingConverters.{u})
    (hπ : ∀ L : Phi.{u}, π L = ∑ i ∈ t, w i • ofPhi (σ i L)) :
    π ∈ nonexpandingConverters.{u} := fun RL SL => by
  rw [show π RL = ∑ i ∈ t, w i • ofPhi (σ i RL) from hπ RL,
    show π SL = ∑ i ∈ t, w i • ofPhi (σ i SL) from hπ SL]
  calc
    PDS.advFullyDefined (∑ i ∈ t, w i • ofPhi (σ i RL))
        (∑ i ∈ t, w i • ofPhi (σ i SL))
        ≤ ∑ i ∈ t, ENNReal.ofReal (w i) *
            PDS.advFullyDefined (ofPhi (σ i RL)) (ofPhi (σ i SL)) :=
          PDS.advFullyDefined_sum_le t w _ _ hw
    _ ≤ ∑ i ∈ t, ENNReal.ofReal (w i) * PDS.advFullyDefined RL SL :=
          Finset.sum_le_sum fun i hi => mul_le_mul' le_rfl (hσ i hi RL SL)
    _ = (∑ i ∈ t, ENNReal.ofReal (w i)) * PDS.advFullyDefined RL SL :=
          (Finset.sum_mul ..).symm
    _ ≤ 1 * PDS.advFullyDefined RL SL := by
          refine mul_le_mul' ?_ le_rfl
          rw [← ENNReal.ofReal_sum_of_nonneg hw]
          exact (ENNReal.ofReal_le_ofReal hsum).trans_eq ENNReal.ofReal_one
    _ = PDS.advFullyDefined RL SL := one_mul _

/-! ## Parallel frames are nonexpanding

MauRen11 Definition 2's eq. (4) reads, for the parallel operation, "`d(R, S)`
does not increase if one puts a resource `T` in parallel to `R` and `S`".  On
the fully defined advantage that is exactly the two theorems below, and both
are the same argument: the frame is a *fixed* partner, so the environment can
run it itself.

The partner is a law, not a system, so the deterministic absorption of
`exists_absorb_par` has to be averaged over the partner's support — which is
what `mem_nonexpandingConverters_of_sum` does, on the decomposition
`Distribution.prod_eq_sum_right`.  Sub-probability is the honest hypothesis:
non-negativity is what makes convexity of `δ` available, and a weight budget
of `1` is what turns the weighted average of the bounds back into the bound. -/

/-- **A parallel frame in the right slot never helps a distinguisher.**  What
an environment learns from `R ‖ T` at a fixed sub-probability frame `T` it
learns from `R` alone, by running `T` itself: a round of `par` is one query to
one component, so the frame's rounds carry no information about `R` and the
inner rounds are relayed one for one. -/
theorem parRight_mem_nonexpandingConverters {c : Set Uni.{u}} {TL : Phi.{u}}
    (h0 : ∀ t, 0 ≤ ofPhi TL t) (h1 : (ofPhi TL).weight ≤ 1) :
    (fun RL => RandomSystems.par c RL TL) ∈ nonexpandingConverters.{u} := by
  refine mem_nonexpandingConverters_of_sum (ofPhi TL).support (fun t => ofPhi TL t)
    (fun t => Distribution.fTransform (fun s => System.par c s t))
    (fun RL => RandomSystems.par c RL TL) (fun i _ => h0 i) ?_ ?_ ?_
  · rw [← Distribution.weight_eq_sum_of_support_subset (ofPhi TL)
      (Finset.Subset.refl _)]
    exact h1
  · exact fun t _ RL SL =>
      PDS.advFullyDefined_fTransform_le (fun s => System.par c s t) RL SL
        fun e n => System.exists_absorb_par c t e n
  · intro L
    show Distribution.fTransform
        (fun p : System.DDS Uni.{u} Uni.{u} × System.DDS Uni.{u} Uni.{u} =>
          System.par c p.1 p.2) (Distribution.prod L TL) = _
    rw [Distribution.prod_eq_sum_right L TL, Distribution.fTransform_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Distribution.fTransform_smul, Distribution.fTransform_fTransform]
    rfl

/-- **A parallel frame in the left slot never helps a distinguisher** — the
right-slot statement at the complementary splitting, since `par` is
commutative up to complementing the splitting (`RandomSystems.par_comm`). -/
theorem parLeft_mem_nonexpandingConverters {c : Set Uni.{u}} {TL : Phi.{u}}
    (h0 : ∀ t, 0 ≤ ofPhi TL t) (h1 : (ofPhi TL).weight ≤ 1) :
    (fun RL => RandomSystems.par c TL RL) ∈ nonexpandingConverters.{u} := by
  refine mem_nonexpandingConverters.mpr fun RL SL => ?_
  show PDS.advFullyDefined (RandomSystems.par c TL RL)
      (RandomSystems.par c TL SL) ≤ _
  rw [RandomSystems.par_comm c TL RL, RandomSystems.par_comm c TL SL]
  exact mem_nonexpandingConverters.mp
    (parRight_mem_nonexpandingConverters (c := cᶜ) h0 h1) RL SL

/-- **The blocking submonoid is nonexpanding.**  Blocks compose to blocks
(`block_block`) and the unit is the empty block, so this is the whole
submonoid they generate. -/
theorem closure_le_nonexpandingConverters :
    Submonoid.closure
        {π : Function.End Phi.{u} | ∃ Q : Set Uni.{u}, π = block Q} ≤
      nonexpandingConverters.{u} := by
  refine Submonoid.closure_le.mpr ?_
  rintro π ⟨Q, rfl⟩
  exact block_mem_nonexpandingConverters Q

/-! ## The scope of this module, and what refutes the rest

`converterMonoid` (`ConnectPhi.lean`) has three generator families:
`connectPhi EL`, `attach E`, and `block Q`.  Only the last is claimed
nonexpanding here, and that is not a gap in the proof effort — the other two
are **false** as stated, for a reason that is about the composite, not about
the metric.

The obstruction, stated once.  `Connect.serve` makes a resource refusal
*fatal to the round*: if the engine's request is refused, `serve` is
undefined, so the outer query is outside `dom (connect E R)`, so the
completion answers `⊥` — and CR18's deletion convention then rewinds the
composite's state, the refused outer query never entering
`keptPrefix (connect E R)`.  The composite's next round is therefore served
by replaying the interpreter *from the previous kept state*.  The inner
resource cannot rewind: the requests the engine issued and the resource
answered before the refusal are in the inner system's kept history for good.
So whenever a round refuses **after** inner traffic, no environment on the
inner side can reproduce the outer view, and the pushforward hypothesis of
`PDS.advFullyDefined_fTransform_le` is unsatisfiable.

This is not merely a failure of the reduction technique: the *conclusion*
fails.  With `X = {a₁, a₂, kill}`, systems `s(β₁, β₂)` accepting exactly
`[a₁]`, `[a₂]`, `[a₁, kill]` (iff `β₁`), `[a₂, kill]` (iff `β₂`) and
answering a constant, and the engine that on outer query `i` requests `aᵢ`,
then `kill`, then answers: the composite's round `i` succeeds iff `βᵢ = 1`,
and a failed round rewinds, so an outer environment asking `1` then `2`
learns `β₁` and — when `β₁ = 0` — also `β₂`.  On the inner side the first
accepted query is `a₁` or `a₂` and is forced by the (deterministic)
environment, after which only the matching `kill` is ever accepted again:
every inner environment learns exactly one of the two bits.  Hence
`Adv⊥(R, S) = 0` and `Adv⊥(attach E R, attach E S) = 1/2` for
`R = ½·s(0,0) + ½·s(1,1)` and `S = ½·s(0,1) + ½·s(1,0)`.

Blocking is exempt for the one reason that matters: a blocked query is
refused **before** any inner traffic, so the two deletions agree.  The same
criterion is what a repaired composite must satisfy — refusal has to reach
the engine as an observable answer (Ruling R2) instead of killing the round,
which means converters at signature `DDS (U ⊕ Option Y) (V ⊕ X)` attached to
`R⊥`.  That is a carrier decision, recorded in PHI-SPEC's B4 line, not a
proof obligation this module can discharge. -/

end

end RandomSystems
