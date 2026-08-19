/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.ConverterEntry
import RandomSystems.System.MetricFullyDefined
import RandomSystems.System.RandomObjects
import RandomSystems.System.FilterPhi
import RandomSystems.Technique.BlindWinning
import RandomSystems.Technique.ConditionalEquivalence
import AbstractCryptography.Metric.Epsilon
import AbstractCryptography.Specification.Parameterized
import Probability.Counting
import Mathlib.Data.List.GetD

/-!
# CR18 §6.2.3: CBC-MAC as a randomness expander

PAPER-FAITHFUL

Cachin–Renner(–Maurer), *Lecture Notes on Cryptography*, **§6.2.2–§6.2.3,
printed pp. 125–127** (every page cited below was read on the rendered page).

**Theorem 6.1, printed p. 126**: "For `θ_r` defined as above, if the
block-former of the `CBC`-converter is prefix-free, we have (for any `r`)
`[r]R_{n,n} --θ_r CBC--> (θ_r V_n)^{ε_r}` for `ε_r = ½ r² 2^{-n}`."

The arrow is CR18 Definition 5.4's construction relation and the superscript is
§5.2.3's `ε`-relaxation, so the endpoint of this file is an
`AbstractCryptography.ApproximatelyConstructs` judgment over `Phi` at
`Σ := ↥converterMonoidAt` — not a bare distance inequality.  The distance is an
intermediate, exactly as on the printed page.

## The bounded message space (F-1 ruling, Marc, 2026-08-19)

Definition 6.1's footnote 2, **printed p. 125**, reads: "Note that because the
input alphabet is infinite, `V_n` can not be described as a probabilistic
discrete system, i.e., as a probability distribution over deterministic
systems."  PHI-SPEC Ruling R1 makes the carrier `Φ := PDS Uni Uni`, a
distribution over deterministic systems, so the variable-input-length ideal
object is outside it by construction.

The ruling is therefore: **the message alphabet `M` is finite, declared as an
explicit hypothesis and never silently swapped in**.  For a bitstring
instantiation this reads `{0,1}^≤max` — messages of at most `max` blocks.  What
this file proves is CR18's theorem at a bounded message space, which is the
same content for every distinguisher this carrier can express, since a
finite-horizon environment only ever touches a bounded slice.  It does not
prove the unbounded statement, and no carrier extension is claimed.

The bound is not bookkeeping, but it must be recorded for what it is.  CR18
Definition 3.8's finite request bound (printed p. 62) is what the entry point
`converterEngine_mem_converterMonoidAt` consumes to place a converter in the
metric-facing `Σ`, and the **operative hypothesis is a bound on encoding
length**, not finiteness of the message type:
`cbcRound_requestsBounded_of_length_le` derives the request bound from
`∀ m, (bf m).length ≤ B` and from nothing else.  Finiteness of `M` enters only
as the cheapest way to produce such a `B` — `blockBound`, a sup over a
`Fintype` — and it is itself a *consequence* of the theorem's other
hypotheses rather than an independent one: prefix-freeness makes `bf`
injective (`PrefixFree.injective`), and an injective encoding into the
length-`≤ B` block sequences over a finite block alphabet has a finite domain
(`finite_of_prefixFree_of_length_le`).

What fails without a length bound is therefore our *sufficient* condition for
membership, not membership.  `converterMonoidAt` is a `Submonoid.closure`, so
"over an unbounded message alphabet the CBC converter is not a member of this
`Σ`" is **not proved here and does not follow** from failing
`attachAt_mem_converterMonoidAt`: the same endomorphism could enter the
closure through a different engine or a product of generators.  Denying
membership needs a separating invariant on the closure, and this tree has
none.

## What is proved here, and what is not

Proved:

* the CBC converter is a member of `↥converterMonoidAt` (`cbcConverter`), and so
  are CR18's two restrictions `θ_r` (`theta`) and `[r]` (`queryLimit`);
* CR18's first proof sentence, printed p. 126 — prefix-freeness plus "no
  non-trivial collision" makes the terminal round-function inputs of distinct
  queried messages distinct (`notBad_implies_distinct_lastInputs`);
* CR18's second proof sentence, printed pp. 126–127, in mass form — conditioned
  on no non-trivial collision the CBC outputs have exactly the law of a uniform
  random function (`notBad_implies_uniform_outputs`), through the
  re-randomization of the terminal call sites;
* the realization equation — `cbcConverter bf` applied to the on-ramped round
  function *is* the on-ramped CBC chain (`attachEngineFully_cbcRound_univ`, and
  at Φ `cbcConverter_smul_Rnn`), which is what ties the `Σ` element to the
  function `cbcState f ∘ bf` at all;
* the crossing from the distance bound to Theorem 6.1's construction
  statement.  That crossing is **notation, not content** — `cbc_mac_constructs`
  is a scaffold, see its docstring — and the one consequence actually
  demonstrated on it is `cbc_mac_trans`.

Not proved, and stated as the hypothesis `hcbc` of the endpoint: the
distinguishing bound itself, which is CR18 Theorem 6.1's mathematics in full.
**Four** of the six obligations listed at `cbc_mac_constructs` are open.
-/

namespace RandomSystems.CBCMAC

open Classical
open Probability
open AbstractCryptography
open scoped ENNReal

set_option linter.unusedSectionVars false

universe u

variable {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X] [AddCommGroup X]
variable {M : Type u} [Fintype M] [DecidableEq M]

/-! ## §6.2.2's two objects, at the bounded message space -/

/-- CR18's fixed-input-length uniform random function `R_{n,n}` (printed
p. 125). -/
noncomputable def Rnn (X : Type u) [Fintype X] [DecidableEq X] [Nonempty X] :
    PDS X X :=
  PDS.urf X X

/-- **CR18 Definition 6.1's VIL-URF `V_n`** (printed p. 125) at the bounded
message space of the F-1 ruling: the system that answers each new message with
a fresh uniform value and repeats consistently.  Over a *finite* `M` that is a
probabilistic discrete system — footnote 2 (printed p. 125) says it is not one
over `{0,1}*`. -/
noncomputable def Vn (M X : Type u) [Fintype M] [DecidableEq M] [Fintype X]
    [DecidableEq X] [Nonempty X] : PDS M X :=
  PDS.urf M X

/-! ## §6.2.3's block former -/

/-- **Prefix-freeness of the block former** (printed p. 126): "it must be
guaranteed that for no two distinct messages `m₁` and `m₂`, the resulting block
sequence (at the output of the block former) for `m₁` is a prefix of the block
sequence for `m₂`." -/
def PrefixFree (bf : M → List X) : Prop :=
  ∀ m m', m ≠ m' → ¬ (bf m <+: bf m')

/-- Prefix-freeness forces every encoding to be nonempty as soon as the message
alphabet is nontrivial. -/
theorem PrefixFree.ne_nil [Nontrivial M] {bf : M → List X}
    (h : PrefixFree bf) (m : M) : bf m ≠ [] := by
  intro hnil
  obtain ⟨m', hm'⟩ := exists_ne m
  exact h m m' hm'.symm (by rw [hnil]; exact List.nil_prefix)

omit [Fintype X] [DecidableEq X] [Nonempty X] [AddCommGroup X] [Fintype M]
  [DecidableEq M] in
/-- Prefix-freeness is an injectivity statement about the block former: two
distinct messages whose encodings agreed would have each encoding a prefix of
the other.  (CR18 states prefix-freeness as the encoding condition, printed
p. 126; this is the part of it the counting arguments use.) -/
theorem PrefixFree.injective {bf : M → List X} (h : PrefixFree bf) :
    Function.Injective bf := by
  intro a b hab
  by_contra hne
  exact h a b hne (hab ▸ List.prefix_refl (bf a))

/-- **Finiteness of the message space is a consequence, not an extra
hypothesis.**  A prefix-free block former of bounded length is an injection of
the message space into the block sequences of length at most `B` over the
block alphabet, and there are finitely many of those when the block alphabet
is finite.  So Theorem 6.1's own hypotheses (printed p. 126) — prefix-freeness,
and the bounded encoding length the request bound needs — already force the
F-1 ruling's finite `M`. -/
theorem finite_of_prefixFree_of_length_le {X' M' : Type u} [Fintype X']
    {bf : M' → List X'} {B : ℕ} (hbf : PrefixFree bf)
    (hB : ∀ m, (bf m).length ≤ B) : Finite M' := by
  have hi : Function.Injective (fun m => fun i : Fin B => (bf m)[(i : ℕ)]?) := by
    intro a b h
    refine hbf.injective (List.ext_getElem? fun n => ?_)
    by_cases hn : n < B
    · exact congrFun h ⟨n, hn⟩
    · rw [List.getElem?_eq_none (le_trans (hB a) (by omega)),
        List.getElem?_eq_none (le_trans (hB b) (by omega))]
  exact Finite.of_injective _ hi

/-- The accumulated number of blocks the block former has emitted. -/
def totalBlocks (bf : M → List X) (messages : List M) : ℕ :=
  (messages.map fun m => (bf m).length).sum

theorem totalBlocks_mono (bf : M → List X) {l₁ l₂ : List M} (h : l₁ <+: l₂) :
    totalBlocks bf l₁ ≤ totalBlocks bf l₂ := by
  obtain ⟨t, rfl⟩ := h
  simp [totalBlocks, List.map_append]

/-- Digest a block sequence with a round function.  The public initial state is
`0`, and a block `b` updates the state by `y ↦ f (y + b)` — CR18 printed
p. 125, "the initial value of the state is a fixed and known parameter". -/
def cbcState (f : X → X) (bs : List X) : X :=
  bs.foldl (fun y b => f (y + b)) 0

/-- Appending one block performs one more round-function call. -/
theorem cbcState_concat (f : X -> X) (bs : List X) (b : X) :
    cbcState f (bs ++ [b]) = f (cbcState f bs + b) := by
  simp only [cbcState, List.foldl_concat]

/-- The input supplied to the round function at block position `j`. -/
def cbcInput (f : X -> X) (bs : List X) (j : Nat) : X :=
  cbcState f (bs.take j) + bs.getD j 0

/-! ## The CBC converter as a member of the metric-facing `Σ`

The converter is written as a history function — the current message and the
round-function answers of the round so far — and enters `Σ` through the
library's one crossing, `RandomSystems.converterEngine_mem_converterMonoidAt`.
No `ProtocolFn` and no `DDC` appears in any statement below.  The history
function `cbcRound` itself is named only in the receipts that crossing
consumes (`cbcRound_innerTotal`, `cbcRound_requestsBounded_of_length_le`,
`cbcRound_requestsBounded`) and the engine only in `cbcConverter_requestsWithin`;
every endpoint of this file speaks about the `Σ` element alone.
-/

/-- **One CBC round** (printed p. 125): "`CBC` applies a block former to the
message and then digests the obtained block sequence block by block, each time
invoking the system at its right interface."  While blocks remain, ask the
round function for the next chaining value; after the last answer, return it.

A refusal from the inner system is read as the initial chaining value: Ruling
R2 makes refusal observable and non-fatal, and a converter that stalled instead
would violate CR18 Definition 3.8's request bound.  Against a fully defined
inner resource — every resource this theorem is about — the branch is never
taken. -/
noncomputable def cbcRound (bf : M → List X) :
    List M × List (Option X) →. X ⊕ X := fun p =>
  if h : p.1 ≠ [] then
    let m := p.1.getLast h
    let ys := p.2.map fun o => o.getD 0
    if ys.length < (bf m).length then
      Part.some (Sum.inl (ys.getLastD 0 + (bf m).getD ys.length 0))
    else
      Part.some (Sum.inr (ys.getLastD 0))
  else
    Part.none

/-- **Ruling R2's inner-facing totality for CBC**: having asked, CBC reacts to
whatever the round function returns. -/
theorem cbcRound_innerTotal (bf : M → List X) :
    System.ConverterInnerTotal (cbcRound bf) := by
  intro us ys x hx o
  have hne : us ≠ [] := by
    by_contra hnil
    rw [cbcRound, dif_neg (by simpa using hnil)] at hx
    exact absurd hx (by simp)
  rw [cbcRound, dif_pos hne]
  dsimp only
  split <;> exact ⟨⟩

/-- The largest number of blocks the block former ever emits.  It is the
cheapest witness for the *length bound* the request receipt actually needs
(`cbcRound_requestsBounded_of_length_le`), and it is where the F-1 ruling's
finite message space is spent — as a producer of that constant, not as the
operative hypothesis. -/
noncomputable def blockBound (bf : M → List X) : ℕ :=
  Finset.univ.sup fun m => (bf m).length

theorem length_le_blockBound (bf : M → List X) (m : M) :
    (bf m).length ≤ blockBound bf :=
  Finset.le_sup (f := fun m => (bf m).length) (Finset.mem_univ m)

/-- **CR18 Definition 3.8's finite request bound for CBC** (printed p. 62),
from the hypothesis that actually carries it: a round asks the round function
one question per block of the current message, so any bound on the encoding
length bounds the round.  Neither finiteness of `M` nor `blockBound` is used —
this is the sharp statement of what the bound costs. -/
theorem cbcRound_requestsBounded_of_length_le (bf : M → List X) {B : ℕ}
    (hB : ∀ m, (bf m).length ≤ B) :
    System.ConverterRequestsBounded (cbcRound bf) B := by
  intro us ys x hx
  have hne : us ≠ [] := by
    by_contra hnil
    rw [cbcRound, dif_neg (by simpa using hnil)] at hx
    exact absurd hx (by simp)
  rw [cbcRound, dif_pos hne] at hx
  dsimp only at hx
  by_cases hlt : (ys.map fun o => o.getD 0).length < (bf (us.getLast hne)).length
  · rw [if_pos hlt] at hx
    rw [List.length_map] at hlt
    exact lt_of_lt_of_le hlt (hB _)
  · rw [if_neg hlt] at hx
    exact absurd hx (by simp)

/-- The request bound at the constant this file carries, `blockBound bf`
(printed p. 62 for the clause).  A specialization of
`cbcRound_requestsBounded_of_length_le`; what fails without *some* such
constant is this sufficient condition for `Σ`-membership, not membership. -/
theorem cbcRound_requestsBounded (bf : M → List X) :
    System.ConverterRequestsBounded (cbcRound bf) (blockBound bf) :=
  cbcRound_requestsBounded_of_length_le bf (length_le_blockBound bf)

/-- **The CBC converter, as the one converter notion an application names**:
the element of `↥converterMonoidAt` that applies CBC to the whole face of the
round function.  That is CR18 §6.2.3's own object (printed pp. 125–126):
`CBC` is applied to the system `R_{n,n}` — it "makes calls to the system … at
the inside (right interface)" and answers messages outside — not to one
interface of a larger resource, and
`attachAt Set.univ` is exactly CR18 Definition 3.9's application (printed p. 62)
through the demotion bridge `attachAt_univ`.

**The whole face is forced, not a default.**  `attachEngineFully` dispatches
*outer* queries on the interface: a query outside it is handed to the resource
verbatim (`System.attachEngineFullyRound_not_mem`).  CBC converts an
`(X,X)`-system into an `(M,X)`-system, so the queries it must own are addressed
at `M` while the requests it emits are addressed at `X`.  An interface holding
only the round function's address would therefore route every *message* past
the converter to the round function, which refuses it, and the composite would
answer nothing at all — the realization equation below would be false.  Where
the engine *reaches* is the separate clause `System.RequestsWithin`, and it is
stated at the round function's address in `cbcConverter_requestsWithin`. -/
noncomputable def cbcConverter (bf : M → List X) : ↥converterMonoidAt.{u} :=
  ⟨attachAt (Set.univ : Set Uni.{u}) (System.converterEngine X X (cbcRound bf)),
    converterEngine_mem_converterMonoidAt _ _ (cbcRound_innerTotal bf)
      (cbcRound_requestsBounded bf)⟩

/-- The CBC converter reaches only into the round function's interface. -/
theorem cbcConverter_requestsWithin (bf : M → List X) :
    System.RequestsWithin {q : Uni.{u} | q.1 = X}
      (System.converterEngine X X (cbcRound bf)) :=
  System.requestsWithin_converterEngine _ fun _ => rfl

/-! ## The realization equation: the converter computes the CBC chain

The receipts above place `cbcConverter` in `Σ`; they say nothing about what it
*answers*.  This section closes that gap — the first of the six obligations
listed at `cbc_mac_constructs`: applied to the on-ramped round function, the
CBC converter **is** the on-ramped system that answers `cbcState f (bf m)` to
the message `m`.  Nothing downstream — the collision game, the conditional
equivalence, the counting — connects to CBC at all until this holds, because
without it nothing ties the `Σ` element to the function `cbcState f ∘ bf`.

The work is done by the library's one round lemma,
`System.attachEngineFully_converterEngine_univ`: an application supplies a
`System.ConverterRunsTo` for its own history function and gets the equation.
What is CBC's own is `cbcRound_runsTo` — the chain induction, one step per
block — and `answer_ofTyped_functionEvaluator`, which says the round function
answers `f x` to `x` whatever it has been asked before.
-/

section Realization

open System

/-- **An on-ramped function answers its own value**, whatever the history: the
completion of `ofTyped (functionEvaluator f)` returns `f a` to `a`, never `⊥`.
The evaluator is defined on every nonempty history, so CR18 Definition 3.3's
deletion pass (printed p. 58) removes nothing and the answer does not depend on
the history at all. -/
theorem answer_ofTyped_functionEvaluator {A B : Type u} (f : A → B)
    (xs : List Uni.{u}) (a : A) :
    answer (System.ofTyped (functionEvaluator f)) xs (encode A a)
      = some (encode B (f a)) := by
  set l₀ : List A := xs.filterMap decodeOption with hl₀
  have hkept : keptPrefix (System.ofTyped (functionEvaluator f)) xs = l₀.map (encode A) := by
    rw [keptPrefix_ofTyped]
    congr 1
    refine keptPrefix_eq_self_of_mem_or_empty _ ?_
    rcases eq_or_ne l₀ [] with h | h
    · exact Or.inr h
    · exact Or.inl (by rw [dom_functionEvaluator]; exact h)
  have hne : l₀ ++ [a] ≠ [] := by simp
  have hdom : (l₀ ++ [a]).map (encode A) ∈ dom (System.ofTyped (functionEvaluator f)) :=
    (mem_dom_ofTyped_encode hne).mpr (by rw [dom_functionEvaluator]; exact hne)
  rw [answer_eq, hkept]
  have hcat : l₀.map (encode A) ++ [encode A a] = (l₀ ++ [a]).map (encode A) := by simp
  rw [hcat, dif_pos hdom]
  congr 1
  have hS : l₀ ++ [a] ∈ dom (functionEvaluator f) := by
    rw [dom_functionEvaluator]; exact hne
  rw [output_ofTyped_encode hS hdom, output_functionEvaluator]
  simp

/-- The round-function answers CBC holds after digesting `k` blocks: the
chaining values of the block prefixes. -/
def cbcRoundAnswers (f : X → X) (bs : List X) (k : ℕ) : List (Option X) :=
  (List.range k).map fun i => some (cbcState f (bs.take (i + 1)))

@[simp] theorem cbcRoundAnswers_zero (f : X → X) (bs : List X) :
    cbcRoundAnswers f bs 0 = [] := rfl

theorem cbcRoundAnswers_length (f : X → X) (bs : List X) (k : ℕ) :
    (cbcRoundAnswers f bs k).length = k := by simp [cbcRoundAnswers]

theorem cbcRoundAnswers_succ (f : X → X) (bs : List X) (k : ℕ) :
    cbcRoundAnswers f bs (k + 1)
      = cbcRoundAnswers f bs k ++ [some (cbcState f (bs.take (k + 1)))] := by
  simp [cbcRoundAnswers, List.range_succ]

/-- The chaining value CBC carries into the next block is the last answer it
received — and the public initial value `0` when it has received none. -/
theorem cbcRoundAnswers_getLastD (f : X → X) (bs : List X) (k : ℕ) :
    ((cbcRoundAnswers f bs k).map fun o => o.getD 0).getLastD 0
      = cbcState f (bs.take k) := by
  cases k with
  | zero => simp [cbcState]
  | succ n => rw [cbcRoundAnswers_succ]; simp

/-- One more block advances the chain by one round-function call at that
block's call-site input. -/
theorem cbcState_take_succ (f : X → X) (bs : List X) {k : ℕ} (hk : k < bs.length) :
    cbcState f (bs.take (k + 1)) = f (cbcInput f bs k) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some]
  rw [cbcState_concat]
  congr 2
  rw [List.getD_eq_getElem _ _ hk]

/-- **The chain induction**: against a resource that answers `f x` to `x`, one
CBC round digests the current message's blocks one at a time and ends at
`cbcState f bs`.  The induction runs on the blocks still to be digested, and
carries the chain state in the round's own answer list — which is what makes
the statement independent of the resource history the round starts from, and so
usable at every round of the outer interaction. -/
theorem cbcRound_runsTo (f : X → X) (bf : M → List X) (R : DDS Uni.{u} Uni.{u})
    (hR : ∀ (xs : List Uni.{u}) (x : X),
      answer R xs (encode X x) = some (encode X (f x)))
    (us : List M) (hne : us ≠ []) (bs : List X) (hbs : bf (us.getLast hne) = bs) :
    ∀ (d k : ℕ), k + d = bs.length →
      ∀ xs : List Uni.{u},
        ConverterRunsTo (cbcRound bf) R us (cbcRoundAnswers f bs k) xs
          (cbcState f bs) := by
  intro d
  induction d with
  | zero =>
      intro k hk xs
      refine ConverterRunsTo.stop ?_
      rw [cbcRound, dif_pos hne]
      dsimp only
      rw [hbs, if_neg (by
        rw [List.length_map, cbcRoundAnswers_length]
        omega)]
      rw [Part.mem_some_iff]
      congr 1
      rw [cbcRoundAnswers_getLastD, show k = bs.length by omega, List.take_length]
  | succ d ih =>
      intro k hk xs
      have hklt : k < bs.length := by omega
      refine ConverterRunsTo.ask (x := cbcInput f bs k) ?_ ?_
      · rw [cbcRound, dif_pos hne]
        dsimp only
        rw [hbs, if_pos (by
          rw [List.length_map, cbcRoundAnswers_length]
          exact hklt)]
        rw [Part.mem_some_iff]
        congr 1
        rw [List.length_map, cbcRoundAnswers_length, cbcRoundAnswers_getLastD]
        rfl
      · rw [hR xs (cbcInput f bs k)]
        simp only [Option.bind_some, decodeOption_encode]
        rw [← cbcState_take_succ f bs hklt, ← cbcRoundAnswers_succ]
        exact ih (k + 1) (by omega) _

/-- **The realization equation, at a deterministic round function** — the first
of the six obligations at `cbc_mac_constructs`, discharged.

The CBC engine applied to the on-ramped round function `f` is the on-ramped
system `m ↦ cbcState f (bf m)`: CR18's own description of the converter
(printed p. 125) — "`CBC` applies a block former to the message and then
digests the obtained block sequence block by block, each time invoking the
system at its right interface" — as an equation between systems, and not a
description.

Both faces of the equation are computed, not assumed: the composite answers a
message exactly where the on-ramped chain does, and refuses everything else,
because the engine must decode the outer history at `M` before it can move. -/
theorem attachEngineFully_cbcRound_univ (f : X → X) (bf : M → List X) :
    attachEngineFully (Set.univ : Set Uni.{u}) (converterEngine X X (cbcRound bf))
        (System.ofTyped (functionEvaluator f))
      = System.ofTyped (functionEvaluator fun m : M => cbcState f (bf m)) := by
  refine attachEngineFully_converterEngine_univ (g := fun m : M => cbcState f (bf m)) ?_
  intro us m xs
  have hne : us ++ [m] ≠ [] := by simp
  have hlast : (us ++ [m]).getLast hne = m := by simp
  have hrun := cbcRound_runsTo f bf (System.ofTyped (functionEvaluator f))
    (answer_ofTyped_functionEvaluator f) (us ++ [m]) hne (bf m) (by rw [hlast])
    (bf m).length 0 (by simp) xs
  simpa using hrun

/-- The law of the CBC function: the block former digested by a uniform round
function.  The image of CR18's `R_{n,n}` (printed p. 125) under the CBC
construction, as a probabilistic discrete system on the bounded message space
of the F-1 ruling. -/
noncomputable def cbcFunctionLaw (bf : M → List X) : PDS M X :=
  Distribution.fTransform
    (fun f : X → X => functionEvaluator fun m : M => cbcState f (bf m))
    (Distribution.uniform (X → X))

/-- **The realization equation at Φ** — the form every endpoint of this file
speaks in: the `Σ` element `cbcConverter bf` applied to the on-ramped uniform
round function is the on-ramped CBC function law.  The pushforward of
`attachEngineFully_cbcRound_univ` along the atoms of `R_{n,n}` (printed
p. 125), which are function evaluators by construction. -/
theorem cbcConverter_smul_Rnn (bf : M → List X) :
    cbcConverter bf • (RandomSystems.ofTyped (Rnn X) : Phi.{u})
      = RandomSystems.ofTyped (cbcFunctionLaw bf) := by
  show Distribution.fTransform
      (attachEngineFully (Set.univ : Set Uni.{u}) (converterEngine X X (cbcRound bf))) _ = _
  rw [RandomSystems.ofTyped, RandomSystems.ofTyped, Rnn, PDS.urf, cbcFunctionLaw,
    Distribution.fTransform_fTransform, Distribution.fTransform_fTransform,
    Distribution.fTransform_fTransform]
  congr 1
  funext f
  exact attachEngineFully_cbcRound_univ f bf

end Realization

/-! ## §6.2.3's two restrictions, as members of the same `Σ` -/

/-- The predicate `θ_r` tests (printed p. 126): "for each message `θ_r`
determines the number of blocks the block-former outputs … and keeps track of
the total number of such blocks resulting for all messages seen so far.  When
this number exceeds `r`, then `θ_r` stops replying to queries." -/
def thetaPred (bf : M → List X) (r : ℕ) : List Uni.{u} → Prop := fun l =>
  totalBlocks bf (l.filterMap (System.decodeOption (X := M))) ≤ r

theorem prefixClosed_thetaPred (bf : M → List X) (r : ℕ) :
    PrefixClosed (thetaPred (X := X) bf r) := by
  intro l₁ l₂ hpre hl₂
  refine le_trans (totalBlocks_mono bf ?_) hl₂
  obtain ⟨t, rfl⟩ := hpre
  exact ⟨t.filterMap (System.decodeOption (X := M)), List.filterMap_append.symm⟩

/-- **CR18's restriction converter `θ_r`** (printed p. 126), as a member of the
metric-facing `Σ`: a domain filter at a prefix-closed predicate is a generator
of `converterMonoidAt` (`filterPhi_mem_converterMonoidAt`). -/
noncomputable def theta (bf : M → List X) (r : ℕ) : ↥converterMonoidAt.{u} :=
  ⟨filterPhi (thetaPred (X := X) bf r) (prefixClosed_thetaPred bf r),
    filterPhi_mem_converterMonoidAt _ _⟩

/-- **CR18 Definition 3.10's filter `[r]`** (printed p. 62), as a member of the
same `Σ` (`filterQueries_mem_converterMonoidAt`). -/
noncomputable def queryLimit (r : ℕ) : ↥converterMonoidAt.{u} :=
  ⟨filterQueries r, filterQueries_mem_converterMonoidAt r⟩


/-! ## CR18 Theorem 6.1's proof, the two steps the paper only asserts

The monotone condition of the proof (printed p. 126): "`A_i = 1` if and only
if, up to the evaluation of the `i`-th message (the `i`-th input to `CBC`), a
non-trivial collision has occurred at the input to `R_{n,n}`.  By non-trivial we
mean that collisions do not count if they hold because two messages have the
same prefix."

Everything below is stated on the round function `f` rather than on a system:
these are the counting facts, and the two sentences CR18 states without proof
are `notBad_implies_distinct_lastInputs` (printed p. 126, "Since the encoding is
prefix-free, `A_i = 0` implies in particular that all the last-block inputs to
`R_{n,n}` … are distinct") and `notBad_implies_uniform_outputs` (printed
pp. 126–127, "Conditioned on this event … all outputs are uniformly random,
except of course that for identical inputs the outputs are also identical").
-/

/-- Maurer's monotone condition `A_i`: some two nontrivially distinct CBC
call sites encountered up to the current message have collided at the input
to `R_{n,n}`.  Equal block prefixes designate the same computation and are
therefore excluded. -/
def cbcBad (f : X -> X) (bf : M -> List X) (l : List M) : Prop :=
  ∃ m ∈ l, ∃ m' ∈ l,
    ∃ j < (bf m).length, ∃ j' < (bf m').length,
      (bf m).take (j + 1) ≠ (bf m').take (j' + 1) ∧
        cbcInput f (bf m) j = cbcInput f (bf m') j'

instance (f : X -> X) (bf : M -> List X) (l : List M) :
    Decidable (cbcBad f bf l) := by
  unfold cbcBad
  infer_instance

/-- The collision condition is monotone in the outer query history. -/
theorem cbcBad_monotone (f : X -> X) (bf : M -> List X)
    {l1 l2 : List M} (hpre : l1 <+: l2) (hbad : cbcBad f bf l1) :
    cbcBad f bf l2 := by
  obtain ⟨m, hm, m', hm', j, hj, j', hj', hkey, hvalue⟩ := hbad
  exact ⟨m, hpre.subset hm, m', hpre.subset hm', j, hj, j', hj', hkey, hvalue⟩

/-- The native monotone-condition object used to augment the real
experiment.  It is introduced only in the proof, after `cbcReal`. -/
def cbcCondition (f : X -> X) (bf : M -> List X) :
    System.MonotoneCondition M :=
  ⟨{l | cbcBad f bf l}, by
    intro l1 l2 hpre hbad
    exact cbcBad_monotone f bf hpre hbad⟩
/-- Before the appended block, CBC's round inputs are unchanged. -/
theorem cbcInput_append_of_lt (f : X -> X) (bs : List X) (b : X)
    {j : Nat} (hj : j < bs.length) :
    cbcInput f (bs ++ [b]) j = cbcInput f bs j := by
  unfold cbcInput
  rw [List.take_append_of_le_length (Nat.le_of_lt hj),
    List.getD_append bs [b] 0 j hj]

/-- The last input of an appended sequence is the previous chaining value
plus the appended block. -/
theorem cbcInput_append_length (f : X -> X) (bs : List X) (b : X) :
    cbcInput f (bs ++ [b]) bs.length = cbcState f bs + b := by
  unfold cbcInput
  rw [List.take_left,
    List.getD_append_right bs [b] 0 bs.length (le_refl _)]
  simp

/-- The MAC of a nonempty block sequence is the round-function output at its
terminal call-site input. -/
theorem cbcState_eq_f_lastInput (f : X -> X) (bs : List X)
    (hbs : bs ≠ []) :
    cbcState f bs = f (cbcInput f bs (bs.length - 1)) := by
  rcases bs.eq_nil_or_concat with h | ⟨bs', b, rfl⟩
  · exact absurd h hbs
  · rw [List.concat_eq_append, cbcState_concat]
    congr 1
    have hlen : (bs' ++ [b]).length - 1 = bs'.length := by simp
    rw [hlen, cbcInput_append_length]

/-- Under `not cbcBad`, distinct call-site keys have distinct round-function
inputs. -/
theorem not_cbcBad_inputs_ne (f : X -> X) (bf : M -> List X)
    {l : List M} (h : ¬ cbcBad f bf l)
    {m m' : M} (hm : m ∈ l) (hm' : m' ∈ l) {j j' : Nat}
    (hj : j < (bf m).length) (hj' : j' < (bf m').length)
    (hkey : (bf m).take (j + 1) ≠ (bf m').take (j' + 1)) :
    cbcInput f (bf m) j ≠ cbcInput f (bf m') j' :=
  fun hvalue => h ⟨m, hm, m', hm', j, hj, j', hj', hkey, hvalue⟩

/-! ### Internal proof of the fresh-URF step

CR18 treats the implication "fresh terminal inputs give fresh uniform
outputs" as immediate.  Until that causal-URF fact is available as a general
library theorem, the declarations below are private implementation machinery
for precisely that implication.  They are not stages of the CBC proof.
-/

/-- Functions agreeing at every CBC call-site input produce the same final
chaining value. -/
theorem cbcState_congr_of_agree_on_inputs (f f' : X -> X) (bs : List X)
    (h : ∀ j < bs.length,
      f (cbcInput f bs j) = f' (cbcInput f bs j)) :
    cbcState f bs = cbcState f' bs := by
  induction bs using List.reverseRecOn with
  | nil => rfl
  | append_singleton bs' b ih =>
    rw [cbcState_concat, cbcState_concat]
    have hstep : ∀ j < bs'.length,
        f (cbcInput f bs' j) = f' (cbcInput f bs' j) := by
      intro j hj
      have hj' : j < (bs' ++ [b]).length := by
        rw [List.length_append]
        omega
      have hcall := h j hj'
      rwa [cbcInput_append_of_lt f bs' b hj] at hcall
    have hbs' : cbcState f bs' = cbcState f' bs' := ih hstep
    have hlast :
        f (cbcInput f (bs' ++ [b]) bs'.length) =
          f' (cbcInput f (bs' ++ [b]) bs'.length) :=
      h bs'.length (by rw [List.length_append]; simp)
    rw [cbcInput_append_length] at hlast
    rw [hlast, hbs']

/-- The terminal round-function input of a message. -/
def cbcLastInput (f : X -> X) (bf : M -> List X) (m : M) : X :=
  cbcInput f (bf m) ((bf m).length - 1)

/-- The key of the terminal call-site is the entire nonempty block list. -/
theorem take_last_key {bs : List X} (hne : bs ≠ []) :
    bs.take (bs.length - 1 + 1) = bs := by
  rw [Nat.sub_add_cancel (List.length_pos_of_ne_nil hne)]
  exact List.take_length

/-- The freshness property consumed by the re-randomization argument. -/
def cbcFresh (f : X -> X) (bf : M -> List X) (l : List M) : Prop :=
  ∀ m ∈ l, ∀ m' ∈ l, ∀ j' < (bf m').length,
    bf m ≠ (bf m').take (j' + 1) ->
      cbcLastInput f bf m ≠ cbcInput f (bf m') j'

/-- Absence of a bad collision implies terminal-input freshness. -/
theorem cbcFresh_of_not_cbcBad (f : X -> X) (bf : M -> List X)
    {l : List M} (hbf_ne : ∀ m, bf m ≠ [])
    (hbad : ¬ cbcBad f bf l) : cbcFresh f bf l := by
  intro m hm m' hm' j' hj' hkey
  refine not_cbcBad_inputs_ne f bf hbad hm hm'
    (by have := List.length_pos_of_ne_nil (hbf_ne m); omega) hj' ?_
  rw [take_last_key (hbf_ne m)]
  exact hkey

/-- For distinct queried messages, freshness and prefix-freeness make the
terminal call-site inputs distinct. -/
theorem cbcLastInput_injOn (f : X -> X) (bf : M -> List X)
    {l : List M} (hbf_ne : ∀ m, bf m ≠ [])
    (hbf_pf : PrefixFree bf) (hfresh : cbcFresh f bf l) :
    Set.InjOn (cbcLastInput f bf) {m | m ∈ l} := by
  intro m hm m' hm' heq
  by_contra hmm
  have hkey : bf m ≠ (bf m').take ((bf m').length - 1 + 1) := by
    rw [take_last_key (hbf_ne m')]
    exact fun h => hbf_pf m m' hmm (h ▸ List.prefix_refl (bf m))
  exact hfresh m hm m' hm' _
    (by have := List.length_pos_of_ne_nil (hbf_ne m'); omega) hkey heq

/-- **CR18's first proof sentence** (printed p. 126): "Since the encoding is
prefix-free, `A_i = 0` implies in particular that all the last-block inputs to
`R_{n,n}` … are distinct, provided of course that the messages themselves are
distinct." -/
theorem notBad_implies_distinct_lastInputs [Nontrivial M]
    (f : X -> X) (bf : M -> List X) {l : List M}
    (hbf : PrefixFree bf) (hbad : ¬ cbcBad f bf l) :
    Set.InjOn (cbcLastInput f bf) {m | m ∈ l} := by
  have hne : ∀ m, bf m ≠ [] := hbf.ne_nil
  exact cbcLastInput_injOn f bf hne hbf
    (cbcFresh_of_not_cbcBad f bf hne hbad)

theorem cbcInput_take_of_lt (f : X -> X) (bs : List X)
    {i j : Nat} (hij : i < j) :
    cbcInput f (bs.take j) i = cbcInput f bs i := by
  unfold cbcInput
  rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hij)]
  congr 1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hij]

/-- Agreement below block position `p` preserves the input at `p`. -/
theorem cbcInput_congr_of_agree_below (f f' : X -> X) (bs : List X)
    {p : Nat}
    (h : ∀ p' < p,
      f' (cbcInput f bs p') = f (cbcInput f bs p')) :
    cbcInput f' bs p = cbcInput f bs p := by
  unfold cbcInput
  congr 1
  refine (cbcState_congr_of_agree_on_inputs f f' (bs.take p) ?_).symm
  intro i hi_len
  have hip : i < p := by
    rw [List.length_take] at hi_len
    omega
  rw [cbcInput_take_of_lt f bs hip]
  exact (h i hip).symm

/-- Chaining after block `t` is evaluation at the block-`t` input. -/
theorem cbcState_take_succ_eq (f : X -> X) (bs : List X)
    {t : Nat} (ht : t < bs.length) :
    cbcState f (bs.take (t + 1)) = f (cbcInput f bs t) := by
  have hne : bs.take (t + 1) ≠ [] := by
    rw [← List.length_pos_iff_ne_nil, List.length_take]
    omega
  rw [cbcState_eq_f_lastInput f _ hne]
  congr 1
  have hlen : (bs.take (t + 1)).length - 1 = t := by
    rw [List.length_take]
    omega
  rw [hlen, cbcInput_take_of_lt f bs (Nat.lt_succ_self t)]

/-- Recurrence for consecutive CBC call-site inputs. -/
theorem cbcInput_succ (f : X -> X) (bs : List X)
    {t : Nat} (ht : t < bs.length) :
    cbcInput f bs (t + 1) =
      f (cbcInput f bs t) + bs.getD (t + 1) 0 := by
  show cbcState f (bs.take (t + 1)) + bs.getD (t + 1) 0 = _
  rw [cbcState_take_succ_eq f bs ht]

/-- Translate `f` by `delta` at one point. -/
def pointShift (f : X -> X) (w delta : X) : X -> X :=
  fun x => if x = w then f x + delta else f x

theorem pointShift_apply_self (f : X -> X) (w delta : X) :
    pointShift f w delta w = f w + delta :=
  if_pos rfl

theorem pointShift_apply_ne (f : X -> X) (w delta : X)
    {x : X} (h : x ≠ w) : pointShift f w delta x = f x :=
  if_neg h

theorem pointShift_pointShift (f : X -> X) (w delta delta' : X) :
    pointShift (pointShift f w delta) w delta' =
      pointShift f w (delta + delta') := by
  funext x
  unfold pointShift
  grind

theorem pointShift_zero (f : X -> X) (w : X) :
    pointShift f w 0 = f := by
  funext x
  unfold pointShift
  grind

/-- A proper-prefix input cannot be a queried message's terminal input. -/
theorem cbcInput_ne_lastInput (f : X -> X) (bf : M -> List X)
    {l : List M} (hbf_pf : PrefixFree bf) (hfresh : cbcFresh f bf l)
    {m : M} (hm : m ∈ l) {i : Nat} (hi : i + 1 < (bf m).length)
    {s : M} (hs : s ∈ l) (_hne_s : bf s ≠ []) :
    cbcInput f (bf m) i ≠ cbcLastInput f bf s := by
  have hkey : bf s ≠ (bf m).take (i + 1) := by
    intro h
    have hpre : bf s <+: bf m := h ▸ List.take_prefix (i + 1) (bf m)
    by_cases hsm : s = m
    · subst hsm
      have hh := congrArg List.length h
      rw [List.length_take] at hh
      omega
    · exact hbf_pf s m hsm hpre
  exact (hfresh s hs m hm i (by omega) hkey).symm

/-- Simultaneously translate `f` at the terminal input of every distinct
queried message. -/
noncomputable def cbcShift (f : X -> X) (bf : M -> List X) (l : List M)
    (delta : ↑l.toFinset -> X) : X -> X :=
  Counting.multiShift
    (fun s : ↑l.toFinset => cbcLastInput f bf s.1) delta f

theorem cbcShift_eq_of_not_terminal (f : X -> X) (bf : M -> List X)
    (l : List M) (delta : ↑l.toFinset -> X) {x : X}
    (h : ∀ s ∈ l.toFinset, cbcLastInput f bf s ≠ x) :
    cbcShift f bf l delta x = f x :=
  Counting.multiShift_apply_of_ne delta f fun s => h s.1 s.2

theorem cbcShift_lastInput (f : X -> X) (bf : M -> List X)
    (l : List M) (delta : ↑l.toFinset -> X)
    (hinj : Set.InjOn (cbcLastInput f bf) {m | m ∈ l})
    (s0 : ↑l.toFinset) :
    cbcShift f bf l delta (cbcLastInput f bf s0.1) =
      f (cbcLastInput f bf s0.1) + delta s0 :=
  Counting.multiShift_apply_site delta f
    (fun a b hab =>
      Subtype.ext (hinj (List.mem_toFinset.mp a.2)
        (List.mem_toFinset.mp b.2) hab)) s0

/-- Shifting terminal outputs leaves all CBC call-site inputs unchanged. -/
theorem cbcInput_cbcShift (f : X -> X) (bf : M -> List X)
    {l : List M} (delta : ↑l.toFinset -> X)
    (hbf_pf : PrefixFree bf) (hbf_ne : ∀ m, bf m ≠ [])
    (hfresh : cbcFresh f bf l) {m : M} (hm : m ∈ l)
    {j : Nat} (hj : j < (bf m).length) :
    cbcInput (cbcShift f bf l delta) (bf m) j = cbcInput f (bf m) j := by
  refine cbcInput_congr_of_agree_below f _ (bf m) fun i hip => ?_
  refine cbcShift_eq_of_not_terminal f bf l delta fun s hs => ?_
  exact (cbcInput_ne_lastInput f bf hbf_pf hfresh hm (by omega)
    (List.mem_toFinset.mp hs) (hbf_ne s)).symm

/-- The multi-shift preserves the not-bad event. -/
theorem not_cbcBad_cbcShift (f : X -> X) (bf : M -> List X)
    {l : List M} (delta : ↑l.toFinset -> X)
    (hbf_pf : PrefixFree bf) (hbf_ne : ∀ m, bf m ≠ [])
    (hbad : ¬ cbcBad f bf l) :
    ¬ cbcBad (cbcShift f bf l delta) bf l := by
  have hfresh := cbcFresh_of_not_cbcBad f bf hbf_ne hbad
  rintro ⟨m, hm, m', hm', j, hj, j', hj', hkey, hvalue⟩
  rw [cbcInput_cbcShift f bf delta hbf_pf hbf_ne hfresh hm hj,
    cbcInput_cbcShift f bf delta hbf_pf hbf_ne hfresh hm' hj'] at hvalue
  exact hbad ⟨m, hm, m', hm', j, hj, j', hj', hkey, hvalue⟩

/-- Every queried message's MAC is translated by its assigned delta. -/
theorem cbcState_cbcShift (f : X -> X) (bf : M -> List X)
    {l : List M} (delta : ↑l.toFinset -> X)
    (hbf_pf : PrefixFree bf) (hbf_ne : ∀ m, bf m ≠ [])
    (hfresh : cbcFresh f bf l) {s : M} (hs : s ∈ l.toFinset) :
    cbcState (cbcShift f bf l delta) (bf s) =
      cbcState f (bf s) + delta ⟨s, hs⟩ := by
  have hinj := cbcLastInput_injOn f bf hbf_ne hbf_pf hfresh
  have hsl : s ∈ l := List.mem_toFinset.mp hs
  have hpos : 0 < (bf s).length := List.length_pos_of_ne_nil (hbf_ne s)
  have hshift := cbcShift_lastInput f bf l delta hinj ⟨s, hs⟩
  rw [cbcState_eq_f_lastInput (cbcShift f bf l delta) (bf s) (hbf_ne s),
    cbcInput_cbcShift f bf delta hbf_pf hbf_ne hfresh hsl (by omega),
    show cbcInput f (bf s) ((bf s).length - 1) =
      cbcLastInput f bf s from rfl, hshift]
  congr 1
  exact (cbcState_eq_f_lastInput f (bf s) (hbf_ne s)).symm

theorem cbcShift_zero (f : X -> X) (bf : M -> List X) (l : List M) :
    cbcShift f bf l 0 = f :=
  Counting.multiShift_zero _ f

/-- Terminal shifts compose additively because the first shift preserves all
terminal call-site inputs. -/
theorem cbcShift_cbcShift (f : X -> X) (bf : M -> List X)
    {l : List M} (delta delta' : ↑l.toFinset -> X)
    (hbf_pf : PrefixFree bf) (hbf_ne : ∀ m, bf m ≠ [])
    (hfresh : cbcFresh f bf l) :
    cbcShift (cbcShift f bf l delta) bf l delta' =
      cbcShift f bf l (delta + delta') := by
  have hsites :
      (fun s : ↑l.toFinset =>
        cbcLastInput (cbcShift f bf l delta) bf s.1) =
      fun s : ↑l.toFinset => cbcLastInput f bf s.1 :=
    funext fun s =>
      cbcInput_cbcShift f bf delta hbf_pf hbf_ne hfresh
        (List.mem_toFinset.mp s.2)
        (by have := List.length_pos_of_ne_nil (hbf_ne s.1); omega)
  show Counting.multiShift
      (fun s : ↑l.toFinset =>
        cbcLastInput (cbcShift f bf l delta) bf s.1) delta'
      (cbcShift f bf l delta) = _
  rw [hsites]
  exact Counting.multiShift_multiShift _ delta delta' f

namespace Plumbing

/-- Balanced MAC fibers conditioned on a shift-stable freshness predicate.
This is the counting heart of CR18 equation (6.2), printed p. 126. -/
theorem cbc_fiber_card (bf : M -> List X) {l : List M}
    (hbf_ne : ∀ m, bf m ≠ []) (hbf_pf : PrefixFree bf)
    (P : (X -> X) -> Prop) [DecidablePred P]
    (hPfresh : ∀ f, P f -> cbcFresh f bf l)
    (hPshift : ∀ (delta : ↑l.toFinset -> X) (f : X -> X),
      P f -> P (cbcShift f bf l delta))
    (a : ↑l.toFinset -> X) :
    (Finset.univ.filter (fun f : X -> X =>
        (∀ s : ↑l.toFinset,
          cbcState f (bf s.1) = a s) ∧ P f)).card
      * Fintype.card X ^ l.toFinset.card =
        (Finset.univ.filter (fun f : X -> X => P f)).card := by
  classical
  have key := Counting.card_filter_shift_univ (A := ↑l.toFinset -> X)
    P (fun f s => cbcState f (bf s.1))
    (fun delta f => cbcShift f bf l delta)
    (fun delta f hf => hPshift delta f hf)
    (fun delta f hf => funext fun s => by
      show cbcState (cbcShift f bf l delta) (bf s.1) =
        cbcState f (bf s.1) + delta s
      rw [cbcState_cbcShift f bf delta hbf_pf hbf_ne
        (hPfresh f hf) s.2])
    (fun delta delta' f hf =>
      cbcShift_cbcShift f bf delta delta' hbf_pf hbf_ne
        (hPfresh f hf))
    (fun f _ => cbcShift_zero f bf l) a
  rw [Fintype.card_fun, Fintype.card_coe] at key
  rw [← key]
  congr 2
  ext f
  simp [funext_iff, and_comm]

end Plumbing

/-- **CR18's second proof sentence, in mass form** (printed pp. 126–127):
"Conditioned on this event (i.e., on `A_i = 0`), all outputs are uniformly
random, except of course that for identical inputs (messages) the outputs are
also identical."  Repeated messages are represented once by `l.toFinset`, so
consistency on repeats is built into both events. -/
theorem notBad_implies_uniform_outputs [Nontrivial M]
    (bf : M -> List X) (hbf : PrefixFree bf) (l : List M)
    (a : ↑l.toFinset -> X) :
    (Distribution.uniform (X -> X)).mass (fun f =>
        (∀ s : ↑l.toFinset, cbcState f (bf s.1) = a s) ∧
          ¬ cbcBad f bf l) =
      (Distribution.uniform (M -> X)).mass (fun g =>
        ∀ s : ↑l.toFinset, g s.1 = a s) *
      (Distribution.uniform (X -> X)).mass (fun f =>
        ¬ cbcBad f bf l) := by
  classical
  let Good : (X -> X) -> Prop := fun f => ¬ cbcBad f bf l
  apply Distribution.uniform_mass_eq_mass_mul_mass_of_card_mul_eq
  have hne : ∀ m, bf m ≠ [] := hbf.ne_nil
  have hfiber := Plumbing.cbc_fiber_card bf hne hbf Good
    (fun f hf => cbcFresh_of_not_cbcBad f bf hne hf)
    (fun delta f hf => not_cbcBad_cbcShift f bf delta hbf hne hf) a
  have hcard : l.toFinset.card ≤ Fintype.card M := Finset.card_le_univ _
  dsimp only [Good] at hfiber
  rw [Fintype.card_fun,
    Counting.card_function_fiber_finset l.toFinset a]
  rw [← hfiber]
  conv_lhs =>
    rw [show Fintype.card M =
      (Fintype.card M - l.toFinset.card) + l.toFinset.card from
        (Nat.sub_add_cancel hcard).symm, pow_add]
  ac_rfl

/-! ## CR18 equation (6.2), printed p. 126: the conditional equivalence

"One can define an MBO `A_i` on the system `CBC R_{n,n}` … resulting in the
system `ĈBC R_{n,n}`, such that `(ĈBC R_{n,n}) ⊨ V_n`" (printed p. 126).  The
augmented object is the joint law of the CBC chain and its own collision
condition; the relation is Maurer13b Definition 13 (printed p. 3153), landed as
`PDG.CondEquiv`.

The two steps CR18 asserts are already proved above —
`notBad_implies_distinct_lastInputs` (its first proof sentence) and
`notBad_implies_uniform_outputs` (its second, in mass form).  What is left is
the reading: at a fixed message list the interaction of a function evaluator is
its list of query/answer pairs, so both sides of Definition 13's product form
are masses of *evaluation* events, and the mass identity is the product form.
-/

section CondEquiv

open System

/-- **The interaction of a function evaluator with a fixed query list.**  A
function evaluator answers every query (`PDS.answer_functionEvaluator`), so the
CR18 Definition 3.7 interaction with `playQueries l` (Lanzenberger fn. 6) is
the list of query/answer pairs of `l`, and it carries exactly the values of the
sampled function on `l`. -/
theorem transcript_functionEvaluator_playQueries {A B : Type u} (h : A → B) (l : List A) :
    ∀ n, n ≤ l.length →
      DDE.Total.transcript (functionEvaluator h) (DDE.Total.playQueries l) n
        = (l.take n).map (fun m => (m, some (h m))) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      have hlt : n < l.length := hn
      have hik := ih (Nat.le_of_succ_le hn)
      have hlen :
          (DDE.Total.transcript (functionEvaluator h) (DDE.Total.playQueries l) n).length = n := by
        rw [hik, List.length_map, List.length_take]
        omega
      have hq : DDE.Total.playQueries (Y := B) l
          (DDE.Total.transcript (functionEvaluator h) (DDE.Total.playQueries l) n)↓ᵧ
          = some l[n] := by
        show l[_]? = _
        simp only [transcriptOutputs, List.length_map, hlen]
        exact List.getElem?_eq_getElem hlt
      rw [DDE.Total.transcript_succ_of_query _ _ hq, hik, PDS.answer_functionEvaluator,
        List.take_add_one, List.getElem?_eq_getElem hlt]
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]

@[simp] theorem transcript_functionEvaluator_playQueries_length {A B : Type u}
    (h : A → B) (l : List A) :
    DDE.Total.transcript (functionEvaluator h) (DDE.Total.playQueries l) l.length
      = l.map (fun m => (m, some (h m))) := by
  rw [transcript_functionEvaluator_playQueries h l l.length le_rfl, List.take_length]

/-- **The interaction determines the sampled function on the queried
messages, and nothing else.**  Two evaluators produce the same fixed-query-list
interaction exactly when they agree on the messages of the list, so the fiber
of the interaction is an evaluation event of the shape
`notBad_implies_uniform_outputs` speaks about. -/
theorem map_pair_eq_iff_forall_toFinset {A B : Type u} [DecidableEq A]
    (h h₀ : A → B) (l : List A) :
    l.map (fun m => (m, some (h m))) = l.map (fun m => (m, some (h₀ m)))
      ↔ ∀ s : ↑l.toFinset, h s.1 = h₀ s.1 := by
  rw [List.map_inj_left]
  constructor
  · intro hm s
    have := hm s.1 (List.mem_toFinset.mp s.2)
    simpa using this
  · intro hm m hml
    have := hm ⟨m, List.mem_toFinset.mpr hml⟩
    simpa using this

/-- **CR18's augmented real system `ĈBC R_{n,n}`** (printed p. 126): "One can
define an MBO `A_i` on the system `CBC R_{n,n}` … resulting in the system
`ĈBC R_{n,n}`."  The joint law of Lanzenberger Definition 2.20's pair — the CBC
chain built from the sampled round function, together with *that* round
function's collision condition — so the system and the condition are correlated
exactly as CR18's `A_i` prescribes.

It is a pushforward of the uniform round function and not a `PDS.adjoin`,
because the condition reads the round function, which the CBC chain does not
determine. -/
noncomputable def cbcGameLaw (bf : M → List X) : PDG M X :=
  Distribution.fTransform
    (fun f : X → X =>
      ((System.functionEvaluator fun m : M => cbcState f (bf m), cbcCondition f bf) :
        System.DDG M X))
    (Distribution.uniform (X → X))

theorem nonNeg_cbcGameLaw (bf : M → List X) : (cbcGameLaw bf).NonNeg :=
  Probability.Distribution.uniform_nonNeg.fTransform _

@[simp] theorem weight_cbcGameLaw (bf : M → List X) : (cbcGameLaw bf).weight = 1 := by
  rw [cbcGameLaw, Distribution.weight_fTransform, Distribution.weight_uniform]

/-- **The forgetting law**: dropping CR18's MBO from `ĈBC R_{n,n}` returns
`CBC R_{n,n}`, the law the realization equation identifies
(`cbcConverter_smul_Rnn`).  This is what ties the augmented object of equation
(6.2) to the converter of Theorem 6.1. -/
@[simp] theorem forget_cbcGameLaw (bf : M → List X) :
    PDG.forget (cbcGameLaw bf) = cbcFunctionLaw bf := by
  rw [cbcGameLaw, cbcFunctionLaw, PDG.forget, Distribution.fTransform_fTransform]
  rfl

/-- Winning CR18's collision game at a fixed message list is exactly the
collision event of the sampled round function on that list: a function
evaluator refuses nothing, so the answered history is the whole list. -/
theorem won_cbcGameLaw_atom (f : X → X) (bf : M → List X) (l : List M) :
    System.Won
        ((System.functionEvaluator fun m : M => cbcState f (bf m), cbcCondition f bf) :
          System.DDG M X)
        (System.DDE.Total.playQueries l) l.length ↔ cbcBad f bf l := by
  show System.answeredQueries _ ∈ _ ↔ _
  rw [answeredQueries_transcript_playQueries_keptPrefix,
    keptPrefix_functionEvaluator]
  exact Iff.rfl

/-- The not-won slice of CR18's collision game at a fixed message list, as a
mass over round functions. -/
theorem notWonLaw_cbcGameLaw_apply (bf : M → List X) (l : List M)
    (t : List (M × Option X)) :
    PDG.notWonLaw (System.DDE.Total.playQueries l) l.length (cbcGameLaw bf) t
      = (Distribution.uniform (X → X)).mass (fun f =>
          ¬ cbcBad f bf l ∧ l.map (fun m => (m, some (cbcState f (bf m)))) = t) := by
  rw [PDG.notWonLaw_apply, cbcGameLaw, Distribution.mass_fTransform]
  refine Distribution.mass_congr _ fun f => ?_
  rw [won_cbcGameLaw_atom, transcript_functionEvaluator_playQueries_length]

theorem notWonMass_cbcGameLaw (bf : M → List X) (l : List M) :
    PDG.notWonMass (System.DDE.Total.playQueries l) l.length (cbcGameLaw bf)
      = (Distribution.uniform (X → X)).mass (fun f => ¬ cbcBad f bf l) := by
  rw [PDG.notWonMass_eq_mass_not_won, cbcGameLaw, Distribution.mass_fTransform]
  exact Distribution.mass_congr _ fun f => not_congr (won_cbcGameLaw_atom f bf l)

/-- The ideal object's transcript law at a fixed message list, as a mass over
functions: `V_n` answers a fresh uniform value per new message, so its
interaction is an evaluation event of the sampled function. -/
theorem trLawFullyDefined_Vn_apply (l : List M) (t : List (M × Option X)) :
    PDS.trLawFullyDefined (System.DDE.Total.playQueries l) l.length (Vn M X) t
      = (Distribution.uniform (M → X)).mass (fun g =>
          l.map (fun m => (m, some (g m))) = t) := by
  rw [PDS.trLawFullyDefined, Vn, PDS.urf, Distribution.fTransform_fTransform,
    Distribution.fTransform_apply_eq_mass]
  refine Distribution.mass_congr _ fun g => ?_
  rw [Function.comp_apply, transcript_functionEvaluator_playQueries_length]

@[simp] theorem weight_Vn : (Vn M X).weight = 1 := by
  rw [Vn, PDS.urf, Distribution.weight_fTransform, Distribution.weight_uniform]

/-- **CR18 equation (6.2), printed p. 126** — the second of the six obligations
at `cbc_mac_constructs`, discharged: `(ĈBC R_{n,n}) ⊨ V_n`.

CR18's proof is two sentences, and both are proved above: prefix-freeness plus
`A_i = 0` makes the terminal round-function inputs distinct
(`notBad_implies_distinct_lastInputs`), and conditioned on `A_i = 0` the
outputs are uniform (`notBad_implies_uniform_outputs`).  What this declaration
adds is the reading of Maurer13b Definition 13's product form (printed p. 3153)
at a fixed message list: a function evaluator refuses nothing, so both sides of
the product form are masses of *evaluation* events on `l.toFinset`, and the
identity is exactly the mass identity already proved.

The case split is on whether the transcript `t` is realizable at all: if it is
not, both sides of the product form vanish, and if it is, its realizations are
the functions agreeing with one witness on the queried messages. -/
theorem cbc_condEquiv [Nontrivial M] (bf : M → List X) (hbf : PrefixFree bf) :
    PDG.CondEquiv (cbcGameLaw bf) (Vn M X) := by
  classical
  intro l
  ext t
  rw [Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, weight_Vn,
    one_mul, notWonLaw_cbcGameLaw_apply, notWonMass_cbcGameLaw,
    trLawFullyDefined_Vn_apply]
  by_cases hreal : ∃ h₀ : M → X, l.map (fun m => (m, some (h₀ m))) = t
  · obtain ⟨h₀, rfl⟩ := hreal
    rw [Distribution.mass_congr _ (Q := fun f =>
        (∀ s : ↑l.toFinset, cbcState f (bf s.1) = h₀ s.1) ∧ ¬ cbcBad f bf l)
      (fun f => by
        rw [and_comm]
        exact and_congr
          (map_pair_eq_iff_forall_toFinset (fun m => cbcState f (bf m)) h₀ l) Iff.rfl),
      Distribution.mass_congr (Distribution.uniform (M → X))
        (Q := fun g => ∀ s : ↑l.toFinset, g s.1 = h₀ s.1)
        (fun g => map_pair_eq_iff_forall_toFinset g h₀ l),
      notBad_implies_uniform_outputs bf hbf l (fun s => h₀ s.1), mul_comm]
  · push Not at hreal
    rw [Distribution.mass_eq_zero_of_forall_not _ (fun f hf => hreal _ hf.2),
      Distribution.mass_eq_zero_of_forall_not (Distribution.uniform (M → X))
        (fun g hg => hreal g hg), mul_zero]

end CondEquiv

/-! ## CR18 Theorem 6.1 as a construction statement

The printed statement is an arrow with a superscript, `[r]R_{n,n} --θ_r CBC-->
(θ_r V_n)^{ε_r}` (printed p. 126): CR18 Definition 5.4's construction relation
into §5.2.3's `ε`-relaxation.  On this carrier that is
`AbstractCryptography.ApproximatelyConstructs` over `Phi`, with the converter
the composite `Σ`-element `θ_r · CBC` and the two endpoints the on-ramped
typed resources.  Everything the abstract layer needs is an instance here:
`Monoid ↥converterMonoidAt`, `MulAction ↥converterMonoidAt Phi`,
`PseudoEMetricSpace Phi` (`MetricFullyDefined.lean`) and
`IsNonexpandingSMul ↥converterMonoidAt Phi` (same file).
-/

/-- **CR18 Theorem 6.1's error term** (printed p. 126): `ε_r = ½ r² 2^{-n}`,
written at `|X|` in place of `2^n`. -/
noncomputable def cbcEpsilon (X : Type u) [Fintype X] (r : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((r : ℝ) ^ 2 / (2 * (Fintype.card X : ℝ)))

/-- The assumed resource `[r]R_{n,n}` (printed p. 126), as a Φ element. -/
noncomputable def assumedResource (X : Type u) [Fintype X] [DecidableEq X]
    [Nonempty X] (r : ℕ) : Phi.{u} :=
  queryLimit r • (ofTyped (Rnn X) : Phi.{u})

/-- The constructed resource `θ_r V_n` (printed p. 126), as a Φ element. -/
noncomputable def constructedResource (bf : M → List X) (r : ℕ) : Phi.{u} :=
  theta bf r • (ofTyped (Vn M X) : Phi.{u})

/-- CR18's constructing converter `θ_r CBC` (printed p. 126), as one element of
the metric-facing `Σ`. -/
noncomputable def cbcRestricted (bf : M → List X) (r : ℕ) : ↥converterMonoidAt.{u} :=
  theta bf r * cbcConverter bf

/-- **The abstract-layer shape of CR18 Theorem 6.1** (printed p. 126): "For
`θ_r` defined as above, if the block-former of the `CBC`-converter is
prefix-free, we have (for any `r`) `[r]R_{n,n} --θ_r CBC--> (θ_r V_n)^{ε_r}`
for `ε_r = ½ r² 2^{-n}`."

**Status: this is a SCAFFOLD, not the theorem.**  Theorem 6.1's mathematics is
assumed here in full, as the hypothesis `hcbc`; what the declaration supplies
is the abstract-layer *shape* of the printed statement — the construction
arrow with its `ε`-superscript, `AbstractCryptography.ApproximatelyConstructs`
over `Phi` at `Σ := ↥converterMonoidAt` — and nothing beyond it.  The proof is
a single application of `constructs_singleton_epsilonRelaxation_iff`, which is
an `Iff`: hypothesis and conclusion are interderivable in one step, so the
statement is a change of notation applied to its own hypothesis.  No CBC lemma
of this file is invoked, and `_hbf` is unused.

The shape is still worth landing — it is what the abstract layer's composition
calculus consumes, and `cbc_mac_trans` is that receipt — but it is not
evidence about CBC-MAC, and it must not be read or recorded as CR18
Theorem 6.1 having been proved.

CR18's own proof structure is what `hcbc` stands for: the printed proof
produces `⟨θ_r CBC [r]R_{n,n} | θ_r V_n⟩ ≤ Γ(b θ_r ĈBC R_{n,n}) ≤ ½ r² 2^{-n}`
(printed p. 127) and reads the arrow off it.  In the printed order, `hcbc`
decomposes into six obligations, of which **four are open — 2, 4, 6, and
the `θ_r` half of 3**:

1. **LANDED.**  The realization equation — that `cbcConverter bf` applied to
   the on-ramped round function is the on-ramped system whose answer to `m` is
   `cbcState f (bf m)` — as `attachEngineFully_cbcRound_univ` at a
   deterministic round function and `cbcConverter_smul_Rnn` at Φ;
2. **OPEN.**  Equation (6.2), printed p. 126, as `PDG.CondEquiv`: the mass
   identity `notBad_implies_uniform_outputs` above, read through
   `PDG.condEquiv_iff_condProb`;
3. **HALF OPEN.**  Equation (6.3), printed p. 127: the general transport is
   landed as `PDG.condEquiv_fTransform`
   (`Technique/ConditionalEquivalence.lean`), but its landed corollary
   `PDG.condEquiv_filterQueries` is the `[r]` instance of printed p. 128
   (Theorem 6.2's step), *not* this `θ_r` instance.  The `θ_r` instance — a
   domain filter at a block-count predicate, needing the filter's admitted
   schedule — is open;
4. **OPEN.**  Equation (6.1), printed p. 126, which the page writes hatted,
   `θ_r ĈBC = θ_r ĈBC[r]` — the MBO-augmented converter, and printed p. 127
   applies it to the augmented system.  It is also CR18 §5.5's coherence
   equation (printed p. 122), and therefore the hypothesis
   `cbc_mac_parameterized_of_coherence` has to assume;
5. **LANDED.**  Theorem 4.17's step, printed p. 127, as
   `PDG.advFullyDefined_forget_le_blindSupWinProb_of_condEquiv`
   (`Technique/BlindWinning.lean`);
6. **OPEN.**  Lemma 4.18's step, printed p. 127: the blind winning probability
   of the collision game is at most `½ r² 2^{-n}`.

The prefix-freeness hypothesis is carried because it is Theorem 6.1's own, and
because obligation 2's proved half (`notBad_implies_distinct_lastInputs`)
consumes it; it is unused by this declaration's own proof. -/
theorem cbc_mac_constructs [Nontrivial M] (bf : M → List X) (r : ℕ)
    (_hbf : PrefixFree bf)
    (hcbc : edist (cbcRestricted bf r • assumedResource X r)
      (constructedResource bf r) ≤ cbcEpsilon X r) :
    ({assumedResource X r} : Specification Phi.{u})
      —[cbcRestricted bf r; cbcEpsilon X r]→
        ({constructedResource bf r} : Specification Phi.{u}) :=
  constructs_singleton_epsilonRelaxation_iff.mpr hcbc

/-! ## What the abstract layer gives, and at what price

The INSTANTIATION RULE asks an application to carry at least one consequence
derived by a LANDED ABSTRACT THEOREM, as the receipt that the instantiation is
real.  `cbc_mac_trans` is that receipt, and it is the only one: it takes
`cbc_mac_constructs` as its input and closes by
`AbstractCryptography.Constructs.epsilonRelaxation_trans`.

Nothing here is *free* in the sense of costing nothing beyond the endpoint.
Both corollaries inherit `hcbc` — Theorem 6.1's whole mathematics — through
`cbc_mac_constructs`, and `cbc_mac_parameterized_of_coherence` inherits
obligation 4 on top of it.  An earlier version of this file carried a
`cbc_mac_parameterized` whose proof term was its own hypothesis:
`ParameterizedConstruction` unfolds definitionally to the family of
construction judgments, so that statement closed by `Iff.rfl`, applied no
abstract theorem, and was a renaming.  It is deleted.  Nothing about CR18 §5.5
(printed p. 122) follows from the endpoint's shape alone; what makes the
parameterized reading a theorem is the coherence equation, and that equation is
open. -/

/-- **Composition**: whatever is constructed from `θ_r V_n` is constructed from
`[r]R_{n,n}` by the composite converter, with the budgets added.  Derived by
`AbstractCryptography.Constructs.epsilonRelaxation_trans` applied to
`cbc_mac_constructs` — the landed statement carries its own attribution and
page — and the instance it consumes is `IsNonexpandingSMul ↥converterMonoidAt
Phi` (`RandomSystems/System/MetricFullyDefined.lean`).

The distance bound `hcbc` is inherited, so this is a consequence of the
endpoint and not of anything cheaper.  (`constructs_epsilonRelaxation_trans_phi`
in that same file is the same abstract theorem read at the larger submonoid
`nonexpandingConverters`; using it here would mean pushing both converters
across `converterMonoidAt_le_nonexpandingConverters` and pulling the result
back, so the abstract statement is invoked directly instead.) -/
theorem cbc_mac_trans [Nontrivial M] {bf : M → List X} {r : ℕ}
    {π' : ↥converterMonoidAt.{u}} {ε' : ℝ≥0∞} {T : Specification Phi.{u}}
    (hbf : PrefixFree bf)
    (hcbc : edist (cbcRestricted bf r • assumedResource X r)
      (constructedResource bf r) ≤ cbcEpsilon X r)
    (h' : ({constructedResource bf r} : Specification Phi.{u}) —[π'; ε']→ T) :
    ({assumedResource X r} : Specification Phi.{u})
      —[π' * cbcRestricted bf r; cbcEpsilon X r + ε']→ T :=
  Constructs.epsilonRelaxation_trans (cbc_mac_constructs bf r hbf hcbc) h'

/-- **CR18 §5.5's parameterized reading, under its own coherence equation** —
equation (5.6), printed p. 122: `φ_r R --ψ_r α--> (ψ_r S)^{f_r}` with the
constructing converter `α` quantified once, outside the family ("the
constructing converter `α` does not depend on `r`").  Theorem 6.1 is printed in
exactly that shape, with `φ_r = [r]`, `ψ_r = θ_r` and `α = CBC`.

What §5.5 buys is the *collapse*: under `ψ_r α φ_r = ψ_r α` the filter on the
assumed resource drops out, and the family becomes a statement about the
**unrestricted** `R_{n,n}`.  That is the content here, and it is
`AbstractCryptography.parameterizedConstruction_iff_of_coherence` applied to
the family of `cbc_mac_constructs` instances.

`coherence` is CR18's equation (6.1), printed p. 126, read at the unaugmented
converter; the page writes it hatted, `θ_r ĈBC = θ_r ĈBC[r]`, because the proof
works on the MBO-augmented converter.  It is **open** (obligation 4 at
`cbc_mac_constructs`) and is assumed here, as is `hcbc`.  This corollary is
therefore a statement about what the abstract layer would yield, not a landed
consequence of anything proved in this file. -/
theorem cbc_mac_parameterized_of_coherence [Nontrivial M] (bf : M → List X)
    (hbf : PrefixFree bf)
    (coherence : ∀ r : ℕ, theta (X := X) bf r * cbcConverter bf * queryLimit.{u} r
      = theta (X := X) bf r * cbcConverter bf)
    (hcbc : ∀ r : ℕ, edist (cbcRestricted bf r • assumedResource X r)
      (constructedResource bf r) ≤ cbcEpsilon X r) :
    ∀ r : ℕ, ({(ofTyped (Rnn X) : Phi.{u})} : Specification Phi.{u})
      —[cbcRestricted bf r; cbcEpsilon X r]→
        ({constructedResource bf r} : Specification Phi.{u}) :=
  (parameterizedConstruction_iff_of_coherence
    (φ := fun r : ℕ => queryLimit.{u} r) (ψ := fun r : ℕ => theta (X := X) bf r)
    (π := cbcConverter bf) (f := fun r : ℕ => cbcEpsilon X r)
    (R := (ofTyped (Rnn X) : Phi.{u})) (S := (ofTyped (Vn M X) : Phi.{u}))
    coherence).mp (fun r => cbc_mac_constructs bf r hbf (hcbc r))

end RandomSystems.CBCMAC
