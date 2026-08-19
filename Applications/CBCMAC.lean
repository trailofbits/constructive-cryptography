/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.ConverterEntry
import RandomSystems.System.MetricFullyDefined
import RandomSystems.System.RandomObjects
import RandomSystems.System.FilterPhi
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

The bound is not bookkeeping.  CR18 Definition 3.8's finite request bound
(printed p. 62) is what makes a converter a member of the metric-facing `Σ`,
and `cbcRequestsBounded` discharges it with the largest block count the block
former ever emits — a number that exists because `M` is finite.  Over an
unbounded message alphabet the CBC converter is not a member of this `Σ` at
all.

## What is proved here, and what is not

Proved:

* the CBC converter is a member of `↥converterMonoidAt` (`cbcProtocol`), and so
  are CR18's two restrictions `θ_r` (`theta`) and `[r]` (`queryLimit`);
* CR18's first proof sentence, printed p. 126 — prefix-freeness plus "no
  non-trivial collision" makes the terminal round-function inputs of distinct
  queried messages distinct (`notBad_implies_distinct_lastInputs`);
* CR18's second proof sentence, printed pp. 126–127, in mass form — conditioned
  on no non-trivial collision the CBC outputs have exactly the law of a uniform
  random function (`notBad_implies_uniform_outputs`), through the
  re-randomization of the terminal call sites;
* the crossing from the distance to Theorem 6.1's construction statement, and
  the composition and parameterization corollaries that follow from the
  abstract layer with no further proof.

Not proved, and stated as the hypothesis `hcbc` of the endpoint: the
distinguishing bound itself.  Its remaining obligations are listed at
`cbc_mac_constructs`.
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

/-! ## The CBC converter as a member of the metric-facing `Σ`

The converter is written as a history function — the current message and the
round-function answers of the round so far — and enters `Σ` through the
library's one crossing, `RandomSystems.protocolEngine_mem_converterMonoidAt`.
No `ProtocolFn` and no `DDC` appears in any statement below.
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
    System.ProtocolInnerTotal (cbcRound bf) := by
  intro us ys x hx o
  have hne : us ≠ [] := by
    by_contra hnil
    rw [cbcRound, dif_neg (by simpa using hnil)] at hx
    exact absurd hx (by simp)
  rw [cbcRound, dif_pos hne]
  dsimp only
  split <;> exact ⟨⟩

/-- The largest number of blocks the block former ever emits.  It exists
because `M` is finite — this is where the F-1 ruling's bounded message space is
spent. -/
noncomputable def blockBound (bf : M → List X) : ℕ :=
  Finset.univ.sup fun m => (bf m).length

theorem length_le_blockBound (bf : M → List X) (m : M) :
    (bf m).length ≤ blockBound bf :=
  Finset.le_sup (f := fun m => (bf m).length) (Finset.mem_univ m)

/-- **CR18 Definition 3.8's finite request bound for CBC** (printed p. 62): a
round asks the round function at most `blockBound bf` questions, one per block.

Over an infinite message alphabet no such constant exists and CBC is not a
member of this `Σ`; the bounded message space of the F-1 ruling is exactly what
supplies it. -/
theorem cbcRound_requestsBounded (bf : M → List X) :
    System.ProtocolRequestsBounded (cbcRound bf) (blockBound bf) := by
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
    exact lt_of_lt_of_le hlt (length_le_blockBound bf _)
  · rw [if_neg hlt] at hx
    exact absurd hx (by simp)

/-- **The CBC converter, as the one converter notion an application names**:
the element of `↥converterMonoidAt` that attaches CBC at the round function's
interface. -/
noncomputable def cbcProtocol (bf : M → List X) : ↥converterMonoidAt.{u} :=
  ⟨attachAt {q : Uni.{u} | q.1 = X} (System.protocolEngine X X (cbcRound bf)),
    protocolEngine_mem_converterMonoidAt _ _ (cbcRound_innerTotal bf)
      (cbcRound_requestsBounded bf)⟩

/-- The CBC converter reaches only into the round function's interface. -/
theorem cbcProtocol_requestsWithin (bf : M → List X) :
    System.RequestsWithin {q : Uni.{u} | q.1 = X}
      (System.protocolEngine X X (cbcRound bf)) :=
  System.requestsWithin_protocolEngine _ fun _ => rfl

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

/-- The input supplied to the round function at block position `j`. -/
def cbcInput (f : X -> X) (bs : List X) (j : Nat) : X :=
  cbcState f (bs.take j) + bs.getD j 0

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
/-- Appending one block performs one more round-function call. -/
theorem cbcState_concat (f : X -> X) (bs : List X) (b : X) :
    cbcState f (bs ++ [b]) = f (cbcState f bs + b) := by
  simp only [cbcState, List.foldl_concat]

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

/-! ## CR18 Theorem 6.1 as a construction statement

The printed statement is an arrow with a superscript, `[r]R_{n,n} --θ_r CBC-->
(θ_r V_n)^{ε_r}` (printed p. 126): CR18 Definition 5.4's construction relation
into §5.2.3's `ε`-relaxation.  On this carrier that is
`AbstractCryptography.ApproximatelyConstructs` over `Phi`, with the protocol
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
  theta bf r * cbcProtocol bf

/-- **CR18 Theorem 6.1** (printed p. 126): "For `θ_r` defined as above, if the
block-former of the `CBC`-converter is prefix-free, we have (for any `r`)
`[r]R_{n,n} --θ_r CBC--> (θ_r V_n)^{ε_r}` for `ε_r = ½ r² 2^{-n}`."

**Status.**  The construction statement is derived here from the distance
bound `hcbc`, which is CR18's own proof structure: the printed proof produces
`⟨θ_r CBC [r]R_{n,n} | θ_r V_n⟩ ≤ Γ(b θ_r ĈBC R_{n,n}) ≤ ½ r² 2^{-n}`
(printed p. 127) and reads the arrow off it.  What is *not* discharged in this
file is `hcbc`.  Its remaining obligations, in the printed order, are:

1. the realization equation — that `cbcProtocol bf` applied to the on-ramped
   round function is the on-ramped system whose answer to `m` is
   `cbcState f (bf m)`.  This is a drive computation for
   `System.attachEngineFully` and is the one obligation with no landed
   counterpart;
2. equation (6.2), printed p. 126, as `PDG.CondEquiv`: the mass identity
   `notBad_implies_uniform_outputs` above, read through
   `PDG.condEquiv_iff_condProb`;
3. equation (6.3), printed p. 127 — landed as
   `PDG.condEquiv_fTransform` (`Technique/ConditionalEquivalence.lean`), whose
   `θ_r` instance needs the filter's admitted schedule;
4. equation (6.1), printed p. 126, `θ_r CBC = θ_r CBC[r]`;
5. Theorem 4.17's step, printed p. 127 — landed as
   `PDG.advFullyDefined_forget_le_blindSupWinProb_of_condEquiv`
   (`Technique/BlindWinning.lean`);
6. Lemma 4.18's step, printed p. 127: the blind winning probability of the
   collision game is at most `½ r² 2^{-n}`.

The prefix-freeness hypothesis is carried because it is Theorem 6.1's own, and
because obligation 2's proved half (`notBad_implies_distinct_lastInputs`)
consumes it. -/
theorem cbc_mac_constructs [Nontrivial M] (bf : M → List X) (r : ℕ)
    (_hbf : PrefixFree bf)
    (hcbc : edist (cbcRestricted bf r • assumedResource X r)
      (constructedResource bf r) ≤ cbcEpsilon X r) :
    ({assumedResource X r} : Specification Phi.{u})
      —[cbcRestricted bf r; cbcEpsilon X r]→
        ({constructedResource bf r} : Specification Phi.{u}) :=
  constructs_singleton_epsilonRelaxation_iff.mpr hcbc

/-! ## What the abstract layer then gives for free

Neither corollary proves anything about CBC-MAC: each is a landed abstract
theorem applied to `cbc_mac_constructs`.  That is the point of stating the
theorem as a construction. -/

/-- **Composition, for free**: whatever is constructed from `θ_r V_n` is
constructed from `[r]R_{n,n}` by the composite protocol, with the budgets
added.  Proved by `AbstractCryptography.Constructs.epsilonRelaxation_trans` and
nothing else — the landed statement carries its own attribution and page — and
the instance it consumes is `IsNonexpandingSMul ↥converterMonoidAt Phi`
(`RandomSystems/System/MetricFullyDefined.lean`). -/
theorem cbc_mac_trans [Nontrivial M] {bf : M → List X} {r : ℕ}
    {π' : ↥converterMonoidAt.{u}} {ε' : ℝ≥0∞} {T : Specification Phi.{u}}
    (h : ({assumedResource X r} : Specification Phi.{u})
      —[cbcRestricted bf r; cbcEpsilon X r]→
        ({constructedResource bf r} : Specification Phi.{u}))
    (h' : ({constructedResource bf r} : Specification Phi.{u}) —[π'; ε']→ T) :
    ({assumedResource X r} : Specification Phi.{u})
      —[π' * cbcRestricted bf r; cbcEpsilon X r + ε']→ T :=
  Constructs.epsilonRelaxation_trans h h'

/-- **CR18 §5.5's parameterized construction, for free** — equation (5.6),
printed p. 122: `φ_r R --ψ_r α--> (ψ_r S)^{f_r}` with the constructing
converter `α` quantified once, outside the family ("the constructing converter
`α` does not depend on `r`").  Theorem 6.1 is printed in exactly that shape,
with `φ_r = [r]`, `ψ_r = θ_r` and `α = CBC`, and this is that reading: the
statement is `AbstractCryptography.ParameterizedConstruction` at our three
families, with no CBC-specific step. -/
theorem cbc_mac_parameterized [Nontrivial M] (bf : M → List X) (f : ℕ → ℝ≥0∞)
    (h : ∀ r : ℕ, ({assumedResource X r} : Specification Phi.{u})
      —[cbcRestricted bf r; f r]→
        ({constructedResource bf r} : Specification Phi.{u})) :
    ParameterizedConstruction (fun r : ℕ => queryLimit.{u} r)
      (fun r : ℕ => theta (X := X) bf r) (cbcProtocol bf) f
      (ofTyped (Rnn X) : Phi.{u}) (ofTyped (Vn M X) : Phi.{u}) :=
  h

end RandomSystems.CBCMAC
