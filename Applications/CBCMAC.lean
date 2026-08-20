/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.ConverterEntry
import RandomSystems.System.MetricFullyDefined
import RandomSystems.System.RandomObjects
import RandomSystems.System.Attainment
import RandomSystems.System.FilterPhi
import RandomSystems.System.ConverterClass
import RandomSystems.Technique.BlindWinning
import RandomSystems.Technique.ConditionalEquivalence
import AbstractCryptography.Metric.Epsilon
import AbstractCryptography.Specification.Parameterized
import Probability.Counting
import Mathlib.Data.List.GetD

/-!
# CR18 §6.2.3: CBC-MAC as a randomness expander

Cachin–Renner(–Maurer), *Lecture Notes on Cryptography*, §6.2.2–§6.2.3,
printed pp. 125–127.

Theorem 6.1, printed p. 126: "For `θ_r` defined as above, if the block-former
of the `CBC`-converter is prefix-free, we have (for any `r`)
`[r]R_{n,n} --θ_r CBC--> (θ_r V_n)^{ε_r}` for `ε_r = ½ r² 2^{-n}`."

The endpoint is `cbc_mac_constructs`; the distance `cbc_mac_distance` is an
intermediate, as on the printed page.  Nothing is assumed beyond
prefix-freeness.

The message alphabet is finite, so this is Theorem 6.1 at a bounded message
space.  Footnote 2, printed p. 125: "Note that because the input alphabet is
infinite, `V_n` can not be described as a probabilistic discrete system, i.e.,
as a probability distribution over deterministic systems" — and this carrier is
exactly such a distribution.  What the proof uses is a bound on encoding
length (`cbcRound_requestsBounded_of_length_le`), from which finiteness
follows.
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

/-! ## Review TODO

Cleanup identified during review; the comment pass of the first item is done.

* Reorder the declarations by dependency — base objects, block former,
  converters, elementary properties, security theorem, instantiation bridge,
  construction theorem — without changing the proved content.
* Put `Rnn` and `Vn` in a `section` with their shared ambient variables.
* Define all base objects and converters together, before proving anything
  about them.
* Add paper-facing local notation for `R_{n,n}`, `V_n` and `θ_r`.
* Add `HSMul (↥converterMonoidAt) (PDS M X) Phi` through the typed inclusion,
  plus the reduction theorem identifying it with the homogeneous action on
  `ofTyped S`; then drop the explicit `ofTyped`/`Phi` casts everywhere here.
* Settle the carrier: `Phi := PDS Uni Uni` is the full universal behaviour
  space, `typed : Set Phi` the untagged union of the images of each `PDS M X`.
* Let Lean infer universes instead of spelling `.{u}`, and alias
  `↥converterMonoidAt`.
* Redesign the Random Systems instantiation so DDS/PDS and DDC/PDC instantiate
  the abstract carrier/converter interface directly, with the action and the
  admissibility bookkeeping internal to the instance — so an application never
  builds an `attachAt` endomorphism or proves membership by hand, and
  `cbcDDC bf • Rnn X` elaborates.
* Promote `cbc_mac_distance_of_classDistance` into that instantiation: the
  abstract distance between two embedded typed systems, controlled by their
  native class distance `Δ`.
-/

/-! ## §6.2.2's two objects, at the bounded message space -/

/-- CR18's fixed-input-length uniform random function `R_{n,n}` (printed
p. 125). -/
noncomputable def Rnn (X : Type u) [Fintype X] [DecidableEq X] [Nonempty X] :
    PDS X X :=
  PDS.urf X X

/-- Definition 6.1's `V_n` (printed p. 125) at the bounded message space: a
fresh uniform value per new message, repeated consistently. -/
noncomputable def Vn (M X : Type u) [Fintype M] [DecidableEq M] [Fintype X]
    [DecidableEq X] [Nonempty X] : PDS M X :=
  PDS.urf M X

/-! ## §6.2.3's block former -/

/-- Printed p. 126: "it must be guaranteed that for no two distinct messages
`m₁` and `m₂`, the resulting block sequence (at the output of the block former)
for `m₁` is a prefix of the block sequence for `m₂`." -/
def PrefixFree (bf : M → List X) : Prop :=
  ∀ m m', m ≠ m' → ¬ (bf m <+: bf m')


/-! ## §6.2.3's CBC converter -/

/-- Printed p. 125: "`CBC` applies a block former to the message and then
digests the obtained block sequence block by block, each time invoking the
system at its right interface." -/
noncomputable def cbcRound (bf : M → List X) :
    List M × List (Option X) →. X ⊕ X := fun p =>
  if h : p.1 ≠ [] then
    let m := p.1.getLast h
    -- a refusal is read as the initial chaining value; stalling instead
    -- would violate CR18 Definition 3.8's request bound.
    let ys := p.2.map fun o => o.getD 0
    if ys.length < (bf m).length then
      Part.some (Sum.inl (ys.getLastD 0 + (bf m).getD ys.length 0))
    else
      Part.some (Sum.inr (ys.getLastD 0))
  else
    Part.none

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
distinct messages with equal encodings would have each encoding a prefix of the
other. -/
theorem PrefixFree.injective {bf : M → List X} (h : PrefixFree bf) :
    Function.Injective bf := by
  intro a b hab
  by_contra hne
  exact h a b hne (hab ▸ List.prefix_refl (bf a))

/-- Finiteness of the message space is a consequence, not an extra hypothesis:
a prefix-free block former of bounded length injects `M` into the block
sequences of length at most `B` over a finite block alphabet. -/
theorem finite_of_prefixFree_of_length_le {X' M' : Type u} [Fintype X']
    {bf : M' → List X'} {B : ℕ} (hbf : PrefixFree bf)
    (hB : ∀ m, (bf m).length ≤ B) : Finite M' := by
  -- read an encoding as its first `B` optional blocks
  have hi : Function.Injective (fun m => fun i : Fin B => (bf m)[(i : ℕ)]?) := by
    intro a b h
    -- equal tuples force equal encodings, and prefix-freeness is injectivity
    refine hbf.injective (List.ext_getElem? fun n => ?_)
    -- below `B` the tuples agree; above it both encodings have run out
    by_cases hn : n < B
    · exact congrFun h ⟨n, hn⟩
    · rw [List.getElem?_eq_none (le_trans (hB a) (by omega)),
        List.getElem?_eq_none (le_trans (hB b) (by omega))]
  -- so `M` injects into a finite type
  exact Finite.of_injective _ hi

/-- The accumulated number of blocks the block former has emitted. -/
def totalBlocks (bf : M → List X) (messages : List M) : ℕ :=
  (messages.map fun m => (bf m).length).sum

theorem totalBlocks_mono (bf : M → List X) {l₁ l₂ : List M} (h : l₁ <+: l₂) :
    totalBlocks bf l₁ ≤ totalBlocks bf l₂ := by
  obtain ⟨t, rfl⟩ := h
  simp [totalBlocks, List.map_append]

/-- The block total is additive: a further stretch of messages adds its own
blocks and nothing else.  `totalBlocks_mono` is the inequality this sharpens. -/
theorem totalBlocks_append (bf : M → List X) (l₁ l₂ : List M) :
    totalBlocks bf (l₁ ++ l₂) = totalBlocks bf l₁ + totalBlocks bf l₂ := by
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


/-- Having asked, CBC reacts to whatever the round function returns. -/
theorem cbcRound_innerTotal (bf : M → List X) :
    System.ConverterInnerTotal (cbcRound bf) := by
  intro us ys x hx o
  -- a request was issued, so the outer history was nonempty
  have hne : us ≠ [] := by
    by_contra hnil
    rw [cbcRound, dif_neg (by simpa using hnil)] at hx
    exact absurd hx (by simp)
  -- and then both branches of the block guard produce a reaction
  rw [cbcRound, dif_pos hne]
  dsimp only
  split <;> exact ⟨⟩

/-- The largest number of blocks the block former ever emits: the cheapest
witness for the length bound `cbcRound_requestsBounded_of_length_le` needs, and
the only place finiteness of the message space is spent. -/
noncomputable def blockBound (bf : M → List X) : ℕ :=
  Finset.univ.sup fun m => (bf m).length

theorem length_le_blockBound (bf : M → List X) (m : M) :
    (bf m).length ≤ blockBound bf :=
  Finset.le_sup (f := fun m => (bf m).length) (Finset.mem_univ m)

/-- Definition 3.8's finite request bound (printed p. 62), from the hypothesis
that carries it: a round asks one question per block of the current message. -/
theorem cbcRound_requestsBounded_of_length_le (bf : M → List X) {B : ℕ}
    (hB : ∀ m, (bf m).length ≤ B) :
    System.ConverterRequestsBounded (cbcRound bf) B := by
  intro us ys x hx
  -- a request was issued, so the outer history was nonempty
  have hne : us ≠ [] := by
    by_contra hnil
    rw [cbcRound, dif_neg (by simpa using hnil)] at hx
    exact absurd hx (by simp)
  rw [cbcRound, dif_pos hne] at hx
  dsimp only at hx
  -- the guard is "fewer answers so far than the current message has blocks",
  -- so the request index is below `(bf m).length`, hence below `B`
  by_cases hlt : (ys.map fun o => o.getD 0).length < (bf (us.getLast hne)).length
  · rw [if_pos hlt] at hx
    rw [List.length_map] at hlt
    exact lt_of_lt_of_le hlt (hB _)
  -- past the last block the round returns instead of asking
  · rw [if_neg hlt] at hx
    exact absurd hx (by simp)

/-- The request bound at the constant this file carries, `blockBound bf`. -/
theorem cbcRound_requestsBounded (bf : M → List X) :
    System.ConverterRequestsBounded (cbcRound bf) (blockBound bf) :=
  cbcRound_requestsBounded_of_length_le bf (length_le_blockBound bf)

/-- The converter of §6.2.3 (printed pp. 125–126) as an element of
`↥converterMonoidAt`: `CBC` is applied to `R_{n,n}` as a whole, which is
Definition 3.9's application (printed p. 62) through `attachAt_univ`. -/
noncomputable def cbcConverter (bf : M → List X) : ↥converterMonoidAt.{u} :=
  -- The whole face is forced, not a default: `attachEngineFully` hands a query
  -- outside the interface to the resource verbatim, and CBC owns queries
  -- addressed at `M` while its requests are addressed at `X`.  An interface
  -- holding only the round function's address would route every message past
  -- the converter, which refuses it, and the realization equation would fail.
  -- Where the engine *reaches* is the separate `cbcConverter_requestsWithin`.
  ⟨attachAt (Set.univ : Set Uni.{u}) (System.converterEngine X X (cbcRound bf)),
    converterEngine_mem_converterMonoidAt _ _ (cbcRound_innerTotal bf)
      (cbcRound_requestsBounded bf)⟩

/-- The CBC converter reaches only into the round function's interface. -/
theorem cbcConverter_requestsWithin (bf : M → List X) :
    System.RequestsWithin {q : Uni.{u} | q.1 = X}
      (System.converterEngine X X (cbcRound bf)) :=
  System.requestsWithin_converterEngine _ fun _ => rfl

section Realization

open System

/-- An on-ramped function answers its own value, whatever the history. -/
theorem answer_ofTyped_functionEvaluator {A B : Type u} (f : A → B)
    (xs : List Uni.{u}) (a : A) :
    answer (System.ofTyped (functionEvaluator f)) xs (encode A a)
      = some (encode B (f a)) := by
  set l₀ : List A := xs.filterMap decodeOption with hl₀
  -- the evaluator is defined on every nonempty history, so Definition 3.3's
  -- deletion pass (printed p. 58) keeps the whole decodable part of `xs`
  have hkept : keptPrefix (System.ofTyped (functionEvaluator f)) xs = l₀.map (encode A) := by
    rw [keptPrefix_ofTyped]
    congr 1
    refine keptPrefix_eq_self_of_mem_or_empty _ ?_
    rcases eq_or_ne l₀ [] with h | h
    · exact Or.inr h
    · exact Or.inl (by rw [dom_functionEvaluator]; exact h)
  have hne : l₀ ++ [a] ≠ [] := by simp
  -- extending it by `a` stays in the domain
  have hdom : (l₀ ++ [a]).map (encode A) ∈ dom (System.ofTyped (functionEvaluator f)) :=
    (mem_dom_ofTyped_encode hne).mpr (by rw [dom_functionEvaluator]; exact hne)
  -- so the answer is the evaluator's output there, which is `f a` whatever
  -- the history was
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

/-- Against a resource that answers `f x` to `x`, one CBC round digests the
current message's blocks one at a time and ends at `cbcState f bs`. -/
theorem cbcRound_runsTo (f : X → X) (bf : M → List X) (R : DDS Uni.{u} Uni.{u})
    (hR : ∀ (xs : List Uni.{u}) (x : X),
      answer R xs (encode X x) = some (encode X (f x)))
    (us : List M) (hne : us ≠ []) (bs : List X) (hbs : bf (us.getLast hne) = bs) :
    ∀ (d k : ℕ), k + d = bs.length →
      ∀ xs : List Uni.{u},
        ConverterRunsTo (cbcRound bf) R us (cbcRoundAnswers f bs k) xs
          (cbcState f bs) := by
  -- the induction runs on the blocks still to digest and carries the chain
  -- state in the round's own answer list, which is what makes the statement
  -- independent of the resource history the round starts from
  intro d
  induction d with
  -- no blocks left: the round stops, returning the last answer it holds,
  -- which is the chain value at the whole block list
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
  -- blocks left: the round asks at the block-`k` call-site input,
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
      -- the resource answers `f` of it, which is the chain value one block on,
      -- so the answer list grows by exactly the entry the induction expects
      · rw [hR xs (cbcInput f bs k)]
        simp only [Option.bind_some, decodeOption_encode]
        rw [← cbcState_take_succ f bs hklt, ← cbcRoundAnswers_succ]
        exact ih (k + 1) (by omega) _

/-- The realization equation at a deterministic round function: the CBC engine
applied to the on-ramped `f` is the on-ramped `m ↦ cbcState f (bf m)`. -/
theorem attachEngineFully_cbcRound_univ (f : X → X) (bf : M → List X) :
    attachEngineFully (Set.univ : Set Uni.{u}) (converterEngine X X (cbcRound bf))
        (System.ofTyped (functionEvaluator f))
      = System.ofTyped (functionEvaluator fun m : M => cbcState f (bf m)) := by
  refine attachEngineFully_converterEngine_univ (g := fun m : M => cbcState f (bf m)) ?_
  -- the library lemma wants one round: from any resource history, the round
  -- opened by `m` runs to `cbcState f (bf m)`
  intro us m xs
  have hne : us ++ [m] ≠ [] := by simp
  have hlast : (us ++ [m]).getLast hne = m := by simp
  -- which is the chain induction started with no answers and all blocks to go
  have hrun := cbcRound_runsTo f bf (System.ofTyped (functionEvaluator f))
    (answer_ofTyped_functionEvaluator f) (us ++ [m]) hne (bf m) (by rw [hlast])
    (bf m).length 0 (by simp) xs
  simpa using hrun

/-- The law of the CBC function: the block former digested by a uniform round
function, i.e. the image of `R_{n,n}` (printed p. 125) under CBC. -/
noncomputable def cbcFunctionLaw (bf : M → List X) : PDS M X :=
  Distribution.fTransform
    (fun f : X → X => functionEvaluator fun m : M => cbcState f (bf m))
    (Distribution.uniform (X → X))

/-- The realization equation at Φ: the pushforward of
`attachEngineFully_cbcRound_univ` along the atoms of `R_{n,n}`. -/
theorem cbcConverter_smul_Rnn (bf : M → List X) :
    cbcConverter bf • (RandomSystems.ofTyped (Rnn X) : Phi.{u})
      = RandomSystems.ofTyped (cbcFunctionLaw bf) := by
  show Distribution.fTransform
      (attachEngineFully (Set.univ : Set Uni.{u}) (converterEngine X X (cbcRound bf))) _ = _
  rw [RandomSystems.ofTyped, RandomSystems.ofTyped, Rnn, PDS.urf, cbcFunctionLaw,
    Distribution.fTransform_fTransform, Distribution.fTransform_fTransform,
    Distribution.fTransform_fTransform]
  -- both sides are pushforwards of the uniform round function, so it is
  -- enough that they agree atom by atom
  congr 1
  funext f
  exact attachEngineFully_cbcRound_univ f bf

end Realization

/-! ## §6.2.3's two restrictions, as members of the same `Σ` -/

/-- Printed p. 126: "for each message `θ_r` determines the number of blocks the
block-former outputs … and keeps track of the total number of such blocks
resulting for all messages seen so far.  When this number exceeds `r`, then
`θ_r` stops replying to queries." -/
def thetaPred (bf : M → List X) (r : ℕ) : List Uni.{u} → Prop := fun l =>
  totalBlocks bf (l.filterMap (System.decodeOption (X := M))) ≤ r

theorem prefixClosed_thetaPred (bf : M → List X) (r : ℕ) :
    PrefixClosed (thetaPred (X := X) bf r) := by
  intro l₁ l₂ hpre hl₂
  refine le_trans (totalBlocks_mono bf ?_) hl₂
  obtain ⟨t, rfl⟩ := hpre
  exact ⟨t.filterMap (System.decodeOption (X := M)), List.filterMap_append.symm⟩

/-- `θ_r` (printed p. 126) as a member of `Σ`: a domain filter at a
prefix-closed predicate is a generator of `converterMonoidAt`. -/
noncomputable def theta (bf : M → List X) (r : ℕ) : ↥converterMonoidAt.{u} :=
  ⟨filterPhi (thetaPred (X := X) bf r) (prefixClosed_thetaPred bf r),
    filterPhi_mem_converterMonoidAt _ _⟩

/-- Definition 3.10's filter `[r]` (printed p. 62), as a member of the same
`Σ`. -/
noncomputable def queryLimit (r : ℕ) : ↥converterMonoidAt.{u} :=
  ⟨filterQueries r, filterQueries_mem_converterMonoidAt r⟩


/-- Printed p. 126: "`A_i = 1` if and only if, up to the evaluation of the
`i`-th message (the `i`-th input to `CBC`), a non-trivial collision has occurred
at the input to `R_{n,n}`.  By non-trivial we mean that collisions do not count
if they hold because two messages have the same prefix." -/
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

/-- The monotone-condition object that augments the real experiment. -/
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

/-- Functions agreeing at every CBC call-site input produce the same final
chaining value. -/
theorem cbcState_congr_of_agree_on_inputs (f f' : X -> X) (bs : List X)
    (h : ∀ j < bs.length,
      f (cbcInput f bs j) = f' (cbcInput f bs j)) :
    cbcState f bs = cbcState f' bs := by
  induction bs using List.reverseRecOn with
  | nil => rfl
  -- induct from the right: the earlier blocks' inputs are unchanged by the
  -- appended one, so the induction hypothesis gives equal chain values there,
  -- and the hypothesis at the last position closes the final call
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
  -- the terminal call site's key is the whole encoding, so "not a prefix of"
  -- is exactly the nontriviality `cbcBad` demands
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
  -- distinct messages have neither encoding a prefix of the other, so their
  -- terminal call sites are nontrivially distinct
  have hkey : bf m ≠ (bf m').take ((bf m').length - 1 + 1) := by
    rw [take_last_key (hbf_ne m')]
    exact fun h => hbf_pf m m' hmm (h ▸ List.prefix_refl (bf m))
  -- and freshness then forbids their inputs from being equal
  exact hfresh m hm m' hm' _
    (by have := List.length_pos_of_ne_nil (hbf_ne m'); omega) hkey heq

/-- Printed p. 126: "Since the encoding is prefix-free, `A_i = 0` implies in
particular that all the last-block inputs to `R_{n,n}` … are distinct, provided
of course that the messages themselves are distinct." -/
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
  -- the input at `p` reads only the chain over the first `p` blocks, whose
  -- call sites are all below `p`
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

/-- A proper-prefix input cannot be a queried message's terminal input. -/
theorem cbcInput_ne_lastInput (f : X -> X) (bf : M -> List X)
    {l : List M} (hbf_pf : PrefixFree bf) (hfresh : cbcFresh f bf l)
    {m : M} (hm : m ∈ l) {i : Nat} (hi : i + 1 < (bf m).length)
    {s : M} (hs : s ∈ l) (_hne_s : bf s ≠ []) :
    cbcInput f (bf m) i ≠ cbcLastInput f bf s := by
  -- if `bf s` were this proper prefix of `bf m` then either `s = m`, and the
  -- lengths disagree, or prefix-freeness is violated
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
  -- the input at block `j` only reads calls strictly before it
  refine cbcInput_congr_of_agree_below f _ (bf m) fun i hip => ?_
  -- and no such call site is a queried message's terminal one, which is where
  -- the shift acts
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
  -- a collision after the shift is a collision before it, because the shift
  -- moves no call-site input
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
  -- the MAC is the round function at the terminal input; that input is
  -- unmoved, and the shift adds `delta s` to the value there
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
  -- the first shift leaves every terminal call-site input where it was,
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
  -- so the second shift acts at the same sites and the offsets simply add
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
  -- the terminal shifts act freely and transitively on the MAC vector: shifting
  -- by `delta` moves the vector by `delta`, shifts compose, and `0` acts
  -- trivially, so every MAC vector has a fiber of the same size
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
  -- and there are `|X|^{#l.toFinset}` such vectors
  rw [Fintype.card_fun, Fintype.card_coe] at key
  rw [← key]
  congr 2
  ext f
  simp [funext_iff, and_comm]

end Plumbing

/-- Printed pp. 126–127: "Conditioned on this event (i.e., on `A_i = 0`), all
outputs are uniformly random, except of course that for identical inputs
(messages) the outputs are also identical." -/
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
  -- not-bad is shift-stable and implies freshness, so the fibers of the MAC
  -- vector inside it are balanced
  have hfiber := Plumbing.cbc_fiber_card bf hne hbf Good
    (fun f hf => cbcFresh_of_not_cbcBad f bf hne hf)
    (fun delta f hf => not_cbcBad_cbcShift f bf delta hbf hne hf) a
  have hcard : l.toFinset.card ≤ Fintype.card M := Finset.card_le_univ _
  dsimp only [Good] at hfiber
  -- the ideal side counts functions `M → X` agreeing on the queried messages,
  -- which is the same balancing over `|M| - #l.toFinset` free values
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
relation is Maurer13b Definition 13 (printed p. 3153), landed as
`PDG.CondEquiv`.
-/

section CondEquiv

open System

/-- The interaction determines the sampled function on the queried messages and
nothing else, so the fiber of a fixed-query-list interaction is an evaluation
event of the shape `notBad_implies_uniform_outputs` speaks about. -/
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

/-- `ĈBC R_{n,n}` (printed p. 126): the joint law of the CBC chain and *that*
round function's collision condition.  A pushforward and not a `PDS.adjoin`,
because the condition reads the round function, which the chain does not
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

/-- Dropping the MBO from `ĈBC R_{n,n}` returns `CBC R_{n,n}` (printed p. 126),
which is what ties equation (6.2) to Theorem 6.1's converter. -/
@[simp] theorem forget_cbcGameLaw (bf : M → List X) :
    PDG.forget (cbcGameLaw bf) = cbcFunctionLaw bf := by
  rw [cbcGameLaw, cbcFunctionLaw, PDG.forget, Distribution.fTransform_fTransform]
  rfl

/-- Winning the collision game (printed p. 126) at a fixed message list is the
collision event of the sampled round function on that list. -/
theorem won_cbcGameLaw_atom (f : X → X) (bf : M → List X) (l : List M) :
    System.Won
        ((System.functionEvaluator fun m : M => cbcState f (bf m), cbcCondition f bf) :
          System.DDG M X)
        (System.DDE.Total.playQueries l) l.length ↔ cbcBad f bf l := by
  show System.answeredQueries _ ∈ _ ↔ _
  -- an evaluator refuses nothing, so the answered history is the whole list,
  -- and the condition read there is exactly `cbcBad`
  rw [answeredQueries_transcript_playQueries_keptPrefix,
    keptPrefix_functionEvaluator]
  exact Iff.rfl

/-- The not-won slice of the collision game (printed p. 126) at a fixed message
list, as a mass over round functions. -/
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

/-- At a repetition-free message list every realizable interaction has mass
`(1/|𝒳|)^{|l|}`, which is Definition 6.1's "for each new input outputs a fresh
uniformly random value" (printed p. 125) as a number. -/
theorem trLawFullyDefined_Vn_uniform (l : List M) (hl : l.Nodup) (g : M → X) :
    PDS.trLawFullyDefined (System.DDE.Total.playQueries l) l.length (Vn M X)
        (l.map (fun m => (m, some (g m)))) = (1 / (Fintype.card X : ℝ)) ^ l.length :=
  PDS.trLawFullyDefined_urf_playQueries_apply l hl g

@[simp] theorem weight_Vn : (Vn M X).weight = 1 := by
  rw [Vn, PDS.urf, Distribution.weight_fTransform, Distribution.weight_uniform]

/-- Equation (6.2), printed p. 126: `(ĈBC R_{n,n}) ⊨ V_n`, which is Definition
13's product form (Maurer13b, printed p. 3153) read at a fixed message list. -/
theorem cbc_condEquiv [Nontrivial M] (bf : M → List X) (hbf : PrefixFree bf) :
    PDG.CondEquiv (cbcGameLaw bf) (Vn M X) := by
  classical
  intro l
  ext t
  rw [Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, weight_Vn,
    one_mul, notWonLaw_cbcGameLaw_apply, notWonMass_cbcGameLaw,
    trLawFullyDefined_Vn_apply]
  by_cases hreal : ∃ h₀ : M → X, l.map (fun m => (m, some (h₀ m))) = t
  -- realizable: the interactions equal to `t` are the functions agreeing with
  -- `h₀` on the queried messages, on both sides, so the product form is the
  -- mass identity already proved
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
  -- unrealizable: no atom on either side produces `t`, so both sides vanish
  · push Not at hreal
    rw [Distribution.mass_eq_zero_of_forall_not _ (fun f hf => hreal _ hf.2),
      Distribution.mass_eq_zero_of_forall_not (Distribution.uniform (M → X))
        (fun g hg => hreal g hg), mul_zero]

end CondEquiv

/-! ## CR18 equation (6.3), printed p. 127: the restriction by `θ_r`

"Hence we have proved (6.2), which is of course still true when both systems
are restricted by `θ_r`" (printed p. 127).  The transport
`PDG.condEquiv_fTransform` asks for one inner query list, the same for every
system in either support; for a domain filter that is the admitted subsequence
of the outer list, which is a function of the outer list alone only because
every atom here answers everything.
-/

section Theta

open System

variable {A : Type u} {B : Type u}

/-- The schedule a domain filter admits from a fixed query list: Definition
3.3's deletion pass run against §3.4.3's filter (printed p. 62), computed from
the query list alone. -/
def filterAdmit (P : List A → Prop) [DecidablePred P] (l : List A) : List A :=
  l.foldl (fun K x => if P (K ++ [x]) then K ++ [x] else K) []

theorem filterAdmit_concat (P : List A → Prop) [DecidablePred P] (l : List A) (x : A) :
    filterAdmit P (l ++ [x])
      = if P (filterAdmit P l ++ [x]) then filterAdmit P l ++ [x] else filterAdmit P l := by
  simp only [filterAdmit, List.foldl_concat]

/-- The admitted schedule grows with the query list: a longer list admits an
extension of what its prefix admitted. -/
theorem filterAdmit_prefix (P : List A → Prop) [DecidablePred P] {l₁ l₂ : List A}
    (h : l₁ <+: l₂) : filterAdmit P l₁ <+: filterAdmit P l₂ := by
  obtain ⟨t, rfl⟩ := h
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t x ih =>
      -- each further query either extends the schedule or leaves it alone
      rw [← List.append_assoc, filterAdmit_concat]
      split
      · exact ih.trans (List.prefix_append _ _)
      · exact ih

/-- The deletion pass of a filtered evaluator is the admitted schedule. -/
theorem keptPrefix_filterDom_functionEvaluator (P : List A → Prop) [DecidablePred P]
    (hP : PrefixClosed P) (h : A → B) (l : List A) :
    keptPrefix (filterDom P hP (functionEvaluator h)) l = filterAdmit P l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x ih =>
      rw [keptPrefix_append_singleton, ih, filterAdmit_concat]
      -- the evaluator answers every nonempty history, so being in the filtered
      -- domain is just satisfying the predicate
      have hdom : (filterAdmit P l ++ [x] ∈ dom (filterDom P hP (functionEvaluator h)))
          ↔ P (filterAdmit P l ++ [x]) := by
        rw [mem_dom_filterDom, dom_functionEvaluator]
        exact and_iff_right (by simp)
      by_cases hPx : P (filterAdmit P l ++ [x])
      · rw [if_pos (hdom.mpr hPx), if_pos hPx]
      · rw [if_neg (fun hc => hPx (hdom.mp hc)), if_neg hPx]

/-- The post-processing that re-inserts the refusals: replay the outer list
against the predicate, taking the next inner entry where it admits and
answering `⊥` where it does not.  It reads the list and the predicate only,
never the system, which is what makes the witness uniform. -/
def filterWeaveState (P : List A → Prop) [DecidablePred P]
    (T : List (A × Option B)) (l : List A) : List A × List (A × Option B) :=
  l.foldl (fun st x =>
      if P (st.1 ++ [x]) then (st.1 ++ [x], st.2 ++ [(x, (T[st.1.length]?).bind Prod.snd)])
      else (st.1, st.2 ++ [(x, none)]))
    ([], [])

@[inherit_doc filterWeaveState]
def filterWeave (P : List A → Prop) [DecidablePred P]
    (T : List (A × Option B)) (l : List A) : List (A × Option B) :=
  (filterWeaveState P T l).2

theorem filterWeaveState_concat (P : List A → Prop) [DecidablePred P]
    (T : List (A × Option B)) (l : List A) (x : A) :
    filterWeaveState P T (l ++ [x])
      = (if P ((filterWeaveState P T l).1 ++ [x])
          then ((filterWeaveState P T l).1 ++ [x],
            (filterWeaveState P T l).2
              ++ [(x, (T[(filterWeaveState P T l).1.length]?).bind Prod.snd)])
          else ((filterWeaveState P T l).1, (filterWeaveState P T l).2 ++ [(x, none)])) := by
  simp only [filterWeaveState, List.foldl_concat]

/-- The replay tracks the admitted schedule in its first component. -/
theorem filterWeaveState_fst (P : List A → Prop) [DecidablePred P]
    (T : List (A × Option B)) (l : List A) :
    (filterWeaveState P T l).1 = filterAdmit P l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x ih =>
      rw [filterWeaveState_concat, filterAdmit_concat, ih]
      split <;> rfl

theorem filterWeave_concat (P : List A → Prop) [DecidablePred P]
    (T : List (A × Option B)) (l : List A) (x : A) :
    filterWeave P T (l ++ [x])
      = filterWeave P T l
        ++ [if P (filterAdmit P l ++ [x])
            then (x, (T[(filterAdmit P l).length]?).bind Prod.snd) else (x, none)] := by
  rw [filterWeave, filterWeaveState_concat, filterWeaveState_fst]
  by_cases hPx : P (filterAdmit P l ++ [x])
  · rw [if_pos hPx, if_pos hPx]
    rfl
  · rw [if_neg hPx, if_neg hPx]
    rfl

@[simp] theorem filterWeave_length (P : List A → Prop) [DecidablePred P]
    (T : List (A × Option B)) (l : List A) : (filterWeave P T l).length = l.length := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x ih =>
      rw [filterWeave_concat, List.length_append, ih]
      simp

/-- The filtered interaction at a fixed query list: the replay of the outer list
over the interaction with the admitted schedule, which is the absorption
witness `PDG.condEquiv_fTransform` asks for. -/
theorem transcript_filterDom_functionEvaluator_playQueries (P : List A → Prop)
    [DecidablePred P] (hP : PrefixClosed P) (h : A → B) (l' : List A) :
    ∀ n, n ≤ l'.length →
      DDE.Total.transcript (filterDom P hP (functionEvaluator h))
          (DDE.Total.playQueries l') n
        = filterWeave P ((filterAdmit P l').map (fun x => (x, some (h x)))) (l'.take n) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      have hlt : n < l'.length := hn
      have hik := ih (Nat.le_of_succ_le hn)
      have hlen : (DDE.Total.transcript (filterDom P hP (functionEvaluator h))
          (DDE.Total.playQueries l') n).length = n := by
        rw [hik, filterWeave_length, List.length_take]
        omega
      -- at step `n` the environment plays `l'[n]` regardless of the answers
      have hq : DDE.Total.playQueries (Y := B) l'
          (DDE.Total.transcript (filterDom P hP (functionEvaluator h))
            (DDE.Total.playQueries l') n)↓ᵧ = some l'[n] := by
        show l'[_]? = _
        simp only [transcriptOutputs, List.length_map, hlen]
        exact List.getElem?_eq_getElem hlt
      have hinp : (DDE.Total.transcript (filterDom P hP (functionEvaluator h))
          (DDE.Total.playQueries l') n)↓ₓ = l'.take n :=
        transcriptInputs_transcript_playQueries _ l' n (Nat.le_of_succ_le hn)
      have hkeptM : keptPrefix (functionEvaluator h) (filterAdmit P (l'.take n))
          = keptPrefix (filterDom P hP (functionEvaluator h)) (l'.take n) := by
        rw [keptPrefix_functionEvaluator, keptPrefix_filterDom_functionEvaluator]
      -- which the filtered evaluator answers when the predicate admits the
      -- extension of the schedule so far, and refuses otherwise
      have hans : answer (filterDom P hP (functionEvaluator h)) (l'.take n) l'[n]
          = if P (filterAdmit P (l'.take n) ++ [l'[n]]) then some (h l'[n]) else none := by
        rw [answer_filterDom P hP (functionEvaluator h) (l'.take n)
          (filterAdmit P (l'.take n)) l'[n] hkeptM,
          keptPrefix_filterDom_functionEvaluator, PDS.answer_functionEvaluator]
        by_cases hPx : P (filterAdmit P (l'.take n) ++ [l'[n]]) <;> simp [hPx]
      rw [DDE.Total.transcript_succ_of_query _ _ hq, hinp, hans, hik,
        List.take_add_one, List.getElem?_eq_getElem hlt]
      simp only [Option.toList_some, filterWeave_concat]
      congr 1
      by_cases hPx : P (filterAdmit P (l'.take n) ++ [l'[n]])
      -- admitted: the schedule grew by `l'[n]`, so the entry the replay reads off
      -- the inner interaction is that query's own answer
      · rw [if_pos hPx, if_pos hPx]
        have hpre : filterAdmit P (l'.take n) ++ [l'[n]] <+: filterAdmit P l' := by
          have htk : l'.take (n + 1) = l'.take n ++ [l'[n]] := by
            rw [List.take_add_one, List.getElem?_eq_getElem hlt]
            rfl
          have hstep : filterAdmit P (l'.take (n + 1))
              = filterAdmit P (l'.take n) ++ [l'[n]] := by
            rw [htk, filterAdmit_concat, if_pos hPx]
          exact hstep ▸ filterAdmit_prefix P (List.take_prefix (n + 1) l')
        have hget : (filterAdmit P l')[(filterAdmit P (l'.take n)).length]? = some l'[n] := by
          obtain ⟨w, hw⟩ := hpre
          rw [← hw, List.append_assoc, List.getElem?_append_right (le_refl _)]
          simp
        rw [List.getElem?_map, hget]
        rfl
      · rw [if_neg hPx, if_neg hPx]

/-- The filtered interaction at the outer list's own length, in the shape the
transport consumes: a post-processing of the interaction with the admitted
schedule. -/
theorem transcript_filterDom_functionEvaluator_playQueries_length (P : List A → Prop)
    [DecidablePred P] (hP : PrefixClosed P) (h : A → B) (l' : List A) :
    DDE.Total.transcript (filterDom P hP (functionEvaluator h))
        (DDE.Total.playQueries l') l'.length
      = filterWeave P (DDE.Total.transcript (functionEvaluator h)
          (DDE.Total.playQueries (filterAdmit P l')) (filterAdmit P l').length) l' := by
  rw [transcript_functionEvaluator_playQueries_length,
    transcript_filterDom_functionEvaluator_playQueries P hP h l' l'.length le_rfl,
    List.take_length]

/-- The queries the filtered interaction actually answered: the admitted
schedule.  This is the winning clause — `System.Won` reads `answeredQueries`
and nothing else. -/
theorem answeredQueries_filterDom_functionEvaluator (P : List A → Prop)
    [DecidablePred P] (hP : PrefixClosed P) (h : A → B) (l' : List A) :
    answeredQueries (DDE.Total.transcript (filterDom P hP (functionEvaluator h))
        (DDE.Total.playQueries l') l'.length)
      = answeredQueries (DDE.Total.transcript (functionEvaluator h)
          (DDE.Total.playQueries (filterAdmit P l')) (filterAdmit P l').length) := by
  -- both sides delete exactly the queries the predicate rejects
  rw [answeredQueries_transcript_playQueries_keptPrefix,
    answeredQueries_transcript_playQueries_keptPrefix,
    keptPrefix_filterDom_functionEvaluator, keptPrefix_functionEvaluator]

/-- CR18's block count is prefix-closed (printed p. 126, "keeps track of the
total number of such blocks resulting for all messages seen so far"), read at
the message alphabet where `θ_r` actually restricts. -/
theorem prefixClosed_totalBlocks_le (bf : M → List X) (r : ℕ) :
    PrefixClosed (fun l : List M => totalBlocks bf l ≤ r) :=
  fun _ _ hpre hl => le_trans (totalBlocks_mono bf hpre) hl

/-- Equation (6.3), printed p. 127: `(θ_r ĈBC R_{n,n}) ⊨ θ_r V_n`, "of course
still true when both systems are restricted by `θ_r`", at the inner query list
`filterAdmit` and the post-processing `filterWeave`. -/
theorem cbc_condEquiv_theta [Nontrivial M] (bf : M → List X) (r : ℕ)
    (hbf : PrefixFree bf) :
    PDG.CondEquiv
      (Distribution.fTransform
        (fun γ : System.DDG M X =>
          ((System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
              (prefixClosed_totalBlocks_le bf r) γ.1, γ.2) : System.DDG M X))
        (cbcGameLaw bf))
      (Distribution.fTransform
        (System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
          (prefixClosed_totalBlocks_le bf r))
        (Vn M X)) := by
  refine PDG.condEquiv_fTransform_of_answeredQueries _
    (fun l' => ⟨filterAdmit (fun l : List M => totalBlocks bf l ≤ r) l',
      fun T => filterWeave (fun l : List M => totalBlocks bf l ≤ r) T l', ?_, ?_⟩)
    (cbc_condEquiv bf hbf)
  -- real side: every atom is a function evaluator, so the schedule is the
  -- admitted subsequence and does not depend on which one
  · intro γ hγ
    obtain ⟨f, -, rfl⟩ :=
      Distribution.exists_mem_support_of_mem_support_fTransform _ _ hγ
    dsimp only
    exact ⟨answeredQueries_filterDom_functionEvaluator _ _ _ l',
      transcript_filterDom_functionEvaluator_playQueries_length _ _ _ l'⟩
  -- ideal side: same, at the atoms of the uniform random function
  · intro s hs
    rw [Vn, PDS.urf] at hs
    obtain ⟨g, -, rfl⟩ :=
      Distribution.exists_mem_support_of_mem_support_fTransform _ _ hs
    exact transcript_filterDom_functionEvaluator_playQueries_length _ _ _ l'

/-- The admitted schedule satisfies the predicate: it is built by admitted
extensions only, starting from the empty history. -/
theorem filterAdmit_sat (P : List A → Prop) [DecidablePred P] (h0 : P ([] : List A))
    (l : List A) : P (filterAdmit P l) := by
  induction l using List.reverseRecOn with
  | nil => exact h0
  | append_singleton l x ih =>
      -- either the query was admitted, and the predicate holds by that very test,
      -- or the schedule is unchanged
      rw [filterAdmit_concat]
      split
      · assumption
      · exact ih

end Theta

/-! ## CR18's collision count, printed p. 127

"For the processing of any such list of messages, as long as the game is not
won, the next value for which a collision should occur to win the game in the
next step is uniformly random (as one can easily see).  The probability of a
collision in such a sequence is the same as the probability of having a
collision in a list [o]f `r` uniform `n`-bit strings, i.e., the upper bound of
Lemma 4.18 can be applied and we have `Γ(bθ_r ĈBC R_{n,n}) ≤ ½ r² 2^{-n}`"
(printed p. 127).

Proved as the lazy-sampling argument it is, at
`Probability.Counting.uniform_mass_walk_repeat_le`.  Sites are block
*prefixes*, so a shared prefix is one site — CR18's `A_i` excluding equal
prefixes, and what keeps the count at `θ_r`'s block budget.
-/

/-- The block prefixes designating the CBC call sites reached by a query
history.  Distinct messages sharing a prefix designate the *same* site. -/
def cbcSites (bf : M → List X) (l : List M) : Finset (List X) :=
  (l.flatMap fun m =>
    (List.range (bf m).length).map fun j => (bf m).take (j + 1)).toFinset

/-- The block consumed at the call site designated by a block prefix: its last
block. -/
def cbcSiteBlock (p : List X) : X := p.getD (p.length - 1) 0

/-- The round-function input at the call site designated by a block prefix.
`cbcLastInput f bf m` is its value at a whole encoded message. -/
def cbcSiteInput (f : X → X) (p : List X) : X := cbcInput f p (p.length - 1)

/-- A block prefix is a call site exactly when some queried message begins with
it. -/
theorem mem_cbcSites {bf : M → List X} {l : List M} {p : List X} :
    p ∈ cbcSites bf l ↔ ∃ m ∈ l, ∃ j < (bf m).length, p = (bf m).take (j + 1) := by
  simp only [cbcSites, List.mem_toFinset, List.mem_flatMap, List.mem_map,
    List.mem_range]
  constructor
  · rintro ⟨m, hm, j, hj, rfl⟩
    exact ⟨m, hm, j, hj, rfl⟩
  · rintro ⟨m, hm, j, hj, rfl⟩
    exact ⟨m, hm, j, hj, rfl⟩

/-- Every call site consumes at least one block. -/
theorem cbcSites_ne_nil {bf : M → List X} {l : List M} {p : List X}
    (hp : p ∈ cbcSites bf l) : p ≠ [] := by
  obtain ⟨m, hm, j, hj, rfl⟩ := mem_cbcSites.mp hp
  intro h
  have hl2 : ((bf m).take (j + 1)).length = 0 := by rw [h]; rfl
  rw [List.length_take] at hl2
  omega

/-- The call sites are closed under dropping the last block: the round before a
round is a round. -/
theorem dropLast_mem_cbcSites {bf : M → List X} {l : List M} {p : List X}
    (hp : p ∈ cbcSites bf l) (hne : p.dropLast ≠ []) :
    p.dropLast ∈ cbcSites bf l := by
  obtain ⟨m, hm, j, hj, rfl⟩ := mem_cbcSites.mp hp
  have hlen : ((bf m).take (j + 1)).length = j + 1 := by
    rw [List.length_take]; omega
  have hdl : ((bf m).take (j + 1)).dropLast = (bf m).take j := by
    rw [List.dropLast_eq_take, hlen, List.take_take]
    congr 1
    omega
  rw [hdl] at hne ⊢
  have hj0 : j ≠ 0 := by
    intro h; exact hne (by simp [h])
  -- dropping the last block of a message's first `j+1` blocks leaves its first
  -- `j`, which is a site of the same message whenever `j ≠ 0`
  refine mem_cbcSites.mpr ⟨m, hm, j - 1, by omega, ?_⟩
  congr 1
  omega

/-- The number of call sites is at most the number of blocks emitted, which is
what `θ_r` bounds. -/
theorem card_cbcSites_le (bf : M → List X) (l : List M) :
    (cbcSites bf l).card ≤ totalBlocks bf l := by
  -- the sites are collected as a `Finset`, so shared prefixes are counted once
  -- while the underlying list has one entry per emitted block
  refine le_trans (List.toFinset_card_le _) (le_of_eq ?_)
  simp [totalBlocks, List.length_flatMap]

/-- The site designated by a message's first `j+1` blocks carries that
message's round-`j` input. -/
theorem cbcSiteInput_take (f : X → X) (bs : List X) {j : ℕ} (hj : j < bs.length) :
    cbcSiteInput f (bs.take (j + 1)) = cbcInput f bs j := by
  have hlen : (bs.take (j + 1)).length = j + 1 := by
    rw [List.length_take]; omega
  unfold cbcSiteInput cbcInput
  rw [hlen]
  have h1 : (bs.take (j + 1)).take (j + 1 - 1) = bs.take j := by
    rw [List.take_take]
    congr 1
    omega
  have h2 : (bs.take (j + 1)).getD (j + 1 - 1) 0 = bs.getD j 0 := by
    simp only [Nat.add_sub_cancel]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take]
    simp
  rw [h1, h2]

/-- A site's input is its parent's chaining value offset by its own block —
the walk's step, at CBC. -/
theorem cbcSiteInput_eq (f : X → X) (p : List X) :
    cbcSiteInput f p = cbcState f p.dropLast + cbcSiteBlock p := by
  rw [cbcSiteInput, cbcInput, cbcSiteBlock, List.dropLast_eq_take]

/-- Two distinct sites with the same parent carry different blocks — the walk's
sibling hypothesis, and what rules out a collision between two *first* blocks,
whose inputs are deterministic. -/
theorem cbcSiteBlock_ne {p q : List X} (hp : p ≠ []) (hq : q ≠ [])
    (hne : p ≠ q) (hd : p.dropLast = q.dropLast) :
    cbcSiteBlock p ≠ cbcSiteBlock q := by
  have hlast : ∀ (t : List X) (ht : t ≠ []), t.dropLast ++ [cbcSiteBlock t] = t := by
    intro t ht
    have hpos : 0 < t.length := List.length_pos_of_ne_nil ht
    have hb : cbcSiteBlock t = t.getLast ht := by
      rw [cbcSiteBlock, List.getLast_eq_getElem, List.getD_eq_getElem]
    rw [hb]
    exact List.dropLast_append_getLast ht
  -- a list is its `dropLast` followed by its last block, so equal parents and
  -- equal blocks would make the sites equal
  intro heq
  exact hne (by rw [← hlast p hp, ← hlast q hq, hd, heq])

/-- The parent call site: the same computation one round earlier, when that is
itself a call site of the history.  A single-block site has no parent — its
input is `0 + b`, read off the public initial chaining value. -/
def cbcParent (bf : M → List X) (l : List M) (p : ↥(cbcSites bf l)) :
    Option ↥(cbcSites bf l) :=
  if h : p.val.dropLast ∈ cbcSites bf l then some ⟨p.val.dropLast, h⟩ else none

/-- Printed p. 127: "the same as the probability of having a collision in a
list [o]f `r` uniform `n`-bit strings" — at most `r(r−1)/2|𝒳|` on any query
history `θ_r` admits. -/
theorem mass_cbcBad_le (bf : M → List X) (r : ℕ) (l : List M)
    (hl : totalBlocks bf l ≤ r) :
    (Distribution.uniform (X → X)).mass (fun f => cbcBad f bf l)
      ≤ (r : ℝ) * ((r : ℝ) - 1) / (2 * Fintype.card X) := by
  classical
  have hne : ∀ p : ↥(cbcSites bf l), p.val ≠ [] := fun p => cbcSites_ne_nil p.2
  -- the parent, when it exists, is the `dropLast`
  have hsome : ∀ p q : ↥(cbcSites bf l), cbcParent bf l p = some q →
      q.val = p.val.dropLast := by
    intro p q hq
    unfold cbcParent at hq
    split_ifs at hq with h
    exact congrArg Subtype.val (Option.some.inj hq).symm
  -- and when it does not, the site is a single block, read off the initial `0`
  have hdrop : ∀ p : ↥(cbcSites bf l), cbcParent bf l p = none →
      p.val.dropLast = [] := by
    intro p hp
    unfold cbcParent at hp
    split_ifs at hp with h
    by_contra hcon
    exact h (dropLast_mem_cbcSites p.2 hcon)
  have hpareq : ∀ p q : ↥(cbcSites bf l), cbcParent bf l p = cbcParent bf l q →
      p.val.dropLast = q.val.dropLast := by
    intro p q h
    rcases hp : cbcParent bf l p with _ | a
    · rw [hp] at h
      rw [hdrop p hp, hdrop q h.symm]
    · rw [hp] at h
      rw [← hsome p a hp, hsome q a h.symm]
  -- length decreases along parents, so the walk is well-founded
  have hrank : ∀ t q : ↥(cbcSites bf l), cbcParent bf l t = some q →
      q.val.length < t.val.length := by
    intro t q hq
    rw [hsome t q hq, List.length_dropLast]
    have := List.length_pos_of_ne_nil (hne t)
    omega
  -- the step `x ↦ x + b` is injective, so a uniform parent value gives a
  -- uniform input here — CR18's "the next value … is uniformly random"
  have hginj : ∀ p : ↥(cbcSites bf l),
      Function.Injective (fun x : X => x + cbcSiteBlock p.val) :=
    fun p => add_left_injective _
  -- and two distinct sites sharing a parent carry different blocks, so they
  -- can never collide; this is what makes the deterministic first blocks safe
  have hsib : ∀ p q : ↥(cbcSites bf l), p ≠ q → cbcParent bf l p = cbcParent bf l q →
      ∀ x : X, x + cbcSiteBlock p.val ≠ x + cbcSiteBlock q.val := by
    intro p q hpq hpar x
    have hb : cbcSiteBlock p.val ≠ cbcSiteBlock q.val :=
      cbcSiteBlock_ne (hne p) (hne q) (fun h => hpq (Subtype.ext h)) (hpareq p q hpar)
    exact fun h => hb (add_left_cancel h)
  -- a site's input is its parent's output offset by its block
  have hinpeq : ∀ (f : X → X) (p : ↥(cbcSites bf l)),
      cbcSiteInput f p.val
        = ((cbcParent bf l p).elim 0 (fun q => f (cbcSiteInput f q.val)))
            + cbcSiteBlock p.val := by
    intro f p
    rw [cbcSiteInput_eq]
    congr 1
    rcases hp : cbcParent bf l p with _ | q
    · simp only [Option.elim]
      rw [hdrop p hp]
      simp [cbcState]
    · simp only [Option.elim]
      have hq := hsome p q hp
      have hqn : q.val ≠ [] := hne q
      rw [← hq]
      exact cbcState_eq_f_lastInput f q.val hqn
  -- the walk at CBC: sites are block prefixes, parent is `dropLast`, step is
  -- `x ↦ x + b`, and the public initial chaining value is `0`
  have key := Probability.Counting.uniform_mass_walk_repeat_le
      (cbcParent bf l) (fun p => fun x : X => x + cbcSiteBlock p.val) (0 : X)
      (fun p => p.val.length) hrank hginj hsib
      (fun f p => cbcSiteInput f p.val) hinpeq
  -- a nontrivial collision is a repeat among the site inputs, since the two
  -- colliding call sites have distinct block prefixes and so are distinct sites
  have hbad : ∀ f : X → X, cbcBad f bf l →
      ¬ Function.Injective (fun p : ↥(cbcSites bf l) => cbcSiteInput f p.val) := by
    rintro f ⟨m, hm, m', hm', j, hj, j', hj', hkey, hval⟩ hinjf
    have hp : (bf m).take (j + 1) ∈ cbcSites bf l :=
      mem_cbcSites.mpr ⟨m, hm, j, hj, rfl⟩
    have hp' : (bf m').take (j' + 1) ∈ cbcSites bf l :=
      mem_cbcSites.mpr ⟨m', hm', j', hj', rfl⟩
    have hEq : (⟨_, hp⟩ : ↥(cbcSites bf l)) = ⟨_, hp'⟩ := by
      refine hinjf ?_
      show cbcSiteInput f ((bf m).take (j + 1)) = cbcSiteInput f ((bf m').take (j' + 1))
      rw [cbcSiteInput_take f (bf m) hj, cbcSiteInput_take f (bf m') hj']
      exact hval
    exact hkey (congrArg Subtype.val hEq)
  refine le_trans (Distribution.mass_mono Distribution.uniform_nonNeg hbad) ?_
  obtain ⟨k, hkdef⟩ : ∃ k, Fintype.card ↥(cbcSites bf l) = k := ⟨_, rfl⟩
  rw [hkdef] at key
  refine le_trans key ?_
  -- finally there are at most `totalBlocks ≤ r` sites, and `k(k-1)` is
  -- monotone there
  have hk : k ≤ r := by
    rw [← hkdef, Fintype.card_coe]
    exact le_trans (card_cbcSites_le bf l) hl
  have hkr : (k : ℝ) ≤ (r : ℝ) := by exact_mod_cast hk
  have hprod : (k : ℝ) * ((k : ℝ) - 1) ≤ (r : ℝ) * ((r : ℝ) - 1) := by
    have h1 : (0 : ℝ) ≤ (r : ℝ) - (k : ℝ) := by linarith
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · have hk0 : k = 0 := by omega
      rw [hk0, hr0]
    · have h2 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrpos
      have h3 : (0 : ℝ) ≤ (k : ℝ) := by positivity
      nlinarith [mul_nonneg h1 (by linarith : (0 : ℝ) ≤ (r : ℝ) + (k : ℝ) - 1)]
  have hXpos : (0 : ℝ) < 2 * (Fintype.card X : ℝ) := by
    have : (0 : ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
    linarith
  gcongr

/-! ## CR18 Lemma 4.18's step, printed p. 127: the blind winning probability

"It remains to analyze `Γ(bθ_r ĈBC R_{n,n})`.  To win the game
`bθ_r ĈBC R_{n,n}` means to win the game `θ_r ĈBC R_{n,n}` *non-adaptively*,
i.e., it means to choose a fixed list of input messages to `ĈBC` (of lengths
allowed by filter `θ_r`)" (printed p. 127).
-/

section Blind

open System

/-- Printed p. 127: whatever bounds the collision probability of a uniform round
function on a message list `θ_r` admits, bounds the blind winning probability.
The cut to non-adaptive environments is what makes it true. -/
theorem blindSupWinProb_cbcGameLaw_theta_le [Nontrivial M] (bf : M → List X) (r : ℕ)
    {c : ℝ}
    (hc : ∀ l : List M, totalBlocks bf l ≤ r →
      (Distribution.uniform (X → X)).mass (fun f => cbcBad f bf l) ≤ c) :
    PDG.blindSupWinProb
        (Distribution.fTransform
          (fun γ : System.DDG M X =>
            ((System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
                (prefixClosed_totalBlocks_le bf r) γ.1, γ.2) : System.DDG M X))
          (cbcGameLaw bf))
      ≤ c := by
  refine PDG.blindSupWinProb_le_of_forall fun e he n => ?_
  set P : List M → Prop := fun l => totalBlocks bf l ≤ r with hP
  set hPc := prefixClosed_totalBlocks_le bf r with hPcdef
  -- a blind environment asks the same queries of every system, so its answered
  -- history is one list, chosen here at an arbitrary reference atom
  set L : List M :=
    (DDE.Total.transcript
      (filterDom P hPc (functionEvaluator fun _ : M => Classical.arbitrary X)) e n)↓ₓ with hL
  have hwin : PDG.winningMass e n
      (Distribution.fTransform
        (fun γ : System.DDG M X => ((filterDom P hPc γ.1, γ.2) : System.DDG M X))
        (cbcGameLaw bf))
      = (Distribution.uniform (X → X)).mass (fun f => cbcBad f bf (filterAdmit P L)) := by
    rw [PDG.winningMass, cbcGameLaw, Distribution.fTransform_fTransform,
      Distribution.mass_fTransform]
    refine Distribution.mass_congr _ fun f => ?_
    show System.answeredQueries _ ∈ _ ↔ _
    rw [DDE.Total.answeredQueries_transcript]
    show keptPrefix (filterDom P hPc (functionEvaluator fun m : M => cbcState f (bf m)))
        (DDE.Total.transcript
          (filterDom P hPc (functionEvaluator fun m : M => cbcState f (bf m))) e n)↓ₓ
      ∈ _ ↔ _
    rw [transcriptInputs_congr_of_nonAdaptive he _
        (filterDom P hPc (functionEvaluator fun _ : M => Classical.arbitrary X)) n,
      ← hL, keptPrefix_filterDom_functionEvaluator]
    exact Iff.rfl
  -- and the list it fixes is admitted by the block-count predicate, since the
  -- schedule is built by admitted extensions only
  rw [hwin]
  exact hc _ (filterAdmit_sat P (by simp [hP, totalBlocks]) L)

/-- Lemma 4.18's step, printed p. 127, with the falling factor kept. -/
theorem blindSupWinProb_cbcGameLaw_theta_le_birthday [Nontrivial M]
    (bf : M → List X) (r : ℕ) :
    PDG.blindSupWinProb
        (Distribution.fTransform
          (fun γ : System.DDG M X =>
            ((System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
                (prefixClosed_totalBlocks_le bf r) γ.1, γ.2) : System.DDG M X))
          (cbcGameLaw bf))
      ≤ (r : ℝ) * ((r : ℝ) - 1) / (2 * Fintype.card X) :=
  blindSupWinProb_cbcGameLaw_theta_le bf r (fun l hl => mass_cbcBad_le bf r l hl)

/-- Printed p. 127: `Γ(b θ_r ĈBC R_{n,n}) ≤ ½ r² 2^{-n}` — the birthday bound
weakened to the page's `r²`. -/
theorem blindSupWinProb_cbcGameLaw_theta_le_sq [Nontrivial M]
    (bf : M → List X) (r : ℕ) :
    PDG.blindSupWinProb
        (Distribution.fTransform
          (fun γ : System.DDG M X =>
            ((System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
                (prefixClosed_totalBlocks_le bf r) γ.1, γ.2) : System.DDG M X))
          (cbcGameLaw bf))
      ≤ (r : ℝ) ^ 2 / (2 * Fintype.card X) := by
  refine le_trans (blindSupWinProb_cbcGameLaw_theta_le_birthday bf r) ?_
  have hXpos : (0 : ℝ) < 2 * (Fintype.card X : ℝ) := by
    have : (0 : ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
    linarith
  have hr : (0 : ℝ) ≤ (r : ℝ) := by positivity
  -- `r(r-1) ≤ r²` at a positive denominator
  gcongr
  nlinarith

end Blind

/-! ## CR18 equation (6.1), unfolded over the converter class

`RandomSystems/System/ConverterClass.lean` proves once, for every converter,
that an inner query limit `[r]` is invisible under an outer restriction
admitting only histories on which the converter issues at most `r` resource
queries — and `θ_r`'s domain condition *is* that admission hypothesis.
-/

/-- CBC's converter satisfies Definition 3.8 (printed p. 62): one application of
the class's program constructor, at `cbcRound`'s two elementary conditions. -/
theorem cbcConverter_isConverterAt (bf : M → List X) :
    IsConverterAt (Set.univ : Set Uni.{u}) (cbcConverter bf).val :=
  isConverterAt_attachAt_univ
    (System.innerTotal_converterEngine (cbcRound_innerTotal bf))
    (System.answersWithinUniformBudget_converterEngine (cbcRound_requestsBounded bf))

/-- Printed p. 126: "`θ_r ĈBC = θ_r ĈBC[r]`, i.e., the filter `[r]` is
irrelevant because the restriction implied by `θ_r` guarantees that at most `r`
queries are made to `R_{n,n}`".  Both hypotheses are discharged at
`cbc_coherence`. -/
theorem cbc_filter_redundant (bf : M → List X) (r : ℕ)
    {β : List (Uni.{u} ⊕ Option Uni.{u}) → ℕ}
    (hβ : System.AnswersWithinBudget (System.converterEngine X X (cbcRound bf)) β)
    (hpay : ∀ (done : List Uni.{u}) (q : Uni.{u})
        (c : List (Converter.DDC.CIn Uni.{u} Uni.{u})),
      β ((c ++ [Sum.inl (Converter.InLabel.outside, q)]).map Converter.DDC.unlabel)
        + totalBlocks bf (done.filterMap (System.decodeOption (X := M)))
        ≤ totalBlocks bf ((done ++ [q]).filterMap (System.decodeOption (X := M)))) :
    theta (X := X) bf r * cbcConverter bf * queryLimit.{u} r
      = theta (X := X) bf r * cbcConverter bf := by
  apply Subtype.ext
  -- the class needs the engine to be local and to reach at most `r` resource
  -- queries on every history the outer filter admits; the budget and the
  -- payment condition give the second, and `θ_r`'s own bound is the first
  exact filterPhi_mul_filterQueries_of_isLocal
    (System.hasFiniteRounds_attachEngineFully
      (System.answersWithinUniformBudget_converterEngine
        (cbcRound_requestsBounded bf))).isLocal
    _ (prefixClosed_thetaPred bf r) r
    (fun l hl => le_trans
      (System.queryCount_le
        (System.reachesWithin_attachEngineFully_of_cost hβ hpay l)) hl)

/-- The blocks of the current message not yet asked about, the current message
being the last outer query decoded at `M`.  No uniform constant, so nothing is
over-estimated on a short message, and no dependence on the answers. -/
noncomputable def cbcRoundBudget (bf : M → List X)
    (l : List (Uni.{u} ⊕ Option Uni.{u})) : ℕ :=
  (((System.outerQueries l).getLast?.bind (System.decodeOption (X := M))).elim 0
      fun m => (bf m).length) - (System.roundAnswers l).length

/-- Definition 3.8's finite-bound clause (printed p. 62) in the well-founded
form the round induction consumes. -/
theorem cbcRound_answersWithinBudget (bf : M → List X) :
    System.AnswersWithinBudget (System.converterEngine X X (cbcRound bf))
      (cbcRoundBudget bf) := by
  intro l x hx o
  obtain ⟨us, hus, n, hn, hm⟩ :=
    System.exists_mem_of_mem_converterMove
      (System.mem_converterMove_of_mem_converterEngine hx)
  -- the move that fired is a request, not a return
  have hreq : ∃ x' : X, n = Sum.inl x' := by
    rcases n with x' | v
    · exact ⟨x', rfl⟩
    · exact absurd hm (by simp)
  obtain ⟨x', rfl⟩ := hreq
  have hne : us ≠ [] := by
    by_contra hnil
    rw [cbcRound, dif_neg (by simpa using hnil)] at hn
    exact absurd hn (by simp)
  rw [cbcRound, dif_pos hne] at hn
  dsimp only at hn
  -- so `cbcRound`'s guard held: strictly fewer answers so far than the current
  -- message has blocks
  have hlt : (System.roundAnswers l).length < (bf (us.getLast hne)).length := by
    by_cases hlt : (((System.roundAnswers l).map
        fun o => o.bind (System.decodeOption (X := X))).map
          fun o => o.getD 0).length < (bf (us.getLast hne)).length
    · simpa using hlt
    · rw [if_neg hlt] at hn
      exact absurd hn (by simp)
  -- the budget reads that same message off the last outer query, and the
  -- answer just received consumes one unit of it
  have hlast : (System.outerQueries l).getLast?.bind (System.decodeOption (X := M))
      = some (us.getLast hne) := by
    rw [System.decodeList_mem_eq hus, List.getLast?_map,
      List.getLast?_eq_some_getLast hne]
    simp
  simp only [cbcRoundBudget, System.outerQueries_concat_inr,
    System.roundAnswers_concat_inr, hlast, List.length_append,
    List.length_singleton, Option.elim]
  omega

/-- One more query adds its own message's blocks to the running total — or, if
it is not a message at all, nothing. -/
theorem totalBlocks_filterMap_concat (bf : M → List X) (done : List Uni.{u})
    (q : Uni.{u}) :
    totalBlocks bf ((done ++ [q]).filterMap (System.decodeOption (X := M)))
      = totalBlocks bf (done.filterMap (System.decodeOption (X := M)))
        + ((System.decodeOption (X := M) q).elim 0 fun m => (bf m).length) := by
  rw [List.filterMap_append, totalBlocks_append]
  rcases hq : System.decodeOption (X := M) q with _ | m <;> simp [hq, totalBlocks]

/-- Opening a round for one more message costs exactly that message's blocks,
with equality: nothing is rounded up, which is why a block-counting `θ_r` and
not a length bound is what pays for it. -/
theorem cbcRoundBudget_add_totalBlocks (bf : M → List X) (done : List Uni.{u})
    (q : Uni.{u}) (c : List (Converter.DDC.CIn Uni.{u} Uni.{u})) :
    cbcRoundBudget bf
        ((c ++ [Sum.inl (Converter.InLabel.outside, q)]).map Converter.DDC.unlabel)
      + totalBlocks bf (done.filterMap (System.decodeOption (X := M)))
      = totalBlocks bf ((done ++ [q]).filterMap (System.decodeOption (X := M))) := by
  rw [totalBlocks_filterMap_concat]
  -- a round is opened by an outer query, so its budget is read with an empty
  -- answer list: exactly `(bf m).length`, which is what the total gains
  simp only [List.map_append, List.map_singleton, Converter.DDC.unlabel_query,
    cbcRoundBudget, System.outerQueries_concat_inl, System.roundAnswers_concat_inl,
    List.getLast?_concat, List.length_nil, Nat.sub_zero]
  exact Nat.add_comm _ _

/-- Equation (6.1), printed p. 126, with nothing assumed.  The page writes it
hatted, on the MBO-augmented converter (printed p. 127); this is the unaugmented
form, which is what §5.5's coherence condition (printed p. 122) asks for. -/
theorem cbc_coherence (bf : M → List X) (r : ℕ) :
    theta (X := X) bf r * cbcConverter bf * queryLimit.{u} r
      = theta (X := X) bf r * cbcConverter bf :=
  cbc_filter_redundant bf r (cbcRound_answersWithinBudget bf)
    fun done q c => le_of_eq (cbcRoundBudget_add_totalBlocks bf done q c)

/-! ## Theorem 6.1's objects on Φ (printed p. 126) -/

/-- Printed p. 126: `ε_r = ½ r² 2^{-n}`, at `|X|` in place of `2^n`. -/
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

/-! ## CR18 Theorem 6.1's proof chain, printed p. 127

> "Hence we have proved (6.2), which is of course still true when both systems
> are restricted by `θ_r`: `(θ_r ĈBC R_{n,n}) ⊨ θ_r V_n` (6.3).  From (6.1) we
> have `θ_r ĈBC R_{n,n} ≡ θ_r ĈBC[r] R_{n,n}`, hence
> `(θ_r ĈBC[r]R_{n,n}) ⊨ θ_r V_n`.  Therefore we can apply Theorem 4.17 to
> obtain `⟨θ_r CBC [r]R_{n,n} | θ_r V_n⟩ ≤ Γ(b θ_r ĈBC R_{n,n})`. … and we have
> `Γ(b θ_r ĈBC R_{n,n}) ≤ ½ r² 2^{-n}`."

The page carries no universal alphabet, so the two crossings below are ours:
`theta_smul_ofTyped` for the objects, and
`edist_eq_advFullyDefined_of_weight_eq` with `PDS.advFullyDefined_ofTyped` for
the metric.
-/

section Chain

open System

/-- UPSTREAM-CANDIDATE (`RandomSystems/System/Phi.lean`, beside
`System.blockSet_ofTyped`, of which this is the general form): a domain filter
commutes with the typed on-ramp, at the predicate read back through the
inclusion. -/
theorem filterDom_ofTyped {A B : Type u} (P : List Uni.{u} → Prop)
    (hP : PrefixClosed P) (S : DDS A B) :
    filterDom P hP (System.ofTyped S)
      = System.ofTyped (filterDom (fun la : List A => P (la.map (encode A)))
          (fun _ _ hpre hl => hP (hpre.map _) hl) S) := by
  apply Subtype.ext
  funext l
  refine Part.ext' ?_ (fun _ _ => rfl)
  constructor
  -- filtering then on-ramping: a decodable history is an included history, so
  -- the universal predicate on it is the pulled-back predicate on its decoding
  · rintro ⟨⟨hne, hall⟩, hPl⟩
    refine ⟨hne, fun l' hl' hne' => ?_⟩
    obtain ⟨hdec, hS⟩ := hall l' hl' hne'
    refine ⟨hdec, hS, ?_⟩
    show P (((decodeList A l').get hdec).map (encode A))
    rw [← decodeList_mem_eq (Part.get_mem hdec)]
    exact hP hl' hPl
  -- and back, with the on-ramp's own domain condition untouched
  · rintro ⟨hne, hall⟩
    obtain ⟨hdec, hS, hPd⟩ := hall l (List.prefix_refl _) hne
    refine ⟨⟨hne, fun l' hl' hne' => ?_⟩, ?_⟩
    · obtain ⟨hdec', hS', -⟩ := hall l' hl' hne'
      exact ⟨hdec', hS'⟩
    · rw [decodeList_mem_eq (Part.get_mem hdec)]
      exact hPd

/-- UPSTREAM-CANDIDATE (`RandomSystems/System/DiscreteSystem.lean`): the
filter reads only the predicate's extension, so the pulled-back predicate may
be replaced by the message-level one the game-side statements use. -/
theorem filterDom_congr {A B : Type u} {P Q : List A → Prop}
    (hP : PrefixClosed P) (hQ : PrefixClosed Q) (h : ∀ l, P l ↔ Q l)
    (S : DDS A B) : filterDom P hP S = filterDom Q hQ S := by
  have hPQ : P = Q := funext fun l => propext (h l)
  subst hPQ
  rfl

/-- UPSTREAM-CANDIDATE (`RandomSystems/System/Absorb.lean`): the typed
on-ramp is a pushforward, so it preserves total weight. -/
theorem weight_ofPhi_ofTyped {A B : Type u} (SL : PDS A B) :
    (ofPhi (RandomSystems.ofTyped SL : Phi.{u})).weight = SL.weight :=
  Distribution.weight_fTransform _ _

/-- `θ_r`'s universal predicate (printed p. 126) read back at the message
alphabet: on an included history the filter-map decoding is the identity. -/
theorem thetaPred_map_encode (bf : M → List X) (r : ℕ) (lm : List M) :
    thetaPred (X := X) bf r (lm.map (encode M)) ↔ totalBlocks bf lm ≤ r := by
  rw [thetaPred, filterMap_decodeOption_map_encode]

/-- The alphabet crossing at `θ_r`: it applied to an on-ramped resource
is the on-ramp of that resource filtered at the message-level block-count
predicate — where the game-side statements live. -/
theorem theta_smul_ofTyped (bf : M → List X) (r : ℕ) (SL : PDS M X) :
    theta (X := X) bf r • (RandomSystems.ofTyped SL : Phi.{u})
      = RandomSystems.ofTyped (Distribution.fTransform
          (filterDom (fun l : List M => totalBlocks bf l ≤ r)
            (prefixClosed_totalBlocks_le bf r)) SL) := by
  show Distribution.fTransform
    (filterDom (thetaPred (X := X) bf r) (prefixClosed_thetaPred bf r)) _ = _
  rw [RandomSystems.ofTyped,
    Distribution.fTransform_fTransform, Distribution.fTransform_fTransform]
  congr 1
  -- both sides are pushforwards, so it is enough to compare the filters atom
  -- by atom
  funext S
  rw [Function.comp_apply, Function.comp_apply, filterDom_ofTyped]
  congr 1
  -- and there the universal block count reads back as the message-level one
  exact filterDom_congr _ _ (fun l => thetaPred_map_encode bf r l) S

/-- Dropping the MBO commutes with `θ_r`: printed p. 127's
`Γ(b θ_r ĈBC R_{n,n})` bounds a distance between the *unhatted* systems. -/
theorem forget_theta_cbcGameLaw (bf : M → List X) (r : ℕ) :
    PDG.forget (Distribution.fTransform
        (fun γ : System.DDG M X =>
          ((System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
            (prefixClosed_totalBlocks_le bf r) γ.1, γ.2) : System.DDG M X))
        (cbcGameLaw bf))
      = Distribution.fTransform
          (System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
            (prefixClosed_totalBlocks_le bf r)) (cbcFunctionLaw bf) := by
  -- both are pushforwards, and restricting then forgetting is forgetting then
  -- restricting
  rw [← forget_cbcGameLaw bf, PDG.forget, PDG.forget,
    Distribution.fTransform_fTransform, Distribution.fTransform_fTransform]
  rfl

/-- `V_n` is a probability law (printed p. 125): a pushforward of a uniform
distribution. -/
theorem nonNeg_Vn : (Vn M X).NonNeg := by
  rw [Vn, PDS.urf]
  exact Distribution.uniform_nonNeg.fTransform _

/-- The direct CBC function law is a probability law, hence nonnegative. -/
theorem nonNeg_cbcFunctionLaw (bf : M → List X) : (cbcFunctionLaw bf).NonNeg := by
  rw [cbcFunctionLaw]
  exact Distribution.uniform_nonNeg.fTransform _

/-- Filtering a law whose atoms all have the total nonempty-history domain by
the CBC block budget gives the displayed common domain. -/
theorem hasDomain_blockFiltered_of_hasDomain_total (bf : M → List X) (r : ℕ)
    (S : PDS M X) (hS : PDS.HasDomain S {l : List M | l ≠ []}) :
    PDS.HasDomain
      (Distribution.fTransform
        (System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
          (prefixClosed_totalBlocks_le bf r)) S)
      {l : List M | l ≠ [] ∧ totalBlocks bf l ≤ r} := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ :=
    Distribution.exists_mem_support_of_mem_support_fTransform _ _ hs
  -- an atom of the filtered law is defined exactly where the original is and
  -- the predicate holds
  ext l
  rw [System.mem_dom_filterDom, hS t ht]
  rfl

/-- A prefix-free block former emits at least one block per message, so the
block-budget domain is also bounded by `r` external queries. -/
theorem qBounded_blockBudget [Nontrivial M] (bf : M → List X) (r : ℕ)
    (hbf : PrefixFree bf) :
    QBounded {l : List M | l ≠ [] ∧ totalBlocks bf l ≤ r} r := by
  intro l hl
  -- prefix-freeness makes every encoding nonempty, so a list of messages has
  -- at least as many blocks as messages
  have hlen : ∀ messages : List M, messages.length ≤ totalBlocks bf messages := by
    intro messages
    induction messages with
    | nil => simp [totalBlocks]
    | cons m messages ih =>
        have hm : 1 ≤ (bf m).length :=
          List.length_pos_of_ne_nil (hbf.ne_nil m)
        have ih' : messages.length ≤
            (messages.map fun m => (bf m).length).sum := by
          simpa [totalBlocks] using ih
        simp only [List.length_cons, totalBlocks, List.map_cons, List.sum_cons]
        omega
  exact (hlen l).trans hl.2

/-- CBC-MAC at the Random Systems layer: both systems are `PDS M X` and
their distance is the class distance `Δ` (`PDS.classDistance`).  No
universal-alphabet embedding, `Phi` action, or ambient `edist` occurs here. -/
theorem cbc_mac_classDistance [Nontrivial M] (bf : M → List X) (r : ℕ)
    (hbf : PrefixFree bf) :
    PDS.classDistance
        (Distribution.fTransform
          (System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
            (prefixClosed_totalBlocks_le bf r)) (cbcFunctionLaw bf))
        (Distribution.fTransform
          (System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
            (prefixClosed_totalBlocks_le bf r)) (Vn M X))
      ≤ cbcEpsilon X r := by
  classical
  let D : Set (List M) :=
    {l : List M | l ≠ [] ∧ totalBlocks bf l ≤ r}
  -- both systems answer exactly the nonempty message lists within the block
  -- budget, and `θ_r` bounds those lists by `r` queries
  have hrealDom : PDS.HasDomain
      (Distribution.fTransform
        (System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
          (prefixClosed_totalBlocks_le bf r)) (cbcFunctionLaw bf)) D := by
    apply hasDomain_blockFiltered_of_hasDomain_total bf r
    exact PDS.hasDomain_fTransform_functionEvaluator _ _
  have hidealDom : PDS.HasDomain
      (Distribution.fTransform
        (System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
          (prefixClosed_totalBlocks_le bf r)) (Vn M X)) D := by
    apply hasDomain_blockFiltered_of_hasDomain_total bf r
    exact PDS.hasDomain_urf M X
  have hbounded : QBounded D r := qBounded_blockBudget bf r hbf
  -- on a shared, query-bounded domain the class distance is the advantage
  rw [PDS.classDistance_eq_advFullyDefined_of_commonDomain_bounded
    ((nonNeg_cbcFunctionLaw bf).fTransform _) (nonNeg_Vn.fTransform _)
    ⟨hrealDom, hidealDom, hbounded⟩]
  have hBw : (Distribution.fTransform
      (System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
        (prefixClosed_totalBlocks_le bf r)) (Vn M X)).weight = 1 := by
    rw [Distribution.weight_fTransform, weight_Vn]
  calc PDS.advFullyDefined
        (Distribution.fTransform
          (System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
            (prefixClosed_totalBlocks_le bf r)) (cbcFunctionLaw bf))
        (Distribution.fTransform
          (System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
            (prefixClosed_totalBlocks_le bf r)) (Vn M X))
      = PDS.advFullyDefined
          (PDG.forget (Distribution.fTransform
            (fun γ : System.DDG M X =>
              ((System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
                (prefixClosed_totalBlocks_le bf r) γ.1, γ.2) : System.DDG M X))
            (cbcGameLaw bf)))
          (Distribution.fTransform
            (System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
              (prefixClosed_totalBlocks_le bf r)) (Vn M X)) := by
        -- the real side is the restricted game with its collision condition dropped
        rw [forget_theta_cbcGameLaw]
    -- Theorem 4.17's step, printed p. 127, fed equation (6.3)
    _ ≤ ENNReal.ofReal (PDG.blindSupWinProb (Distribution.fTransform
            (fun γ : System.DDG M X =>
              ((System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
                (prefixClosed_totalBlocks_le bf r) γ.1, γ.2) : System.DDG M X))
            (cbcGameLaw bf))) :=
        PDG.advFullyDefined_forget_le_blindSupWinProb_of_condEquiv
          ((nonNeg_cbcGameLaw bf).fTransform _) (nonNeg_Vn.fTransform _)
          (by rw [Distribution.weight_fTransform, weight_cbcGameLaw, hBw])
          (cbc_condEquiv_theta bf r hbf)
    -- Lemma 4.18's step, printed p. 127
    _ ≤ cbcEpsilon X r :=
        ENNReal.ofReal_le_ofReal (blindSupWinProb_cbcGameLaw_theta_le_sq bf r)

/-- Instantiation boundary for CBC-MAC: realization and the alphabet crossing
turn the typed class-distance bound into the ambient construction metric
bound. -/
theorem cbc_mac_distance_of_classDistance (bf : M → List X) (r : ℕ)
    (hDelta : PDS.classDistance
        (Distribution.fTransform
          (System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
            (prefixClosed_totalBlocks_le bf r)) (cbcFunctionLaw bf))
        (Distribution.fTransform
          (System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
            (prefixClosed_totalBlocks_le bf r)) (Vn M X))
      ≤ cbcEpsilon X r) :
    edist (cbcRestricted bf r • assumedResource X r)
      (constructedResource bf r) ≤ cbcEpsilon X r := by
  classical
  -- equation (6.1) then the realization equation move the left endpoint to an
  -- on-ramped typed law; `theta_smul_ofTyped` is the alphabet crossing
  have hleft : cbcRestricted bf r • assumedResource X r
      = (RandomSystems.ofTyped (Distribution.fTransform
          (System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
            (prefixClosed_totalBlocks_le bf r)) (cbcFunctionLaw bf)) : Phi.{u}) := by
    rw [cbcRestricted, assumedResource, smul_smul, cbc_coherence, mul_smul,
      cbcConverter_smul_Rnn, theta_smul_ofTyped]
  have hright : constructedResource bf r
      = (RandomSystems.ofTyped (Distribution.fTransform
          (System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
            (prefixClosed_totalBlocks_le bf r)) (Vn M X)) : Phi.{u}) := by
    rw [constructedResource, theta_smul_ofTyped]
  -- both endpoints are probability laws, so the symmetrization in `edist` is
  -- invisible and the on-ramp is an isometry for the advantage
  have hAw : (Distribution.fTransform
      (System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
        (prefixClosed_totalBlocks_le bf r)) (cbcFunctionLaw bf)).weight = 1 := by
    rw [Distribution.weight_fTransform, cbcFunctionLaw,
      Distribution.weight_fTransform, Distribution.weight_uniform]
  have hBw : (Distribution.fTransform
      (System.filterDom (fun l : List M => totalBlocks bf l ≤ r)
        (prefixClosed_totalBlocks_le bf r)) (Vn M X)).weight = 1 := by
    rw [Distribution.weight_fTransform, weight_Vn]
  rw [hleft, hright,
    edist_eq_advFullyDefined_of_weight_eq
      (by rw [weight_ofPhi_ofTyped, weight_ofPhi_ofTyped, hAw, hBw]),
    PDS.advFullyDefined_ofTyped]
  exact (PDS.advFullyDefined_le_classDistance _ _).trans hDelta

/-- Printed p. 127: `⟨θ_r CBC [r]R_{n,n} | θ_r V_n⟩ ≤ Γ(b θ_r ĈBC R_{n,n}) ≤
½ r² 2^{-n}`, on `Phi` at the `Adv⊥` that `edist` is (`edist_def`). -/
theorem cbc_mac_distance [Nontrivial M] (bf : M → List X) (r : ℕ)
    (hbf : PrefixFree bf) :
    edist (cbcRestricted bf r • assumedResource X r)
      (constructedResource bf r) ≤ cbcEpsilon X r := by
  exact cbc_mac_distance_of_classDistance bf r
    (cbc_mac_classDistance bf r hbf)

end Chain

/-! ## CR18 Theorem 6.1 as a construction statement

Everything the abstract layer needs is an instance here: `Monoid`, `MulAction`,
`PseudoEMetricSpace Phi` and `IsNonexpandingSMul` (`MetricFullyDefined.lean`).
-/


/-- Printed p. 126: "For `θ_r` defined as above, if the block-former of the
`CBC`-converter is prefix-free, we have (for any `r`)
`[r]R_{n,n} --θ_r CBC--> (θ_r V_n)^{ε_r}` for `ε_r = ½ r² 2^{-n}`."

The arrow is `AbstractCryptography.ApproximatelyConstructs`, and
`constructs_singleton_epsilonRelaxation_iff` reads it off `cbc_mac_distance`. -/
theorem cbc_mac_constructs [Nontrivial M] (bf : M → List X) (r : ℕ)
    (hbf : PrefixFree bf) :
    ({assumedResource X r} : Specification Phi.{u})
      —[cbcRestricted bf r; cbcEpsilon X r]→
        ({constructedResource bf r} : Specification Phi.{u}) :=
  constructs_singleton_epsilonRelaxation_iff.mpr (cbc_mac_distance bf r hbf)

/-! ## Consequences derived by abstract theorems

`cbc_mac_trans` and `cbc_mac_parameterized` are the receipts that the
instantiation is real: both take `cbc_mac_constructs` as input and close by a
theorem of the abstract layer.
-/

/-- Whatever is constructed from `θ_r V_n` is constructed from
`[r]R_{n,n}` by the composite converter, with the budgets added.  Derived by
`AbstractCryptography.Constructs.epsilonRelaxation_trans`. -/
theorem cbc_mac_trans [Nontrivial M] {bf : M → List X} {r : ℕ}
    {π' : ↥converterMonoidAt.{u}} {ε' : ℝ≥0∞} {T : Specification Phi.{u}}
    (hbf : PrefixFree bf)
    (h' : ({constructedResource bf r} : Specification Phi.{u}) —[π'; ε']→ T) :
    ({assumedResource X r} : Specification Phi.{u})
      —[π' * cbcRestricted bf r; cbcEpsilon X r + ε']→ T :=
  Constructs.epsilonRelaxation_trans (cbc_mac_constructs bf r hbf) h'

/-- §5.5's parameterized reading — equation (5.6), printed p. 122:
`φ_r R --ψ_r α--> (ψ_r S)^{f_r}`, with "the constructing converter `α` does not
depend on `r`".  What §5.5 buys is the collapse: under `ψ_r α φ_r = ψ_r α` the
filter on the assumed resource drops out and the family becomes a statement
about the *unrestricted* `R_{n,n}`. -/
theorem cbc_mac_parameterized [Nontrivial M] (bf : M → List X)
    (hbf : PrefixFree bf) :
    ∀ r : ℕ, ({(ofTyped (Rnn X) : Phi.{u})} : Specification Phi.{u})
      —[cbcRestricted bf r; cbcEpsilon X r]→
        ({constructedResource bf r} : Specification Phi.{u}) :=
  (parameterizedConstruction_iff_of_coherence
    (φ := fun r : ℕ => queryLimit.{u} r) (ψ := fun r : ℕ => theta (X := X) bf r)
    (π := cbcConverter bf) (f := fun r : ℕ => cbcEpsilon X r)
    (R := (ofTyped (Rnn X) : Phi.{u})) (S := (ofTyped (Vn M X) : Phi.{u}))
    (fun r => cbc_coherence bf r)).mp (fun r => cbc_mac_constructs bf r hbf)

end RandomSystems.CBCMAC
