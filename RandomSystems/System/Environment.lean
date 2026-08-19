/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.ProbabilisticSystem
import Probability.StatisticalDistance
import Probability.Coupling
import Probability.SimpAttr
import Mathlib.Data.ENNReal.BigOperators

/-!
# Environments

Lanzenberger Ch. 2 is the primary source for this layer; CR18 Ch. 3 is
secondary validation.

* `DDE Y X` — Lanzenberger **Definition 2.11**: a deterministic discrete
  environment for an `(X, Y)`-DDS is a partial function `e : 𝒴* ⇀ 𝒳` with
  prefix-closed domain.  The domain admits the empty history — `e(ε)` is the
  environment's opening move — which is exactly what separates the
  self-activating environment from the passive system (`Valid`'s `[] ∉ dom`
  conjunct).  Stopping is undefinedness; there is no stop symbol and no
  verdict bit in the primary source.
* `trN`, `tr`, `Compatible`, `Stops` — Lanzenberger **Definition 2.12**: the
  transcript of `s` in `e`, by round recursion, with the compatibility side
  condition ("the environment must not query `s` outside of the system's
  domain") and stopping by stabilization.
* `PDE Y X` — Lanzenberger **Definition 2.15**: a probabilistic discrete
  environment is a distribution over DDE.
* `PDS.trLaw`, `PDS.Adv` — Lanzenberger **Definition 2.26**: the optimal
  distinguishing advantage `Adv(S, T) := sup_e δ(tr(S,e), tr(T,e))` over
  compatible environments.  The output-bit forms (Jost 2.2.8 — the existing
  `Distinguisher`/`maxEDist` — and CR18 3.24's DDD) are secondary
  presentations, related by characterization theorems, not definitions.
* `PDS.HasDomain`, `System.CompatibleD`, `System.DDE.Halts`, `PDS.AdvD` — the
  **domain-indexed** reading of the same definition.  Definition 2.14 equips a
  PDS with one domain and Definition 2.26 is indexed by *that*; `Adv` above
  indexes by the two supports instead, which is presentation data.  `AdvD` is
  Definition 2.26 with the theory's indexing, and the payoff is that it
  descends to Notation 2.19's classes (`PDS.AdvD_congr`, `ClassDistance.lean`).
* `DDE.Total` and the `transcript` machinery — CR18 **Definitions 3.6/3.7**
  (secondary): the `⊥`/`⊣`-coded total presentation of the environment and
  its transcript engine, relocated here from `DiscreteSystem.lean` so that
  every environment notion lives in one module.  The coding map from the
  Lanzenberger form arrives with the `Adv`/DDD migration.

Lanzenberger works with finite systems throughout ("we restrict ourselves to
finite systems", p. 13); there compatibility forces the interaction to stop.
Our carrier is not finiteness-bounded, so `Adv`'s supremum ranges over
environments that are compatible *and* stop on the support — on finite
systems the second condition is implied and the index set is Lanzenberger's.
-/

namespace RandomSystems

namespace System

noncomputable section

open Classical

universe u v

variable {X : Type u} {Y : Type v}

/-! ## Lanzenberger Definition 2.11: deterministic discrete environments -/

/-- The domain condition of Lanzenberger Definition 2.11: full prefix
closure, with the empty history admitted.  Compare `Valid`, whose first
conjunct `[] ∉ dom` is exactly what this drops: a system is passive, an
environment is self-activating. -/
def EnvValid (e : Raw Y X) : Prop :=
  ∀ ⦃l₁ l₂ : List Y⦄, l₁ <+: l₂ → l₂ ∈ e.Dom → l₁ ∈ e.Dom

/-- Lanzenberger **Definition 2.11**: a deterministic discrete environment
for an `(X, Y)`-DDS — a `(Y, X)`-DDE — is a partial function `e : 𝒴* ⇀ 𝒳`
with prefix-closed domain.  `e(ε)` is the opening query; the environment
stops by undefinedness. -/
abbrev DDE (Y : Type v) (X : Type u) : Type (max u v) :=
  { e : Raw Y X // EnvValid e }

namespace DDE

/-- An environment that is defined anywhere is defined at the empty history:
self-activation is forced by full prefix closure. -/
theorem nil_mem_dom (e : DDE Y X) {l : List Y} (hl : l ∈ e.1.Dom) :
    [] ∈ e.1.Dom :=
  e.2 (List.nil_prefix) hl

/-- **Definition 2.12's stopping clause, re-cut so that it reads the
environment.**  `e` *halts* when it has a round bound: after `N` answers it asks
nothing more, whatever those answers were.

`PDS.Stops` reads the **support** — it asks that the interaction stabilize with
each sampled deterministic system — and that is presentation data, exactly like
the compatibility clause `System.CompatibleD` repairs.  Halting is the
environment-side clause instead, and it implies stopping against *every*
deterministic system, at one uniform stage
(`System.Stops.of_halts`/`PDS.stops_of_halts`).

Lanzenberger works with finite systems throughout, where compatibility already
forces the interaction to stop (see this file's header); halting is what plays
that role on a carrier that is not finiteness-bounded.  A `q`-bounded domain
supplies it for free to any `CompatibleD` environment, and the rejection-pruning
environment of `ClassDistance.lean` has it by construction
(`System.halts_prunedEnv`).

COINAGE (the thesis names no such class; it assumes finiteness globally). -/
def Halts (e : DDE Y X) : Prop :=
  ∃ N : ℕ, ∀ l : List Y, N ≤ l.length → l ∉ e.1.Dom

end DDE

/-! ## Lanzenberger Definition 2.12: transcripts

`tr(s, e)` is the sequence of pairs `(x₁, y₁), (x₂, y₂), …` with
`xᵢ = e(y₁, …, yᵢ₋₁)` and `yᵢ = s(x₁, …, xᵢ)`.  We present it as the round
recursion `trN`, the length-`n` stage; the interaction stalls when the
environment stops (undefinedness) — and, off the compatible pairs, when the
environment steps outside the system's domain, which Definition 2.12's
compatibility requirement rules out. -/

/-- Lanzenberger Definition 2.12's interaction records: a **transcript** is a
finite sequence of query/answer pairs `(x₁, y₁), …, (xₗ, yₗ)`.  (The CR18
coded form's entries are `X × Option Y`; stripping the coding lands here —
see `DDE.Total.transcript_total`.) -/
abbrev Transcript (X : Type u) (Y : Type v) : Type (max u v) :=
  List (X × Y)

/-- One interaction round: the environment moves on the outputs seen so far,
the system answers on the inputs so far.  If either side has no move the
transcript stalls (for compatible pairs, only the environment stops). -/
def trStep (e : DDE Y X) (s : DDS X Y) (t : Transcript X Y) : Transcript X Y :=
  if hx : (t.map Prod.snd) ∈ e.1.Dom then
    let x := (e.1 (t.map Prod.snd)).get hx
    if hy : (t.map Prod.fst ++ [x]) ∈ dom s then
      t ++ [(x, output s (t.map Prod.fst ++ [x]) hy)]
    else t
  else t

/-- The transcript after at most `n` environment moves (Lanzenberger
Definition 2.12, staged). -/
def trN (e : DDE Y X) (s : DDS X Y) : ℕ → Transcript X Y
  | 0 => []
  | n + 1 => trStep e s (trN e s n)

/-- The transcript's input history is empty or in the system's domain: the
step function only appends answered queries. -/
theorem trN_map_fst_mem_dom_or_nil (e : DDE Y X) (s : DDS X Y) (n : ℕ) :
    trN e s n = [] ∨ (trN e s n).map Prod.fst ∈ dom s := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
      show trStep e s (trN e s n) = [] ∨
        (trStep e s (trN e s n)).map Prod.fst ∈ dom s
      by_cases hx : (trN e s n).map Prod.snd ∈ e.1.Dom
      · by_cases hy : (trN e s n).map Prod.fst ++
            [(e.1 ((trN e s n).map Prod.snd)).get hx] ∈ dom s
        · rw [trStep, dif_pos hx, dif_pos hy]
          right
          simpa using hy
        · rw [trStep, dif_pos hx, dif_neg hy]
          exact ih
      · rw [trStep, dif_neg hx]
        exact ih

/-- A stalled transcript stays stalled: the step function depends only on
the current stage. -/
theorem trN_eq_of_le {e : DDE Y X} {s : DDS X Y} {n : ℕ}
    (h : trN e s (n + 1) = trN e s n) :
    ∀ m, n ≤ m → trN e s m = trN e s n := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m _ ih => show trStep e s (trN e s m) = _; rw [ih]; exact h

/-- Lanzenberger Definition 2.12: the interaction stops — the transcript
stabilizes.  On finite systems every compatible environment stops. -/
def Stops (e : DDE Y X) (s : DDS X Y) : Prop :=
  ∃ n, trN e s (n + 1) = trN e s n

/-- Lanzenberger **Definition 2.12**: the transcript `tr(s, e)`, defined
when the interaction stops. -/
def tr (e : DDE Y X) (s : DDS X Y) : Part (Transcript X Y) :=
  ⟨Stops e s, fun h => trN e s (Nat.find h)⟩

/-- Lanzenberger Definition 2.12 notation: `tr(s, e)` is the transcript of
the system `s` in the environment `e`. -/
scoped notation "tr(" s ", " e ")" => tr e s

/-- The transcript's value is the stage at stabilization. -/
theorem tr_get (e : DDE Y X) (s : DDS X Y) (h : Stops e s) :
    (tr e s).get h = trN e s (Nat.find h) :=
  rfl

/-- Lanzenberger **Definition 2.12**, side condition: `e` is compatible with
`s` when, along the interaction, the environment never queries `s` outside
its domain. -/
def Compatible (e : DDE Y X) (s : DDS X Y) : Prop :=
  ∀ n x, x ∈ e.1 ((trN e s n).map Prod.snd) →
    (trN e s n).map Prod.fst ++ [x] ∈ dom s

/-- **Definition 2.12's compatibility clause, re-cut at the domain.**  `e` is
compatible with *the domain* `D` when it is compatible with every deterministic
system presenting `D` — "the environment must not query outside the domain",
with the domain named rather than read off a particular system.

This is the repair of a substitution the tree made and the theory does not.
Lanzenberger's Definition 2.14 equips every PDS with a *domain attribute* —
all deterministic systems in a support share one domain — and Definition 2.26's
advantage is indexed by the environments compatible with that attribute.  The
carrier here deliberately carries no such attribute (Rulings R1/R2: partiality
is per-atom), so the strict compatibility clause had to be rendered per-atom
over the **support**, which is presentation data.  `CompatibleD` puts the
attribute back where the theory has it: it reads `e` and `D`, and nothing about
any system law.  See LEDGER.md, the Adv-descent TAXONOMY paragraph.

Every system with domain `D` is quantified over, so nothing is assumed about
which of them exist; when none does the clause is vacuous, and then so is every
statement it feeds, `PDS.HasDomain S D` forcing `S` to have empty support. -/
def CompatibleD (e : DDE Y X) (D : Set (List X)) : Prop :=
  ∀ s : DDS X Y, dom s = D → Compatible e s

/-- For a compatible pair the transcript stalls exactly when the environment
stops: undefinedness is the only exit.  This is the formal content of the
compatibility requirement. -/
theorem trN_succ_eq_iff_of_compatible {e : DDE Y X} {s : DDS X Y}
    (h : Compatible e s) (n : ℕ) :
    trN e s (n + 1) = trN e s n ↔ (trN e s n).map Prod.snd ∉ e.1.Dom := by
  constructor
  · intro hst hdom
    have hx : (e.1 ((trN e s n).map Prod.snd)).get hdom ∈
        e.1 ((trN e s n).map Prod.snd) := Part.get_mem hdom
    have hy := h n _ hx
    have : trN e s (n + 1) = trN e s n ++
        [((e.1 ((trN e s n).map Prod.snd)).get hdom,
          output s _ hy)] := by
      show trStep e s (trN e s n) = _
      rw [trStep, dif_pos hdom, dif_pos hy]
    rw [this] at hst
    simpa using congrArg List.length hst
  · intro hnd
    show trStep e s (trN e s n) = trN e s n
    rw [trStep, dif_neg hnd]

end

end System

/-! ## The probabilistic layer -/

noncomputable section

open Classical

open Probability (Distribution statDist)

open scoped ENNReal

universe u v

variable {X : Type u} {Y : Type v}

/-- Lanzenberger **Definition 2.15**: a probabilistic discrete environment
is a distribution over deterministic discrete environments — the environment
counterpart of `PDS`. -/
abbrev PDE (Y : Type v) (X : Type u) : Type (max u v) :=
  Distribution (System.DDE Y X)

namespace PDS

/-- **Lanzenberger Definition 2.14's domain attribute**, named: the
deterministic systems `S` samples all present the domain `D`.

Definition 2.14 equips a PDS with *one* domain — "the domain of `S`" — and
Definition 2.17 fixes it classwide; Definitions 2.26 and 2.31 then read that
attribute, never a support.  This carrier has no such attribute built in
(Rulings R1/R2), so the theory's `dom(S)` is spelled here as an explicit
hypothesis, at a named `D` so that two systems can be said to share one.

The one-system existential form `PDS.HasFixedDomain` is *not* usable for
two-system statements: two instances of it supply two possibly different
domains, and across distinct domains the statements below are false.  Naming
`D` is what makes the clause say what Definition 2.14 says. -/
def HasDomain (S : PDS X Y) (D : Set (List X)) : Prop :=
  ∀ s ∈ S.support, System.dom s = D

/-- `PDS.HasFixedDomain` is `PDS.HasDomain` with the domain existentially
quantified — the same clause, read as a property of one system rather than as a
relation between a system and a named domain.  The two are not
interchangeable in a two-system statement: see `PDS.HasDomain`. -/
theorem hasFixedDomain_iff_exists_hasDomain {S : PDS X Y} :
    HasFixedDomain S ↔ ∃ D : Set (List X), HasDomain S D :=
  ⟨fun h => h.exists_common, fun h => ⟨h⟩⟩

/-- Compatibility with a probabilistic system: compatibility with every
deterministic system in its support (Lanzenberger Definition 2.12, lifted
along Definition 2.14). -/
def Compatible (e : System.DDE Y X) (S : PDS X Y) : Prop :=
  ∀ s ∈ S.support, System.Compatible e s

/-- The interaction with every deterministic system in the support stops.
On finite systems this follows from compatibility. -/
def Stops (e : System.DDE Y X) (S : PDS X Y) : Prop :=
  ∀ s ∈ S.support, System.Stops e s

/-- The transcript distribution `tr(S, e)`: the pushforward of the law along
the deterministic transcript.  `none` codes an interaction that never stops,
which does not occur on the index set of `Adv`. -/
def trLaw (e : System.DDE Y X) (S : PDS X Y) :
    Distribution (Option (System.Transcript X Y)) :=
  Distribution.fTransform (fun s => (System.tr e s).toOption) S

/-- Lanzenberger notation, probabilistic level: `tr(S, e)` is the transcript
distribution. -/
scoped notation "tr(" S ", " e ")" => trLaw e S

/-- Lanzenberger **Definition 2.26**: the optimal distinguishing advantage,
`Adv(S, T) := sup_e δ(tr(S, e), tr(T, e))` — the supremum statistical
distance of the transcript distributions over compatible (stopping)
deterministic environments.  Deterministic environments suffice in the
information-theoretic setting (Lanzenberger's remark before Definition
2.25); the output-bit distinguisher form is a characterization, not the
definition. -/
def Adv (S T : PDS X Y) : ℝ≥0∞ :=
  ⨆ e : {e : System.DDE Y X //
      (Compatible e S ∧ Stops e S) ∧ (Compatible e T ∧ Stops e T)},
    ENNReal.ofReal (statDist (trLaw e.1 S) (trLaw e.1 T))

/-- Lanzenberger Definition 2.26 notation: `Adv(S, T)`. -/
scoped notation "Adv(" S ", " T ")" => Adv S T

@[simp]
theorem Adv_self (S : PDS X Y) : Adv S S = 0 :=
  le_antisymm
    (iSup_le fun _ => by simp [Probability.statDist_self])
    (zero_le _)

/-- **Lanzenberger Definition 2.26, indexed by the domain**:

  `Adv_D(S, T) := sup_e δ(tr(S, e), tr(T, e))`

over the environments admitted by the *domain* `D` — compatible with it
(`System.CompatibleD`) and halting (`System.DDE.Halts`).

`Adv` reads the two supports twice over: its index set is cut out by
compatibility and stopping *with the sampled systems*.  That is presentation
data, and it is why `Adv` is not visible as a function of the two behaviours.
The theory never does this — Definition 2.26 is indexed by `dom(S)`, the single
attribute Definition 2.14 supplies and Definition 2.17 fixes classwide — and
`AdvD` is Definition 2.26 with that indexing restored.  The consequence is
`PDS.AdvD_congr`: the index set mentions no system at all, and on it the
transcript law is pinned by the transcript laws Definition 2.17 equates, so
`AdvD D` descends to Notation 2.19's quotient with no hypothesis
(`PDS.Behaviour.AdvD`).  On the systems Definition 2.14 admits — those with
domain `D` — it *is* `Adv`, and it is `Adv⊥` (`PDS.AdvD_eq_Adv`,
`PDS.advFullyDefined_eq_AdvD`).

COINAGE (the thesis writes only `Adv`, its domain indexing being implicit in
Definition 2.14's attribute). -/
def AdvD (D : Set (List X)) (S T : PDS X Y) : ℝ≥0∞ :=
  ⨆ e : {e : System.DDE Y X // System.CompatibleD e D ∧ System.DDE.Halts e},
    ENNReal.ofReal (statDist (trLaw e.1 S) (trLaw e.1 T))

@[simp]
theorem AdvD_self (D : Set (List X)) (S : PDS X Y) : AdvD D S S = 0 :=
  le_antisymm
    (iSup_le fun _ => by simp [Probability.statDist_self])
    (zero_le _)

end PDS

end

namespace System

/-! ## CR18 presentation (secondary)

CR18 Definitions 3.6/3.7: the `⊥`/`⊣`-coded **total** presentation of the
environment and its transcript engine, relocated from `DiscreteSystem.lean`.
The environment is a total function whose stop is the symbol `⊣` (coded
`none`) and which interacts with the totalized system `s⊥`, so no
compatibility side condition is threaded.  The coding map from the
Lanzenberger form — and CR18 Definition 3.24's verdict-carrying DDD — arrive
with the `Adv`/DDD migration. -/

noncomputable section

open Classical

universe u' v'

variable {X : Type u'} {Y : Type v'}

namespace DDE

/-- CR18 Definition 3.6 (secondary presentation): the total `⊥`/`⊣`-coded
environment `e : (Y ∪ {⊥})* → X ∪ {⊣}`.  We represent `Y ∪ {⊥}` by
`Option Y` and `X ∪ {⊣}` by `Option X`. -/
abbrev Total (Y : Type v') (X : Type u') : Type (max u' v') :=
  List (Option Y) → Option X

end DDE

/-! ### CR18 Definition 3.7: transcripts of the total presentation -/

/-- Input projection of a transcript prefix:
`[(x₁,y₁), ..., (xₖ,yₖ)]↓ₓ = [x₁, ..., xₖ]`. -/
def transcriptInputs (t : List (X × Option Y)) : List X :=
  t.map Prod.fst

/-- Output projection of a transcript prefix:
`[(x₁,y₁), ..., (xₖ,yₖ)]↓ᵧ = [y₁, ..., yₖ]`. -/
def transcriptOutputs (t : List (X × Option Y)) : List (Option Y) :=
  t.map Prod.snd

/-- CR18 transcript input-projection notation. -/
scoped postfix:1024 "↓ₓ" => transcriptInputs

/-- CR18 transcript output-projection notation. -/
scoped postfix:1024 "↓ᵧ" => transcriptOutputs

@[simp]
theorem transcriptInputs_notation (t : List (X × Option Y)) :
    t↓ₓ = transcriptInputs t :=
  rfl

@[simp]
theorem transcriptOutputs_notation (t : List (X × Option Y)) :
    t↓ᵧ = transcriptOutputs t :=
  rfl

/-- Discard rejected attempts from a partial-resource transcript, retaining
the answered query/response pairs in order. -/
def answeredEntries (t : List (X × Option Y)) : List (X × Y) :=
  t.filterMap fun entry => entry.2.map fun y => (entry.1, y)

/-- The successful query history visible in a partial-resource transcript. -/
def answeredQueries (t : List (X × Option Y)) : List X :=
  t.filterMap fun entry => entry.2.map fun _ => entry.1

@[simp]
theorem answeredQueries_concat_some (t : List (X × Option Y)) (x : X) (y : Y) :
    answeredQueries (t ++ [(x, some y)]) = answeredQueries t ++ [x] := by
  simp [answeredQueries]

@[simp]
theorem answeredQueries_concat_none (t : List (X × Option Y)) (x : X) :
    answeredQueries (t ++ [(x, none)]) = answeredQueries t := by
  simp [answeredQueries]

/-- The answered query history is the first projection of the answered-pair
list. -/
theorem answeredEntries_map_fst (t : List (X × Option Y)) :
    (answeredEntries t).map Prod.fst = answeredQueries t := by
  change
    (t.filterMap (fun entry => entry.2.map fun y => (entry.1, y))).map Prod.fst =
      t.filterMap (fun entry => entry.2.map fun _ => entry.1)
  induction t with
  | nil => rfl
  | cons entry t ih =>
      rcases entry with ⟨x, _ | y⟩ <;> simp [ih]

namespace DDE.Total

/-- CR18 Definition 3.7, **functional** form: the transcript `tr(s,e)` is the
(possibly infinite) sequence `x₁,y₁,x₂,y₂,…` defined by the recurrence
`xᵢ = e(y₁,…,yᵢ₋₁)`, `yᵢ = s⊥(x₁,…,xᵢ)`. We present it as the function sending a
length `n` to its length-`n` prefix; when the environment returns `⊣` the
sequence stalls (the prefix stops growing). This is `tr(·,·)` as the function
through which `tr(S,E)` is defined — *not* a relation or a set of prefixes. -/
noncomputable def transcript (s : DDS X Y) (e : DDE.Total Y X) :
    ℕ → List (X × Option Y)
  | 0 => []
  | n + 1 =>
      let t := transcript s e n
      match e t↓ᵧ with
      | some x => t ++ [(x, output s⊥ (t↓ₓ ++ [x]) (by simp [fullyDefined, dom]))]
      | none => t

/-- A transcript answers exactly the queries retained by CR18's skip-state
semantics. -/
theorem answeredQueries_transcript (s : DDS X Y) (e : DDE.Total Y X) (m : ℕ) :
    answeredQueries (transcript s e m) =
      keptPrefix s (transcriptInputs (transcript s e m)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rcases hx : e (transcriptOutputs (transcript s e m)) with _ | x
      · simpa [transcript, hx] using ih
      · have hdrop :
            ((List.map Prod.fst (transcript s e m)) ++ [x]).dropLast =
              List.map Prod.fst (transcript s e m) := by simp
        have hlast :
            ((List.map Prod.fst (transcript s e m)) ++ [x]).getLast (by simp) = x :=
          by simp
        by_cases hc :
            keptPrefix s (List.map Prod.fst (transcript s e m)) ++ [x] ∈ dom s
        · have hkey : ∀ h,
              output (fullyDefined s)
                  ((List.map Prod.fst (transcript s e m)) ++ [x]) h =
                some (output s _ hc) := by
            intro h
            rw [output_fullyDefined, hdrop, hlast]
            dsimp
            rw [dif_pos (by simpa [dom, toPFun] using hc)]
          simp only [transcript, hx, answeredQueries, List.filterMap_append,
            transcriptInputs, List.map_append, List.map_cons, List.map_nil,
            keptPrefix_append_singleton, hkey, if_pos hc, Option.map_some,
            List.filterMap_cons, List.filterMap_nil]
          exact congrArg (· ++ [x]) ih
        · have hkey : ∀ h,
              output (fullyDefined s)
                  ((List.map Prod.fst (transcript s e m)) ++ [x]) h =
                (none : Option Y) := by
            intro h
            rw [output_fullyDefined, hdrop, hlast]
            dsimp
            rw [dif_neg (by simpa [dom, toPFun] using hc)]
          simp only [transcript, hx, answeredQueries, List.filterMap_append,
            transcriptInputs, List.map_append, List.map_cons, List.map_nil,
            keptPrefix_append_singleton, hkey, if_neg hc, Option.map_none,
            List.filterMap_cons, List.filterMap_nil]
          rw [List.append_nil]
          exact ih

/-- A domain-filtered deterministic system only answers queries whose retained
history satisfies the filter.  This is the generic support receipt behind any
resource-budget argument. -/
theorem filterDom_answeredQueries (P : List X → Prop) (hP : PrefixClosed P)
    (hnil : P []) (S : DDS X Y) (e : DDE.Total Y X) (m : ℕ) :
    P (answeredQueries (transcript (filterDom P hP S) e m)) := by
  rw [answeredQueries_transcript]
  rcases keptPrefix_mem_or (filterDom P hP S) _ with h | h
  · exact h.2
  · rw [h]
    exact hnil

/-- CR18 Definition 3.7, prefix predicate: `Transcript s e t` says `t` is a
finite prefix of Maurer's transcript `tr(s,e)`.

The empty list is the initial transcript. If `t = [(x₁,y₁), ..., (xₖ,yₖ)]`
is a transcript prefix and the environment emits `x` after seeing
`(y₁, ..., yₖ)`, then the next prefix appends `(x, s⊥(x₁, ..., xₖ, x))`.

This is a *characterization* of the `transcript` function (see
`transcript_mem_iff`), kept for the membership/prefix view — not the
definition of the transcript. -/
inductive Transcript (S : DDS X Y) (e : DDE.Total Y X) :
    List (X × Option Y) → Prop where
  | nil : Transcript S e []
  | snoc {t : List (X × Option Y)} (ht : Transcript S e t)
      {x : X} (hx : e t↓ᵧ = some x) :
      Transcript S e
        (t ++ [(x, output S⊥ (t↓ₓ ++ [x]) (by
          simp [fullyDefined, dom]))])

/-- The inductive prefix predicate holds exactly on the prefixes produced by the
transcript function `tr(s,e)`: the relation is a *characterization* of the
function, not the definition. -/
theorem transcript_mem_iff (s : DDS X Y) (e : DDE.Total Y X)
    (t : List (X × Option Y)) :
    Transcript s e t ↔ ∃ n, transcript s e n = t := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨0, rfl⟩
    | snoc _ht hx ih =>
        obtain ⟨n, rfl⟩ := ih
        exact ⟨n + 1, by simp only [transcript, hx]⟩
  · rintro ⟨n, rfl⟩
    induction n with
    | zero => exact Transcript.nil
    | succ n ih =>
        simp only [transcript]
        cases hx : e (transcript s e n)↓ᵧ with
        | none => simpa using ih
        | some x => exact Transcript.snoc ih hx

namespace Transcript

/-- CR18 Definition 3.7: a transcript prefix is complete exactly when the
environment stops after seeing its output projection.

This is the formal content of “if `e(y₁, ..., yᵢ₋₁) = ⊣`, the transcript ends
with `yᵢ₋₁`.” -/
def Complete {S : DDS X Y} {e : DDE.Total Y X} (t : List (X × Option Y)) : Prop :=
  Transcript S e t ∧ e t↓ᵧ = none

end Transcript

end DDE.Total

/-! ### The coding, and the agreement theorem

The two presentations describe **one object**.  `DDE.total` codes a
Lanzenberger environment into CR18's total form; `DDE.Total.transcript_total`
is the unification receipt: on any compatible pair, the CR18 engine run on
the coded environment reproduces the Lanzenberger transcript — every query
is answered, no `⊥` ever appears — and stripping the coding recovers `trN`
exactly (`DDE.Total.answeredEntries_transcript_total`). -/

/-- Sequencing with `some` always succeeds, with the list itself. -/
theorem mapM_some {α : Type*} (l : List α) :
    l.mapM (some : α → Option α) = some l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.mapM_cons, ih]

/-- Stripping the coding from an all-answered transcript recovers it. -/
theorem answeredEntries_map_some (t : List (X × Y)) :
    answeredEntries (t.map fun p => (p.1, some p.2)) = t := by
  simp [answeredEntries, List.filterMap_map]

namespace DDE

/-- The coding of a Lanzenberger environment (Definition 2.11) into CR18's
total `⊥`/`⊣` form (Definition 3.6): on a `⊥`-free history in the domain,
the next query; everywhere else `⊣`.  The value on `⊥`-carrying histories is
junk — on compatible pairs they are never reached. -/
noncomputable def total (e : DDE Y X) : Total Y X := fun l =>
  (l.mapM id).bind fun ys =>
    if h : ys ∈ e.1.Dom then some ((e.1 ys).get h) else none

@[simp]
theorem total_map_some (e : DDE Y X) (ys : List Y) :
    e.total (ys.map some) =
      if h : ys ∈ e.1.Dom then some ((e.1 ys).get h) else none := by
  simp [total, mapM_some]

end DDE

/-- **The unification receipt** (the two environment presentations are one
object): on a compatible pair, the CR18 transcript engine (Definition 3.7)
run on the coded environment reproduces the Lanzenberger transcript
(Definition 2.12) with every query answered — no `⊥` appears. -/
theorem DDE.Total.transcript_total (e : DDE Y X) (s : DDS X Y)
    (h : Compatible e s) (n : ℕ) :
    DDE.Total.transcript s e.total n =
      (trN e s n).map fun p => (p.1, some p.2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have houts : (DDE.Total.transcript s e.total n)↓ᵧ =
          ((trN e s n).map Prod.snd).map some := by
        rw [ih]
        simp [transcriptOutputs, List.map_map, Function.comp_def]
      have hins : (DDE.Total.transcript s e.total n)↓ₓ =
          (trN e s n).map Prod.fst := by
        rw [ih]
        simp [transcriptInputs, List.map_map, Function.comp_def]
      by_cases hdom : (trN e s n).map Prod.snd ∈ e.1.Dom
      · -- the environment moves; compatibility answers it
        have hy : (trN e s n).map Prod.fst ++
            [(e.1 ((trN e s n).map Prod.snd)).get hdom] ∈ dom s :=
          h n _ (Part.get_mem hdom)
        have hxval : e.total ((DDE.Total.transcript s e.total n)↓ᵧ) =
            some ((e.1 ((trN e s n).map Prod.snd)).get hdom) := by
          rw [houts, DDE.total_map_some, dif_pos hdom]
        have hout : ∀ hh,
            output s⊥ ((DDE.Total.transcript s e.total n)↓ₓ ++
              [(e.1 ((trN e s n).map Prod.snd)).get hdom]) hh =
              some (output s ((trN e s n).map Prod.fst ++
                [(e.1 ((trN e s n).map Prod.snd)).get hdom]) hy) := by
          intro hh
          rw [output_fullyDefined]
          have hdrop : (((DDE.Total.transcript s e.total n)↓ₓ) ++
              [(e.1 ((trN e s n).map Prod.snd)).get hdom]).dropLast =
              (DDE.Total.transcript s e.total n)↓ₓ := by simp
          have hlast : (((DDE.Total.transcript s e.total n)↓ₓ) ++
              [(e.1 ((trN e s n).map Prod.snd)).get hdom]).getLast (by simp) =
              (e.1 ((trN e s n).map Prod.snd)).get hdom := by simp
          rw [hdrop, hlast, hins]
          have hkept : keptPrefix s ((trN e s n).map Prod.fst) =
              (trN e s n).map Prod.fst := by
            rcases trN_map_fst_mem_dom_or_nil e s n with hnil | hmem
            · simp [hnil, keptPrefix]
            · exact keptPrefix_eq_self_of_mem s hmem
          dsimp only
          rw [hkept, dif_pos hy]
        simp only [DDE.Total.transcript, hxval, hout]
        have hstep : trN e s (n + 1) = trN e s n ++
            [((e.1 ((trN e s n).map Prod.snd)).get hdom,
              output s ((trN e s n).map Prod.fst ++
                [(e.1 ((trN e s n).map Prod.snd)).get hdom]) hy)] := by
          show trStep e s (trN e s n) = _
          rw [trStep, dif_pos hdom, dif_pos hy]
        rw [hstep, List.map_append, ← ih]
        rfl
      · -- the environment stops; both presentations stall
        have hxval : e.total ((DDE.Total.transcript s e.total n)↓ᵧ) = none := by
          rw [houts, DDE.total_map_some, dif_neg hdom]
        have hstep : trN e s (n + 1) = trN e s n := by
          show trStep e s (trN e s n) = _
          rw [trStep, dif_neg hdom]
        simp only [DDE.Total.transcript, hxval, hstep]
        exact ih

/-- Stripping the coding recovers the primary transcript exactly. -/
theorem DDE.Total.answeredEntries_transcript_total (e : DDE Y X)
    (s : DDS X Y) (h : Compatible e s) (n : ℕ) :
    answeredEntries (DDE.Total.transcript s e.total n) = trN e s n := by
  rw [DDE.Total.transcript_total e s h n, answeredEntries_map_some]

end

end System

/-! ## The fully defined advantage (carrier-v2 Ruling R4)

CR18 Definitions 3.6/3.7 supply the total presentation of the interaction;
Lanzenberger Definition 2.26 supplies the metric.  Composing them at the
completed signature is the statement-facing distance of the fully defined
carrier: `Adv⊥(S, T)` is the supremum, over *all* total environments and all
interaction lengths, of the statistical distance of the length-`n` transcript
laws.

Two side conditions of `PDS.Adv` are gone, and that is the point of the
ruling.  There is no compatibility premise: the completion `s⊥` answers every
query, refusal being the observable answer `none` (Ruling R2), so every total
environment interacts with every system.  There is no stopping premise
either: the interaction is indexed by its length, and the supremum over
lengths replaces the stabilization stage that `PDS.trLaw` had to wait for.
The completion itself is not written here — it lives inside
`System.DDE.Total.transcript`, which queries `s⊥` by construction. -/

noncomputable section

open Probability (Distribution statDist)

open scoped ENNReal

universe u' v'

variable {X : Type u'} {Y : Type v'}

namespace PDS

/-- CR18 **Definition 3.7** transcript law at length `n`: the pushforward of
the system law along the total-environment transcript.  The completion is
internal to `System.DDE.Total.transcript`, so this is the law of the CR18
interaction of `S⊥` with `e` after `n` environment moves. -/
def trLawFullyDefined (e : System.DDE.Total Y X) (n : ℕ) (S : PDS X Y) :
    Distribution (List (X × Option Y)) :=
  Distribution.fTransform (fun s => System.DDE.Total.transcript s e n) S

/-- **Ruling R4**: the fully defined advantage — Lanzenberger **Definition
2.26** taken over the CR18 total presentation (Definitions 3.6/3.7).  No
compatibility and no stopping side condition: every total environment
interacts with every system through `s⊥`, and the interaction length is an
index of the supremum rather than a hypothesis. -/
def advFullyDefined (S T : PDS X Y) : ℝ≥0∞ :=
  ⨆ e : System.DDE.Total Y X, ⨆ n : ℕ,
    ENNReal.ofReal
      (statDist (trLawFullyDefined e n S) (trLawFullyDefined e n T))

/-- Ruling R4 notation: `Adv⊥(S, T)` is the fully defined advantage. -/
scoped notation "Adv⊥(" S ", " T ")" => PDS.advFullyDefined S T

@[simp]
theorem advFullyDefined_self (S : PDS X Y) : advFullyDefined S S = 0 :=
  le_antisymm
    (iSup_le fun _ => iSup_le fun _ => by simp [Probability.statDist_self])
    (zero_le _)

/-! ### Pseudometric laws

`Adv⊥` is a supremum of `ENNReal.ofReal ∘ δ` over a fixed index set, so the
pseudometric laws are the laws of `δ` transported index by index: reflexivity
is `statDist_self`, the triangle inequality is `statDist_triangle` at a
*common* `(e, n)`, and symmetry is `statDist_symm_of_eq_weight` — Lanzenberger
Definition 2.4 is one-sided, and its own remark makes it symmetric exactly at
equal weight.  Systems of equal weight is not a restriction on the intended
objects (probability laws all have weight one); it is the honest hypothesis
for the signed carrier, where `δ` genuinely is not symmetric. -/

/-- The transcript law has the weight of the system law: pushing forward moves
mass without creating or destroying it.

In `dist_simp` (`Probability/SimpAttr.lean`): the weight of a derived law is
bookkeeping no source states, and a proof that has to name it is spending a
line on the pushforward rather than on the argument. -/
@[dist_simp] theorem weight_trLawFullyDefined (e : System.DDE.Total Y X) (n : ℕ)
    (S : PDS X Y) :
    (trLawFullyDefined e n S).weight = S.weight :=
  Distribution.weight_fTransform _ S

/-- Symmetry of `Adv⊥` for systems of equal weight — in particular for any two
probability laws.  The hypothesis is exactly the one under which Lanzenberger
Definition 2.4 is symmetric; on the signed carrier `δ` is one-sided and no
unconditional symmetry holds. -/
theorem advFullyDefined_comm_of_weight_eq (S T : PDS X Y)
    (h : S.weight = T.weight) :
    advFullyDefined S T = advFullyDefined T S := by
  refine iSup_congr fun e => iSup_congr fun n => ?_
  rw [Probability.statDist_symm_of_eq_weight _ _
    (by rw [weight_trLawFullyDefined, weight_trLawFullyDefined, h])]

/-- Triangle inequality for `Adv⊥`: the two right-hand suprema are taken at
the same environment and the same length as the left-hand one, so the
distribution-level triangle inequality suffices. -/
theorem advFullyDefined_triangle (S T U : PDS X Y) :
    advFullyDefined S U ≤ advFullyDefined S T + advFullyDefined T U := by
  refine iSup_le fun e => iSup_le fun n => ?_
  calc
    ENNReal.ofReal (statDist (trLawFullyDefined e n S) (trLawFullyDefined e n U))
        ≤ ENNReal.ofReal
            (statDist (trLawFullyDefined e n S) (trLawFullyDefined e n T)) +
          ENNReal.ofReal
            (statDist (trLawFullyDefined e n T) (trLawFullyDefined e n U)) := by
          rw [← ENNReal.ofReal_add (Probability.statDist_nonneg _ _)
            (Probability.statDist_nonneg _ _)]
          exact ENNReal.ofReal_le_ofReal (Probability.statDist_triangle _ _ _)
    _ ≤ advFullyDefined S T + advFullyDefined T U :=
        add_le_add (le_iSup_of_le e (le_iSup_of_le n le_rfl))
          (le_iSup_of_le e (le_iSup_of_le n le_rfl))

/-- **Convexity of `Adv⊥` along a mixture**: a law that samples an index and
then runs the indexed system is no further from its counterpart than the
weighted average of the indexed advantages.

The transcript law is a pushforward, hence linear (`fTransform_sum`,
`fTransform_smul`), so a mixture of system laws is the same mixture of
transcript laws at every `(e, n)`; the probability-level `statDist_sum_le`
then applies index by index and the bound no longer depends on `(e, n)`.

Non-negative weights, as at the probability level: this is the estimate that
reduces a probabilistic converter to its deterministic support, and a signed
weight would break it. -/
theorem advFullyDefined_sum_le {ι : Type*} (t : Finset ι) (w : ι → ℝ)
    (R S : ι → PDS X Y) (hw : ∀ i ∈ t, 0 ≤ w i) :
    advFullyDefined (∑ i ∈ t, w i • R i) (∑ i ∈ t, w i • S i) ≤
      ∑ i ∈ t, ENNReal.ofReal (w i) * advFullyDefined (R i) (S i) := by
  refine iSup_le fun e => iSup_le fun n => ?_
  have hlin : ∀ L : ι → PDS X Y,
      trLawFullyDefined e n (∑ i ∈ t, w i • L i) =
        ∑ i ∈ t, w i • trLawFullyDefined e n (L i) := by
    intro L
    show Distribution.fTransform _ (∑ i ∈ t, w i • L i) = _
    rw [Distribution.fTransform_sum]
    exact Finset.sum_congr rfl fun i _ => Distribution.fTransform_smul _ _ _
  rw [hlin R, hlin S]
  calc
    ENNReal.ofReal
        (statDist (∑ i ∈ t, w i • trLawFullyDefined e n (R i))
          (∑ i ∈ t, w i • trLawFullyDefined e n (S i)))
        ≤ ENNReal.ofReal (∑ i ∈ t, w i *
            statDist (trLawFullyDefined e n (R i))
              (trLawFullyDefined e n (S i))) :=
          ENNReal.ofReal_le_ofReal (Probability.statDist_sum_le t w _ _ hw)
    _ = ∑ i ∈ t, ENNReal.ofReal (w i *
          statDist (trLawFullyDefined e n (R i))
            (trLawFullyDefined e n (S i))) :=
          ENNReal.ofReal_sum_of_nonneg fun i hi =>
            mul_nonneg (hw i hi) (Probability.statDist_nonneg _ _)
    _ ≤ ∑ i ∈ t, ENNReal.ofReal (w i) * advFullyDefined (R i) (S i) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [ENNReal.ofReal_mul (hw i hi)]
          refine mul_le_mul' le_rfl ?_
          show ENNReal.ofReal
              (statDist (trLawFullyDefined e n (R i))
                (trLawFullyDefined e n (S i))) ≤ advFullyDefined (R i) (S i)
          exact le_iSup_of_le e (le_iSup_of_le n le_rfl)

/-- **The Ruling-R4 bridge**: interaction never tells two systems apart by
more than their laws already differ.  Every transcript law is a pushforward
of the system law along a fixed deterministic map — the environment and the
length are fixed before the system is sampled — so the data processing
inequality (Lanzenberger Lemma 2.7, `statDist_fTransform_le`) bounds every
index of the supremum by the static distance `δ(S, T)`.

This is the inequality half of R4's `Adv⊥ ≤ δ`; equality on the finite
shared-domain slice (Lanzenberger Theorem 2.31) is separate work. -/
theorem advFullyDefined_le_statDist (S T : PDS X Y) :
    advFullyDefined S T ≤ ENNReal.ofReal (statDist S T) :=
  iSup_le fun e => iSup_le fun n =>
    ENNReal.ofReal_le_ofReal
      (Probability.statDist_fTransform_le S T
        (fun s => System.DDE.Total.transcript s e n))

/-- **The coupling method on Φ**: exhibit a coupling of the two system laws
and the fully defined advantage is bounded by the mass that coupling puts off
the diagonal.

  `IsCoupling J R S → J ≥ 0 → Adv⊥(R, S) ≤ Pr_{(r,s) ∼ J}(r ≠ s)`.

This is the whole method in one statement: a proof no longer has to reason
about environments at all — it exhibits a joint law under which the two
systems are *equal* except on a small event, and that event's mass is the
bound.  Interaction is already accounted for by the R4 bridge
(`advFullyDefined_le_statDist`), which is the data processing inequality at
every environment and length; couplings then bound the static distance
(Lanzenberger Lemma 2.8, `Probability.statDist_le_offDiagonalMass`), and
Lemma 2.8's attainment half (`Probability.exists_coupling_offDiagonalMass_eq`)
says the best coupling loses nothing against `δ` — the whole slack of the
chain sits in the first inequality, where the environment cannot see the
system's identity.

The non-negativity hypothesis is the signed-carrier caveat inherited from
Lemma 2.8: `IsCoupling` constrains the marginals, and the honesty of the joint
law is separate.  For probability systems it is automatic. -/
theorem advFullyDefined_le_offDiagonalMass {R S : PDS X Y}
    {J : Distribution (System.DDS X Y × System.DDS X Y)}
    (hJ : Distribution.IsCoupling J R S) (hnn : ∀ p, 0 ≤ J p) :
    advFullyDefined R S ≤ ENNReal.ofReal (Distribution.offDiagonalMass J) :=
  (advFullyDefined_le_statDist R S).trans
    (ENNReal.ofReal_le_ofReal (Probability.statDist_le_offDiagonalMass hJ hnn))

end PDS

end

end RandomSystems
