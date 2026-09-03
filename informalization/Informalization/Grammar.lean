/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Grammatical engine

Pure, total, unit-tested grammar primitives (DESIGN §6). No metaprogramming, no
`Lean` import — the reusable jewel, and the piece cnl-rs most lacks
(`UPSTREAM_TO_CNL_RS.md`).

## Theoretical grounding (DESIGN §6.0 — not invented here)

This module is a small, faithful Lean rendering of two established frameworks; it
does not invent grammar rules.

* **Grammatical Framework (GF) and its Resource Grammar Library** (Aarne Ranta).
  GF separates an abstract syntax (meaning) from a concrete syntax (realization
  via *feature structures*) — exactly the talk's Lean-ontology → English-ontology
  mapping. Following GF's English RGL (`ParadigmsEng`):
  - agreement (number/determiner) is computed from a `Features` record, not
    guessed (`realizeNP`);
  - the indefinite article is a **lexical feature** carried on the noun, the
    written-form allomorphy heuristic only *seeds* it and is advisory
    (`seedArticle` / `indefiniteArticle`). This is the principled fix to the
    "a/an is a guess" critique: at realization the article is *data*, not a
    spelling computation.
* **Reiter & Dale, _Building NLG Systems_ (2000)** — microplanning. Entity
  *merging* is their **aggregation**; article/name choice is
  *referring-expression generation*; the `Let …`/`For all …` templates are
  *surface realization*. We use the standard names and the standard soundness
  obligation (aggregation must preserve truth conditions — our `isolation`).

## Correctness commitments (theorems)

* `mergeGroups_flatten` — **content preservation**: aggregation is a pure
  *grouping*; flattening recovers the original introductions unchanged.
  `mergeGroups_names` is the names corollary.
* `mergeGroups_isolation` — aggregation only ever groups introductions that do
  **not** cross-reference each other (the Reiter–Dale truth-preservation
  obligation; DESIGN §6.3, Round-1 finding 5).
-/

namespace Informalization.Grammar

/-! ## Articles -/

/-- An indefinite article. -/
inductive Article | a | an
  deriving DecidableEq, Repr, BEq, Inhabited

/-- How an article choice was reached — surfaced to the author so a wrong guess
is visible and fixable, never silent. -/
inductive ArticleSource
  | overridden  -- matched the math-word table
  | heuristic   -- leading-sound guess
  | unknown     -- genuinely ambiguous; defaulted to `a`, flagged
  deriving DecidableEq, Repr, BEq, Inhabited

def Article.toString : Article → String
  | .a => "a"
  | .an => "an"

instance : ToString Article := ⟨Article.toString⟩

/-- The first whitespace/hyphen-delimited token of a phrase (what determines the
article). E.g. `"n-cube"` → `"n"`, `"natural number"` → `"natural"`. -/
def firstToken (s : String) : String :=
  String.ofList (s.trimAscii.toString.toList.takeWhile
    (fun c => c != ' ' && c != '-' && c != '\t'))

/-- Single-symbol / single-letter heads whose *spoken* form starts with a vowel
sound (so they take "an"): "an n-cube", "an x", "an ε-net", "an SVD". Exact match
on the first token only — never a prefix (so "natural" is unaffected). -/
def vowelSoundHeads : List String :=
  ["a", "e", "i", "o", "x", "f", "h", "l", "m", "n", "r", "s",
   "ε", "ℝ", "8", "SVD", "MMU", "FPGA", "honest", "honour", "honor", "hour", "heir"]

/-- Single-symbol / word heads whose *spoken* form starts with a consonant sound
despite a leading vowel letter (so they take "a"): "a unique map", "a one-form",
"a 1-form", "a unit". -/
def consonantSoundHeads : List String :=
  ["u", "unique", "unit", "unitary", "universal", "unital", "union", "useful",
   "one", "1", "y", "European"]

/-- Whether a string begins with a vowel *letter*. -/
def startsWithVowelLetter (s : String) : Bool :=
  match s.toList with
  | c :: _ => c.toLower ∈ ['a', 'e', 'i', 'o', 'u']
  | [] => false

/-- **Article allomorphy seeder** (GF `ParadigmsEng` style). Given a noun's
written head, *suggest* its indefinite-article allomorph and say how the guess
was made. This is **only a seeder** for the lexical `Noun.article` feature
(DESIGN §6.0): at realization time the article is read from the lexicon, not
recomputed here. Advisory — a/an depends on pronunciation, which is
reader-dependent. -/
def seedArticle (phrase : String) : Article × ArticleSource :=
  let tok := firstToken phrase
  if consonantSoundHeads.contains tok then (.a, .overridden)
  else if vowelSoundHeads.contains tok then (.an, .overridden)
  else if tok.isEmpty then (.a, .unknown)
  -- a lone unrecognised symbol/number we cannot pronounce → ambiguous
  else if tok.length == 1 && !(tok.toList.head!.isAlpha) then (.a, .unknown)
  else if startsWithVowelLetter tok then (.an, .heuristic)
  else (.a, .heuristic)

/-- Backwards-compatible name for `seedArticle`. -/
abbrev indefiniteArticle := seedArticle

/-- Just the seeded article (drops the source). -/
def article (phrase : String) : Article := (seedArticle phrase).1

/-! ## Number, agreement, and the subjunctive -/

/-- Grammatical number. -/
inductive Number | singular | plural
  deriving DecidableEq, Repr, BEq, Inhabited

/-- The verb "to be", agreeing with number and mood. The *subjunctive* ("Let n
*be* …") vs the indicative ("Suppose n *is* …") — slide 58. -/
def verbToBe (n : Number) (subjunctive : Bool) : String :=
  if subjunctive then "be"
  else match n with | .singular => "is" | .plural => "are"

/-! ## List joining (Oxford comma) -/

/-- Join names as an English list: `["α"] → "α"`, `["α","β"] → "α and β"`,
`["α","β","γ"] → "α, β and γ"`. -/
def joinAnd : List String → String
  | [] => ""
  | [a] => a
  | [a, b] => a ++ " and " ++ b
  | a :: rest => a ++ ", " ++ joinAnd rest

/-! ## Entity-introduction merging -/

/-- One entity introduction, before merging. Carries everything the merge needs:
the shared "shape" (noun + adjectives + accessories + mood) and the `mentions`
set used to detect cross-references. -/
structure Intro where
  name : String
  nounSingular : String
  nounPlural : String
  adjectives : List String := []
  accessories : List String := []
  subjunctive : Bool := true
  /-- Optional per-name type annotation, e.g. `"α → β"`, rendered as
  "Let f : α → β be …" (matches Kyle's `inj_comp` slide). Plain text/Unicode. -/
  typeStr : String := ""
  /-- Names this introduction's text/type refers to (for `crossRef`). -/
  mentions : List String := []
  deriving Repr, BEq, Inhabited

/-- Two introductions have the same *shape* (everything except name and
mentions). Mergeable conjuncts must share a shape so "Let α, β be types" is
well-formed. -/
def sameShape (a b : Intro) : Bool :=
  a.nounSingular == b.nounSingular && a.nounPlural == b.nounPlural &&
  a.adjectives == b.adjectives && a.accessories == b.accessories &&
  a.subjunctive == b.subjunctive

/-- `a` and `b` cross-reference if either names the other (DESIGN §6.3). -/
def crossRef (a b : Intro) : Bool :=
  b.name ∈ a.mentions || a.name ∈ b.mentions

/-- `x` may join the group `g` (to its right): `g` is nonempty, `x` shares its
shape, and `x` cross-references none of `g`'s members. -/
def canMerge (x : Intro) (g : List Intro) : Bool :=
  match g with
  | [] => false
  | m :: _ => sameShape x m && g.all (fun y => !crossRef x y)

/-- Group consecutive introductions into maximal mergeable runs. Returns a list
of nonempty groups; each group becomes one sentence at the realize step. -/
def mergeGroups : List Intro → List (List Intro)
  | [] => []
  | x :: xs =>
    match mergeGroups xs with
    | [] => [[x]]
    | g :: gs =>
      if canMerge x g then (x :: g) :: gs
      else [x] :: g :: gs

/-! ### Correctness of merging -/

/-- **Content preservation (strong form).** Merging is a pure grouping:
flattening the groups recovers the original introductions, in order. Nothing is
lost, duplicated, or reordered. -/
theorem mergeGroups_flatten (xs : List Intro) : (mergeGroups xs).flatten = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [mergeGroups]
    split
    · rename_i heq
      rw [heq] at ih
      simp only [List.flatten_nil] at ih
      simp [← ih]
    · rename_i g gs heq
      rw [heq] at ih
      simp only [List.flatten_cons] at ih
      split <;> simp [List.flatten_cons, List.cons_append, ih]

/-- **Content preservation (names corollary).** The names a merge introduces,
read left-to-right across all groups, are exactly the original names in order. -/
theorem mergeGroups_names (xs : List Intro) :
    ((mergeGroups xs).flatten).map (·.name) = xs.map (·.name) := by
  rw [mergeGroups_flatten]

/-- **Isolation.** Every group emitted by `mergeGroups` is *internally
cross-reference free at its head*: the first member cross-references none of the
others. With the left-to-right construction (each new head is admitted only when
`canMerge` holds against the whole group), this is the well-formedness guarantee
of DESIGN §6.3 — a merged sentence never asserts a dependency the unmerged form
did not. -/
theorem mergeGroups_isolation (xs : List Intro) :
    ∀ g ∈ mergeGroups xs, ∀ m ms, g = m :: ms →
      ms.all (fun y => !crossRef m y) = true := by
  induction xs with
  | nil => intro g hg m ms _; simp [mergeGroups] at hg
  | cons x xs ih =>
    simp only [mergeGroups]
    split
    · intro g hg m ms hgm
      simp only [List.mem_singleton] at hg
      subst hg; cases hgm; rfl
    · rename_i g0 gs heq
      split
      · rename_i hc
        intro g hg m ms hgm
        rw [List.mem_cons] at hg
        rcases hg with hg | hg
        · -- the freshly grown group (x :: g0); head x cross-references none of g0
          subst hg
          cases hgm
          unfold canMerge at hc
          cases hg0 : g0 with
          | nil => rw [hg0] at hc; simp at hc
          | cons m0 ms0 =>
            rw [hg0] at hc
            simp only [Bool.and_eq_true] at hc
            simpa using hc.2
        · exact ih g (by rw [heq]; exact List.mem_cons_of_mem _ hg) m ms hgm
      · intro g hg m ms hgm
        rw [List.mem_cons] at hg
        rcases hg with hg | hg
        · subst hg; cases hgm; rfl
        · exact ih g (by rw [heq]; exact hg) m ms hgm

/-- Reiter–Dale name for `mergeGroups`: combining simple phrase specifications
into more complex sentence structures. Provided so call sites read with the
standard NLG vocabulary. -/
abbrev aggregate := mergeGroups

/-! ## Surface realization (GF-RGL feature model)

A noun phrase is realized from a `Features` record (GF's parameter/table model):
the determiner and number agree by *computation*, and the indefinite article is
read as a *lexical feature* (`art`), not recomputed from spelling. -/

/-- The determiner slot of a noun phrase. -/
inductive Determiner
  | indefinite      -- "a"/"an", realized from the lexical article feature
  | none_           -- bare (e.g. plurals after a numeral, or "types")
  deriving DecidableEq, Repr, BEq, Inhabited

/-- A GF-style feature bundle for realizing a common-noun phrase. -/
structure Features where
  number : Number
  det : Determiner
  /-- the lexical article feature (used only when `det = indefinite` and singular) -/
  art : Article
  deriving Repr, Inhabited

/-- Realize the determiner+core-noun of a noun phrase from its features and the
noun's singular/plural surface forms. Pure GF-style realization: the article is
*read* from `f.art`, agreement is *computed* from `f.number`. -/
def realizeNounPhrase (f : Features) (singular plural : String) : String :=
  match f.number, f.det with
  | .singular, .indefinite => s!"{f.art} {singular}"
  | .singular, .none_      => singular
  | .plural,   _           => plural

/-- Attributive adjective prefix: stacked, space-separated ("injective
continuous "), empty when there are none. -/
def adjPrefix (adjs : List String) : String :=
  if adjs.isEmpty then "" else String.intercalate " " adjs ++ " "

/-- A name, optionally with its type annotation: `f` or `f : α → β`. -/
def nameWithType (i : Intro) : String :=
  if i.typeStr.isEmpty then i.name else i.name ++ " : " ++ i.typeStr

/-- Surface-realize one aggregated group of introductions as a single sentence
(Reiter–Dale surface realization of a `Let …` message). A singleton uses the
singular noun with its lexical article; a merged group uses the bare plural with
an Oxford-comma name list and plural agreement. The mood selects the verb
(subjunctive "be" vs indicative "is/are", slide 58). -/

def realizeIntroGroup : List Intro → String
  | [] => ""
  | [x] =>
    -- GF: the indefinite article is seeded from the *head of the noun phrase*,
    -- i.e. the first adjective if present ("an injective function").
    let adj := adjPrefix x.adjectives
    let art := (seedArticle (adj ++ x.nounSingular)).1
    let acc := if x.accessories.isEmpty then "" else " with " ++ joinAnd x.accessories
    s!"Let {nameWithType x} {verbToBe .singular x.subjunctive} {art} {adj}{x.nounSingular}{acc}."
  | x :: xs =>
    let g := x :: xs
    let names := joinAnd (g.map nameWithType)
    let adj := adjPrefix x.adjectives
    let acc := if x.accessories.isEmpty then "" else " with " ++ joinAnd x.accessories
    -- plural noun phrase takes no indefinite article ("be injective functions")
    s!"Let {names} {verbToBe .plural x.subjunctive} {adj}{x.nounPlural}{acc}."

/-- Realize a whole list of introductions: aggregate, then surface-realize each
group, joined by spaces. This is the end-to-end GF/Reiter–Dale path. -/
def realizeIntros (xs : List Intro) : String :=
  String.intercalate " " ((aggregate xs).map realizeIntroGroup)

end Informalization.Grammar

section GrammarTests
open Informalization.Grammar

-- Article seeding (advisory): vowel-letter heuristic, math overrides, ambiguity.
/-- info: (Informalization.Grammar.Article.an, Informalization.Grammar.ArticleSource.heuristic) -/
#guard_msgs in #eval seedArticle "injective function"
#guard (seedArticle "natural number").1 == Article.a
#guard (seedArticle "unique map").1 == Article.a          -- "a unique", not "an"
#guard (seedArticle "n-cube").1 == Article.an             -- "an n-cube"

-- Agreement and the subjunctive.
#guard verbToBe Number.singular true == "be"
#guard verbToBe Number.plural false == "are"

-- Oxford-comma aggregation.
#guard joinAnd ["α", "β", "γ"] == "α, β and γ"

-- End-to-end realization: three same-shape, non-cross-referencing intros merge.
private def tyIntro (n : String) : Intro :=
  { name := n, nounSingular := "type", nounPlural := "types" }
#guard realizeIntros [tyIntro "α", tyIntro "β", tyIntro "γ"]
        == "Let α, β and γ be types."
#guard realizeIntros [tyIntro "n"] == "Let n be a type."

-- A cross-reference blocks aggregation (isolation): "β is an α-module" must not
-- merge with "α is a type" (different shape anyway, but also mentions α).
private def modIntro : Intro :=
  { name := "β", nounSingular := "module", nounPlural := "modules", mentions := ["α"] }
#guard (aggregate [tyIntro "α", modIntro]).length == 2

end GrammarTests
