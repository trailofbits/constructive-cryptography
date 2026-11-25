/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Literary Mathematical Grammar & Maurer-Voice Discourse Engine

Pure, total, unit-tested grammar and microplanning primitives grounded in:
* **Kyle Miller & Patrick Massot's InformalLean ontology** (`Entity`/`Noun`/`Adjective`/`Accessory`,
  number/article agreement, subjunctive mood, and entity merging);
* **Grammatical Framework (GF) English RGL** (morphosyntactic feature agreement, lexical articles,
  arity-driven singular/plural inflection — never emitting legalisms like `"interface(s)"`);
* **Reiter & Dale microplanning** (content-preserving, cross-reference-isolated aggregation,
  first-mention vs. definite anaphora, and rhetorical cadence);
* **Knuth / Halmos mathematical writing rules** and **Ueli Maurer's calm, top-down didactic voice**
  (MR16, Maurer 2011, CR18).

Zero `Lean` metaprogramming imports: this module is pure, fast, and formally checked.
-/

namespace Informalization.Core.Grammar

/-! ## Articles & Crypto/Math Spoken Phonology -/

inductive Article | a | an
  deriving DecidableEq, Repr, BEq, Inhabited

def Article.toString : Article → String
  | .a => "a"
  | .an => "an"

instance : ToString Article := ⟨Article.toString⟩

/-- First lexical head token (ignoring leading math delimiters `\(` or `$`). -/
def firstToken (s : String) : String :=
  let s := s.trimAscii.toString
  let s := if s.startsWith "\\(" then (s.drop 2).toString.trimAscii.toString else s
  let s := if s.startsWith "$" then (s.drop 1).toString.trimAscii.toString else s
  let s := if s.startsWith "\\" then (s.drop 1).toString else s
  String.ofList (s.toList.takeWhile fun c =>
    c != ' ' && c != '-' && c != '\t' && c != '_' && c != '^' && c != '\\' && c != ')' && c != '$')

/-- Heads whose spoken mathematical/cryptographic pronunciation begins with a vowel sound
(`"an ε-ball"`, `"an ℓ-byte key"`, `"an n-bit digest"`, `"an MBO"`, `"an AEAD scheme"`,
`"an H-coefficient"`, `"an IV"`). -/
def vowelSoundHeads : List String :=
  [ "a", "e", "f", "h", "i", "l", "m", "n", "o", "r", "s", "x",
    "α", "ε", "η", "ℓ", "ω", "Ω",
    "alpha", "varepsilon", "epsilon", "eta", "ell", "omega", "Omega",
    "ℝ", "8", "11", "18", "80",
    "MBO", "AEAD", "AE", "IV", "H", "IND", "INT", "CCA", "CPA", "UF", "EUF",
    "HMAC", "HKDF", "SVD", "MMU", "FPGA",
    "honest", "hour", "ideal", "injective", "independent", "insecure", "inside", "outside",
    "adversarial", "arbitrary", "authenticated", "abstract", "adaptive", "explicit", "exact",
    "equal", "extended", "effective", "empty", "ordered", "unbounded", "uniformly" ]

/-- Heads whose spoken pronunciation begins with a consonant sound despite a vowel letter
(`"a URF"`, `"a URP"`, `"a uniform"`, `"a unique"`, `"a unit"`, `"a one-time pad"`). -/
def consonantSoundHeads : List String :=
  [ "u", "y", "one", "1", "URF", "URP", "UC",
    "uniform", "unique", "unit", "unitary", "universal", "unital", "union", "useful",
    "user", "users", "European" ]

private def startsWithVowelLetter (s : String) : Bool :=
  match s.toList with
  | c :: _ => c.toLower ∈ ['a', 'e', 'i', 'o', 'u']
  | [] => false

/-- Determine the indefinite article `"a"` / `"an"` from spoken math/crypto phonology. -/
def article (phrase : String) : Article :=
  let tok := firstToken phrase
  if consonantSoundHeads.contains tok then .a
  else if vowelSoundHeads.contains tok then .an
  else if tok.isEmpty then .a
  else if startsWithVowelLetter tok then .an
  else .a

/-! ## Number, Arity-Driven Inflection & Verb Conjugation -/

inductive Number | singular | plural
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Exact grammatical number from a concrete cardinality. Never emits `"X(s)"`. -/
def numberOfNat (n : Nat) : Number :=
  if n == 1 then .singular else .plural

/-- A countable English noun with explicit singular and plural forms. -/
structure CountNoun where
  singular : String
  plural : String
  deriving DecidableEq, Repr, BEq, Inhabited

def CountNoun.inflect (n : CountNoun) : Number → String
  | .singular => n.singular
  | .plural => n.plural

/-- Standard CC & mathematical nouns with exact singular/plural forms. -/
def nounInterface : CountNoun := ⟨"interface", "interfaces"⟩
def nounResource : CountNoun := ⟨"resource", "resources"⟩
def nounConverter : CountNoun := ⟨"converter", "converters"⟩
def nounProtocol : CountNoun := ⟨"protocol", "protocols"⟩
def nounSpecification : CountNoun := ⟨"specification", "specifications"⟩
def nounDistinguisher : CountNoun := ⟨"distinguisher", "distinguishers"⟩
def nounSimulator : CountNoun := ⟨"simulator", "simulators"⟩
def nounQuery : CountNoun := ⟨"query", "queries"⟩
def nounUser : CountNoun := ⟨"user", "users"⟩
def nounKey : CountNoun := ⟨"key", "keys"⟩
def nounGame : CountNoun := ⟨"game", "games"⟩
def nounSystem : CountNoun := ⟨"system", "systems"⟩
def nounStep : CountNoun := ⟨"step", "steps"⟩
def nounBound : CountNoun := ⟨"bound", "bounds"⟩
def nounHypothesis : CountNoun := ⟨"hypothesis", "hypotheses"⟩

/-- Inflect a noun by exact count: `countPhrase 1 nounQuery = "one query"`,
`countPhrase 2 nounInterface = "two interfaces"`. -/
def smallCardinal : Nat → Option String
  | 0 => some "zero"
  | 1 => some "one"
  | 2 => some "two"
  | 3 => some "three"
  | 4 => some "four"
  | 5 => some "five"
  | 6 => some "six"
  | _ => none

def countPhrase (k : Nat) (noun : CountNoun) (useWordsForSmall : Bool := true) : String :=
  let numStr :=
    if useWordsForSmall then (smallCardinal k).getD (toString k) else toString k
  s!"{numStr} {noun.inflect (numberOfNat k)}"

/-- A present-tense English verb with third-person singular, plural, and subjunctive forms. -/
structure Verb where
  thirdSingular : String
  plural : String
  subjunctive : String := plural
  deriving DecidableEq, Repr, BEq, Inhabited

def Verb.conjugate (v : Verb) (num : Number) (subj : Bool := false) : String :=
  if subj then v.subjunctive
  else match num with
    | .singular => v.thirdSingular
    | .plural => v.plural

def verbBe : Verb := ⟨"is", "are", "be"⟩
def verbHave : Verb := ⟨"has", "have", "have"⟩
def verbSatisfy : Verb := ⟨"satisfies", "satisfy", "satisfy"⟩
def verbConstruct : Verb := ⟨"constructs", "construct", "construct"⟩
def verbBound : Verb := ⟨"bounds", "bound", "bound"⟩
def verbPreserve : Verb := ⟨"preserves", "preserve", "preserve"⟩
def verbCommute : Verb := ⟨"commutes", "commute", "commute"⟩
def verbYield : Verb := ⟨"yields", "yield", "yield"⟩
def verbReduce : Verb := ⟨"reduces", "reduce", "reduce"⟩
def verbImply : Verb := ⟨"implies", "imply", "imply"⟩
def verbHold : Verb := ⟨"holds", "hold", "hold"⟩
def verbAct : Verb := ⟨"acts", "act", "act"⟩
def verbMap : Verb := ⟨"maps", "map", "map"⟩
def verbExpose : Verb := ⟨"exposes", "expose", "expose"⟩
def verbProvide : Verb := ⟨"provides", "provide", "provide"⟩
def verbGuarantee : Verb := ⟨"guarantees", "guarantee", "guarantee"⟩

/-! ## Natural List Joining -/

/-- Natural academic English coordination: `["A"] → "A"`, `["A","B"] → "A and B"`,
`["A","B","C"] → "A, B, and C"`. -/
def joinAnd : List String → String
  | [] => ""
  | [a] => a
  | [a, b] => a ++ " and " ++ b
  | a :: b :: c :: rest =>
      let init := (a :: b :: c :: rest).dropLast
      let last := (a :: b :: c :: rest).getLast!
      String.intercalate ", " init ++ ", and " ++ last

/-- Clause coordination with semicolons when clauses contain internal commas. -/
def joinClauses (clauses : List String) : String :=
  match clauses with
  | [] => ""
  | [c] => c
  | [a, b] =>
      if a.contains ',' || b.contains ',' then a ++ "; and " ++ b
      else a ++ ", and " ++ b
  | _ =>
      let init := clauses.dropLast
      let last := clauses.getLast!
      String.intercalate "; " init ++ "; and " ++ last

/-- Render an interface specification phrase with exact singular/plural inflection
(e.g., `["A"] → "with interface A"`, `["H", "P"] → "with interfaces H and P"`). -/
def withInterfacesPhrase (ifaceNames : List String) : String :=
  match ifaceNames with
  | [] => ""
  | [a] => s!"with interface {a}"
  | xs => s!"with interfaces {joinAnd xs}"

/-! ## Entity-Introduction Aggregation (Proved Content-Preserving & Isolated) -/

structure Intro where
  name : String
  noun : CountNoun
  adjectives : List String := []
  accessories : List String := []
  subjunctive : Bool := true
  typeStr : String := ""
  mentions : List String := []
  deriving Repr, BEq, Inhabited

def sameShape (a b : Intro) : Bool :=
  a.noun == b.noun && a.adjectives == b.adjectives &&
  a.accessories == b.accessories && a.subjunctive == b.subjunctive

def crossRef (a b : Intro) : Bool :=
  b.name ∈ a.mentions || a.name ∈ b.mentions

def canMerge (x : Intro) (g : List Intro) : Bool :=
  match g with
  | [] => false
  | m :: _ => sameShape x m && g.all (fun y => !crossRef x y)

/-- Group consecutive compatible, non-cross-referencing entity introductions. -/
def mergeGroups : List Intro → List (List Intro)
  | [] => []
  | x :: xs =>
    match mergeGroups xs with
    | [] => [[x]]
    | g :: gs =>
      if canMerge x g then (x :: g) :: gs
      else [x] :: g :: gs

/-- Content preservation: aggregation never drops, duplicates, or reorders introductions. -/
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

/-- Isolation: no group head cross-references any later member of its group. -/
theorem mergeGroups_isolation (xs : List Intro) :
    ∀ g ∈ mergeGroups xs, ∀ m ms, g = m :: ms →
      ms.all (fun y => !crossRef m y) = true := by
  induction xs with
  | nil => intro g hg _ _ _; simp [mergeGroups] at hg
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
        · subst hg; cases hgm
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

private def adjPrefix (adjs : List String) : String :=
  if adjs.isEmpty then "" else String.intercalate " " adjs ++ " "

private def nameWithType (i : Intro) : String :=
  if i.typeStr.isEmpty then i.name
  else if i.name.startsWith "\\(" && i.name.endsWith "\\)" then
    let inner := ((i.name.drop 2).dropEnd 2).toString
    s!"\\({inner} : {i.typeStr}\\)"
  else
    i.name ++ " : " ++ i.typeStr

/-- Realize one aggregated introduction clause (without leading `"Let "` or trailing period),
so multiple clauses can be coordinated smoothly into a single flowing sentence. -/
def realizeIntroClause : List Intro → String
  | [] => ""
  | [x] =>
    let adj := adjPrefix x.adjectives
    let art := article (adj ++ x.noun.singular)
    let acc := if x.accessories.isEmpty then "" else " " ++ joinAnd x.accessories
    s!"{nameWithType x} {verbBe.conjugate .singular x.subjunctive} {art} {adj}{x.noun.singular}{acc}"
  | x :: xs =>
    let g := x :: xs
    let names := joinAnd (g.map nameWithType)
    let adj := adjPrefix x.adjectives
    let acc := if x.accessories.isEmpty then "" else " " ++ joinAnd x.accessories
    s!"{names} {verbBe.conjugate .plural x.subjunctive} {adj}{x.noun.plural}{acc}"

/-- Realize a sequence of entity introductions in Maurer's clean opening style:
aggregates same-shape entities and coordinates short clauses naturally. -/
def realizeIntros (xs : List Intro) : String :=
  let groups := mergeGroups xs
  let clauses := groups.map realizeIntroClause |>.filter (!·.isEmpty)
  match clauses with
  | [] => ""
  | [c] => s!"Let {c}."
  | [c1, c2] => s!"Let {c1}, and let {c2}."
  | _ =>
    let body := joinClauses clauses
    s!"Let {body}."

/-! ## Discourse State: Definiteness, Anaphora & Maurer Rhetorical Cadence -/

/-- Rhetorical roles for proof transitions, calibrated to Ueli Maurer's writing style. -/
inductive TransitionKind
  | setup          -- introducing objects / assumptions
  | elaboration    -- "More precisely, …" / "In other words, …"
  | consequence    -- "Hence …" / "Therefore …" / "It follows that …" / "Consequently, …"
  | justification  -- "Since …" / "Because …" / "By …"
  | reduction      -- "It suffices to show that …" / "It remains to bound …"
  | caveat         -- "Note, however, that …" / "Observe that …"
  | closing        -- "Combining these estimates yields …" / "This establishes the claim."
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Lightweight microplanning state threaded through a proof so prose stays varied,
uses definite anaphora after first mention, and never drones with repeated openers. -/
structure DiscourseState where
  introduced : List String := []
  lastOpener? : Option String := none
  stepCounter : Nat := 0
  deriving Repr, Inhabited

def DiscourseState.hasIntroduced (st : DiscourseState) (sym : String) : Bool :=
  st.introduced.contains sym

/-- Refer to a named mathematical object: first mention uses indefinite description,
subsequent mentions use concise definite anaphora (`"the resource R"`). -/
def DiscourseState.refer (st : DiscourseState) (sym : String) (noun : CountNoun)
    (firstMentionQualifiers : String := "") : String × DiscourseState :=
  if st.hasIntroduced sym then
    (s!"the {noun.singular} {sym}", st)
  else
    let full := if firstMentionQualifiers.isEmpty then noun.singular
      else s!"{firstMentionQualifiers} {noun.singular}"
    let art := article full
    (s!"{art} {full} {sym}", { st with introduced := sym :: st.introduced })

private def transitionCandidates : TransitionKind → List String
  | .setup         => ["Fix", "Consider", "Let"]
  | .elaboration   => ["More precisely,", "In other words,", "Specifically,"]
  | .consequence   => ["Hence,", "Therefore,", "It follows that", "Consequently,"]
  | .justification => ["By", "Applying", "From"]
  | .reduction     => ["It suffices to show that", "It remains to show that", "It suffices to bound"]
  | .caveat        => ["Note, however, that", "Observe that", "Remark that"]
  | .closing       => ["Combining these bounds yields", "Putting these steps together gives",
                       "This establishes"]

private def initialCandidates : TransitionKind → List String
  | .setup         => ["Fix", "Consider", "Let"]
  | .elaboration   => ["To prove the claim,", "First,"]
  | .consequence   => ["To prove the claim,", "First,"]
  | .justification => ["By", "Applying", "From"]
  | .reduction     => ["It suffices to show that", "It remains to show that", "It suffices to bound"]
  | .caveat        => ["Observe that", "Note that"]
  | .closing       => ["Direct verification establishes", "We establish"]

/-- Pick a Maurer-style discourse opener for `kind`, rotating away from the immediately
preceding opener so consecutive sentences keep natural literary rhythm. At the very start
of a proof (`stepCounter == 0 && lastOpener?.isNone`), never open with `"Consequently,"`,
`"Hence,"`, or `"Therefore,"`. -/
def DiscourseState.pickOpener (st : DiscourseState) (kind : TransitionKind) :
    String × DiscourseState :=
  let cands :=
    if st.stepCounter == 0 && st.lastOpener?.isNone then
      initialCandidates kind
    else
      transitionCandidates kind
  let filtered := match st.lastOpener? with
    | some prev => let f := cands.filter (· != prev); if f.isEmpty then cands else f
    | none => cands
  let chosen := filtered[st.stepCounter % filtered.length]?.getD ""
  (chosen, { st with lastOpener? := some chosen, stepCounter := st.stepCounter + 1 })

/-- Record that a sentence has been emitted (advancing discourse state away from proof start). -/
def DiscourseState.markEmitted (st : DiscourseState) (opener? : Option String := none) :
    DiscourseState :=
  { st with
    lastOpener? := opener? <|> st.lastOpener?
    stepCounter := st.stepCounter + 1 }

/-! ## Knuth / Halmos Mathematical Typography Rules -/

def capitalizeFirst (s : String) : String :=
  match s.toList with
  | [] => ""
  | c :: cs => String.ofList (c.toUpper :: cs)

def lowercaseFirst (s : String) : String :=
  match s.toList with
  | [] => ""
  | c :: cs => String.ofList (c.toLower :: cs)

/-- Ensure a sentence never opens with a bare math formula (`\(…\)` or `$…$`):
if a bare symbol leads, supply a grammatical subject noun (e.g., `"The system"`). -/
def protectLeadingMath (leadNoun : String) (sentence : String) : String :=
  let s := sentence.trimAscii.toString
  if s.startsWith "\\(" || s.startsWith "$" then
    s!"{capitalizeFirst leadNoun} {s}"
  else
    capitalizeFirst s

/-- Punctuate a sentence cleanly, avoiding double periods. -/
def ensurePeriod (s : String) : String :=
  let s := s.trimAscii.toString
  if s.isEmpty then ""
  else if s.endsWith "." || s.endsWith "!" || s.endsWith "?" || s.endsWith ":" then s
  else s ++ "."

/-- Format a display equation grammatically inside prose, placing punctuation inside the
display block per Knuth's *Mathematical Writing* (`punct` is `"."`, `","`, or `""`). -/
def displayEquation (latex : String) (punct : String := ".") : String :=
  let body := latex.trimAscii.toString
  let body :=
    if body.endsWith "." || body.endsWith "," then (body.dropEnd 1).toString.trimAscii.toString
    else body
  s!"\\[{body}{punct}\\]"

end Informalization.Core.Grammar

section GrammarUnitTests
open Informalization.Core.Grammar

-- Crypto/math spoken phonology
#guard article "ε-ball" == .an
#guard article "ℓ-byte key" == .an
#guard article "n-bit digest" == .an
#guard article "MBO" == .an
#guard article "AEAD scheme" == .an
#guard article "URF" == .a
#guard article "URP" == .a
#guard article "uniform random permutation" == .a
#guard article "unique map" == .a
#guard article "q-query distinguisher" == .a

-- Arity-driven interface inflection (zero "interface(s)"!)
#guard withInterfacesPhrase ["\\(A\\)"] == "with interface \\(A\\)"
#guard withInterfacesPhrase ["\\(H\\)", "\\(P\\)"] == "with interfaces \\(H\\) and \\(P\\)"
#guard countPhrase 1 nounQuery == "one query"
#guard countPhrase 2 nounInterface == "two interfaces"

-- Verb agreement
#guard verbConstruct.conjugate .singular == "constructs"
#guard verbConstruct.conjugate .plural == "construct"
#guard verbSatisfy.conjugate .singular == "satisfies"
#guard verbBe.conjugate .singular true == "be"

-- Aggregation + Maurer-style coordination
private def resIntro (n : String) : Intro := { name := n, noun := nounResource }
private def convIntro (n : String) : Intro := { name := n, noun := nounConverter }
#guard realizeIntros [resIntro "\\(R\\)", resIntro "\\(S\\)", convIntro "\\(\\pi\\)"] ==
  "Let \\(R\\) and \\(S\\) be resources, and let \\(\\pi\\) be a converter."

-- Anaphora: indefinite first mention -> definite subsequent mention
#guard (let (s1, st) := ({} : DiscourseState).refer "\\(\\Pi^{\\pm}\\)" nounResource "uniform"
        let (s2, _) := st.refer "\\(\\Pi^{\\pm}\\)" nounResource "uniform"
        (s1, s2)) == ("a uniform resource \\(\\Pi^{\\pm}\\)", "the resource \\(\\Pi^{\\pm}\\)")

-- Anti-repetition discourse cadence & valid initial opener
#guard (let (o1, st) := ({} : DiscourseState).pickOpener .consequence
        let (o2, _) := st.pickOpener .consequence
        o1 != o2 && o1 != "Hence," && o1 != "Therefore," && o1 != "Consequently,")

-- Knuth typography
#guard protectLeadingMath "the resource" "\\(R\\) satisfies the bound." ==
  "The resource \\(R\\) satisfies the bound."
#guard displayEquation "\\pi R \\approx_{\\varepsilon} S\\sigma" "." ==
  "\\[\\pi R \\approx_{\\varepsilon} S\\sigma.\\]"

end GrammarUnitTests
