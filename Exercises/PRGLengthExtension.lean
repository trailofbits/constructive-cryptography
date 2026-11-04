import Commons.Definitions.ReplyTransform
import ConstructiveCryptography.Tactics.Substitution

/-!
# PRG length extension: from definitions to a proof

Given `G : S → S × S`, let `H(s) = (a, c, d)` where `(a, b) = G(s)` and `(c, d) = G(b)`.
Prove that pseudorandomness of `G` implies pseudorandomness of `H`, with a fresh seed on each
of at most `q` calls and explicit losses for the two reductions.

Start with ordinary Lean functions and tuples. Sections 1–4 introduce the library through
worked examples and small edits. Section 5 introduces security proofs. Section 6 asks you to build
the PRG components, then section 7 asks for the final bounds.

The six `sorry` holes concern your PRG construction and proof. The reusable constructors and
contracts are available; you choose the reductions, intermediate systems and argument.

Put the cursor after `by` to see a goal. Check the file with
`lake env lean Exercises/PRGLengthExtension.lean`. The placeholders initially produce warnings.
Finish with no placeholders or extra assumptions, and check that each definition implements its
stated behavior.
-/

open Commons Commons.Evaluation ConstructiveCryptography Probability Probability.Distribution
  SystemAlgebra SystemAlgebra.DSL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Human.PRGLengthExtension

noncomputable section

/-! ## 1. Functions, laws and systems

Read three different types below:

* `F : S → R` computes a value from a supplied seed.
* `outputLaw F : ProbDist R` describes `F(s)` for a uniform seed `s`.
* `generated F q : TypedSystem (Samples R q)` draws afresh on each call.

`Samples R q` has a port named `eval`. Its input type is `Unit`, whose only value `()` means
"give me a sample"; its reply type is `R`. The budget function `fun _ => q` allows `q` calls.
`𝒰[S]` is uniform on `S`; `P.map F` gives `y` the total mass of inputs with `F x = y`.
-/

-- `S` is the finite, nonempty seed alphabet.
variable {S : Type} [Fintype S] [Nonempty S]

/-- `expand G s = (a, c, d)`, where `(a, b) = G s` and `(c, d) = G b`. -/
def expand
    -- `G` expands a seed into two `S` values; `s` is the initial seed.
    (G : S → S × S) (s : S) : S × S × S :=
  let (a, b) := G s
  let (c, d) := G b
  (a, c, d)

/-- The normalized law of `F(s)` when `s` is uniform in `S`. -/
def outputLaw
    -- `R` is the finite output alphabet; `F` is any deterministic generator on `S`.
    {R : Type} [Fintype R] (F : S → R) : ProbDist R :=
  (𝒰[S]).map F

/-- One `eval(())` port returning `R`, with at most `q` queries. This is a stock interface. -/
abbrev Samples
    -- `R` carries replies; `q` bounds the number of `eval(())` calls.
    (R : Type) [Fintype R] (q : ℕ) : Interface :=
  Evaluation.perPort Unit R (fun _ => q)

/-- On each admitted evaluation, return an independent sample from `outputLaw F`. -/
def generated
    -- `F` supplies the generator; `q` bounds evaluations, each with a fresh seed.
    {R : Type} [Fintype R] (F : S → R) (q : ℕ) : TypedSystem (Samples R q) :=
  MemorylessSource.perPort R (outputLaw F) (budget := fun _ => q)

/-- On each admitted evaluation, return a fresh uniform value in `R`. -/
def uniformOutput
    -- Nonempty `R` ensures that the uniform reply law is normalized.
    (R : Type) [Fintype R] [Nonempty R]
    -- `q` bounds evaluations of this fresh uniform source.
    (q : ℕ) : TypedSystem (Samples R q) :=
  MemorylessSource.perPort R (𝒰[R]) (budget := fun _ => q)

/-!
Before continuing, identify which definition computes from a given seed, which describes one
random reply, and which answers repeated calls. Locate the choice between fresh and retained
randomness: here the source draws afresh on each call.
-/

-- Uncomment a `#check` command to display a declaration's type. Commands go outside `by`.
-- #check outputLaw
-- #check generated

/-! ## 2. Read, then modify, a converter

A converter sits between its caller and an inside system. This one asks for a Boolean reply
and returns its negation. The inside system is supplied later, when we attach the converter.

```text
caller ── eval(()) ──► [FlipReply] ── eval(()) ──► inside system
       ◄── not b ────             ◄──── b ──────
```
-/

namespace Tutorial

/-- On `eval(())`, request one inside bit `b` and return its negation. -/
converter FlipReply : Evaluation Unit Bool
  -- Name the inside connection `oracle`, with the same query and reply types.
  inside oracle : Evaluation Unit Bool
  -- Handle one call to the outside `eval` port; `_trigger` is its unused `()` argument.
  on eval(_trigger : Unit) → Bool
    -- Send `()` inside and bind the reply to `b`. The arrow is an interaction.
    b ← oracle.eval(())
    -- This ordinary Lean expression computes the reply to the outside caller.
    return !b

-- `.perPort` selects allowances. One inside call per outside call needs the same `q`.
example (q : ℕ) : TypedConverter (Samples Bool q) (Samples Bool q) :=
  FlipReply.perPort (budget := fun _ => q)

-- Attachment supplies the missing inside system. The result is a system, not a converter.
example (q : ℕ) : TypedSystem (Samples Bool q) :=
  FlipReply.perPort • uniformOutput Bool q

end Tutorial

/-!
Try one edit: change `return !b` to `return b`, then check the file. The types stay the same,
but the converter now forwards its reply unchanged. Restore it before continuing.

Check your understanding: which line performs an interaction, and which computes a value?
Where is the inside system supplied? These are the same distinctions used by the PRG components.
-/

/-! ## 3. Reuse a component by supplying an ordinary function

Generalize the Boolean example: `mapReplies f (fun _ => q)` takes inside replies in `X` and returns
`f x : Y`. `sampleReplies P f (fun _ => q)` also draws a fresh `k : K` from `P` and returns `f k x`.
For `source Q := MemorylessSource.perPort X Q (budget := b)`, their contracts read:

```text
mapReplies f b • source Q       = source (Q.map f)
sampleReplies P f b • source Q  = source ((prodProbDist P Q).map (fun kx => f kx.1 kx.2))

caller ── eval(()) ──► [fresh k ∼ P] ── eval(()) ──► source Q
       ◄── f k x ────               ◄────── x ──────
```

The right-hand source uses the reply type of `f`. `prodProbDist P Q` describes independent draws,
with joint mass `P(x) * Q(y)`. The [reuse guide](../REUSE.md#start-from-the-type-you-need) gives
constructor types and their owners.
-/

-- Use `#check` to inspect the complete constructor and contract signatures.
-- #check Evaluation.mapReplies
-- #check Evaluation.sampleReplies
-- #check Evaluation.mapReplies_smul_memorylessSource
-- #check Evaluation.sampleReplies_smul_memorylessSource

/-!
Your function computes the reply; the constructor implements the draw and inside call.

Try replacing the function below by `fun _ => false`. The converter's interfaces do not change.
The function controls its reply rule; the supplied declaration handles the interaction.
-/

example (q : ℕ) : TypedConverter (Samples Bool q) (Samples Bool q) :=
  mapReplies (fun b : Bool => !b) (fun _ => q)

/-! ## 4. Use contracts to prove equalities

A goal is a missing term of the displayed type: an object in a `def`, or a proof in a theorem.
`:= t` supplies it directly; `:= by exact t` supplies the same term using a tactic block.

* `exact t` fills the goal with `t`.
* `unfold name` opens a definition. `rw [h]` rewrites by equality `h`; `rw [← h]` reverses it.
  The term `h.symm` is the reversed equality.
* `congr 1` reduces the goal `f a = f b` to `a = b`, one application level down.
* `funext s` reduces function equality to an arbitrary input; `rfl` proves equality by computation.
* `have name : statement := by ...` proves a named fact inside the current proof.

Start with an identity reply map, then swap a generator's two Boolean coordinates.
-/

-- The contract leaves only a normalized probability-law equation.
example
    -- `P` is any bit law; `q` bounds calls to its source.
    (P : ProbDist Bool) (q : ℕ) :
    mapReplies (fun b : Bool => b) (fun _ => q) •
        MemorylessSource.perPort Bool P (budget := fun _ => q) =
      MemorylessSource.perPort Bool P (budget := fun _ => q) := by
  rw [mapReplies_smul_memorylessSource]
  -- Both sources use the same constructor; compare their reply laws.
  congr 1
  exact ProbDist.map_id P

namespace Tutorial

/-- Swap the two coordinates of the pair `F s`. -/
def swapped
    -- `F` returns two bits from seed `s`; the result reverses their order.
    (F : S → Bool × Bool) (s : S) : Bool × Bool :=
  let (x, y) := F s
  (y, x)

/-- Assemble a reply swap around the fresh-seed experiment of `F`. -/
def swappedReplies
    -- `F` supplies the fresh-seed reply law; `q` is the evaluation allowance.
    (F : S → Bool × Bool) (q : ℕ) : TypedSystem (Samples (Bool × Bool) q) :=
  mapReplies Prod.swap (fun _ => q) • generated F q

example
    -- `F` supplies pair replies; `q` is shared by both source presentations.
    (F : S → Bool × Bool) (q : ℕ) :
    swappedReplies F q = generated (swapped F) q := by
  -- Open the assembly and source definitions, then apply the component contract.
  unfold swappedReplies generated outputLaw
  rw [mapReplies_smul_memorylessSource, ProbDist.map_map]
  -- The remaining equation concerns an ordinary function at an arbitrary seed.
  have sameFunction : Prod.swap ∘ F = swapped F := by
    funext s
    rfl
  rw [sameFunction]

end Tutorial

/-!
Now compare two assemblies: draw a fair flag beside a fresh bit and conditionally negate it,
or draw one uniform pair and perform the same computation. They have the same reply law.
-/

example
    -- `q` is the common allowance for both presentations of the fresh-bit experiment.
    (q : ℕ) :
    sampleReplies 𝒰[Bool] (fun flag b => if flag then !b else b) (fun _ => q) •
        uniformOutput Bool q =
      mapReplies (fun fb : Bool × Bool => if fb.1 then !fb.2 else fb.2) (fun _ => q) •
        uniformOutput (Bool × Bool) q := by
  -- Open the sources; the two contracts leave a product law and a uniform-pair law.
  unfold uniformOutput
  rw [sampleReplies_smul_memorylessSource, mapReplies_smul_memorylessSource, prodProbDist_uniform]

/-!
Try replacing the conditional on both sides by Boolean conjunction (`flag && b`, respectively
`fb.1 && fb.2`). Predict why the same proof works, then check the file.
-/

/-- Negating the second independent bit before conjunction equals mapping that computation once. -/
example
    -- `P`, `Q` supply independent bits; the second bit is negated before combining them.
    (P Q : ProbDist Bool) :
    (prodProbDist P (Q.map Bool.not)).map (fun ab => ab.1 && ab.2) =
      (prodProbDist P Q).map (fun ab => ab.1 && !ab.2) := by
  -- Move the second-coordinate map onto the joint law, then compose the two computations.
  rw [prodProbDist_map_right, ProbDist.map_map]
  rfl

/-!
Between declarations, a helper can start as `lemma name : statement := by sorry`. Inside a
proof, use `have name : statement := by sorry`. Both let you work on later steps while keeping
the missing proof as an explicit obligation. An underscore prefix marks an intentionally unused
parameter.
-/

/-! ## 5. Read a security statement and use a bound

`R ≃[ε] T` means every test `D` in the selected class has distinguishing advantage at most
`ε D`. `ENNReal` is `ℝ≥0∞`, the nonnegative reals with infinity. The class records which tests
are admitted; the loss is allowed to depend on the particular test.

For `α : TypedConverter A B`, an outside test `D` on `A` becomes `D.absorb α` on `B`:

```text
D ── [α] ── [R]    =    [D.absorb α] ── [R]
```

`ClosedUnder ... α` says this transformed test remains admitted. The named arguments
`Phi := TypedSystem` and `D := TypedDistinguisher` fix the system and test type families.
They do not choose an individual system or test.
-/

-- Transport two supplied comparisons through `α`, with exact equations at the endpoints.
example
    -- This instance selects the admitted tests at every interface.
    [AdmissibleDistinguishers Interface TypedDistinguisher]
    -- `α` exposes `A` and uses an inside system on `B`.
    {A B : Interface} (α : TypedConverter A B)
    -- `closed` keeps tests admitted after absorbing this particular `α`.
    (closed : AdmissibleDistinguishers.ClosedUnder
      (Phi := TypedSystem) (D := TypedDistinguisher) α)
    -- `P`, `Q`, `R` are inside systems; `X`, `Y` name the outside endpoints.
    {P Q R : TypedSystem B} {X Y : TypedSystem A}
    -- `ε`, `δ` are the supplied bounds on the two inside comparisons.
    {ε δ : TypedDistinguisher B → ENNReal} (first : P ≃[ε] Q) (second : Q ≃[δ] R)
    -- `start`, `finish` identify the assembled endpoints with the desired outside systems.
    (start : X = α • P) (finish : α • R = Y) :
    X ≃[fun D => ε (D.absorb α) + δ (D.absorb α)] Y := by
  cc_calc quantitative
    X = α • P := start
    _ ≃[fun D => ε (D.absorb α)] α • Q := TypedConverter.substitutesWithin_attach α closed first
    _ ≃[fun D => δ (D.absorb α)] α • R := TypedConverter.substitutesWithin_attach α closed second
    _ = Y := finish

/-!
Try deleting the `second` hypothesis and its calculation link. Predict the new loss and the
endpoint that `finish` must identify, then adapt the statement and proof. Restore it afterward.
-/

/-! ## 6. Build your PRG construction

Your security task is:

```text
assume  generated G q ≃[ε] uniformOutput (S × S) q
prove   generated (expand G) q
          ≃[fun D => ε (D.absorb (reduction₁ G q)) + ε (D.absorb (reduction₂ G q))]
        uniformOutput (S × S × S) q
```

The assumption bounds each admitted test `D` by `ε D` across at most `q` evaluations:
`generated G q` draws a fresh seed each time, and the other system draws fresh uniform replies.
A reduction context is a converter `α`; `D.absorb α` is the reduced test charged by the loss.
Choose the contexts so the given bound proves this target.

Choose two contexts, each exposing triple replies and using a pair-reply system with allowance
`q`. Give each one's input/output rule before defining it. Use the supplied `mapReplies` or
`sampleReplies` by choosing their ordinary function and, where needed, their sampling law.

Both `mapReplies f (fun _ => q)`, for `f : X → Y`, and
`sampleReplies P g (fun _ => q)`, for `P : ProbDist K` and `g : K → X → Y`, have type
`TypedConverter (Samples Y q) (Samples X q)`. The order is outside first, inside second.
Assemble the system with `α • R`.
-/

/-- Your first reduction context. Add its input/output rule before filling the body. -/
def reduction₁
    -- `G` is available to your reply computation; `q` fixes both interfaces' allowances.
    (G : S → S × S) (q : ℕ) :
    TypedConverter (Samples (S × S × S) q) (Samples (S × S) q) := by
  sorry

/-- Your second reduction context. Add its input/output rule before filling the body. -/
def reduction₂
    -- `G` is available to your reply computation; `q` fixes both interfaces' allowances.
    (G : S → S × S) (q : ℕ) :
    TypedConverter (Samples (S × S × S) q) (Samples (S × S) q) := by
  sorry

/-- Build the extended generator from named components and algebraic operations.
Its observable experiment must be the one specified by `generated (expand G) q`. -/
def assembled
    -- `G` is the seed expander; `q` bounds calls to the assembled triple-reply experiment.
    (G : S → S × S) (q : ℕ) : TypedSystem (Samples (S × S × S) q) := by
  sorry

/-!
State the intermediate equations your argument needs here. The supplied component contracts
reduce source comparisons to probability laws. `ProbDist.map_map` composes deterministic maps;
`prodProbDist_map` moves maps across independent draws. Inspect their types with `#check`.
`ProbDist.map_id` and `prodProbDist_uniform` give the identity and uniform-product laws.
`prodProbDist_map_left` and `prodProbDist_map_right` transform one independent coordinate.
-/

-- Add the mathematical contracts of your chosen components and any intermediate lemmas here.

/-- Your assembly implements the stated generator at every admitted interaction. -/
theorem assembly_spec
    -- Compare your assembly for `G` with its functional specification at allowance `q`.
    (G : S → S × S) (q : ℕ) :
    assembled G q = generated (expand G) q := by
  sorry

/-! ## 7. Prove your bound, then reuse it

Use `TypedConverter.substitutesWithin_attach α closed bound` under a chosen converter, and
`cc_calc quantitative` to chain your chosen systems, exact equalities and bounds.
An exact link is written `P = Q := equality`; a bounded link is `P ≃[ε] Q := bound`.
The library transports the supplied facts and adds errors; you choose the argument.
-/

section Security

-- This instance selects which distinguishers are admitted at each interface.
variable [AdmissibleDistinguishers Interface TypedDistinguisher]

-- Add any helper lemmas about security here, with the selected class now in scope.

-- These hypotheses are shared by the two endpoints below.
variable
    -- `G` is the seed expander; `q` bounds evaluations of both experiments.
    (G : S → S × S) (q : ℕ)
    -- `ε D` bounds `D`'s advantage against `G` for the whole `q`-call experiment.
    -- `secure` already covers fresh seeds on all those calls.
    (ε : TypedDistinguisher (Samples (S × S) q) → ENNReal)
    (secure : generated G q ≃[ε] uniformOutput (S × S) q)
    -- `closed₁`, `closed₂` admit `D` with your chosen reduction absorbed on its right.
    (closed₁ : AdmissibleDistinguishers.ClosedUnder
      (Phi := TypedSystem) (D := TypedDistinguisher) (reduction₁ G q))
    (closed₂ : AdmissibleDistinguishers.ClosedUnder
      (Phi := TypedSystem) (D := TypedDistinguisher) (reduction₂ G q))

-- `secure`, `closed₁`, `closed₂` do not occur in the statements; `include` adds them as hypotheses.
include secure closed₁ closed₂

/-- Establish the PRG length-extension bound at the two reduced distinguishers. -/
theorem length_extension :
    generated (expand G) q ≃[fun D =>
      ε (D.absorb (reduction₁ G q)) + ε (D.absorb (reduction₂ G q))]
        uniformOutput (S × S × S) q := by
  sorry

/-!
Finally reuse `length_extension` and `assembly_spec` inside the chosen context.
`TypedConverter.substitutesWithin_attach` transports the bound through it.
Keep the component implementations opaque: their contracts carry the argument.
The shared `variable` declarations become theorem arguments; `#check` shows their order.
-/

-- #check length_extension

/-- The same security guarantee inside an explicitly chosen surrounding context. -/
theorem length_extension_in_context
    -- `O` is the outside interface; `context` uses your triple-reply experiment inside it.
    {O : Interface} (context : TypedConverter O (Samples (S × S × S) q))
    -- `closedContext` admits each outside distinguisher with `context` absorbed.
    (closedContext : AdmissibleDistinguishers.ClosedUnder
      (Phi := TypedSystem) (D := TypedDistinguisher) context) :
    context • assembled G q ≃[fun D =>
      ε ((D.absorb context).absorb (reduction₁ G q)) +
        ε ((D.absorb context).absorb (reduction₂ G q))]
      context • uniformOutput (S × S × S) q := by
  sorry

end Security

-- At the end, uncomment these. Only `propext`, `Classical.choice` and `Quot.sound`
-- should remain; `sorryAx` indicates an unfinished proof.
-- #print axioms assembly_spec
-- #print axioms length_extension
-- #print axioms length_extension_in_context

end
end Human.PRGLengthExtension
