# Cryptographic component DSL

This is a DSL embedded in Lean for the finite systems algebra.
The surface uses indentation, `←` for computation/assignment, `←$` for sampling,
and `𝒰[T]` for the uniform law on a finite nonempty type. There are no braces,
semicolons, `do` blocks, or combined assignment/bind operators in the surface.
Lean remains the language for types, pure expressions, propositions, and proofs.

## Grammar

`block(P)` is a newline followed by one or more equally indented occurrences
of `P`. Nested blocks must be further indented. Square brackets in the grammar
denote optional syntax; quoted brackets are literal. `*` means repetition.

```text
declaration ::= interface | system | converter | filter | system_definition | LeanDeclaration
parameters  ::= ("(" names ":" Type ")" | "[" Instance "]")*
arguments   ::= [argument ("," argument)*]
argument    ::= Name ":" Type

interface ::= "interface" Name parameters block(port)
port      ::= Name "(" arguments ")" "→" Type

system ::= "system" Name parameters [":" InterfaceApplication]
           block(system_member) ["by" Proof]
system_member ::= requirement | domain | initialization | reply

converter ::= "converter" Name parameters [":" InterfaceApplication]
              block(converter_member)
converter_member ::= requirement | inside | initialization | reply
inside        ::= "inside" Name ":" InterfaceType
InterfaceType ::= Type "→" Type | InterfaceApplication
requirement   ::= "requires" Name ":" Proposition
domain        ::= "domain" Name "↦" Proposition

filter ::= "filter" Name parameters ":" InterfaceApplication
           "domain" Name "↦" Proposition ["by" Proof]

initialization ::= "initialize" block(statement)
reply ::= "on" Name "(" arguments ")" "→" Type block(statement)

statement ::= assignment | sampling | conditional | iteration | matching | returning
assignment ::= target [":" Type] "←" Expression
             | target [":" Type] "←" oracle_call
sampling   ::= target [":" Type] "←$" Distribution
target     ::= Name | "(" Name ("," Name)+ ")"
Distribution ::= "𝒰[" Type "]" | Expression
oracle_call  ::= PortPath "(" [Expression ("," Expression)*] ")"
conditional  ::= "if" Expression block(statement) ["else" block(statement)]
iteration    ::= "for" Name "∈" Expression block(statement)
matching     ::= "match" Expression block(match_case)
match_case   ::= "|" Pattern "→" block(statement)
returning    ::= "return" Expression

system_definition ::= "system" Name parameters "≔" SystemExpression
SystemExpression ::= ComponentExpression | "(" SystemExpression ")"
                   | SystemExpression "∥" SystemExpression
                   | SystemExpression "≫" SystemExpression
                   | SystemExpression "•" SystemExpression
                   | SystemExpression "⊗ₘ" SystemExpression
```

Single-port interface declarations supply their unique label automatically.

## Binding and effects

The first assignment in a scope introduces a binding; reassignment updates the
existing binding. Bindings introduced at the outer level of initialization
persist across invocations. New bindings inside an `on` block belong to that
invocation. Branch and loop locals do not escape their block; assignments to
existing bindings do. Tuple assignment is simultaneous. Initialization must
define every persistent binding before use. The parameters of an `on` block cannot silently
shadow persistent bindings. Every reachable path of an `on` block returns exactly once.

Only a call to a declared inside port is an interaction. It appears as the
right-hand side of an assignment. Pure Lean expressions cannot hide such calls.
Sampling draws from the specified normalized finite-support law each time the
statement is reached. The law is closed: it may depend on declaration parameters, not on
bindings or procedure arguments; sample from a fixed law and compute from the sample. A sample
in initialization is made once; samples in `on` blocks are fresh on successive invocations.

Loops traverse ordered finite sequences. A finite list for each input does not
by itself establish a uniform inside-query bound. No unbounded `while` or
recursive effectful calls are implicit in this grammar. Ordinary terminating
Lean functions remain available in pure expressions.

## Interfaces, budgets, and obligations

Every generated object is finite: alphabets are finite types and histories have a bounded
length. Oracle names are local interface labels. Their argument types form that interface's
input type; their return type is its output type. Both must be finite (`Fintype`); a type
parameter of an interface carries its `[Fintype]` instance. Return types may depend on
component parameters, but not on the current query value. `interface I` declares the family
`I q := Interface.queryBudget … q` of its query budgets. A `: InterfaceApplication` annotation
selects that vocabulary. Without the annotation, the declaration creates its own `Name.Port`,
`Name.Input`, and `Name.Output`, with their finiteness at each port, `Name.fintypeInput` and
`Name.fintypeOutput`. Each alphabet takes only the parameters its ports mention (closed under the
parameters' types and instance arguments), so instance search on the alphabet at a port
determines every argument. With two or more ports these are instances, so the alphabet at a variable
port is finite by instance search; with one port the alphabet reduces to its declared type, whose
own instances apply.

A system declares a resource for every budget: `S : Interface.Resource (I q)` with the implicit
argument `budget`. Its default domain consists of the histories of one to `q` inputs. An
explicit `domain h ↦ P` is intersected with the budget and requires the nonempty-prefix
condition, proved in `by`. This clause belongs to a system without an interface annotation.
Private initialization does not emit a message. An error reply is an ordinary declared output
value.

`interface I` also declares `I.perPort q := Interface.portBudget … q` for a budget
`q : I.Port → ℕ` per port: at most `q i` queries at each port `i`. A system without an exact
domain also gets `S.perPort : Interface.Resource (I.perPort q)`. A converter with a single inside
port is typed by per-port budgets along a partial port map `C.portMap : I.Port → Option J.Port`,
which sends each procedure to the inside label it calls, or to `none` when it calls none
(`C.preserving`, a `Program.PortPreserving` proof: each procedure calls at most its own label, at
most once).
- When the inside port has the outside interface `I`, each procedure calling its own port, it is
  the endomorphism `C.perPort : I.perPort q ⟶ I.perPort q`.
- When the inside port has another declared interface `J`, each of whose labels one procedure
  calls, it is `C.perPort : I.perPort q ⟶ J.perPort (C.insideBudget q)`: the budget at an inside
  label is that of the procedure calling it, and a procedure calling nothing needs none (Banfi's
  `ρ^ctxt`, from `AE M C` to `Encryption M C`).

Its sources have the budget `C.bound * ∑ i, q i`. Other converters have no per-port typing.

The budget is the implicit argument `budget` in both forms, a number for `I q` and a function
of the port for `I.perPort q`: `S (budget := k)`, `C.perPort (budget := q)`. `C.exact` also takes
the implicit `queries`. These two names are reserved. Every other name the generated
declarations bind is hygienic, and a system, converter or filter that mentions `budget` or
`queries`, as a parameter, a binding or a reference, is rejected; a named argument
`(budget := k)` is not a mention. So a component's own names keep their meaning in every
generated declaration.

`requires h : P` is a visible premise, supplied when the component is instantiated.

A converter's per-invocation inside-query bound is inferred from its operations. When the
procedures have no loops, `C.bound` is the numeral read off the displayed calls: a call counts
one, a conditional or a match the largest count of its branches, and the bound is the largest
count over the procedures, initialization included. Otherwise, for finite inputs and private
bindings, `C.bound` is the least bound, a supremum over them. The elaborator generates `C.bound`,
`C.bound_spec`, and
`C : I q ⟶ J (C.bound * q)` for every budget `q`, where the inside interfaces `J` are at budget
`C.bound * q`. A converter without a uniform bound is rejected. When a converter samples nothing
and the number of inside calls of an invocation is a function of its input alone, the
elaborator also infers that count `C.cost` and generates the exact typing
`C.exact : (I n).restrict (fun h => (h.map C.cost).sum ≤ q) ⟶ J q`: outside histories of total
cost at most `q` need `q` inside queries. It is omitted when the count depends on inside
replies or private bindings.

A `filter F : I domain h ↦ P` gives `F : (I q).restrict P ⟶ I q` for every budget: it forwards
the queries of an admitted history and stops on the others (CR18 §3.4.3). The admitted
predicate must be closed under prefixes; `by` supplies a proof when the default tactic does
not find one.

## Compilation

A component compiles to a deterministic program with sources of randomness: sampling stays in
the surface, and randomness enters the generated systems only through sources
(`Interface.Resource.source`, Maurer 2002, Definition 1).

- Every sampling statement `x ←$ P` becomes a call `x ← sample_k()` to a synthetic inside port
  whose source draws fresh samples from `P`; the law is `C.law_k`.
- The body `C.body : Program (Option S) …` is a function of the inside exchanges of the current
  invocation, giving the next inside query or the reply and the new private bindings (a
  deterministic automaton, Maurer 2002, Definition 2). Initialization runs in the first
  invocation, when no bindings are stored yet; `S` is the type of `C.initial`, the initial
  bindings with each sample replaced by a value of its law.
- Computation is ordinary `let` bindings; control flow is ordinary conditionals, pattern
  matching and list folds (`forEach`); a call is `callProg`, a reply `returnProg`.
- `C.program : I q ⟶ J (C.bound * q)` is the converter of the program
  (`Interface.Converter.ofProgram`), on the outside domain of `I q`.
- A converter is `C.program ≫ Interface.rightContext J (C.randomness k)`: its program with its
  sources attached beside the declared inside ports, each source at the inside budget `k`. A
  converter that samples nothing is `C.program`.
- A system is `C.program • C.randomness k`. A system that samples nothing is the automaton of
  its program started in `C.initial`, `Interface.Resource.ofAutomaton I step (single s)`.

Attaching a program to a resource runs its body against the resource
(`Program.apply_ofProgram`, Maurer 2002, §3.3). A transcript of `C.program • R` has the mass of
the resource's deterministic systems on which the inlined program gives it
(`Interface.ofDDC_ofProgramOn_smul_ofPDS`). Sources are automata whose initial state is a table
of samples (`Interface.Resource.ofAutomaton I step initial`, Maurer 2002, Definition 2, with the
randomness in the initial state); parallel automata are the automaton of both
(`Interface.parallel_ofAutomaton`), and a program attached to an automaton is the combined
automaton (`Interface.Converter.ofProgram_smul_ofAutomaton`, `Program.combine`). Every compiled
component is therefore an automaton with a sampled initial state; bisimilar automata have the
same system (`automatonSystem_eq_of_bisim`).

The assembly operators denote the existing CC operations. `α • R` applies a
converter, `α ≫ β` composes converters, and `∥` and `⊗ₘ` compose systems and
converters in parallel. Parallel composition is independent; copying
a system expression does not create shared state. Sharing is expressed by
one component with multiple interfaces or by initialization enclosing all the
shared behavior. A definition `system D ≔ e` takes its outside interface from the outermost
component of `e`, at the implicit `budget`; the inner budgets follow from the converters' types.

The earlier proposed `attach A[ports] ↔ B[ports]` surface is not implemented.
The grammar above records the implemented DSL; it makes no claim that
arbitrary feedback wiring can omit the existing domain and termination obligations.

## Validation

Examples must cover persistent and fresh randomness, state across interleaved
interfaces, reassignment and tuple binding, branches and matching, bounded
multi-query iteration, exact partial domains, and typed composition. Rejection
checks must cover uninitialized variables, hidden calls, wrong message types,
missing return paths, unproved bounds, laws that depend on bindings, and inside calls in
initialization. The AES example uses AES-256 of `Commons.Schemes.BlockCipher.AES`.
Semantic and construction theorems are checked by Lean with the standard axiom envelope only.

`Examples/DSL/Components.lean` covers counters, interleaved interfaces, fresh versus persistent
bits, branches, matching, tuple assignment, list folds, an exact domain, the inferred cost of
`Padding` (`Padding.exact`), a write-through converter from `Cache` to `Store` whose reads need no
inside budget (`WriteThrough.perPort`), and a filter. `Examples/DSL/AES.lean` uses AES-256 of
Commons,
answering at the interface `Evaluation`, for serial converters, fresh masks, a two-key cascade,
and CBC-MAC over a finite message space `M`. `CBC blockForm` processes `blockForm message`, so each invocation
can have a different number of blocks; `CBC.exact` types it by the total number of blocks.
These examples specify systems; they do not establish new security bounds.

`Examples/DSL/AEAD.lean` builds AES-CTR with PMAC authentication and associated data from
three converters: `CTR` and `PMAC` of Commons, and `EncryptThenMAC`. Its complete assembly is

```lean
EncryptThenMAC • ((CTR (2 ^ 36) • AES) ∥ (PMAC authenticationBytes • AES))
```

The two AES systems sample independent AES-256 keys. Messages and associated
data are byte strings of at most 2³⁶ bytes; each CTR call runs from the counter
block of a 96-bit nonce with a 32-bit block counter. Authentication covers the
nonce, both string lengths, associated data, and ciphertext. Decryption verifies
the tag with PMAC before calling CTR. Nonce uniqueness for encryption is the caller's security
obligation. This example specifies the composition, without claiming a security
reduction or a standardized AEAD mode.

`Examples/DSL/AEADTests.lean` proves the generated encrypt/verify/reject interaction paths of
the program's converter (`Interface.ofDDC_apply`), checks the encoding bounds, and checks the
combination as functions (`CTR.crypt` and `PMAC.pmac`): decryption inverts encryption, and
modified inputs are rejected. The published CTR and PMAC vectors are checked in
`Commons/Tests`, on the functions; they are separate from a proof that the converters
compute them, or of the scheme's security.

`Tests/DSL/Semantics.lean` checks behavior across calls on the inlined programs,
`Tests/DSL/Diagnostics.lean` checks rejected declarations, and `Tests/DSL/Axioms.lean` audits
the compilation and semantic results.

Import `ConstructiveCryptography.DSL` and open
`SystemAlgebra.DSL` plus `open scoped SystemAlgebra.DSL` to use the
declarations. Open `CategoryTheory` and its `MonoidalCategory` namespace for
the inherited composition and tensor notation, as in `Examples/DSL/AES.lean`.

Environment and distinguisher declarations are not syntax forms of the DSL. Environments
(`DDE`), distinguishers and their compatibility with a domain are systems-level definitions;
see `Domain.Compatible` and `Domain.DecisionCompatible` in
[Decision](../../RandomSystems/Distance/Decision.lean).

To check the DSL and its tests, run from the repository root:

```sh
lake build Tests.DSL.Diagnostics Tests.DSL.Axioms
```
