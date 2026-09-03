# Swiss Crypto Day 2026 transcript

Target duration: 8 minutes. The 908 spoken words are designed for a moderate
pace of roughly 115 words per minute, with short pauses during the demo.

## Introduction — 2 minutes

### Slide 1 — Informalizing a cryptographic proof

We are entering a period in which more mathematics, more cryptography, and
more software will be produced with the help of artificial intelligence. That
can make us much faster. It can also make the gap between producing an
argument and understanding it much larger.

A proof assistant such as Lean gives us one essential guarantee. It checks
that a theorem follows from the definitions and assumptions that we supplied.
But that guarantee does not answer every human question. Why were these the
right definitions? What is the main idea of the proof? Which step uses the
cryptographic insight, and which step is only bookkeeping?

When a proof is short, the author can explain those things. When a proof is
large—or partly produced by an AI system—we need the explanation to remain
connected to the checked object. Otherwise, we risk having two artifacts: one
that the machine trusts, and another that humans can read, with no reliable
link between them.

So the question behind this talk is simple: once Lean has checked a
cryptographic proof, who explains it to us?

I will show a small experiment that tries to answer that question. It starts
from the checked Lean declaration and produces an interactive, human-oriented
view. The example is a familiar CBC security proof. The important point is not
the particular theorem. It is that the prose, the mathematical structure, and
the detailed formal evidence all remain views of the same proof.

## Demo — 3 minutes

### Slide 2 — Randomness expansion with CBC

Let me first recall the construction. On the left is a random function on the
block space, from `X` to `X`. The CBC converter attaches to that interface and
splits a message into blocks. The first block goes directly to the random
function. Each later block is combined with the previous chaining value before
the next call. The final value is the tag.

The converter turns a one-block primitive into a system for variable-length
messages. We ask whether an observer can distinguish it from an ideal random
function mapping complete messages directly to tags.

### Slide 3 — CBC proof

Now I will open the proof. What you see is generated from the Lean theorem,
but it is meant to be read as mathematical prose.

The collapsed view gives the usual cryptographic argument. We identify the
real system, define the collision game, reduce distinguishing to winning that
game blindly, and bound the collision probability.

Each small dot opens the checked support for that claim. I can inspect its
subargument and continue as deeply as the Lean proof tree goes. Hovering over a
declared object recovers its Lean information. When the exact formal state
matters, I can inspect the local assumptions and goal.

So this is still Lean. The proof has not been replaced by a hand-written
summary. We are changing how much of its structure is visible, and how that
structure is expressed.

The idea builds on work by Patrick Massot and Kyle Miller. Massot’s Verbose
Lean exposes proof structure through controlled natural language. Miller’s
work with Massot on InformalLean goes in the reverse direction: it turns a
Lean module into an interactive explanation with detail on demand.

This prototype adds a cryptographic layer. It reads the elaborated declaration,
proof term, and information tree; recovers mathematical entities and
dependencies; and forms a semantic proof plan. A registered vocabulary turns
that plan into prose. An unrecognized step must expose formal evidence or fail
clearly—not be assigned a plausible but invented story.

## Conclusion — 3 minutes

### Slide 4 — Informalization reverses the usual direction

Formalization usually translates a human explanation into a language that a
machine can check. Here, we reverse the direction. We begin with the checked
proof and derive a presentation for humans. That is informalization.

The output need not be one fixed paragraph. A cryptographer may care about the
game transition. A Lean developer may need the exact theorem behind it. A
reviewer may inspect one suspicious step without unfolding everything else.

### Slide 5 — Correctness and explanation are different guarantees

This matters in the age of AI because generation is becoming cheap, while
understanding is not. A model may construct a valid proof term, but validity
alone does not tell us whether the definitions capture the intended security
notion or communicate the right intuition.

But this is useful beyond AI. Cryptographic results already serve researchers,
auditors, protocol designers, implementers, and students. They do not need
identical documents. Their explanations do need the same checked source.

An interactive proof can also improve review. Instead of choosing between a
short argument and thousands of formal lines, a reviewer can follow the
conceptual route and open only the claims that need attention. The formal proof
becomes a source from which explanations can be derived.

### Slide 6 — The prototype keeps provenance visible

The second conclusion is that you can make this your own. Checked structure
determines what may be claimed, but it does not dictate one universal style.
A project can register its objects, notation, theorem roles, vocabulary, and
preferred detail. An author can choose the emphasis and add reader guidance.

That customization has a boundary. Presentation choices may change how a
checked fact is described; they may not create a fact that Lean did not prove.
That visible boundary makes the system useful rather than merely fluent.

### Slide 7 — One checked proof

My point is not that every proof should look like this demo. It is that
communication should be part of the formalization problem.

If formal methods and AI give us many more checked proofs, we should help
people explore, question, teach, and adapt them. One checked source can serve
different readers at different levels of detail.

One checked proof. Different readers. Detail on demand.

Thank you.

## References

- Patrick Massot, “Teaching Mathematics Using Lean and Controlled Natural
  Language,” *ITP 2024*, LIPIcs 309, Article 27.
  <https://doi.org/10.4230/LIPIcs.ITP.2024.27>
- Kyle Miller, “From Lean to Natural Language and Back: Interfaces for Formal
  Proofs,” ICERM, *Autoformalization for the Working Mathematician*, 2025.
  <https://kmill.github.io/informalization/icerm_talk.pdf>
