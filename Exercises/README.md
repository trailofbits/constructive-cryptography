# Human exercises

[PRG length extension](PRGLengthExtension.lean) walks through definitions, component assembly,
contracts, security and reuse. It assumes ordinary Lean functions and tuples. Read the worked
examples, try the suggested edits, then fill six construction and proof holes.

From the repository root, run:

```sh
lake build
lake env lean Exercises/PRGLengthExtension.lean
```

The initial file reports six placeholder warnings. Exercises are outside the library build;
finish with no placeholders and only the standard axioms listed at the end of the file.
Use the [reuse guide](../REUSE.md#start-from-the-type-you-need) to find constructors and contracts.
