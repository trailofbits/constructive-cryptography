module

public import Examples.AuthenticatedEncryption.Security
public import Examples.DSL.AEAD
public import Examples.DSL.AEADTests
public import Examples.DSL.AES
public import Examples.DSL.Components
public import Examples.Games
public import Examples.PRGLengthExtension
public import Examples.Substitution
public import Examples.Usability

/-! Applications and examples: AES and components in the DSL, authenticated encryption with
AES-CTR and PMAC, `(ind-cca, int-ptxt) → ae` (Banfi, Theorem 2.3.10(4), corrected), the proof
commands on interfaces, single substitutions, and games: reductions for real-valued winners
with a converter action, and the collision step of authenticated encryption by conditional
equivalence; PRG length extension, whose hops are equalities of memoryless sources. -/
