import Examples.AuthenticatedEncryption.Security
import Examples.DSL.AEAD
import Examples.DSL.AEADTests
import Examples.DSL.AES
import Examples.DSL.Components
import Examples.Games
import Examples.Substitution
import Examples.Usability

/-! Applications and examples: AES and components in the DSL, authenticated encryption with
AES-CTR and PMAC, `(ind-cca, int-ptxt) → ae` (Banfi, Theorem 2.3.10(4), corrected), the proof
commands on interfaces, single substitutions, and games: reductions in any compatible solver
class and the collision step of authenticated encryption as a game. -/
