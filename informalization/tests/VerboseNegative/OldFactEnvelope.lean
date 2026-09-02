import Verbose
import Verbose.RandomSystems

open scoped CryptoVerbose

example {X Y : Type*} (game : RandomSystems.PDG X Y)
    (system : RandomSystems.PDS X Y)
    (conditionalLaw : RandomSystems.PDG.CondEquiv game system) : True := by
  Fact oldHeading.
    The game game is conditionally equivalent to system by conditionalLaw
  trivial
