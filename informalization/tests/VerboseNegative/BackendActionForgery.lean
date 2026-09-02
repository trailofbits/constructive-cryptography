import Verbose

open CryptoLanguage.Verbose

/- The legacy constructor accepted an arbitrary tactic closure paired with a
claimed declaration. The capability macro now accepts only one function head,
so this spelling must remain a compile-time error. -/
def forgedBackend :=
  backendAction ``CryptoLanguage.Verbose.Backend.closeFrom (pure ())
