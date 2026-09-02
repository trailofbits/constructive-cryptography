import Verbose
import Verbose.English.Statements

open scoped CryptoVerbose

Theorem oldNaturalBudget "Old natural-number binder"
  Given:
    a natural-number query budget q
  Conclusion:
    q = q
  Proof:
    rfl
  QED
