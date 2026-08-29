/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Applications.CBCMAC.Construction

/-!
# CBC-MAC

Maurer 2002, Figure 6 (printed p. 17), defines `C(F)` by “applying some
prefix-free encoding σ to the message”, applying CBC feedback, and “taking the
last output (for a given message) as the MAC-value”. Theorem 6 on the same page
gives the resulting quasi-random-oracle bound.

The CBC-MAC application is developed over the normalized random-systems
carrier. `Applications.CBCMAC.Objects` defines the pure CBC functions, DDCs,
and PDSs; `Attachment` proves their complete-history equations; `Probability`
proves the collision bound; and `Construction` states the resulting random-
system distance and heterogeneous CC construction.
-/
