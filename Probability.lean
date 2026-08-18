/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Probability.Distribution
import Probability.Expectation
import Probability.Lift
import Probability.Conditional
import Probability.Coupling
import Probability.MultiCoupling
import Probability.FiberCoupling
import Probability.StatisticalDistance
import Probability.Counting
import Probability.CountingResidue
import Probability.UniversalHash
import Probability.Entropy
import Probability.ShannonEntropy
import Probability.Divergence
import Probability.DistributionMeasure

/-!
# Probability

Finitely supported distributions, expectation, conditional probability,
statistical distance, couplings, universal hashing, the counting kernel
concrete bounds bottom out in (`Counting` plus the staging module
`CountingResidue`, which merges into it), and the information theory stated on
that carrier — min-entropy and the collision calculus, the Shannon layer, and
Kullback-Leibler divergence with Pinsker's inequality, together with the
one-way `isProbDist → PMF` transport (`DistributionMeasure`) that lets the
divergence be checked against mathlib's.  Independent of any system model.
-/
