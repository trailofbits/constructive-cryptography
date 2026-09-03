/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Probability.Distribution
import Probability.Expectation
import Probability.Lift
import Probability.Conditional
import Probability.Coupling
import Probability.SignedCoupling
import Probability.MultiCoupling
import Probability.FiberCoupling
import Probability.StatisticalDistance
import Probability.Counting
import Probability.UniversalHash
import Probability.Entropy
import Probability.ShannonEntropy
import Probability.Divergence
import Probability.DistributionMeasure
import Probability.Simp

/-!
# Probability

Finitely supported distributions, expectation, conditional probability,
statistical distance, couplings, universal hashing, and finite counting
bounds. The same carrier supports min-entropy, collision entropy, Shannon
entropy, Kullback--Leibler divergence, and Pinsker's inequality. The one-way
`isProbDist → PMF` bridge in `DistributionMeasure` connects these definitions
to Mathlib. This root is independent of every system model.
-/
