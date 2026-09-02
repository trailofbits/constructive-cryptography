/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.DDS
import RandomSystems.DDE
import RandomSystems.PDS
import RandomSystems.Observation
import RandomSystems.RandomSystem
import RandomSystems.Uniform
import RandomSystems.Distance
import RandomSystems.Parallel
import RandomSystems.TranscriptFactor
import RandomSystems.Technique.HCoefficient
import RandomSystems.XorUniform
import RandomSystems.Technique.ConditionalEquivalence.Advantage
import RandomSystems.Technique.ConditionalEquivalence.Blind
import RandomSystems.Technique.ConditionalEquivalence.Filter
import RandomSystems.Technique.ConditionalEquivalence.FunctionEvaluator
import RandomSystems.Tactics.ProofAutomation

/-!
# Random systems

Lanzenberger's fixed-interface random-systems layer: deterministic discrete systems
and environments, probabilistic systems, observation, random-system
equivalence and quotients, standard finite uniform objects, distance, parallel
composition, exact transcript factorization, H-coefficient bounds, and
conditional equivalence with its deterministic proof automation.

Converters and their attachment machinery form an optional extension and are
not imported by this root.
-/
