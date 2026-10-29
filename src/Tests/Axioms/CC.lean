import ConstructiveCryptography

/-!
# Axioms of the Constructive Cryptography layer

The abstract results of the Constructive Cryptography classes, and the instances of those classes
on interfaces, depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

-- ConstructiveCryptography.CryptographicAlgebra.Basic
#print axioms ConstructiveCryptography.CryptographicAlgebra.attach_parallel
#print axioms ConstructiveCryptography.CryptographicAlgebra.parallel_assoc
#print axioms ConstructiveCryptography.CryptographicAlgebra.parallel_dummy_left
#print axioms ConstructiveCryptography.CryptographicAlgebra.parallel_dummy_right
#print axioms ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial
#print axioms ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.parallel

-- ConstructiveCryptography.CryptographicAlgebra.Distinguisher
#print axioms ConstructiveCryptography.CompatibleDistinguisherClass.ofClosure

-- ConstructiveCryptography.CryptographicAlgebra.Game
#print axioms ConstructiveCryptography.Games.absorb_comp
#print axioms ConstructiveCryptography.Games.win_le_of_reduction
#print axioms ConstructiveCryptography.Problem.performance_le_of_reduction
#print axioms ConstructiveCryptography.DistinctionGames.absorb_mem

-- ConstructiveCryptography.CryptographicAlgebra.PseudoMetric
#print axioms ConstructiveCryptography.CryptographicAlgebra.distance_attach_le
#print axioms ConstructiveCryptography.CryptographicAlgebra.distance_eq_of_mutual_attach
#print axioms ConstructiveCryptography.CryptographicAlgebra.distance_parallel_le
#print axioms ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial
#print axioms ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.parallel

-- ConstructiveCryptography.CryptographicAlgebra.Star
#print axioms ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_of_simulator
#print axioms ConstructiveCryptography.CryptographicAlgebra.Specification.star_idem
#print axioms ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.star

-- ConstructiveCryptography.Instances.Algebra
#print axioms SystemAlgebra.Interface.resourcesLaxMonoidal
#print axioms SystemAlgebra.Interface.cc_parallel_eq
#print axioms SystemAlgebra.Interface.cc_distance_eq
#print axioms SystemAlgebra.Interface.resourceTheory
#print axioms SystemAlgebra.Interface.cryptographicAlgebra
#print axioms SystemAlgebra.Interface.compatibleDistinguisherClass
#print axioms SystemAlgebra.Interface.distinguishers_attach
#print axioms SystemAlgebra.Interface.distinguishers_parallel_left
#print axioms SystemAlgebra.Interface.distinguishers_parallel_right
#print axioms SystemAlgebra.Interface.cc_dummy_eq
-- The decision layer (`ConstructiveCryptography.Distinguisher`), typed absorption
-- (`RandomSystems.Typed.Distinguisher`) and admitted reductions
-- (`ConstructiveCryptography.CryptographicAlgebra.DistinguisherAction`)
#print axioms ConstructiveCryptography.Distinguishers.distinguisherAdvantage
#print axioms ConstructiveCryptography.DistinguisherAction.advantage_absorb
#print axioms SystemAlgebra.TypedDistinguisher.absorb_comp
#print axioms ConstructiveCryptography.AdmissibleDistinguishers.substitutesWithin_attach
#print axioms ConstructiveCryptography.AdmissibleDistinguishers.substitutesWithin_context
-- ConstructiveCryptography.Instances.Algebra, continued
#print axioms SystemAlgebra.Interface.distinguisherAdvantageDominated
#print axioms SystemAlgebra.Interface.parallel_assoc
#print axioms SystemAlgebra.Interface.parallel_dummy_left
#print axioms SystemAlgebra.Interface.parallel_dummy_right
#print axioms SystemAlgebra.Interface.parallel_swap

-- ConstructiveCryptography.Instances.Category
#print axioms SystemAlgebra.Interface.category
#print axioms SystemAlgebra.Interface.identity_attach
#print axioms SystemAlgebra.Interface.comp_smul

-- ConstructiveCryptography.Instances.Game
#print axioms SystemAlgebra.Interface.games
#print axioms SystemAlgebra.Interface.distinctionGames
#print axioms SystemAlgebra.Interface.win_le
#print axioms SystemAlgebra.Interface.dist_visible_le
#print axioms SystemAlgebra.Interface.game_dist_le
#print axioms SystemAlgebra.Interface.game_dist_ofSingleFunction_le

-- ConstructiveCryptography.Instances.Monoidal
#print axioms SystemAlgebra.Interface.monoidal

-- ConstructiveCryptography.Notation
#print axioms SystemAlgebra.Interface.distance_triangle
#print axioms SystemAlgebra.Interface.distance_eq_of_mutual_smul
#print axioms SystemAlgebra.Interface.tensor_smul
#print axioms SystemAlgebra.Interface.distance_parallel_le
