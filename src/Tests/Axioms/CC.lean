import ConstructiveCryptography

/-!
# Axioms of the Constructive Cryptography layer

Interfaces, resources and converters, their instances of the Constructive Cryptography
classes, and the abstract results of those classes depend only on `propext`,
`Classical.choice` and `Quot.sound`.
-/

-- ConstructiveCryptography.Automaton
#print axioms SystemAlgebra.Interface.Resource.ofAutomaton
#print axioms SystemAlgebra.Interface.Resource.ofAutomaton_mass
#print axioms SystemAlgebra.Interface.parallel_ofAutomaton

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

-- ConstructiveCryptography.CryptographicAlgebra.PseudoMetric
#print axioms ConstructiveCryptography.CryptographicAlgebra.distance_attach_le
#print axioms ConstructiveCryptography.CryptographicAlgebra.distance_parallel_le
#print axioms ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial
#print axioms ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.parallel

-- ConstructiveCryptography.CryptographicAlgebra.Star
#print axioms ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_of_simulator
#print axioms ConstructiveCryptography.CryptographicAlgebra.Specification.star_idem
#print axioms ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.star


-- ConstructiveCryptography.GameBound
#print axioms SystemAlgebra.Interface.Game.visible_ofPDG
#print axioms SystemAlgebra.Interface.Resource.sample_ofFunction_eq_behavior
#print axioms SystemAlgebra.Interface.ofSingleFunction_conditionallyEquivalent
#print axioms SystemAlgebra.Interface.game_dist_le
#print axioms SystemAlgebra.Interface.game_dist_ofSingleFunction_le

-- ConstructiveCryptography.Interface
#print axioms SystemAlgebra.Interface.category
#print axioms SystemAlgebra.Interface.identity_attach
#print axioms SystemAlgebra.Interface.comp_smul
#print axioms SystemAlgebra.Interface.Resource.exists_ofPDS

-- ConstructiveCryptography.InterfaceAlgebra
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
#print axioms SystemAlgebra.Interface.distinguisherAdvantage
#print axioms SystemAlgebra.Interface.distinguisherAdvantage_attach
#print axioms SystemAlgebra.Interface.substitutesWithin_attach
#print axioms SystemAlgebra.Interface.AdmissibleDistinguishers.substitutesWithin_attach
#print axioms SystemAlgebra.Interface.AdmissibleDistinguishers.substitutesWithin_context
#print axioms SystemAlgebra.Interface.absorb_comp
#print axioms SystemAlgebra.Interface.distinguisherAdvantage_le_distance

-- ConstructiveCryptography.InterfaceFilter
#print axioms SystemAlgebra.Interface.filter
#print axioms SystemAlgebra.Interface.restrict
#print axioms SystemAlgebra.Interface.filter_smul
#print axioms SystemAlgebra.Interface.filter_comp_filter_smul

-- ConstructiveCryptography.InterfaceGame
#print axioms SystemAlgebra.Interface.games
#print axioms SystemAlgebra.Interface.distinctionGames
#print axioms SystemAlgebra.Interface.win_le
#print axioms SystemAlgebra.Interface.dist_visible_le

-- ConstructiveCryptography.InterfaceMonoidal
#print axioms SystemAlgebra.Interface.monoidal

-- ConstructiveCryptography.InterfaceParallel
#print axioms SystemAlgebra.Interface.parallel
#print axioms SystemAlgebra.Interface.parallelConverter

-- ConstructiveCryptography.Notation
#print axioms SystemAlgebra.Interface.distance_triangle
#print axioms SystemAlgebra.Interface.tensor_smul
#print axioms SystemAlgebra.Interface.distance_parallel_le

-- ConstructiveCryptography.ResourceCoherence
#print axioms SystemAlgebra.Interface.parallel_assoc
#print axioms SystemAlgebra.Interface.parallel_dummy_left
#print axioms SystemAlgebra.Interface.parallel_dummy_right
#print axioms SystemAlgebra.Interface.parallel_swap

-- ConstructiveCryptography.ResourceParallel
#print axioms SystemAlgebra.Interface.rename_mass
#print axioms SystemAlgebra.Interface.parallel_ofPDS

-- ConstructiveCryptography.ResourceParallelAttachment
#print axioms SystemAlgebra.Interface.parallel_attach
