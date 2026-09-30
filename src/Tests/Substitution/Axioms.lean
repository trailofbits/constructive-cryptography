import Examples.Substitution
import Tests.Substitution.Implication
import Tests.Substitution.Relaxation
import Tests.Substitution.Construction
import Tests.Substitution.Quantitative
import Tests.Substitution.Tactics
import Tests.Substitution.Calculation

/-!
# Axioms of the substitution calculus

The substitution calculus, its instance on interfaces and its tests depend only on `propext`,
`Classical.choice` and `Quot.sound`.
-/

open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra

#print axioms SubstitutionRelation.substitutes_of_hybrid
#print axioms SubstitutionRelation.distance_hybrid_le
#print axioms SubstitutionRelation.Implication.substitutes
#print axioms SubstitutionRelation.Implication.distance_le
#print axioms SubstitutionRelation.Implication.map
#print axioms SubstitutionRelation.Implication.reverse
#print axioms SubstitutionRelation.Implication.append
#print axioms SubstitutionRelation.Implication.usageCount_append
#print axioms SubstitutionRelation.Implication.usageCount_reverse
#print axioms SubstitutionRelation.generatedRelation
#print axioms SubstitutionRelation.derivable_substitutes
#print axioms SubstitutionRelation.Implication.exists_serial_simulators
#print axioms Specification.Constructs.derivable_serial_simulators
#print axioms SubstitutionRelation.Implication.substitutesWithin
#print axioms SubstitutionRelation.Implication.substitutesWithin_of_mixed
#print axioms DistinguisherAdvantage.SubstitutesWithin.attach
#print axioms DistinguisherAdvantage.SubstitutesWithin.attach_serial
#print axioms Specification.map_reductionRelaxation_subset
#print axioms Specification.singleSubstitutionRelaxation_apply
#print axioms Specification.singleSubstitutionRelaxation_compatible
#print axioms Specification.substitutionRelaxation_compatible
#print axioms Specification.substitutionRelaxation_idem
#print axioms Specification.Constructs.substitutionRelaxation_serial_simulators

open SystemAlgebra SystemAlgebra.Substitution

#print axioms resourceDDC_isDDC
#print axioms resourceDDC_isDDCFrom
#print axioms apply_resourceDDC
#print axioms discardSystem_isDDCFrom
#print axioms SystemAlgebra.Interface.attach_resourceConverter
#print axioms SystemAlgebra.Interface.resource_empty_eq
#print axioms SystemAlgebra.Interface.attach_constant
#print axioms SystemAlgebra.Interface.attach_rightContext
#print axioms SystemAlgebra.Interface.attach_leftContext
#print axioms singleSubstitutionRelaxation_parallelCompatible

#print axioms SubstitutionExamples.unrestricted_diagonal
#print axioms SubstitutionExamples.construction_with_right_context
#print axioms SubstitutionExamples.construction_with_left_context
#print axioms SubstitutionExamples.constructsWithin_of_two_substitutions
#print axioms Tests.Substitution.Construction.repeated_assumption_counts
#print axioms Tests.Substitution.Construction.construction_serial_disjoint
#print axioms Tests.Substitution.Quantitative.mixed_three_steps
