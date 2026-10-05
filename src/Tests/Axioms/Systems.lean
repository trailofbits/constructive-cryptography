import RandomSystems
import Tests.Counterexamples

/-!
# Axioms of the systems layer

The laws of random systems, deterministic and probabilistic converters, attachment,
parallel composition, distance and games, and the counterexamples, depend only on
`propext`, `Classical.choice` and `Quot.sound`. Comments name the laws of
`papers/SYSTEM_ALGEBRA_SPEC.md`.
-/

-- RandomSystems.Converter.ConverterAttachment
#print axioms SystemAlgebra.PDCBehavior.attach_id
#print axioms SystemAlgebra.PDCBehavior.attach_comp
#print axioms SystemAlgebra.PDCBehavior.attach_presents
#print axioms SystemAlgebra.PDCBehavior.attach_mass_eq_one

-- RandomSystems.Converter.ConverterDomain
#print axioms SystemAlgebra.IsDDC.eq_of_admitted_replies
#print axioms SystemAlgebra.IsDDCFrom.mapsDomain
#print axioms SystemAlgebra.IsDDCFrom.replies_iff_of_le
#print axioms SystemAlgebra.IsRandomSystem.restrict

-- RandomSystems.Converter.ConverterTensor
#print axioms SystemAlgebra.replies_tensorRaw_canon_iff
#print axioms SystemAlgebra.IsDDC.trim_serialM_tensorL
#print axioms SystemAlgebra.trim_apply_tensorL_pair
#print axioms SystemAlgebra.PDCBehavior.tensor_id
#print axioms SystemAlgebra.PDCBehavior.comp_tensor
#print axioms SystemAlgebra.PDCBehavior.tensor_presents
#print axioms SystemAlgebra.IsDDCFrom.tensorL
#print axioms SystemAlgebra.parallelInputs_of_length_le

-- RandomSystems.Converter.PDCBehavior
#print axioms SystemAlgebra.PDCBehavior.comp_assoc
#print axioms SystemAlgebra.PDCBehavior.id_comp
#print axioms SystemAlgebra.PDCBehavior.comp_id
#print axioms SystemAlgebra.isPDCBehavior_of_transcripts

-- RandomSystems.Converter.ParallelPDS
#print axioms SystemAlgebra.parallelStep_congr
#print axioms SystemAlgebra.parallel_automatonSystem
#print axioms SystemAlgebra.parallelPDS

-- RandomSystems.Converter.PartialIdentity
#print axioms SystemAlgebra.IsDDC.trim_serialM_id
#print axioms SystemAlgebra.IsDDC.trim_id_serialM

-- RandomSystems.Converter.ResourceAttachment
#print axioms SystemAlgebra.MapsDomain.comp
#print axioms SystemAlgebra.IsResponsiveDDC.mapsDomain_of_replies

-- RandomSystems.Converter.ResourceCanon
#print axioms SystemAlgebra.trim_apply_canon

-- RandomSystems.Cumulative.ConnectionObservation
#print axioms SystemAlgebra.replies_connection_iff
#print axioms SystemAlgebra.RandomSystem.connectionLaw_length
#print axioms SystemAlgebra.RandomSystem.connectionLaw_isProbDist
#print axioms SystemAlgebra.RandomSystem.connectionLaw_eq_mass
#print axioms SystemAlgebra.RandomSystem.connectionLaw_stable

-- RandomSystems.Cumulative.Cumulative
#print axioms SystemAlgebra.PDS.behavior_eq_iff
#print axioms SystemAlgebra.RandomSystem.ofPDSClass_injective
#print axioms SystemAlgebra.RandomSystem.conditional_apply
#print axioms SystemAlgebra.RandomSystem.ofConditional
#print axioms SystemAlgebra.RandomSystem.relabel
#print axioms SystemAlgebra.RandomSystem.relabel_injective

-- RandomSystems.Cumulative.CumulativeObservation
#print axioms SystemAlgebra.RandomSystem.sLaw_isProbDist
#print axioms SystemAlgebra.RandomSystem.sLaw_completed_eq_mass
#print axioms SystemAlgebra.RandomSystem.sLaw_completed_stable
#print axioms SystemAlgebra.RandomSystem.eq_iff_sLaw
#print axioms SystemAlgebra.RandomSystem.eq_iff_sLaw_fixedQueries

-- RandomSystems.Cumulative.CumulativeOperations
#print axioms SystemAlgebra.RandomSystem.mix
#print axioms SystemAlgebra.RandomSystem.parallel
#print axioms SystemAlgebra.RandomSystem.parallel_ofPDS_mass
#print axioms SystemAlgebra.PDS.parallel_mass

-- RandomSystems.Cumulative.Presentation
#print axioms SystemAlgebra.RandomSystem.exists_presentation

-- RandomSystems.DDC.Absorb
#print axioms SystemAlgebra.close_attachL  -- E1
#print axioms SystemAlgebra.decision_attachL
#print axioms SystemAlgebra.IsDDC.count_le
#print axioms SystemAlgebra.absorbL_isDDD  -- D ⋄ α is a distinguisher

-- RandomSystems.DDC.CanonWiring
#print axioms SystemAlgebra.replies_serialM_canon_iff

-- RandomSystems.DDC.DDC
#print axioms SystemAlgebra.IsResponsiveDDC.converges_along
#print axioms SystemAlgebra.idConverter_isResponsiveDDC  -- 𝟙 is a converter
#print axioms SystemAlgebra.IsResponsiveDDC.totalResource_along
#print axioms SystemAlgebra.attachAlong_canon
#print axioms SystemAlgebra.attachAlong_idConverter  -- I

-- RandomSystems.DDC.DDCParallelLaws
#print axioms SystemAlgebra.trim_serialM_tensorL

-- RandomSystems.DDC.Serial
#print axioms SystemAlgebra.IsResponsiveDDC.comp  -- trim (β ⊙ α) is a converter
#print axioms SystemAlgebra.attachAlong_serialM  -- A3, raw composite
#print axioms SystemAlgebra.attachAlong_comp  -- A3, trim (β ⊙ α)
#print axioms SystemAlgebra.attachAlong_comp_behEq

-- RandomSystems.DDC.SingleAlphabet
#print axioms SystemAlgebra.attachL_relabelL  -- naturality
#print axioms SystemAlgebra.attachL_idConverter
#print axioms SystemAlgebra.attachL_comp
#print axioms SystemAlgebra.attachL_comm
#print axioms SystemAlgebra.attachL_parL
#print axioms SystemAlgebra.parL_dummyL

-- RandomSystems.DDC.Tensor
#print axioms SystemAlgebra.canon_isResponsiveDDC
#print axioms SystemAlgebra.IsResponsiveDDC.renameOut
#print axioms SystemAlgebra.attachL_renameOut
#print axioms SystemAlgebra.IsResponsiveDDC.tensorL
#print axioms SystemAlgebra.attachL_tensorL

-- RandomSystems.Distance.Absorption
#print axioms SystemAlgebra.close_apply
#print axioms SystemAlgebra.absorbAll_isDDD

-- RandomSystems.Distance.Decision
#print axioms SystemAlgebra.RandomSystem.statDist_le_transcriptDistance
#print axioms SystemAlgebra.Domain.decisionCompatible_iff_deterministic

-- RandomSystems.Distance.Distinguisher
#print axioms SystemAlgebra.RandomSystem.transcriptDistance_eq_iSup
#print axioms SystemAlgebra.Domain.Distinguisher.advantage_triangle
#print axioms SystemAlgebra.Domain.Distinguisher.advantage_le_transcriptDistance
#print axioms SystemAlgebra.RandomSystem.transcriptDistance_eq_iSup_behavior
#print axioms SystemAlgebra.Domain.DistinguisherBehavior.absorb
#print axioms SystemAlgebra.Domain.DistinguisherBehavior.absorb_comp
#print axioms SystemAlgebra.Domain.DecisionCompatible.absorbAll
#print axioms SystemAlgebra.RandomSystem.decisionProbability_attach
#print axioms SystemAlgebra.Domain.Distinguisher.exists_absorbAll
#print axioms SystemAlgebra.Domain.Distinguisher.exists_absorbRight

-- RandomSystems.Distance.ParallelObservation
#print axioms SystemAlgebra.Domain.DecisionCompatible.absorbRight
#print axioms SystemAlgebra.RandomSystem.decisionProbability_parallel

-- RandomSystems.Distance.Restriction
#print axioms SystemAlgebra.admitted_ofInputs_iff
#print axioms SystemAlgebra.RandomSystem.restrict_restrict
#print axioms SystemAlgebra.RandomSystem.sLaw_restrict
#print axioms SystemAlgebra.RandomSystem.transcriptDistance_restrict_le

-- RandomSystems.Distance.Transcript
#print axioms SystemAlgebra.IsDDD.relabel
#print axioms SystemAlgebra.eRun_fst
#print axioms SystemAlgebra.envProbe_isDDD
#print axioms SystemAlgebra.ddeOf_bounded

-- RandomSystems.Game.DiscreteMBO
#print axioms SystemAlgebra.PDG.visible_behavior
#print axioms SystemAlgebra.PDG.monotoneMBO_behavior
#print axioms SystemAlgebra.PDG.unsetProbability_behavior
#print axioms SystemAlgebra.PDG.one_sub_le_unsetProbability_behavior
#print axioms SystemAlgebra.PDG.conditionallyEquivalent_behavior

-- RandomSystems.Game.FunctionGame
#print axioms SystemAlgebra.PDG.ofFunction_conditionallyEquivalent

-- RandomSystems.Game.MBO
#print axioms SystemAlgebra.RandomSystem.visible
#print axioms SystemAlgebra.RandomSystem.abs_decisionProbability_sub_le_winProbability
#print axioms SystemAlgebra.Domain.Distinguisher.advantage_le_winProbability
#print axioms SystemAlgebra.Domain.Distinguisher.winProbability_le_of_unsetProbability
#print axioms SystemAlgebra.RandomSystem.transcriptDistance_visible_le_of_unsetProbability

-- RandomSystems.Game.MBOAttachment
#print axioms SystemAlgebra.PDCBehavior.liftMBO_id
#print axioms SystemAlgebra.PDCBehavior.liftMBO_comp
#print axioms SystemAlgebra.RandomSystem.visible_attach_liftMBO
#print axioms SystemAlgebra.RandomSystem.MonotoneMBO.attach_liftMBO
#print axioms SystemAlgebra.RandomSystem.winProbability_attach_liftMBO
#print axioms SystemAlgebra.Domain.Distinguisher.exists_absorbAll_winProbability
#print axioms SystemAlgebra.Domain.SolverBehavior.absorb

-- RandomSystems.PDS.Function
#print axioms SystemAlgebra.DDS.ofFunction
#print axioms SystemAlgebra.DDS.replies_ofFunction_iff

-- RandomSystems.System.Basic
#print axioms SystemAlgebra.interconnect_interconnect  -- C1 (engine)
#print axioms SystemAlgebra.interconnect_relabel  -- C2 (engine)
#print axioms SystemAlgebra.relabel_interconnect  -- C2 (engine)
#print axioms SystemAlgebra.parAll_reindex  -- P1
#print axioms SystemAlgebra.parAll_flatten  -- P2
#print axioms SystemAlgebra.parAll_relabel  -- P3
#print axioms SystemAlgebra.parAll_interconnect  -- C3, under convergence
#print axioms SystemAlgebra.Finite.terminating  -- T0
#print axioms SystemAlgebra.Terminating.parAll  -- T1
#print axioms SystemAlgebra.Terminating.interconnect  -- T2
#print axioms SystemAlgebra.Terminating.converges  -- T2
#print axioms SystemAlgebra.Terminating.relabel  -- T3
#print axioms SystemAlgebra.trim_behEq  -- R1
#print axioms SystemAlgebra.trim_prefix_closed  -- R1
#print axioms SystemAlgebra.finite_trim_parAll  -- R2
#print axioms SystemAlgebra.Finite.interconnect  -- R3
#print axioms SystemAlgebra.EqOnReachable.relabel  -- B
#print axioms SystemAlgebra.EqOnReachable.parAll  -- B
#print axioms SystemAlgebra.EqOnReachable.interconnect  -- B
#print axioms SystemAlgebra.converges_pair_of_terminating
#print axioms SystemAlgebra.behEq_iff_transcript
#print axioms SystemAlgebra.converges_pair  -- attachments of bounded converters converge
#print axioms SystemAlgebra.EqOnReachable.eq_of_isDDS
#print axioms SystemAlgebra.IsDDS.trim_eq
#print axioms SystemAlgebra.reach_parAll_iff
#print axioms SystemAlgebra.trim_parAll_dom
#print axioms SystemAlgebra.Transcript.eq_of_stopped

-- RandomSystems.System.Automaton
#print axioms SystemAlgebra.IsBisim.comp
#print axioms SystemAlgebra.automatonSystem_eq_of_bisim

-- RandomSystems.System.InterfaceSystem
#print axioms SystemAlgebra.connect_connect  -- C1
#print axioms SystemAlgebra.connect_comm  -- C4
#print axioms SystemAlgebra.connect_relabelI  -- C2
#print axioms SystemAlgebra.attach_assoc  -- A1
#print axioms SystemAlgebra.attachAlong_comm  -- A2, under convergence
#print axioms SystemAlgebra.attachAlong_protocol  -- protocol of two converters, under convergence
#print axioms SystemAlgebra.close_pair  -- E2, only `D` terminating
#print axioms SystemAlgebra.partialClose_isDDD  -- `S` arbitrary

-- RandomSystems.System.Observation
#print axioms SystemAlgebra.close_decision
#print axioms SystemAlgebra.close_dom_iff_compatible
#print axioms SystemAlgebra.behEq_iff_decision
#print axioms SystemAlgebra.behEq_iff_transcript_DDD
#print axioms SystemAlgebra.dde_blind_beyond_resources

-- RandomSystems.System.Replies
#print axioms SystemAlgebra.replies_trim_iff

-- Tests.Counterexamples
#print axioms SystemAlgebra.Counterexamples.locality_fails_without_termination
#print axioms SystemAlgebra.Counterexamples.identity_fails_without_reactivity
