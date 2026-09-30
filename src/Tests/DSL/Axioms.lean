import Examples.DSL.AEADTests
import Tests.DSL.Diagnostics
import Tests.DSL.Semantics

/-!
# Axioms of the DSL

The compilation of declarations, the obligation lemmas, the example components and their
checks depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

-- Programs and their converters.
#print axioms SystemAlgebra.DDC.ofProgram_isResponsiveDDC
#print axioms SystemAlgebra.DDC.ofProgramOn_isDDCFrom
#print axioms SystemAlgebra.DDC.insideQueries_length_le_of_budget
#print axioms SystemAlgebra.DDC.insideQueries_length_le_of_costs
#print axioms SystemAlgebra.Interface.Converter.ofProgram
#print axioms SystemAlgebra.Interface.Converter.ofCostedProgram
#print axioms SystemAlgebra.DDC.insideQueries_restrict_length_le
#print axioms SystemAlgebra.Interface.Converter.ofPreservingProgram
#print axioms SystemAlgebra.Interface.perPort_tensor_admits

-- Inlining: attaching a program runs its body against the resource.
#print axioms SystemAlgebra.Program.apply_ofProgram
#print axioms SystemAlgebra.Program.trim_apply_ofProgram
#print axioms SystemAlgebra.Program.trim_apply_ofProgramOn
#print axioms SystemAlgebra.apply_filterDom_outside
#print axioms SystemAlgebra.PDCBehavior.ofDDC_apply
#print axioms SystemAlgebra.Interface.ofDDC_apply
#print axioms SystemAlgebra.Interface.ofDDC_ofProgramOn_smul_ofPDS
#print axioms SystemAlgebra.Program.inline_automatonSystem
#print axioms SystemAlgebra.Program.trim_apply_ofProgramOn_automaton
#print axioms SystemAlgebra.Program.combine_eq_of_invoke
#print axioms SystemAlgebra.Program.combine_congr
#print axioms SystemAlgebra.Interface.ofDDC_ofProgramOn_smul_ofAutomaton
#print axioms SystemAlgebra.Interface.Converter.ofProgram_smul_ofAutomaton
#print axioms SystemAlgebra.Interface.Converter.ofPreservingProgram_smul_ofAutomaton

-- Sources, contexts and automata.
#print axioms SystemAlgebra.Interface.Resource.source
#print axioms SystemAlgebra.Interface.stateAfter_sourceStep
#print axioms SystemAlgebra.Interface.rightContext
#print axioms SystemAlgebra.Interface.attach_rightContext
#print axioms SystemAlgebra.Interface.filter

-- Obligation lemmas.
#print axioms SystemAlgebra.DSL.sampleWitness
#print axioms SystemAlgebra.DSL.cost_prefix_closed
#print axioms SystemAlgebra.DSL.callBound_return
#print axioms SystemAlgebra.DSL.callBound_call
#print axioms SystemAlgebra.DSL.callBound_ite
#print axioms SystemAlgebra.DSL.callBound_foldr
#print axioms SystemAlgebra.DSL.callBound_uniform
#print axioms SystemAlgebra.DSL.callCost_return
#print axioms SystemAlgebra.DSL.callCost_call
#print axioms SystemAlgebra.DSL.callCost_foldr
#print axioms SystemAlgebra.DSL.avoids_call
#print axioms SystemAlgebra.DSL.preservesAt_call_self
#print axioms SystemAlgebra.DSL.preservesAt_call_other

-- Example components.
#print axioms DSLExamples.FreshBits
#print axioms DSLExamples.SecretBit
#print axioms DSLExamples.BoundedCounter
#print axioms DSLExamples.Padding
#print axioms DSLExamples.Padding.exact
#print axioms DSLExamples.WriteThrough.perPort
#print axioms DSLExamples.FirstRequests
#print axioms DSLExamples.Cipher.AES
#print axioms DSLExamples.Cipher.AES.perPort
#print axioms DSLExamples.Cipher.Whitening.perPort
#print axioms DSLExamples.Cipher.RandomMask.perPort
#print axioms DSLExamples.Cipher.WhitenedMaskedAES
#print axioms DSLExamples.Cipher.CBCMAC
#print axioms DSLExamples.Cipher.IndependentKeys
#print axioms DSLExamples.Cipher.composedAES_eq
#print axioms DSLExamples.Cipher.parallelAES_eq
#print axioms DSLExamples.Cipher.cbc_nonexpanding
#print axioms DSLExamples.Authenticated.AuthenticatedEncryption
#print axioms DSLExamples.Authenticated.authenticatedEncryption_eq

-- Checks.
#print axioms DSLTests.Semantics.freshBits_independent
#print axioms DSLTests.Semantics.secretBit_retained
#print axioms DSLTests.Semantics.counter_interleaving
#print axioms DSLTests.Semantics.counter_perPort_interleaving
#print axioms DSLTests.Semantics.counter_perPort_exceeded
#print axioms DSLExamples.Authenticated.bound_pos
#print axioms DSLExamples.Authenticated.encrypt_transcript
#print axioms DSLExamples.Authenticated.decrypt_transcript
#print axioms DSLExamples.Authenticated.decrypt_rejects
#print axioms DSLExamples.Authenticated.blockCount_le
#print axioms DSLExamples.Authenticated.authenticationBytes_length
#print axioms DSLExamples.Authenticated.aeadDecrypt_aeadEncrypt
