import Verbose
import Applications.CBCMAC.Construction

/-!
This is the opt-in reachability gate for the live dependency. It proves
that the sister project sees the current CBC construction root.  The internal
collision game, conditional-equivalence lemma, and theta/application bridges
are intentionally private in `Applications.CBCMAC.Probability`; the complete
Stage 4 Verbose proof must remain unavailable until that owning module exposes
the public semantic seam required by `VERBOSE_SPEC.md`.

The file is outside the default test target because it intentionally follows
the evolving CBC application boundary. Building `CBCVerboseTests` is the
explicit readiness gate.
-/

#check Applications.CBCMAC.cbc_distance_le
#check Applications.CBCMAC.cbc_constructs_within
#check Applications.CBCMAC.cbcPDS_advantage_le
#check Applications.CBCMAC.realPDS_advantage_le

#print axioms Applications.CBCMAC.cbc_distance_le
#print axioms Applications.CBCMAC.cbc_constructs_within
