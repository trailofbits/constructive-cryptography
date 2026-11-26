module

public import Probability.Expectation
public import Tests.KEMDEM

/-!
# Averaging KEM decapsulation failures

The joint-event law averages failure first over encapsulation and then over key generation.
The existing correct KEM has zero failure mass by its supported correctness contract.
-/

@[expose] public section

namespace Tests.KEMAveraging

open Commons Probability Distribution

/-- Generate `(pk,sk)`, then encapsulate `(c,k)` under that same `pk`.
Failure mass is the expected conditional mass of `decaps sk c ≠ some k`. -/
example
    -- `PK` and `SK` carry public and secret keys; `C` and `K` carry ciphertexts and shared keys.
    -- The key-generation and encapsulation laws have finite support on these carriers.
    {PK SK C K : Type} (kem : KEM PK SK C K) :
    (ProbDist.jointLaw kem.gen (fun keys => kem.encaps keys.1)).1.mass
        (fun result => kem.decaps result.1.2 result.2.1 ≠ some result.2.2) =
      kem.gen.1.expect (fun keys => (kem.encaps keys.1).1.mass
        (fun encapsulation => kem.decaps keys.2 encapsulation.1 ≠ some encapsulation.2)) :=
  ProbDist.jointLaw_mass_eq_expect kem.gen (fun keys => kem.encaps keys.1)
    (fun result => kem.decaps result.1.2 result.2.1 ≠ some result.2.2)

/-- The existing KEM's supported encapsulations always decapsulate,
so their averaged failure is zero. -/
lemma falseKeyKEM_failure_eq_zero :
    (ProbDist.jointLaw KEMDEM.falseKeyKEM.gen
      (fun keys => KEMDEM.falseKeyKEM.encaps keys.1)).1.mass
        (fun result => KEMDEM.falseKeyKEM.decaps result.1.2 result.2.1 ≠ some result.2.2) = 0 := by
  rw [ProbDist.jointLaw_mass_eq_expect]
  calc
    _ = KEMDEM.falseKeyKEM.gen.1.expect (fun _ => 0) := by
      apply expect_congr_of_support
      intro keys supportedKeys
      -- Correctness is needed only on the supported key pair and encapsulation.
      calc
        _ = (KEMDEM.falseKeyKEM.encaps keys.1).1.mass (fun _ => False) := by
          apply mass_congr_of_support
          intro encapsulation supportedEncapsulation
          exact iff_false_intro (fun failed => failed
            (KEMDEM.falseKeyKEM_correct keys.1 keys.2 supportedKeys
              encapsulation.1 encapsulation.2 supportedEncapsulation))
        _ = 0 := mass_eq_zero_of_forall_not _ (fun _ => id)
    _ = 0 := expect_zero_right _

#print axioms falseKeyKEM_failure_eq_zero

end Tests.KEMAveraging
