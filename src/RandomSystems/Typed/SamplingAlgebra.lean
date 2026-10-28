import RandomSystems.Typed.Functional
import RandomSystems.Typed.Parallel

/-!
# Algebra of retained samples

These equalities rearrange *initial* independent choices. `sample_prod` groups two choices into
one product draw; `sample_comm` changes their order; `parallel_sample_right` carries a single
right-side draw through parallel composition. None resamples a choice during interaction.

```text
sample (k,l) once; R(k,l)  =  sample k once; sample l once; R(k,l)
R ∥ (sample k once; S(k))  =  sample k once; (R ∥ S(k))
```
-/

namespace SystemAlgebra.TypedSystem

open Probability

/-- Product sampling is nested sampling of two independent initial choices. -/
lemma sample_prod {A : Interface} {K L : Type}
    (P : Distribution K) [Distribution.IsProbability P]
    (Q : Distribution L) [Distribution.IsProbability Q]
    (R : K × L → TypedSystem A) :
    TypedSystem.sample (P.prod Q) R =
      TypedSystem.sample P (fun k => TypedSystem.sample Q (fun l => R (k, l))) := by
  -- Product mass is the iterated weighted sum of the same component system.
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  change (P.prod Q).sum (fun x w => w * (R x).1 h) = _
  rw [Distribution.sum_prod_mul]
  rfl

/-- Independent initial choices commute even when the system uses both choices. -/
lemma sample_comm {A : Interface} {K L : Type}
    (P : Distribution K) [Distribution.IsProbability P]
    (Q : Distribution L) [Distribution.IsProbability Q]
    (R : K → L → TypedSystem A) :
    TypedSystem.sample P (fun k => TypedSystem.sample Q (R k)) =
      TypedSystem.sample Q (fun l => TypedSystem.sample P (fun k => R k l)) := by
  -- Exchange the two finite sums, preserving each sample throughout the transcript.
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  simp only [sample_mass, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- A parallel system with a once-sampled right component retains that draw as one shared
choice in the whole parallel system. -/
lemma parallel_sample_right {A B : Interface} {K : Type}
    (R : TypedSystem A) (P : Distribution K) [Distribution.IsProbability P]
    (S : K → TypedSystem B) :
    TypedSystem.parallel R (TypedSystem.sample P S) =
      TypedSystem.sample P (fun k => TypedSystem.parallel R (S k)) := by
  classical
  -- Parallel observation is linear in the right component's mixture.
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  change RandomSystem.parallel R.1
      (RandomSystem.mix ⟨P, Distribution.IsProbability.isProbDist P⟩ (fun k => (S k).1))
      (h.map ((sumAlphabet (Sum.rec A.X B.X)).symm.prodCongr
        (sumAlphabet (Sum.rec A.Y B.Y)).symm)) = _
  rw [RandomSystem.parallel_mix_right, RandomSystem.mix_mass]
  rfl

end SystemAlgebra.TypedSystem
