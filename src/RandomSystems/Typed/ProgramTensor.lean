module

public import RandomSystems.Converter.ProgramTensor
public import RandomSystems.Typed.ProbProgramAttachment

/-!
# Program converters on the interfaces of one joint automaton

Running `P` and `Q` on separate ports gives one program with state `(s,t)`. On each query
the selected program runs and the other retains its state. `parallel_ofDDC_ofProgramOn`
identifies the resulting converter on the parallel domain; `id_eq_ofDDC_forward` gives the
identity branch for one-sided attachment.

## References

1. U. Maurer. Indistinguishability of Random Systems. In *Advances in Cryptology —
   EUROCRYPT 2002*, LNCS 2332, pp. 110–132, Springer, 2002. Page numbers refer to the preprint.
-/

@[expose] public section

namespace SystemAlgebra.TypedConverter

open Probability.Distribution

variable
  -- `A ⊗ C` is the outside and `B ⊗ D` the inside interface; `S`, `T` carry program states.
  {A B C D : Interface} {S T : Type}
  -- `P` runs from `s` on `A`'s domain with at most `b` inside queries per invocation; `hP`
  -- certifies its converter from `B.domain` to `A.domain` with that bound.
  (s : S) (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
  (hP : IsDDCFrom B.domain A.domain b (DDC.ofProgramOn s P A.domain))
  -- `Q`, `t`, `c`, `hQ` are the same data for the second converter `C → D`.
  (t : T) (Q : Program T C.I D.I C.X C.Y D.X D.Y) {c : ℕ} (hc : Q.Bounded c)
  (hQ : IsDDCFrom D.domain C.domain c (DDC.ofProgramOn t Q C.domain))

include hb hc hP hQ in
/-- The paired program certifies the parallel domain map `(B ⊗ D).domain → (A ⊗ C).domain`. -/
lemma isDDCFrom_ofProgramOn_sum :
    IsDDCFrom (B.tensor D).domain (A.tensor C).domain (max b c)
      (DDC.ofProgramOn (s, t) (P.sum Q) (A.tensor C).domain) :=
  DDC.tensorL_ofProgramOn_sum hb hc hP hQ A.nonempty_prefix.2 C.nonempty_prefix.2 ▸
    IsDDCFrom.tensorL hP hQ

/-- **Program converters side by side are a program converter**: the parallel composition is
the converter of `P.sum Q` from `(s, t)` on the parallel domain. -/
theorem parallel_ofDDC_ofProgramOn :
    TypedConverter.parallel (TypedConverter.ofDDC (DDC.ofProgramOn s P A.domain) hP)
        (TypedConverter.ofDDC (DDC.ofProgramOn t Q C.domain) hQ) =
      TypedConverter.ofDDC (DDC.ofProgramOn (s, t) (P.sum Q) (A.tensor C).domain)
        (isDDCFrom_ofProgramOn_sum s P hb hP t Q hc hQ) := by
  -- Behaviors of DDCs compose as DDCs; the composed DDC is the paired program converter.
  rw [TypedConverter.parallel, TypedConverter.ofDDC, TypedConverter.ofDDC,
    PDCBehavior.tensor_ofDDC]
  exact PDCBehavior.ofDDC_eq_of_le _ _
    (W := DDC.ofProgramOn (s, t) (P.sum Q) (A.tensor C).domain)
    (fun _ _ hr => by
      rwa [DDC.tensorL_ofProgramOn_sum hb hc hP hQ A.nonempty_prefix.2
        C.nonempty_prefix.2] at hr)
    (fun _ _ hr => hr)

/-- **The identity is the forwarding program converter** on the same domain. -/
lemma id_eq_ofDDC_forward (A : Interface) :
    TypedConverter.id A =
      TypedConverter.ofDDC (DDC.ofProgramOn () (Program.forward A.I A.X A.Y) A.domain)
        (DDC.isDDCFrom_ofProgramOn_forward A.nonempty_prefix) := by
  -- `TypedConverter.id A` is the identity filter, which equals the forwarding converter.
  unfold TypedConverter.id PDCBehavior.id
  exact PDCBehavior.ofDDC_eq_of_le _ _
    (W := DDC.ofProgramOn () (Program.forward A.I A.X A.Y) A.domain)
    (fun _ _ hr => by rwa [DDC.filter_eq_ofProgramOn_forward A.nonempty_prefix] at hr)
    (fun _ _ hr => hr)

end SystemAlgebra.TypedConverter
