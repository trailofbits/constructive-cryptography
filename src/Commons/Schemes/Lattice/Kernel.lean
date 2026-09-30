import Commons.Schemes.Lattice.Core

/-!
# Generic Negacyclic Ring Kernels

Adapted from VCVio (`Verified-zkEVM/VCVio`, `LatticeCrypto/Ring/Kernel.lean` at `f5119c6`), by Quang Dao.

Executable layer for the generic lattice ring architecture. Defines:

- `PolyKernel`: array-level read/write interface for a `PolyBackend`, bridging
  semantic coefficient indexing to mutable `Array` operations.
- `NegacyclicRing`: the principal executable bundle carrying a backend, a kernel,
  and coefficient-domain ring operations (zero, add, sub, neg, mul). This is the
  type that downstream scheme `Arithmetic.lean` modules instantiate.
- `NegacyclicRingSemantics`: a proof-facing soundness certificate relating the
  executable operations of a `NegacyclicRing` to the quotient ring
  `R[X] / (X^n + 1)` via a homomorphism `quotientOf`.
- `negacyclicConvCoeff`, `negacyclicMul`: the negacyclic convolution and the
  backend-generic multiplication it defines.
- `coeff_add/sub/zero/neg`: `@[simp]` API projecting the four kernel axioms to
  the `backend.coeff` accessor, used for coefficient-wise proof automation.
- `AddCommGroup ring.Poly`: global instance derived from the coefficient axioms
  via `ext_coeff`, so downstream code never needs local arithmetic instances.

The executable / proof boundary is enforced structurally: `NegacyclicRing` is
computable and carries no quotient types, while `NegacyclicRingSemantics` is
`noncomputable` and provides the algebraic soundness bridge.
-/




universe u v

namespace LatticeCrypto

/-- Executable array interface for a `PolyBackend`.

Bridges the semantic coefficient-indexed carrier to mutable `Array` operations
(`toArray` / `ofArray`) with round-trip and size laws. Scheme-specific fast
paths (e.g. concrete NTTs) operate on arrays via the kernel, then convert back
to the backend carrier. -/
structure PolyKernel (Coeff : Type u) (backend : PolyBackend Coeff) where
  toArray : backend.Poly → Array Coeff
  ofArray : Array Coeff → backend.Poly
  toArray_size : ∀ p, (toArray p).size = backend.degree
  coeff_ofArray : ∀ a (h : a.size = backend.degree) i,
    backend.coeff (ofArray a) i = a[i.val]'(by
      exact Nat.lt_of_lt_of_eq i.isLt h.symm)
  ofArray_toArray : ∀ p, ofArray (toArray p) = p

namespace PolyKernel

variable {Coeff : Type u} {backend : PolyBackend Coeff}

/-- Reify a kernel array back to the backend coefficient function. -/
def coeffFn (_kernel : PolyKernel Coeff backend) (a : Array Coeff) (h : a.size = backend.degree) :
    Fin backend.degree → Coeff :=
  fun i => a[i.val]'(by
    exact Nat.lt_of_lt_of_eq i.isLt h.symm)

end PolyKernel

/-- Bundled executable coefficient-domain arithmetic for `R[X] / (X^n + 1)`.

Packages a `PolyBackend`, a `PolyKernel`, and the five basic ring operations
into a single computable bundle. Downstream scheme `Arithmetic.lean` modules
(`MLDSA.Arithmetic`, `MLKEM.Arithmetic`) instantiate
this structure via `vectorNegacyclicRing` and then expose scheme-local type
aliases (`Rq`, `Tq`, `RqVec`, etc.) that the rest of the scheme imports. -/
structure NegacyclicRing (Coeff : Type u) [CommRing Coeff] where
  backend : PolyBackend.{u, v} Coeff
  kernel : PolyKernel.{u, v} Coeff backend
  zero : backend.Poly
  one : backend.Poly
  add : backend.Poly → backend.Poly → backend.Poly
  sub : backend.Poly → backend.Poly → backend.Poly
  neg : backend.Poly → backend.Poly
  mul : backend.Poly → backend.Poly → backend.Poly
  add_coeff : ∀ f g i, backend.coeff (add f g) i = backend.coeff f i + backend.coeff g i
  sub_coeff : ∀ f g i, backend.coeff (sub f g) i = backend.coeff f i - backend.coeff g i
  zero_coeff : ∀ i, backend.coeff zero i = 0
  neg_coeff : ∀ f i, backend.coeff (neg f) i = -backend.coeff f i

/-- Proof-facing soundness certificate for a `NegacyclicRing`.

Provides a ring homomorphism `quotientOf` from the executable carrier into the
semantic quotient `R[X] / (X^n + 1)`, together with proofs that each executable
operation is sound with respect to the corresponding quotient-ring operation.

This structure is `noncomputable` by design — it exists only for proof-level
reasoning and is never evaluated at runtime. -/
structure NegacyclicRingSemantics {Coeff : Type u} [CommRing Coeff]
    (ring : NegacyclicRing Coeff) where
  quotientOf : ring.backend.Poly → NegacyclicQuotient Coeff ring.backend.degree
  zero_sound : quotientOf ring.zero = 0
  one_sound : quotientOf ring.one = 1
  add_sound : ∀ f g, quotientOf (ring.add f g) = quotientOf f + quotientOf g
  sub_sound : ∀ f g, quotientOf (ring.sub f g) = quotientOf f - quotientOf g
  neg_sound : ∀ f, quotientOf (ring.neg f) = -quotientOf f
  mul_sound : ∀ f g, quotientOf (ring.mul f g) = quotientOf f * quotientOf g

namespace NegacyclicRing

variable {Coeff : Type u} [CommRing Coeff]

/-- The coefficient-domain carrier of a bundled negacyclic ring. -/
abbrev Poly (ring : NegacyclicRing Coeff) : Type _ :=
  ring.backend.Poly

/-- The degree of the bundled polynomial carrier. -/
abbrev degree (ring : NegacyclicRing Coeff) : Nat :=
  ring.backend.degree

/-- The semantic quotient associated to a bundled negacyclic ring. -/
abbrev Quotient (ring : NegacyclicRing Coeff) : Type _ :=
  NegacyclicQuotient Coeff ring.degree

/-- Coefficient projection from the bundled backend. -/
def coeff (ring : NegacyclicRing Coeff) (p : ring.Poly) : Fin ring.degree → Coeff :=
  ring.backend.coeff p

instance (ring : NegacyclicRing Coeff) : Zero ring.Poly :=
  ⟨ring.zero⟩

instance (ring : NegacyclicRing Coeff) : One ring.Poly :=
  ⟨ring.one⟩

instance (ring : NegacyclicRing Coeff) : Add ring.Poly :=
  ⟨ring.add⟩

instance (ring : NegacyclicRing Coeff) : Sub ring.Poly :=
  ⟨ring.sub⟩

instance (ring : NegacyclicRing Coeff) : Neg ring.Poly :=
  ⟨ring.neg⟩

instance (ring : NegacyclicRing Coeff) : Mul ring.Poly :=
  ⟨ring.mul⟩

/-- The `i`-th coefficient of `f + g` equals the sum of the individual coefficients. -/
@[simp] theorem coeff_add (ring : NegacyclicRing Coeff) (f g : ring.Poly) (i : Fin ring.degree) :
    ring.backend.coeff (f + g) i = ring.backend.coeff f i + ring.backend.coeff g i :=
  ring.add_coeff f g i

/-- The `i`-th coefficient of `f - g` equals the difference of the individual coefficients. -/
@[simp] theorem coeff_sub (ring : NegacyclicRing Coeff) (f g : ring.Poly) (i : Fin ring.degree) :
    ring.backend.coeff (f - g) i = ring.backend.coeff f i - ring.backend.coeff g i :=
  ring.sub_coeff f g i

/-- Every coefficient of the zero polynomial is zero. -/
@[simp] theorem coeff_zero (ring : NegacyclicRing Coeff) (i : Fin ring.degree) :
    ring.backend.coeff (0 : ring.Poly) i = 0 :=
  ring.zero_coeff i

/-- The `i`-th coefficient of `-f` is the negation of the `i`-th coefficient of `f`. -/
@[simp] theorem coeff_neg (ring : NegacyclicRing Coeff) (f : ring.Poly) (i : Fin ring.degree) :
    ring.backend.coeff (-f) i = -ring.backend.coeff f i :=
  ring.neg_coeff f i

instance (ring : NegacyclicRing Coeff) : AddCommGroup ring.Poly where
  add_assoc a b c     := by ext i; simp only [coeff_add, add_assoc]
  zero_add a          := by ext i; simp only [coeff_add, coeff_zero, zero_add]
  add_zero a          := by ext i; simp only [coeff_add, coeff_zero, add_zero]
  neg_add_cancel a    := by ext i; simp only [coeff_add, coeff_neg, neg_add_cancel, coeff_zero]
  add_comm a b        := by ext i; simp only [coeff_add, add_comm]
  sub_eq_add_neg a b  := by ext i; simp only [coeff_sub, coeff_add, coeff_neg, sub_eq_add_neg]
  nsmul               := nsmulRec
  zsmul               := zsmulRec

/-- Indexed access into a polynomial carrier by coefficient position. -/
instance (ring : NegacyclicRing Coeff) :
    GetElem ring.Poly Nat Coeff (fun _ i => i < ring.degree) where
  getElem p i hi := ring.backend.coeff p ⟨i, hi⟩

end NegacyclicRing

namespace NegacyclicRingSemantics

variable {Coeff : Type u} [CommRing Coeff] {ring : NegacyclicRing Coeff}

/-- The semantic quotient associated to a bundled soundness interpretation. -/
abbrev Quotient (_sem : NegacyclicRingSemantics ring) : Type _ :=
  NegacyclicQuotient Coeff ring.degree

end NegacyclicRingSemantics

/-- The k-th coefficient of the negacyclic convolution `(f · g) mod (X^n + 1)`.

Sums over all input-pair contributions `f[i] · g[j]` that land at output
index `k` under the negacyclic wrap rule: add when `i + j < n`, subtract
when `i + j ≥ n` (because `X^n ≡ -1`). -/
def negacyclicConvCoeff {Coeff : Type u} [Ring Coeff] {n : Nat}
    (f g : Fin n → Coeff) (k : Fin n) : Coeff :=
  ∑ ij : Fin n × Fin n,
    if (ij.1.val + ij.2.val) % n = k.val then
      if ij.1.val + ij.2.val < n then f ij.1 * g ij.2
      else -(f ij.1 * g ij.2)
    else 0

/-- Negacyclic multiplication: coefficient `k` of the product is `negacyclicConvCoeff`. -/
def negacyclicMul {Coeff : Type u} [Ring Coeff]
    (backend : PolyBackend.{u, u} Coeff) (f g : backend.Poly) : backend.Poly :=
  backend.build fun k =>
    negacyclicConvCoeff (backend.coeff f) (backend.coeff g) k

/-- The `i`-th coefficient of `negacyclicMul backend f g` is `negacyclicConvCoeff`. -/
@[simp] theorem negacyclicMul_coeff {Coeff : Type u} [Ring Coeff]
    (backend : PolyBackend.{u, u} Coeff) (f g : backend.Poly) (i : Fin backend.degree) :
    backend.coeff (negacyclicMul backend f g) i =
      negacyclicConvCoeff (backend.coeff f) (backend.coeff g) i :=
  backend.coeff_build _ i

end LatticeCrypto
