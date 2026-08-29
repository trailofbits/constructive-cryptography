/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import ConstructiveCryptography

/-!
# The algebraic sponge: indifferentiability from a random oracle

The sponge over an additive abelian group `F` (BDPV, EUROCRYPT 2008, algebraic
form — Poseidon, Rescue, … over a field): from a **public** random permutation of
the state `F^(r+c)` it constructs a random oracle, indifferentiably, with
advantage `≈ N²/|F|^c` (`N` primitive queries, capacity `c`).  The binary sponge
is `F = 𝔽₂`.  Only `F`'s `+` is needed here — absorption adds message blocks into
the rate `F^r`; the intended instantiations take `F` a finite field.

* The **statement** applies Maurer--Renner 2016, Lemma 5, in the typed
  `ResourceAlgebra`: an explicit sponge converter and an admitted simulator
  turn their distance bound into construction of the relaxed ideal. Jost's
  construction relation has the same direct-image form; simulation remains a
  proof route rather than part of construction semantics.
* The **functional core** is the deterministic map the construction converter
  realizes — pure `F`-algebra over the state `F^r × F^c`, in the spirit of
  `Applications/Sha256.lean`.

Deferred to the random-system instantiation are `RPerm` and `RO`, the sponge
and BDPV simulator as DDCs, and the `N²/|F|^c` capacity-collision bound.
-/

open scoped ENNReal

namespace Sponge

/-- Paper notation: `F ^ᵗ n` is the type of `n`-tuples over `F` (`Fin n → F`).  Spelled `^ᵗ`, not the paper's bare `^`, which is ambiguous with `HPow`. -/
scoped notation:75 F:75 " ^ᵗ " n:76 => (Fin n → F)

/-- Sponge parameters (field-element counts): rate `r`, capacity `c`, fixed
output length.  State `F^(r+c)`, digest `F^output`, security `≈ N²/|F|^c`. -/
structure Params where
  /-- Rate `r`: the outer part `F^r`. -/
  rate : ℕ
  /-- Capacity `c`: the inner part `F^c`, the security parameter. -/
  capacity : ℕ
  /-- Fixed output length: the digest is `F^output`. -/
  output : ℕ

/-- State width `r + c`. -/
def Params.width (p : Params) : ℕ := p.rate + p.capacity

/-! ### The sponge functional core

A pure function of the permutation `π` and the message, over the algebraic state
`F^r × F^c` (`.1` the rate, `.2` the capacity).  `hash` is the full map on a raw
message `List F` — `pad` (the `pad10*` rule), then `blocks` (chunk to rate
blocks), then absorb/squeeze. -/

section FunctionalCore

variable {F : Type} [AddCommGroup F] {p : Params}
  (π : F ^ᵗ p.rate × F ^ᵗ p.capacity → F ^ᵗ p.rate × F ^ᵗ p.capacity)

/-- Absorb one rate block `m`: add it into the rate part, then permute. -/
def absorb (s : F ^ᵗ p.rate × F ^ᵗ p.capacity) (m : F ^ᵗ p.rate) :
    F ^ᵗ p.rate × F ^ᵗ p.capacity :=
  π (s.1 + m, s.2)

/-- Absorb a message (as rate blocks) from the zero state. -/
def absorbList (ms : List (F ^ᵗ p.rate)) : F ^ᵗ p.rate × F ^ᵗ p.capacity :=
  ms.foldl (absorb π) 0

/-- The `k`-th squeezed rate block: the rate part after `k` further permutations. -/
def squeezeBlock (s : F ^ᵗ p.rate × F ^ᵗ p.capacity) (k : ℕ) : F ^ᵗ p.rate :=
  (π^[k] s).1

/-- The sponge hash `List (F^r) → F^output`: absorb, then read `output` field
elements off the squeezed rate stream — output index `i` is block `i / r`,
coordinate `i % r`. -/
def sponge (hr : 0 < p.rate) (ms : List (F ^ᵗ p.rate)) : F ^ᵗ p.output :=
  fun i => squeezeBlock π (absorbList π ms) (i.val / p.rate)
    ⟨i.val % p.rate, Nat.mod_lt i.val hr⟩

variable [One F]

/-- The `pad10*` rule: append `1`, then zeros up to the next multiple of the rate.
Injective (given `(1 : F) ≠ 0`) with a nonzero final block — the sponge-compliant
padding; that injectivity is the later proof obligation. -/
def pad (m : List F) : List F :=
  m ++ (1 : F) :: List.replicate ((p.rate - (m.length + 1) % p.rate) % p.rate) 0

/-- The padded message as rate blocks: block `k`, coordinate `j`, is padded element
`k * r + j` (all in range, since `pad` lands on a rate multiple). -/
def blocks (m : List F) : List (F ^ᵗ p.rate) :=
  let pm := pad (p := p) m
  (List.range (pm.length / p.rate)).map fun k j => pm.getD (k * p.rate + j.val) 0

/-- **The sponge hash** on a raw field-element message: pad, chunk, absorb, squeeze. -/
def hash (hr : 0 < p.rate) (m : List F) : F ^ᵗ p.output :=
  sponge π hr (blocks m)

end FunctionalCore

/-! ### The indifferentiability construction -/

open CategoryTheory
open AbstractCryptography.Categorical
open AbstractCryptography.Categorical.ResourceAlgebra

universe u v w

/-- An explicit sponge converter and admitted simulator establish the typed
indifferentiability construction once the concrete carrier supplies their
distance bound. Nothing sponge-specific is hidden in this theorem; the BDPV
simulator and capacity-collision argument are the instantiation obligations. -/
theorem sponge_indifferentiable
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {Phi : Opposite C ⥤ Type w} [ResourceAlgebra C Phi]
    {A B : C} {converters : EndoFamily (Opposite.op A)}
    {error : ENNReal} {RPerm : Resource Phi B} {RO : Resource Phi A}
    (converter : A ⟶ B) (simulator : CategoryTheory.End A)
    (simulatorAdmitted : simulator.op ∈ converters)
    (close : distance (Phi := Phi)
      (attach (Phi := Phi) converter RPerm)
      (attach (Phi := Phi) simulator RO) ≤ error) :
    ResourceAlgebra.Specification.Constructs (Phi := Phi) converter
      ({RPerm} : ResourceAlgebra.Specification Phi B)
      (ResourceAlgebra.Specification.epsilonRelaxation
        (Phi := Phi) error
        (ResourceAlgebra.Specification.star (Phi := Phi) converters
          ({RO} : ResourceAlgebra.Specification Phi A))) :=
  ResourceAlgebra.Specification.constructs_of_simulator
    simulator simulatorAdmitted close

end Sponge
