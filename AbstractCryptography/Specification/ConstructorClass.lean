/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import AbstractCryptography.Algebra.Star
import AbstractCryptography.Specification.Outbound

/-!
# The admitted constructor set `Γ` (MauRen16 §2.1, §3.5)

MauRen16 §2.1 (printed p. 4): "Typically one considers a certain set `Γ` of
constructors, possibly restricted in terms of efficiency or implementation
cost.  One is then interested in constructibility and also in
non-constructibility statements, where `𝒮` is not constructible from `ℛ`,
denoted `ℛ ↛ 𝒮`, if there exists no constructor `γ` for which `ℛ —γ→ 𝒮`:

  `ℛ ↛ 𝒮 :⟺ ¬∃ γ ∈ Γ : ℛ —γ→ 𝒮`."

`Constructs π ℛ 𝒮` (`Specification.Basic`) is the *labelled* relation, with the
constructor exhibited and no class restricting it; `Unconstructible`
(`Specification.Outbound`) already carries `Γ`, but only underneath a negation.
This module supplies the positive side, `Constructible`, so that possibility
and impossibility quantify over one and the same admitted set
(`unconstructible_iff_not_constructible`).

## Why `Γ` is a parameter, and what may be substituted for it

MauRen16 §3.5 (printed pp. 9–10) makes the choice of converter set a *modeling
decision* rather than part of the theory: "The general guiding principle in
constructive cryptography is that everything that is considered relevant for
the analysis one wants to perform is modeled as part of the resource.  In
contrast, the choice of a converter is, by definition, irrelevant with regard
to the entailed cost or complexity."  Four such choices are listed, each of
which "can be thought of as a particular security model".  All four are
*instantiations* of the parameter below — they are not four further
definitions:

1. **Information-theoretic.** "The term *information-theoretic security* is
   usually used when computation (at least by the adversary) is irrelevant.  In
   such a case the converter set includes all systems, regardless of the
   computational complexity of implementing them."  This is the class `⊤`, and
   it is the only one any carrier in this development currently instantiates.
2. **Memory-explicit.** "Even for information-theoretic security one may be
   interested in making nevertheless the memory requirements explicit …  In
   this case, memory is modeled as part of the resource and the converters are
   all systems that can compute arbitrary functions but cannot keep state
   between invocations."
3. **Computation-as-resource.** "If computing power is considered relevant,
   then one can consider converters that perform no computation by themselves
   but only connect systems and possibly input constants.  Any computational
   resource can be modeled as a (parallel) resource. …  In such a view,
   converters only route information, without performing computation."  This is
   the model MauRen16 §4.3 argues in, and
   `constructs_star_par_of_smul_eq` (`Algebra.Star`) is what it buys: an
   equation whose right factor is *not* a mere connection is re-read by moving
   the computation into a parallel resource.
4. **Efficiency-bounded.** "If, for some notion of efficiency, efficient
   computing power is considered irrelevant, then one can consider `Σ` to be
   the set of efficiently implementable converter systems."  Footnote 6
   supplies the closure property that makes `Submonoid` the right structure for
   the composition law below: "converters `α` and `β` from this particular set
   `Σ` can be composed to a new converter, say `α ∘ β`, and this composition is
   closed in the sense that the function `Φ → Φ` induced by `α ∘ β` is
   contained in the class of functions induced by converters in `Σ`."

## Why the constructor class is a *second* parameter

§3.5 closes on exactly this point: "Clearly, one could consider different
converter sets for honest parties and for dishonest parties.  For example, it
would be natural to consider a notion of efficiency and a different, larger
notion of feasibility, where the converters of honest parties must be
efficiently implementable and the converters of dishonest parties must only be
feasibly implementable.  It does not really seem well-justified to use the same
polynomial-time notion for both, except by tradition and possibly by the set of
results one can prove for this choice."

So the class the *constructor* is drawn from is a modeling choice separate from
the class the simulator and the `∗`-relaxation are drawn from.  Below, `Γ`
restricts the constructor and `H` — the paper's `Σ` — keeps carrying the
relaxations: `Constructible.epsilonRelaxation_trans` composes `ε`-balls of the
ambient metric under a `Γ`-constructor, and `Constructible.star` relaxes by `H`
while the constructor stays in `Γ`.

## References

* [U. Maurer, R. Renner, *From Indifferentiability to Constructive
  Cryptography (and Back)*, TCC 2016-B][MauRen16], §2.1 and §3.5.
-/

namespace AbstractCryptography

open Pointwise
open scoped ENNReal

variable {Sigma Φ : Type*} [Monoid Sigma] [MulAction Sigma Φ]

/-- MauRen16 §2.1: `𝒮` is **constructible** from `𝓡` within the admitted
constructor set `Γ` — "there exists a constructor `γ ∈ Γ` for which
`ℛ —γ→ 𝒮`".  This is the positive form of the paper's `↛`, and it is what the
labelled `Constructs` refines: `Constructs` exhibits the constructor and
restricts it to nothing, while `Constructible` hides it and confines it to `Γ`.

The parameter is a bare `Set Sigma`, matching `Unconstructible`; the two laws
that need `Γ` to hold a composite or the identity — `Constructible.trans` and
`constructible_of_subset` — ask for a `Submonoid` at their own site, which is
where MauRen16 footnote 6's closure requirement actually bites. -/
def Constructible (Γ : Set Sigma) (𝓡 𝒮 : Specification Φ) : Prop :=
  ∃ π ∈ Γ, Constructs π 𝓡 𝒮

/-- `𝓡 —[∈ Γ]→ 𝒮` is `Constructible Γ 𝓡 𝒮`: the class-restricted companion of
`Refinement.Basic`'s type-level `𝓡 —[∃ Γ]→ 𝒮`, which quantifies over an entire
constructor *type* instead of a subset of one. -/
scoped notation:50 R " —[∈ " Γ "]→ " S:51 => Constructible Γ R S

/-- MauRen16 §2.1's `ℛ ↛ 𝒮 :⟺ ¬∃ γ ∈ Γ : ℛ —γ→ 𝒮`, with both directions now
over one and the same `Γ`: impossibility is the negation of possibility,
definitionally.  Until `Constructible` existed, the tree's impossibility side
carried a class that its possibility side could not name. -/
theorem unconstructible_iff_not_constructible {Γ : Set Sigma} {𝓡 𝒮 : Specification Φ} :
    Unconstructible Γ 𝓡 𝒮 ↔ ¬ 𝓡 —[∈ Γ]→ 𝒮 := Iff.rfl

/-- A labelled construction whose constructor is admitted is a construction
within the class. -/
theorem Constructs.constructible {Γ : Set Sigma} {π : Sigma} {𝓡 𝒮 : Specification Φ}
    (hπ : π ∈ Γ) (h : 𝓡 —[π]→ 𝒮) : 𝓡 —[∈ Γ]→ 𝒮 :=
  ⟨π, hπ, h⟩

/-- MauRen16 §2.3's monotonicity, relativized: "the smaller `𝓡` or the larger
`𝒮`", the weaker the construction statement.  The constructor is untouched, so
the class plays no role. -/
theorem Constructible.mono {Γ : Set Sigma} {𝓡 𝓡' 𝒮 𝒮' : Specification Φ}
    (h𝓡 : 𝓡' ⊆ 𝓡) (h𝒮 : 𝒮 ⊆ 𝒮') (h : 𝓡 —[∈ Γ]→ 𝒮) : 𝓡' —[∈ Γ]→ 𝒮' :=
  let ⟨π, hπ, hc⟩ := h
  ⟨π, hπ, hc.mono h𝓡 h𝒮⟩

/-- **A larger admitted set proves more constructions.**  This is the transfer
§3.5's closing paragraph asks for: a construction carried out by honest
converters that "must be efficiently implementable" is a fortiori one carried
out within a "different, larger notion of feasibility".  Nothing is required of
either class — the same constructor witnesses both statements. -/
theorem Constructible.mono_constructors {Γ Γ' : Set Sigma} (hΓ : Γ ⊆ Γ')
    {𝓡 𝒮 : Specification Φ} (h : 𝓡 —[∈ Γ]→ 𝒮) : 𝓡 —[∈ Γ']→ 𝒮 :=
  let ⟨π, hπ, hc⟩ := h
  ⟨π, hΓ hπ, hc⟩

/-- The impossibility side is antitone in the class exactly where the
possibility side is monotone: an impossibility proved against the *larger*
admitted set is the stronger statement.  Together with `Unconstructible.anti`,
which is antitone in the two endpoints, this is the full monotonicity picture
of MauRen16 §2.3 once `Γ` is visible on both sides. -/
theorem Unconstructible.mono_constructors {Γ Γ' : Set Sigma} (hΓ : Γ ⊆ Γ')
    {𝓡 𝒮 : Specification Φ} (h : Unconstructible Γ' 𝓡 𝒮) : Unconstructible Γ 𝓡 𝒮 :=
  fun hc => h (Constructible.mono_constructors hΓ hc)

/-- **MauRen16 §4.1 Lemma 1, relativized to `Γ`**: "`ℛ —γ→ 𝒮 ∧ 𝒮 —γ′→ 𝒯 ⟹
ℛ —γ′∘γ→ 𝒯`".

`Constructs.trans` produces the composite label `π' * π`, and `Constructible`
forgets the label, so the class must be able to *hold* that composite.  That is
precisely MauRen16 footnote 6's closure requirement on the admitted set ("this
composition is closed"), and a `Submonoid` is the least structure supplying it.
On a bare `Set Sigma` the statement is false in general: this is the one place
where the constructor class needs algebraic structure at all. -/
theorem Constructible.trans {Γ : Submonoid Sigma} {𝓡 𝒮 𝒯 : Specification Φ}
    (h : 𝓡 —[∈ (Γ : Set Sigma)]→ 𝒮) (h' : 𝒮 —[∈ (Γ : Set Sigma)]→ 𝒯) :
    𝓡 —[∈ (Γ : Set Sigma)]→ 𝒯 := by
  obtain ⟨π, hπ, hc⟩ := h
  obtain ⟨π', hπ', hc'⟩ := h'
  exact ⟨π' * π, Γ.mul_mem hπ' hπ, hc.trans hc'⟩

/-- MauRen16 §3.3's "`id ∈ Σ`" transported to the constructor class: with the
identity admitted, CR18 §5.2.2's "`ℛ ⊆ 𝒮 ⟹ ℛ —id→ 𝒮`" is already a
construction within `Γ`. -/
theorem constructible_of_subset {Γ : Submonoid Sigma} {𝓡 𝒮 : Specification Φ}
    (h : 𝓡 ⊆ 𝒮) : 𝓡 —[∈ (Γ : Set Sigma)]→ 𝒮 :=
  ⟨1, Γ.one_mem, constructs_one_of_subset h⟩

/-- Constructibility within a submonoid is reflexive. -/
theorem Constructible.refl {Γ : Submonoid Sigma} (𝓡 : Specification Φ) :
    𝓡 —[∈ (Γ : Set Sigma)]→ 𝓡 :=
  constructible_of_subset Set.Subset.rfl

/-- **MauRen16 §4.1 Lemma 3, relativized**: "`ℛ —π→ 𝒮 ⟹ ℛ∗ —π→ 𝒮∗`", with the
two classes kept apart — the constructor ranges over `Γ`, the `∗`-relaxation
over `H`, which is the paper's `Σ`.

The premise is §3.3's `(αR)β = α(Rβ)` restricted to the pair of classes that
actually meet: every admitted constructor commutes with every converter the
relaxation may attach.  §3.5's closing paragraph is what makes this the right
shape — honest and dishonest parties need not draw their converters from the
same set — and in a concrete interface model it is discharged by the
honest/adversary support disjointness, not by a commutative converter monoid.
No closure of `Γ` is needed: the constructor is carried across unchanged. -/
theorem Constructible.star {Γ : Set Sigma} {H : Submonoid Sigma}
    {𝓡 𝒮 : Specification Φ}
    (commutes : ∀ π ∈ Γ, ∀ β ∈ H, π * β = β * π)
    (h : 𝓡 —[∈ Γ]→ 𝒮) :
    (Relaxation.star H : Relaxation Φ) 𝓡 —[∈ Γ]→ (Relaxation.star H) 𝒮 := by
  obtain ⟨π, hπ, hc⟩ := h
  exact ⟨π, hπ, Relaxation.constructs_star (commutes π hπ) hc⟩

section Metric

variable [PseudoEMetricSpace Φ]

/-- **MauRen16 §4.1 Corollary 1.1 / JM20 Corollary 1, relativized**: the error
budgets add up while the constructor stays inside `Γ`.

This is the statement in which the two classes visibly do different jobs.  The
`ε`-balls belong to the *ambient* converter class — MauRen16 Definition 2 asks
non-expansion of every `c : Sigma`, because the metric must survive whatever a
distinguisher or a simulator attaches — while the constructor carrying the
chain is confined to `Γ`.  Only the forgotten composite label `π' * π` needs
`Γ` closed, which is why the class is a `Submonoid` here and a bare set in
`Constructible.star`. -/
theorem Constructible.epsilonRelaxation_trans [IsNonexpandingSMul Sigma Φ]
    {Γ : Submonoid Sigma} {𝓡 𝒮 𝒯 : Specification Φ} {ε ε' : ℝ≥0∞}
    (h : 𝓡 —[∈ (Γ : Set Sigma)]→ Relaxation.epsilonRelaxation ε 𝒮)
    (h' : 𝒮 —[∈ (Γ : Set Sigma)]→ Relaxation.epsilonRelaxation ε' 𝒯) :
    𝓡 —[∈ (Γ : Set Sigma)]→ Relaxation.epsilonRelaxation (ε + ε') 𝒯 := by
  obtain ⟨π, hπ, hc⟩ := h
  obtain ⟨π', hπ', hc'⟩ := h'
  exact ⟨π' * π, Γ.mul_mem hπ' hπ, hc.epsilonRelaxation_trans hc'⟩

end Metric

end AbstractCryptography
