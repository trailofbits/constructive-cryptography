# Probability

This library holds the finitely supported laws on which the random systems are built:
distributions and probability distributions, kernels, the statistical distance, couplings and the
$`n`$-ary maximal coupling, expectation, and the counting behind collision bounds. Citations refer
to the numbered [references](#references) at the end; [1]–[3] are those of
[THEORY.md](../../THEORY.md#references).

## Distributions and kernels

*Finitely supported laws [1, Definitions 1–4]:*

```math
\mathrm{Distribution}(A) = A \to_0 \mathbb R, \qquad
\delta(X, Y) = \sum_a \max\big(X(a) - Y(a),\ 0\big) .
```

A [**distribution**][Distribution] is a finitely supported function to $`\mathbb R`$, and a
[**probability distribution**][ProbDist] one that is [nonnegative with weight one][isProbDist].
Distributions have [masses][mass] of events, [pushforwards][fTransform], [products][prod] of two
laws and of [families][pi], and [uniform][uniform] laws. The
[heterogeneous finite product][piDep] assigns the product mass to a dependent family of
coordinate outcomes. The alphabets may be infinite; only the index set and each support are
finite. [`ProbDist.pi`](Distribution.lean) and [`ProbDist.piDep`](DependentProduct.lean)
construct normalized independent families directly, carrying the coordinate normalization
proofs into the product.
For example, `ProbDist.pi (fun _ : Fin q => ν)` is the law of `q` independent samples from `ν`.
A [**kernel**][bindK] $`f`$ is a conditional distribution [3, §3.6.1]; mixed over a law $`\mu`$
it gives $`\sum_a \mu(a)\, f(a)`$:
[mixtures compose][bindK_bindK], a pushforward
[is the point kernel of its function][bindK_single_comp], and an independent product
[disintegrates][pi_eq_bindK_update] at a coordinate. Probability laws have
[pushforwards][ProbDist.map] and [sequential compositions][ProbDist.bind]; a
[constant probability kernel][ProbDist.bind_const] returns its law.
[Successive maps][ProbDist.map_map] compose, and [independent maps][prodProbDist_map] satisfy
$`(f_*P) \times (g_*Q) = (f \times g)_*(P \times Q)`$.
[The identity map][ProbDist.map_id] leaves a law unchanged, so $`g=\mathrm{id}`$ or
$`f=\mathrm{id}`$ gives the [left][prodProbDist_map_left] and
[right][prodProbDist_map_right] one-coordinate forms.
[Independent uniform coordinates][prodProbDist_uniform] form a uniform pair.
A [joint law][ProbDist.jointLaw] retains both successive draws:
$`J_{\mu,K}(h,z)=\mu(h)K(h,z)`$, with [first marginal][ProbDist.jointLaw_fst] $`\mu`$. For
arbitrary maps $`d_H, d_Z`$ with $`(d_H)_*\mu'=\mu`$ and $`(d_Z)_*K'(h)=K(d_H h)`$,
[`ProbDist.jointLaw_map`][ProbDist.jointLaw_map] gives
$`(d_H\times d_Z)_*J_{\mu',K'}=J_{\mu,K}`$. The outcome types are arbitrary; each law has finite
support. For a nonnegative mass function $`X`$, [`normalizeOr`][normalizeOr] is
$`\lvert X\rvert^{-1}X`$ at nonzero weight and an explicit fallback law at weight zero. Its
identity $`\lvert X\rvert\,\operatorname{normalizeOr}(X)=X`$ also holds at zero weight, where
the fallback is multiplied by zero.
[Conditioning on an observation](Conditioning.lean) then disintegrates a law into its
normalized fibers. `ProbDist.uniformOn E fallback` names the normalized uniform restriction
to `E`, using the explicit fallback at an empty event. Symmetries preserving a conditioning event preserve its restricted uniform
law; equal masses on that event identify the normalized uniform restriction.

The notation `𝒰[A]` denotes the [normalized uniform law][ProbDist.uniform] of type
`Distribution.ProbDist A`, with mass $`1/\lvert A \rvert`$ at each point of a finite nonempty
$`A`$; its underlying raw distribution `𝒰[A].1` is `Distribution.uniform A`.

For a finite group $`G`$ with $`\gcd(|G|,e)=1`$, [blinding](Group.lean) sends a uniform
$`r`$ to a uniform $`yr^e`$. `ProbDist.bind_uniform_mul_pow` transports any output kernel
through this map. `ProbDist.blindRootSolver` unblinds the returned root with the same multiplier;
`ProbDist.rootSuccessLaw` observes success, rejecting failure. For commutative groups,
`ProbDist.blinding_success_eq` equates this success law at a fixed challenge with the original
solver's uniform-challenge success law.

## Statistical distance

The [**statistical distance**][statDist]
satisfies the [triangle inequality][statDist_triangle] and [data processing][statDist_fTransform_le],
$`\delta(fX, fY) \le \delta(X, Y)`$; with [positive parts][statDist_eq_weight_posPart] it is
$`\delta(X, Y) = \lvert (X - Y)^{+} \rvert`$, and with [overlaps][statDist_eq_weight_sub_weight_inf]
$`\delta(X, Y) = \lvert X \rvert - \lvert X \wedge Y \rvert`$.

[`statDist_fTransform_le_expect_of_ratio`][statDist_fTransform_le_expect_of_ratio] combines
data processing [1, Lemma 3] with the expectation method [4, Lemma 2.2.1] after any common
function $`f`$:

```math
(1-\varepsilon(a))Q(a)\le P(a)\ \text{for all } a,\quad \varepsilon\ge0
\quad\Longrightarrow\quad
\delta(f_*P,f_*Q)\le\delta(P,Q)\le\mathbb E_Q[\varepsilon].
```

Here $`P,Q`$ have equal total weight, $`Q`$ is nonnegative and $`P`$ may be signed; the
nonnegative loss $`\varepsilon`$ may exceed one. Systems specialize $`P,Q`$ to probability laws
and $`f`$ to a transcript projection, then take a supremum over environments.

## Couplings, expectation and counting

For a [coupling][IsCoupling] of $`X`$ and $`Y`$,
[the distance is at most the off-diagonal mass][statDist_le_offDiagonalMass],
$`\delta(X, Y) \le \Pr[X \ne Y]`$, and [some coupling attains it][exists_coupling_offDiagonalMass_eq].
For the $`n`$-ary maximal coupling [2, Theorem 2.29], the [largest agreement][supAgreement] of $`n`$
laws of one weight [is the weight of their overlap][supAgreement_eq_weight_overlapDist].
[**Expectation**][expect] is linear [in the distribution][expect_add_left] and
[in the function][expect_add_right], with [Markov's][mass_ge_le_expect_div],
the [Cauchy–Schwarz][expect_mul_sq_le_sq_mul_sq] and [Jensen's][ConvexOn.map_expect_le]
inequalities. Collision bounds [count][card_function_fiber_finset] the functions $`X \to Y`$
agreeing with a map on a finite set $`S`$: there are $`\lvert Y \rvert^{\lvert X \rvert - \lvert S \rvert}`$.
For a uniform function table, [a consistent query transcript][uniform_mass_transcript_eq]
fixes one independent value per distinct input; repeated inputs add no factor. Two query
families with [the same equality pattern][fTransform_eval_uniform_eq_of_same_fibers] have the
same output law, even when their table domains have different sizes. The index type may be
infinite; the finite table domains keep both query images finite.
A batch $`\mathrm{next}(b) : I \to X`$ may also be chosen from the revealed base values
$`b = F \circ \mathrm{base}`$. If base and selected coordinates are jointly injective whenever
$`\mathrm{good}(b)`$ holds, then [the joint mass][uniform_mass_adaptive_eval_eq_mul] is

```math
\Pr\big[\mathrm{good}(b) \wedge F \circ \mathrm{next}(b) = v\big]
  = \Pr\big[\mathrm{good}(b)\big] \cdot \lvert Y \rvert^{-\lvert I \rvert} .
```

Outside the good event, coordinates may repeat, and the good event may have probability zero.

An event that ignores one table coordinate [factors from its fresh value]
[uniform_mass_fresh_eval_eq]. A [symmetric pair union bound][mass_exists_pair_le_choose]
counts each unordered pair once; [uniform-table collisions][uniform_mass_not_injOn_le_choose]
therefore cost at most $`\binom{|S|}{2}/|Y|`$ on a fixed queried set $`S`$.
A uniform-preserving [projection of a fresh full reply][uniform_mass_fresh_projected_eval_eq]
remains uniform after a transcript event that ignores its coordinate. The
[projected collision bound][uniform_mass_transcript_projected_collision_le] keeps the full
reply table and charges only the visible output alphabet. The
[distinct-input form][uniform_mass_transcript_collision_le_card] charges `d / |Y|` after `d`
distinct tested inputs, and zero for a repeat on a collision-free history.
[Disjoint finite table restrictions][uniform_mass_disjoint_events] factor for arbitrary
events on their respective output tuples. The [base-set form]
[uniform_mass_fresh_outputs_eq] applies when an event depends only on a named finite set
of coordinates and the other outputs lie outside it.

For an adaptive evaluator whose complete output tuple pins its queried sites,
[`uniform_mass_replay_public_eq`](Replay.lean) counts the joint replay/public table fiber.
[`uniform_replay_public_good_factor`](Replay.lean) factors an event over the good output
tuples from fixed public values. Both retain the explicit pinned-fiber equivalence and
injectivity of all replay and public sites; neither asserts independence on bad runs.

## References

1. D. Lanzenberger and U. Maurer. Coupling of Random Systems. In *Theory of Cryptography
   (TCC 2020)*, Springer, 2020. Cryptology ePrint Archive, Paper 2020/1187.
2. D. Lanzenberger. *A Theory of Random Systems, Games, and Hardness Amplification*. Doctoral
   thesis, ETH Zurich.
3. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
4. A. Jha. *Provable Security of Symmetric-key Cryptographic Schemes*. Doctoral thesis,
   Indian Statistical Institute, 2020. https://digitalcommons.isical.ac.in/doctoral-theses/456/.

<!-- Declarations -->

[Distribution]: Distribution.lean#L68
[ProbDist]: Distribution.lean#L161
[isProbDist]: Distribution.lean#L140
[mass]: Distribution.lean#L229
[fTransform]: Distribution.lean#L727
[prod]: Distribution.lean#L1101
[pi]: Distribution.lean#L1747
[piDep]: DependentProduct.lean#L53
[uniform]: Distribution.lean#L656
[ProbDist.uniform]: Distribution.lean#L689
[bindK]: Kernel.lean#L51
[bindK_bindK]: Kernel.lean#L97
[bindK_single_comp]: Kernel.lean#L119
[pi_eq_bindK_update]: Kernel.lean#L346
[ProbDist.map]: Kernel.lean#L362
[ProbDist.map_map]: Kernel.lean#L375
[prodProbDist_map]: Kernel.lean#L497
[ProbDist.bind]: Kernel.lean#L406
[ProbDist.bind_const]: Kernel.lean#L420
[ProbDist.jointLaw]: Kernel.lean#L438
[ProbDist.jointLaw_fst]: Kernel.lean#L445
[ProbDist.jointLaw_map]: Kernel.lean#L465
[normalizeOr]: Lift.lean#L189
[statDist]: StatisticalDistance.lean#L99
[statDist_triangle]: StatisticalDistance.lean#L249
[statDist_fTransform_le]: StatisticalDistance.lean#L638
[statDist_fTransform_le_expect_of_ratio]: StatisticalDistance.lean#L678
[statDist_eq_weight_posPart]: Lift.lean#L108
[statDist_eq_weight_sub_weight_inf]: Lift.lean#L265
[IsCoupling]: Coupling.lean#L50
[statDist_le_offDiagonalMass]: Coupling.lean#L245
[exists_coupling_offDiagonalMass_eq]: Coupling.lean#L324
[supAgreement]: MultiCoupling.lean#L91
[supAgreement_eq_weight_overlapDist]: MultiCoupling.lean#L401
[expect]: Expectation.lean#L48
[expect_add_left]: Expectation.lean#L70
[expect_add_right]: Expectation.lean#L100
[mass_ge_le_expect_div]: Expectation.lean#L203
[expect_mul_sq_le_sq_mul_sq]: Expectation.lean#L219
[ConvexOn.map_expect_le]: Expectation.lean#L301
[card_function_fiber_finset]: Counting.lean#L66
[uniform_mass_transcript_eq]: Counting.lean#L483
[fTransform_eval_uniform_eq_of_same_fibers]: Counting.lean#L539
[uniform_mass_adaptive_eval_eq_mul]: Counting.lean#L611

[uniform_mass_fresh_eval_eq]: Counting.lean#L217
[mass_exists_pair_le_choose]: Distribution.lean#L528
[uniform_mass_not_injOn_le_choose]: Counting.lean#L331

[uniform_mass_fresh_projected_eval_eq]: Counting.lean#L356
[uniform_mass_transcript_projected_collision_le]: Counting.lean#L406

[uniform_mass_disjoint_events]: Counting.lean#L685
[uniform_mass_fresh_outputs_eq]: Counting.lean#L729

[uniform_mass_transcript_collision_le_card]: Counting/Collision.lean

[ProbDist.map_id]: Kernel.lean#L371
[prodProbDist_uniform]: Kernel.lean#L507
[prodProbDist_map_left]: Kernel.lean#L514
[prodProbDist_map_right]: Kernel.lean#L521
