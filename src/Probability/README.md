# Probability

This library holds the finitely supported laws on which the random systems are built:
distributions and probability distributions, kernels, the statistical distance, couplings and the
$`n`$-ary maximal coupling, expectation, and the counting behind collision bounds. Citations refer
to the numbered [references](../../THEORY.md#references) of THEORY.md.

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
coordinate outcomes; it is normalized when each coordinate law is normalized. A
[**kernel**][bindK] $`f`$ is a conditional distribution [3, §3.6.1]; mixed over a law $`\mu`$
it gives $`\sum_a \mu(a)\, f(a)`$:
[mixtures compose][bindK_bindK], a pushforward
[is the point kernel of its function][bindK_single_comp], and an independent product
[disintegrates][pi_eq_bindK_update] at a coordinate. Probability laws have
[pushforwards][ProbDist.map] and [sequential compositions][ProbDist.bind].
The notation `𝒰[A]` denotes the [normalized uniform law][ProbDist.uniform] of type
`Distribution.ProbDist A`; `Distribution.uniform A` is its underlying raw distribution.

## Statistical distance

The [**statistical distance**][statDist]
satisfies the [triangle inequality][statDist_triangle] and [data processing][statDist_fTransform_le],
$`\delta(fX, fY) \le \delta(X, Y)`$; with [positive parts][statDist_eq_weight_posPart] it is
$`\delta(X, Y) = \lvert (X - Y)^{+} \rvert`$, and with [overlaps][statDist_eq_weight_sub_weight_inf]
$`\delta(X, Y) = \lvert X \rvert - \lvert X \wedge Y \rvert`$.

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
same output law, even when their table domains have different sizes.
If fresh coordinates are chosen from previously observed values, their
[joint mass][uniform_mass_adaptive_eval_eq_mul] still contributes one independent uniform
factor per chosen coordinate, provided the combined coordinate family is injective on the
stated good event.

<!-- Declarations -->

[Distribution]: Distribution.lean#L56
[ProbDist]: Distribution.lean#L149
[isProbDist]: Distribution.lean#L128
[mass]: Distribution.lean#L217
[fTransform]: Distribution.lean#L632
[prod]: Distribution.lean#L1005
[pi]: Distribution.lean#L1646
[piDep]: DependentProduct.lean#L29
[uniform]: Distribution.lean#L566
[ProbDist.uniform]: Distribution.lean#L599
[bindK]: Kernel.lean#L49
[bindK_bindK]: Kernel.lean#L95
[bindK_single_comp]: Kernel.lean#L117
[pi_eq_bindK_update]: Kernel.lean#L283
[ProbDist.map]: Kernel.lean#L329
[ProbDist.bind]: Kernel.lean#L341
[statDist]: StatisticalDistance.lean#L88
[statDist_triangle]: StatisticalDistance.lean#L243
[statDist_fTransform_le]: StatisticalDistance.lean#L615
[statDist_eq_weight_posPart]: Lift.lean#L89
[statDist_eq_weight_sub_weight_inf]: Lift.lean#L170
[IsCoupling]: Coupling.lean#L46
[statDist_le_offDiagonalMass]: Coupling.lean#L241
[exists_coupling_offDiagonalMass_eq]: Coupling.lean#L320
[supAgreement]: MultiCoupling.lean#L87
[supAgreement_eq_weight_overlapDist]: MultiCoupling.lean#L397
[expect]: Expectation.lean#L44
[expect_add_left]: Expectation.lean#L66
[expect_add_right]: Expectation.lean#L96
[mass_ge_le_expect_div]: Expectation.lean#L199
[expect_mul_sq_le_sq_mul_sq]: Expectation.lean#L215
[ConvexOn.map_expect_le]: Expectation.lean#L297
[card_function_fiber_finset]: Counting.lean#L47
[uniform_mass_transcript_eq]: Counting.lean#L194
[fTransform_eval_uniform_eq_of_same_fibers]: Counting.lean#L222
[uniform_mass_adaptive_eval_eq_mul]: Counting.lean#L266
