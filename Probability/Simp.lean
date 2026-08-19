/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Probability.SimpAttr
import Probability.Distribution

/-!
# `dist_simp` — Curated Simp Set for Distributions

Tags `Distribution` lemmas with the `@[dist_simp]` attribute.
Use as `simp only [dist_simp]`.

## Included (terms get smaller/simpler)

- Weight: `weight_fTransform`, `weight_prod`, `weight_uniform`,
  `weight_ofFiniteMassFunction`
- Uniform: `uniform_apply`, `prod_uniform`
- Finite mass/support adapters: `ofFiniteMassFunction_apply`,
  `supportProbDist_mass_preimage`, `prodProbDist_val`
- Pushforward events: `mass_fTransform`, `evalPred_fTransform`
- Composition: `fTransform_comp`, `fTransform_bijection_uniform`,
  `fTransform_equiv_uniform`, `fTransform_fst_uniform`, `fTransform_snd_uniform`,
  `fTransform_fst_const_pair`, `fTransform_id`
- Predicate: `evalPred_eq_evalSet`

## Excluded (too expansive — use `rw`)

- `fTransform_apply_eq_sum`, `transcriptDist_apply_eq_sum`
-/

open Probability.Distribution in
attribute [dist_simp]
  evalPred_eq_evalSet
  uniform_apply
  mass_singleton
  ofFiniteMassFunction_apply
  weight_ofFiniteMassFunction
  weight_uniform
  weight_fTransform
  weight_prod
  prodProbDist_val
  prod_uniform
  fTransform_comp
  fTransform_id
  mass_fTransform
  evalPred_fTransform
  mass_preimage_eq_fTransform_apply
  supportProbDist_mass_preimage
  fTransform_bijection_uniform
  fTransform_equiv_uniform
  fTransform_fst_uniform
  fTransform_snd_uniform
  fTransform_map_snd_prod_uniform
  fTransform_map_snd_prod_uniform_pi
  fTransform_eval_snd_prod_uniform
  fTransform_fst_pair_eval_snd_prod_uniform
  fTransform_fst_const_pair
