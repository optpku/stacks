/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.NumberTheory.Transcendental.LindemannWeierstrass
public import ReasLib.FieldTheory.IntermediateField.Adjoin.Generators
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open IntermediateField
open Cardinal
open IntermediateField.AdjoinPair
open scoped IntermediateField.algebraAdjoinAdjoin

noncomputable section

section

/- Domain-style sampling for Example 9.26.6:
- primary domain: transcendence degree of finitely generated field extensions;
- sampled owner declarations:
  `Algebra.trdeg`,
  `AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic`,
  `IsTranscendenceBasis.cardinalMk_eq_trdeg`,
  `IntermediateField.AdjoinPair.gen₁` / `IntermediateField.AdjoinPair.gen₂`;
- best owner abstraction: the transcendence-degree owner `Algebra.trdeg` of the intermediate field
  `ℚ⟮Real.exp 1, Real.pi⟯`.

Primitive data are the two generators `Real.exp 1` and `Real.pi` and the intermediate field they
generate. The `Fin 2` family in `K` is only bridge/view API into the canonical owner
`IsTranscendenceBasis` and the resulting invariant `Algebra.trdeg`.

Source/core/bridge triage:
- `source-facing`: the concrete field `ℚ(e, π)` and the question whether its transcendence degree
  is `1` or `2`;
- `core/canonical`: `Algebra.trdeg ℚ K`;
- `bridge/view`: the two-generator family in `K`, used only to invoke
  `AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic` and then
  `IsTranscendenceBasis.cardinalMk_eq_trdeg`;
- `layer`: `source-facing`.
-/

-- Local declaration justification (source-local notation): the source example repeatedly names
-- the concrete field `ℚ(e, π)` and does not introduce reusable field-extension vocabulary.
local notation "K" => ℚ⟮Real.exp 1, Real.pi⟯

-- Proof sketch: exhibit a transcendental element of `K` over `ℚ` and then apply the canonical
-- owner lemma `trdeg_pos`, converting `0 < Algebra.trdeg ℚ K` into the equivalent lower bound
-- `1 ≤ Algebra.trdeg ℚ K`.
/-- Example 9.26.6: the field `ℚ(e, π)` has transcendence degree at least `1` over `ℚ`. -/
@[stacks 09I9]
theorem rat_e_pi_field_trdeg_one_le :
    1 ≤ Algebra.trdeg ℚ K := by
  have hπK : Transcendental ℚ (gen₂ ℚ (Real.exp 1) Real.pi) :=
    (AdjoinPair.transcendental_gen₂_iff (F := ℚ) (Real.exp 1) Real.pi).2
      real_pi_transcendental
  exact hπK.one_le_trdeg

-- Proof sketch: transport algebraic independence of `![Real.exp 1, Real.pi]` to the canonical
-- two-generator family in `K`, show that `K` is algebraic over the intermediate field generated
-- by that family, and conclude that this family is a transcendence basis. The equality
-- `Algebra.trdeg ℚ K = 2` is then the canonical basis-cardinality formula
-- `IsTranscendenceBasis.cardinalMk_eq_trdeg`.
/-- If `e` and `π` are algebraically independent over `ℚ`, then `ℚ(e, π)` has transcendence
degree `2` over `ℚ`. -/
theorem rat_e_pi_field_trdeg_eq_two_of_algebraicIndependent
    (h_alg : AlgebraicIndependent ℚ (![Real.exp 1, Real.pi] : Fin 2 → ℝ)) :
    Algebra.trdeg ℚ K = 2 := by
  exact h_alg.trdeg_adjoin_pair_eq_two

/- Stacks Example 9.26.6 also records the meta-mathematical third point: it is currently unknown
whether `e` and `π` are algebraically independent over `ℚ`, so the exact value of
`Algebra.trdeg ℚ ℚ⟮Real.exp 1, Real.pi⟯` remains an open problem. -/

end
