/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.DualNumberCounterexample

universe u

open CategoryTheory

/- Remark 31.21.10: for a field `k`, the quotient chain
`Spec(k[x]/(x)) ⟶ Spec(k[x]/(x)²) ⟶ Spec(k[x])` has regular composite and second
morphism near every source point, while its two factors are not both regular there. -/
@[stacks 0691] #check
  (AlgebraicGeometry.DualNumberRegularImmersionCounterexample.regularImmersionNear_factors_not_iff_composite_and_second :
    ∀ (k : Type u) [Field k]
      (z : AlgebraicGeometry.DualNumberRegularImmersionCounterexample.closedPoint k),
      ¬ ((AlgebraicGeometry.IsRegularImmersionNear
              (AlgebraicGeometry.DualNumberRegularImmersionCounterexample.closedPointEmbedding k) z ∧
            AlgebraicGeometry.IsRegularImmersionNear
              (AlgebraicGeometry.DualNumberRegularImmersionCounterexample.doublePointEmbedding k)
              ((AlgebraicGeometry.DualNumberRegularImmersionCounterexample.closedPointEmbedding k).base z)) ↔
          (AlgebraicGeometry.IsRegularImmersionNear
              (AlgebraicGeometry.DualNumberRegularImmersionCounterexample.closedPointEmbedding k ≫
                AlgebraicGeometry.DualNumberRegularImmersionCounterexample.doublePointEmbedding k) z ∧
            AlgebraicGeometry.IsRegularImmersionNear
              (AlgebraicGeometry.DualNumberRegularImmersionCounterexample.doublePointEmbedding k)
              ((AlgebraicGeometry.DualNumberRegularImmersionCounterexample.closedPointEmbedding k).base z))))
