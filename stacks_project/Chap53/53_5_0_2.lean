/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree.ChernClass

universe u

open AlgebraicGeometry TopologicalSpace

/- 53.5.0.2: The degree of `E` equals the degree of `c₁(E) ∩ [X]₁`. -/
@[stacks 0BRY] #check (AlgebraicGeometry.Scheme.Modules.curveDegree_eq_chowDegree_firstChernClassCap :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      (hdim : topologicalKrullDim X.left ≤ 1) (E : X.left.Modules) (n : ℕ)
      [E.IsFiniteLocallyFreeOfRank n],
      Scheme.Modules.curveDegree X.hom hdim E n =
        ChowGroup.degree X (Scheme.Modules.firstChernClassCapFundamental X E))
