/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.LimitPreserving
import StacksCheckRecall

universe u

/- Lemma 98.27.11: In Situation 98.27.1 the functor F is limit preserving:
for any directed limit V = lim V_λ of Noetherian affine schemes over S we have
F(V) = colim F(V_λ). -/
@[stacks 0GI5] #check
  (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.preservesDirectedAffineLimits :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
      (σ : AlgebraicGeometry.AlgebraicSpace.ContractionSituation S),
      AlgebraicGeometry.Scheme.Over.Extension.PreservesDirectedAffineLimits
        (AlgebraicGeometry.Scheme.Over.locallyNoetherian S) σ.functor)
