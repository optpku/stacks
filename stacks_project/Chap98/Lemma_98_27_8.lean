/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.ClosedImmersion
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization

universe u

/- Lemma 98.27.8: Closed immersions on the complementary open and formal
completion yield a contraction solution whose target is closed in the base. -/
@[stacks 0GHE] #check
  (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.exists_solutionFor_of_closedImmersions :
    ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
      (σ : ContractionSituation S) (Z : Closeds S)
      (h_inv : σ.T' =
        (AlgebraicGeometry.FormalAlgebraicSpace.pointsCloseds (Over.mk (𝟙 S)) Z).preimage
          (Points.continuous_map (toBase σ.X')))
      [IsClosedImmersion
        (openComplementAlong.map (toBase σ.X')
          (AlgebraicGeometry.FormalAlgebraicSpace.pointsCloseds (Over.mk (𝟙 S)) Z))]
      (w : σ.W ⟶ completionAlong (ofOver (Over.mk (𝟙 S)))
        (AlgebraicGeometry.FormalAlgebraicSpace.pointsCloseds (Over.mk (𝟙 S)) Z))
      [FormalAlgebraicSpace.ClosedImmersion w],
      ∃ (X : AlgebraicSpace S) (_ : LocallyOfFiniteType (toBase X)),
        Nonempty (ContractionSituation.SolutionFor σ X) ∧ IsClosedImmersion (toBase X))
