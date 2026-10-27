/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Solution
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.ComplementMap
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.CompletionAlong.Scheme
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- A contraction situation over a locally Noetherian scheme admits a solution
whose structure morphism is a closed immersion if a closed subset of the base
has the prescribed inverse image and the induced morphisms on the open
complement and formal completion are closed immersions. -/
theorem exists_solutionFor_of_closedImmersions
    (σ : ContractionSituation S) (Z : Closeds S)
    (h_inv : σ.T' =
      (AlgebraicGeometry.FormalAlgebraicSpace.pointsCloseds (Over.mk (𝟙 S)) Z).preimage
        (Points.continuous_map (toBase σ.X')))
    [IsClosedImmersion
      (openComplementAlong.map (toBase σ.X')
        (AlgebraicGeometry.FormalAlgebraicSpace.pointsCloseds (Over.mk (𝟙 S)) Z))]
    (w : σ.W ⟶ completionAlong (ofOver (Over.mk (𝟙 S)))
      (AlgebraicGeometry.FormalAlgebraicSpace.pointsCloseds (Over.mk (𝟙 S)) Z))
    [FormalAlgebraicSpace.ClosedImmersion w] :
    ∃ (X : AlgebraicSpace S) (_ : LocallyOfFiniteType (toBase X)),
      Nonempty (SolutionFor σ X) ∧ IsClosedImmersion (toBase X) := sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
