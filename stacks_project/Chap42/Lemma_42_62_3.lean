/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.Total
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules hiding dual

noncomputable section

universe u

open AlgebraicGeometry.ChowGroup AlgebraicGeometry.SchemeOverField

/- Lemma 42.62.3: a morphism between schemes smooth over a field has a Gysin map,
and its action preserves the intersection product on every clopen dimension component. -/
@[stacks 0FFB] #check
  (AlgebraicGeometry.ChowGroup.hasGysinMap_and_gysin_intersectionProductOfRankLoci :
    ∀ {k : Type u} [Field k] {X Y : SchemeOverField k}
      [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
      (D : ∀ d, GraphSpecializationOfRankLoci (dimensionComponentι X d ≫ f))
      (DX : ∀ d, DiagonalSpecializationOfRankLoci (dimensionComponent X d))
      (DY : DiagonalSpecializationOfRankLoci Y) (alpha beta : Total (fun _ ↦ 0) Y),
      BivariantClass.HasGysinMap f ∧
        gysinMapOfRankLoci f D (Total.intersectionProductOfRankLoci Y DY alpha beta) =
          DimensionCompleted.intersectionProduct X DX (gysinMapOfRankLoci f D alpha)
            (gysinMapOfRankLoci f D beta))
