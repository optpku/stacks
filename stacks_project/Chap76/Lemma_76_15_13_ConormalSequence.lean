/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.ConormalSequence

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} {B X Z Z' : AlgebraicSpace S}
variable (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
variable [IsUniversalFirstOrder i h'] [FormallyUnramified h] (w : i ≫ h' = h)

/- The transported conormal map recovers the derivation-induced map of the
universal first-order thickening. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Differentials.conormalMap_comp_pullbackDifferentialsComparison
      i h' h f w :
    AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Differentials.conormalMap i h' h f w ≫
      IsUniversalFirstOrder.pullbackDifferentialsComparison i h' h f w =
        Hom.Conormal.Differentials.map i (h' ≫ f))
