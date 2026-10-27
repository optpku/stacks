/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.Differentials

/-!
# Pullback of differentials along a universal first-order thickening

The canonical comparison and its isomorphism property are provided by the
universal-first-order-thickening differentials owner.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

noncomputable section

universe u

variable {S : Scheme.{u}} {B X Z Z' : AlgebraicSpace S}
variable (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
variable [IsUniversalFirstOrder i h'] [FormallyUnramified h]
variable (w : i ≫ h' = h)

#check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.pullbackDifferentialsComparison
    i h' h f w :
    (Modules.pullback h).obj (relativeDifferentials f) ⟶
      (Modules.pullback i).obj (relativeDifferentials (h' ≫ f)))

#check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.pullbackDifferentialsComparison_isIso
    i h' h f w :
    IsIso (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.pullbackDifferentialsComparison
      i h' h f w))

