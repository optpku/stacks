/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.SectionTensor
public import ReasLib.CategoryTheory.Monoidal.Invertible.Duality

/-! # Pullback of tensor inverse objects -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.isInvertibleObject CategoryTheory.ExactPairing

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.PullbackTensor

variable {S : Scheme.{u}}

/-- The image pairing of an invertible module under algebraic-space module pullback. -/
@[implicit_reducible]
def imagePairing {Y Z : AlgebraicSpace S} (h : Y ⟶ Z)
    (L : Z.Modules) [isInvertibleObject L] :
    ExactPairing ((Modules.pullback h).obj L)
      ((Modules.pullback h).obj (inverse L)) where
  coevaluation' :=
    (unitIso h).inv ≫
      (Modules.pullback h).map (exactPairing L).coevaluation' ≫
        RelativeProj.pullbackTensorOplax h L (inverse L)
  evaluation' :=
    RelativeProj.pullbackTensorLax h (inverse L) L ≫
      (Modules.pullback h).map (exactPairing L).evaluation' ≫
        (unitIso h).hom
  coevaluation_evaluation' := sorry
  evaluation_coevaluation' := sorry

/-- Pullback of a chosen tensor inverse compared with the chosen inverse of the pullback. -/
def inverseComparison {Y Z : AlgebraicSpace S} (h : Y ⟶ Z)
    (L : Z.Modules) [isInvertibleObject L]
    [isInvertibleObject ((Modules.pullback h).obj L)] :
    (Modules.pullback h).obj (inverse L) ⟶ inverse ((Modules.pullback h).obj L) :=
  (rightDualIso (imagePairing h L)
      (exactPairing ((Modules.pullback h).obj L))).hom

end AlgebraicGeometry.AlgebraicSpace.Modules.PullbackTensor
