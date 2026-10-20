/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage

/-! # Open complement and support compatibility checks -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory.Limits

universe u

variable {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]

#check (AlgebraicGeometry.AlgebraicSpace.closedImmersionComplement i : AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.mem_closedImmersionComplementSubfunctor_obj i :
  ∀ {U : (Over S)ᵒᵖ} (α : X.functorOfPoints.obj U),
    α ∈ (closedImmersionComplementSubfunctor i).obj U ↔ missesClosedImage i α)

#check (AlgebraicGeometry.AlgebraicSpace.closedImmersionComplement_spec i :
  (closedImmersionComplement i).functorOfPoints =
      (closedImmersionComplementSubfunctor i).toFunctor ∧
    closedImmersionComplementι i = (closedImmersionComplementSubfunctor i).ι ∧
    IsOpenImmersion (closedImmersionComplementι i) ∧
    pointsImage (closedImmersionComplementι i) = (pointsImage i)ᶜ)

#check (AlgebraicGeometry.AlgebraicSpace.restrictsToTerminalOnComplement_iff i :
  ∀ F : Sheaf (smallEtaleTopology X) (Type (u + 1)),
    restrictsToTerminalOnComplement i F ↔
      Nonempty (IsTerminal
        ((etaleRestrictionSheaf (closedImmersionComplementι i) (Type (u + 1))).obj F)))

#check (AlgebraicGeometry.AlgebraicSpace.supportSubsetImage_iff i :
  ∀ [∀ (xbar : GeometricPoint X) (G : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (etaleBaseChange xbar.hom).op.HasLeftKanExtension G]
    [∀ xbar : GeometricPoint X,
      HasWeakSheafify (spacesEtaleTopology (ofOver xbar.toFieldValuedPoint.overObj))
        AddCommGrpCat.{u + 1}]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}),
    supportSubsetImage i F ↔
      ∀ xbar : GeometricPoint X,
        ¬ IsZero
            (((sheafInverseImage AddCommGrpCat.{u + 1} xbar.hom).obj F).obj.obj
              (Opposite.op xbar.toFieldValuedPoint.sourceObj)) →
          xbar.image ∈ pointsImage i)
