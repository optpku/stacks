/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctionField
public import ReasLib.AlgebraicGeometry.GroupScheme.Torsor.FunctionField
import StacksCheckRecall

/-!
# Fppf torsor sections and H¹ over regular bases, without a dimension hypothesis
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

/- Remark 110.72.2: restriction of torsor sections and first fppf cohomology
to the function field, for regular bases and for bases whose smooth schemes
have factorial local rings. -/
@[stacks 0H8E] #check (AlgebraicGeometry.GroupScheme.sectionsRestrictFunctionField_bijective :
    ∀ {W : Scheme.{u}}
    [IsIntegral W] [IsNoetherian W] [Scheme.Regular W]
    (G : GroupScheme W) [AlgebraicGeometry.GroupScheme.AbelianScheme G]
    (P : GroupAlgebraicSpace.Action (AlgebraicGeometry.GroupScheme.toGroupAlgebraicSpace G))
    (hP : GroupAlgebraicSpace.IsStandardTorsor (AlgebraicGeometry.GroupScheme.toGroupAlgebraicSpace G) P .fppf),
    Function.Bijective (AlgebraicGeometry.AlgebraicSpace.sectionsRestrictFunctionField P.X))

#check (AlgebraicGeometry.GroupScheme.fppfH1RestrictFunctionField_injective_regular :
    ∀ {W : Scheme.{u}}
    [IsIntegral W] [IsNoetherian W] [Scheme.Regular W]
    (G : GroupScheme W) [AlgebraicGeometry.GroupScheme.AbelianScheme G]
    [HasSheafify (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left)
        AddCommGrpCat.{u})],
    Function.Injective (AlgebraicGeometry.GroupScheme.fppfH1RestrictFunctionField G).hom)

#check (AlgebraicGeometry.GroupScheme.sectionsRestrictFunctionField_bijective_of_smoothLocallyFactorial :
    ∀ {W : Scheme.{u}} [IsIntegral W] [IsNoetherian W]
    (h_smoothLocallyFactorial :
      ∀ {X : Scheme.{u}} (f : X ⟶ W) [Smooth f] (x : X),
        UniqueFactorizationMonoid (X.presheaf.stalk x))
    (G : GroupScheme W) [AlgebraicGeometry.GroupScheme.AbelianScheme G]
    (P : GroupAlgebraicSpace.Action (AlgebraicGeometry.GroupScheme.toGroupAlgebraicSpace G))
    (hP : GroupAlgebraicSpace.IsStandardTorsor (AlgebraicGeometry.GroupScheme.toGroupAlgebraicSpace G) P .fppf),
    Function.Bijective (AlgebraicGeometry.AlgebraicSpace.sectionsRestrictFunctionField P.X))

#check (AlgebraicGeometry.GroupScheme.fppfH1RestrictFunctionField_injective_of_smoothLocallyFactorial :
    ∀ {W : Scheme.{u}} [IsIntegral W] [IsNoetherian W]
    (h_smoothLocallyFactorial :
      ∀ {X : Scheme.{u}} (f : X ⟶ W) [Smooth f] (x : X),
        UniqueFactorizationMonoid (X.presheaf.stalk x))
    (G : GroupScheme W) [AlgebraicGeometry.GroupScheme.AbelianScheme G]
    [HasSheafify (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left)
        AddCommGrpCat.{u})],
    Function.Injective (AlgebraicGeometry.GroupScheme.fppfH1RestrictFunctionField G).hom)

