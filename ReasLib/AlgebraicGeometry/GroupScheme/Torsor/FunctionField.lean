/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctionField
public import ReasLib.AlgebraicGeometry.GroupScheme.Cohomology
public import ReasLib.AlgebraicGeometry.GroupScheme.AlgebraicSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-!
# Function-field restriction for torsors under abelian schemes
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry.GroupScheme

/-- Restriction to the function field is bijective on sections of any fppf torsor
under an abelian scheme over a regular integral Noetherian scheme. -/
theorem sectionsRestrictFunctionField_bijective {W : Scheme.{u}}
    [IsIntegral W] [IsNoetherian W] [Scheme.Regular W]
    (G : GroupScheme W) [AbelianScheme G]
    (P : GroupAlgebraicSpace.Action (toGroupAlgebraicSpace G))
    (hP : GroupAlgebraicSpace.IsStandardTorsor (toGroupAlgebraicSpace G) P .fppf) :
    Function.Bijective (AlgebraicSpace.sectionsRestrictFunctionField P.X) :=
  sorry

/-- Restriction of first fppf cohomology to the function field is injective for
an abelian scheme over a regular integral Noetherian scheme. -/
theorem fppfH1RestrictFunctionField_injective_regular {W : Scheme.{u}}
    [IsIntegral W] [IsNoetherian W] [Scheme.Regular W]
    (G : GroupScheme W) [AbelianScheme G]
    [HasSheafify (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left)
        AddCommGrpCat.{u})] :
    Function.Injective (fppfH1RestrictFunctionField G).hom :=
  sorry

/-- Restriction to the function field is bijective on sections of any fppf torsor
under an abelian scheme over an integral Noetherian scheme whose smooth schemes
have factorial local rings. -/
theorem sectionsRestrictFunctionField_bijective_of_smoothLocallyFactorial
    {W : Scheme.{u}} [IsIntegral W] [IsNoetherian W]
    (h_smoothLocallyFactorial :
      ∀ {X : Scheme.{u}} (f : X ⟶ W) [Smooth f] (x : X),
        UniqueFactorizationMonoid (X.presheaf.stalk x))
    (G : GroupScheme W) [AbelianScheme G]
    (P : GroupAlgebraicSpace.Action (toGroupAlgebraicSpace G))
    (hP : GroupAlgebraicSpace.IsStandardTorsor (toGroupAlgebraicSpace G) P .fppf) :
    Function.Bijective (AlgebraicSpace.sectionsRestrictFunctionField P.X) :=
  sorry

/-- Restriction of first fppf cohomology to the function field is injective for
an abelian scheme over an integral Noetherian scheme whose smooth schemes have
factorial local rings. -/
theorem fppfH1RestrictFunctionField_injective_of_smoothLocallyFactorial
    {W : Scheme.{u}} [IsIntegral W] [IsNoetherian W]
    (h_smoothLocallyFactorial :
      ∀ {X : Scheme.{u}} (f : X ⟶ W) [Smooth f] (x : X),
        UniqueFactorizationMonoid (X.presheaf.stalk x))
    (G : GroupScheme W) [AbelianScheme G]
    [HasSheafify (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left)
        AddCommGrpCat.{u})] :
    Function.Injective (fppfH1RestrictFunctionField G).hom :=
  sorry

end AlgebraicGeometry.GroupScheme
