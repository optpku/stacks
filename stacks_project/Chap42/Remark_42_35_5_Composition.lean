/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Composition

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.BivariantClass.comp :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) {p q : ℤ},
    AlgebraicGeometry.BivariantClass delta f p →
      AlgebraicGeometry.BivariantClass delta g q →
        AlgebraicGeometry.BivariantClass delta (f ≫ g) (p + q))

#check (AlgebraicGeometry.BivariantClass.Nonnegative.comp :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z),
    AlgebraicGeometry.BivariantClass.Nonnegative delta f →
      AlgebraicGeometry.BivariantClass.Nonnegative delta g →
        AlgebraicGeometry.BivariantClass.Nonnegative delta (f ≫ g))
