/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.StructureMorphism

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupScheme
open scoped Bicategory

universe u

/- The structure morphism of the Picard stack forgets the invertible module. -/
#check (AlgebraicGeometry.AlgebraicSpace.Picard.toBase :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
    ((picardStack f).toGroupoids :
      FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)) ⟶
        Classifying.toGroupoids B)
