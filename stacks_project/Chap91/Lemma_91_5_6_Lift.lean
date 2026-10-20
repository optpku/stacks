/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatLift

/-!
# Flat lifts of modules along a morphism of first-order thickenings

The shared flat lift API records a module flat over the thickened base and its
specified reduction isomorphism. The identity infinitesimal comparison and the
associated extension are available from the same owner.
-/

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open scoped AlgebraicGeometry

universe u

#check (AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift :
  {T U : Thickening.{u}} → [IsFirstOrderThickening T.hom] →
    [IsFirstOrderThickening U.hom] → (g : T ⟶ U) → (F : T.left.Modules) → Type (u + 1))

#check (AlgebraicGeometry.RingedSpace.Modules.infMapId :
  ∀ {X X' : AlgebraicGeometry.RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i] (F : X.Modules),
    kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj (idealModule i ⊗ F))
