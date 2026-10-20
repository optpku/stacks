/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.PresheafModule

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

universe u z

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)

/- Inverse image of module presheaves by precomposition and canonical restriction of scalars. -/
#check (AlgebraicGeometry.GroupoidsOver.presheafModuleInverseImage f :
  PresheafOfModules.{z} (structureSheaf Y).obj ⥤
    PresheafOfModules.{z} (structureSheaf X).obj)
