/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Affine

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.GroupoidsOver.affineInclusion :
  ∀ {S : Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S),
    AlgebraicGeometry.GroupoidsOver.Affine X ⥤ X.total)
