/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeIsom.Construction
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Restriction

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Definition 101.5.3 (2): the relative isomorphism sheaf associated
to `α : x1 ≫ f ≅ x2 ≫ f` is `(Z ×_X Z) ×_{Z ×_Y Z, Δ^α} Z`. -/
#check (AlgebraicGeometry.AlgebraicStack.RelativeIsom.relativeIsom :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f), GroupoidsOver S)
