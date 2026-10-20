/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Coproduct

/-! # Coproduct cocones of algebraic spaces -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u v
namespace AlgebraicGeometry.AlgebraicSpace
variable {J : Type v} [Category.{v} J] {S : Scheme.{u}} {B : AlgebraicSpace S}
variable {D : J ⥤ Over B}

/-- The canonical morphism from the coproduct of a diagram to a cocone apex. -/
def coproductToColimit [Small.{u} J] (c : Cocone D) :
    (∐ fun i : J ↦ (D.obj i).left) ⟶ c.pt.left :=
  Sigma.desc fun i ↦ (c.ι.app i).left

/-- The canonical coproduct morphism restricts to each cocone leg. -/
theorem coproductToColimit_ι [Small.{u} J] (c : Cocone D) (i : J) :
    Sigma.ι (fun j : J ↦ (D.obj j).left) i ≫ coproductToColimit c = (c.ι.app i).left :=
  sorry
end AlgebraicGeometry.AlgebraicSpace
