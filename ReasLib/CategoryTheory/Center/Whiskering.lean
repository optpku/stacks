/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Center.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Whiskering the center of a category

Whiskering an endomorphism of the identity functor on either side of an endofunctor defines an
endomorphism of the identity functor on the endofunctor category.  The constructions are bundled
as monoid homomorphisms so that unit and composition laws are available through the standard
`MonoidHom` API.
-/

@[expose] public section

open CategoryTheory

universe uC uD vC vD

namespace CategoryTheory.CatCenter

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- Right-whiskering sends a central endomorphism of `C` to the induced central endomorphism of
the functor category `C ⟶ D`. -/
@[stacks 0G5S "right-whiskering the center of a category"]
def whiskerRight (D : Type uD) [Category.{vD} D] :
    CatCenter C →* CatCenter (C ⥤ D) :=
  (Functor.whiskeringLeft C C D).mapEnd (𝟭 C)

/-- The component of `whiskerRight z` at an endofunctor `F` is the usual right-whiskering of
`z` by `F`. -/
@[simp, stacks 0G5S "component of right-whiskering the category center"]
theorem whiskerRight_app (D : Type uD) [Category.{vD} D]
    (z : CatCenter C) (F : C ⥤ D) :
    (whiskerRight D z).app F = Functor.whiskerRight z F := sorry

/-- Right-whiskering a central endomorphism by the identity functor recovers the original
central endomorphism. -/
@[simp, stacks 0G5S "right-whiskering the category center by the identity"]
theorem whiskerRight_app_id (z : CatCenter C) :
    (whiskerRight C z).app (𝟭 C) = z := sorry

/-- Left-whiskering sends a central endomorphism of `D` to the induced central endomorphism of
the functor category `C ⟶ D`. -/
@[stacks 0G5S "left-whiskering the center of a category"]
def whiskerLeft (C : Type uC) [Category.{vC} C] :
    CatCenter D →* CatCenter (C ⥤ D) :=
  (Functor.whiskeringRight C D D).mapEnd (𝟭 D)

/-- The component of `whiskerLeft z` at an endofunctor `F` is the usual left-whiskering of `z`
by `F`. -/
@[simp, stacks 0G5S "component of left-whiskering the category center"]
theorem whiskerLeft_app (C : Type uC) [Category.{vC} C]
    (z : CatCenter D) (F : C ⥤ D) :
    (whiskerLeft C z).app F = Functor.whiskerLeft F z := sorry

/-- Left-whiskering a central endomorphism by the identity functor recovers the original
central endomorphism. -/
@[simp, stacks 0G5S "left-whiskering the category center by the identity"]
theorem whiskerLeft_app_id (z : CatCenter D) :
    (whiskerLeft D z).app (𝟭 D) = z := sorry

end CategoryTheory.CatCenter
