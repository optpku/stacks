/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Category.Pointed
public import Mathlib.CategoryTheory.ConcreteCategory.Forget

/-!
# Abelian groups as pointed types

An abelian group is pointed by its zero element, compatibly with group homomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AddCommGrpCat

/-- The functor sending an abelian group to its underlying pointed type. -/
def toPointed : _root_.AddCommGrpCat.{u} ⥤ Pointed.{u} where
  obj A := Pointed.of (0 : A)
  map f := ⟨f.hom, map_zero f.hom⟩
  map_id := sorry
  map_comp := sorry

/-- The underlying type of `toPointed.obj A` is the carrier of `A`. -/
theorem toPointed_obj (A : _root_.AddCommGrpCat.{u}) : (toPointed.obj A).X = A := rfl

/-- A homomorphism preserves the distinguished zero element. -/
theorem toPointed_map_point {A B : _root_.AddCommGrpCat.{u}} (f : A ⟶ B) :
    (toPointed.map f).toFun (0 : A) = (0 : B) := map_zero f.hom

/-- The distinguished point of `toPointed.obj A` is zero. -/
theorem toPointed_obj_point (A : _root_.AddCommGrpCat.{u}) :
    (toPointed.obj A).point = (0 : A) := rfl

/-- The underlying function of `toPointed.map f` is `f`. -/
theorem toPointed_map_apply {A B : _root_.AddCommGrpCat.{u}} (f : A ⟶ B) (a : A) :
    (toPointed.map f).toFun a = f.hom a := rfl

/-- The canonical forgetful functor from abelian groups to pointed types. -/
def hasForget₂Pointed : HasForget₂ _root_.AddCommGrpCat Pointed where
  forget₂ := toPointed
  forget_comp := sorry

end AddCommGrpCat

end
