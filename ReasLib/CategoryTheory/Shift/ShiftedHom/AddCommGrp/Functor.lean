/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Shift.ShiftedHom.AddCommGrp
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functorial shifted Hom groups

This leaf packages the additive shifted Hom construction in its two categorical variables.  The
source variable is presented on the opposite category, so the resulting bifunctor has ordinary
covariant map direction in both slots.  The definitions are independent of derived categories;
derived `Ext` APIs should use these owners instead of rebuilding the same functors locally.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.ShiftedHom.AddCommGrp

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]

/-- The shifted Hom group is covariant in its target variable. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
def targetFunctor (X : C) (n : ℤ) : C ⥤ AddCommGrpCat.{v} where
  obj Y := ShiftedHom.addCommGrp X Y n
  map f := ShiftedHom.postcomp X f n
  map_id := by sorry
  map_comp := by sorry

/-- Evaluation of the target-variable shifted Hom functor on objects. -/
@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem targetFunctor_obj (X Y : C) (n : ℤ) :
    (targetFunctor X n).obj Y = ShiftedHom.addCommGrp X Y n := rfl

/-- Evaluation of the target-variable shifted Hom functor on morphisms. -/
@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem targetFunctor_map {X Y Z : C} (n : ℤ) (f : Y ⟶ Z) :
    (targetFunctor X n).map f = ShiftedHom.postcomp X f n := rfl

/-- Identity computation for target-variable shifted Hom groups. -/
@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem targetFunctor_map_id (X Y : C) (n : ℤ) :
    ShiftedHom.postcomp X (𝟙 Y) n = 𝟙 (ShiftedHom.addCommGrp X Y n) := sorry

/-- Composition computation for target-variable shifted Hom groups. -/
@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem targetFunctor_map_comp {X Y Z W : C} (n : ℤ) (f : Y ⟶ Z) (g : Z ⟶ W) :
    ShiftedHom.postcomp X (f ≫ g) n =
      ShiftedHom.postcomp X f n ≫ ShiftedHom.postcomp X g n := sorry

/-- The shifted Hom group is contravariant in its source variable. -/
@[stacks 0G1X, stacks 0G1Z]
def sourceFunctor (Y : C) (n : ℤ) : Cᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj X := ShiftedHom.addCommGrp X.unop Y n
  map f := ShiftedHom.precomp f.unop Y n
  map_id := by sorry
  map_comp := by sorry

/-- Evaluation of the source-variable shifted Hom functor on objects. -/
@[simp, stacks 0G1X, stacks 0G1Z]
theorem sourceFunctor_obj (Y : C) (n : ℤ) (X : Cᵒᵖ) :
    (sourceFunctor Y n).obj X = ShiftedHom.addCommGrp X.unop Y n := rfl

/-- Evaluation of the source-variable shifted Hom functor on morphisms. -/
@[simp, stacks 0G1X, stacks 0G1Z]
theorem sourceFunctor_map (Y : C) (n : ℤ) {X X' : Cᵒᵖ} (f : X ⟶ X') :
    (sourceFunctor Y n).map f = ShiftedHom.precomp f.unop Y n := rfl

/-- Identity computation for source-variable shifted Hom groups. -/
@[simp, stacks 0G1X, stacks 0G1Z]
theorem sourceFunctor_map_id (X Y : C) (n : ℤ) :
    ShiftedHom.precomp (𝟙 X) Y n = 𝟙 (ShiftedHom.addCommGrp X Y n) := sorry

/-- Composition computation for source-variable shifted Hom groups. -/
@[simp, stacks 0G1X, stacks 0G1Z]
theorem sourceFunctor_map_comp {X Y Z : C} (n : ℤ) (f : X ⟶ Y) (g : Y ⟶ Z) :
    ShiftedHom.precomp (f ≫ g) Z n =
      ShiftedHom.precomp g Z n ≫ ShiftedHom.precomp f Z n := sorry

/-- The shifted Hom bifunctor, with the source variable placed in the opposite category. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
def bifunctor (n : ℤ) : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{v} where
  obj X := targetFunctor X.unop n
  map f := {
    app := fun Y => ShiftedHom.precomp f.unop Y n
    naturality := by intro Y Z g; sorry }
  map_id := by
    intro X
    apply NatTrans.ext
    funext Y
    sorry
  map_comp := by
    intro X X' X'' f g
    apply NatTrans.ext
    funext Y
    sorry

/-- Object computation for the shifted Hom bifunctor. -/
@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem bifunctor_obj (n : ℤ) (X : Cᵒᵖ) :
    (bifunctor n).obj X = targetFunctor X.unop n := rfl

/-- Morphism computation for the shifted Hom bifunctor at a target object. -/
@[simp, stacks 0G1X, stacks 0G1Z]
theorem bifunctor_map_app (n : ℤ) {X X' : Cᵒᵖ} (f : X ⟶ X') (Y : C) :
    ((bifunctor n).map f).app Y = ShiftedHom.precomp f.unop Y n := rfl

/-- Evaluation of both variables of the shifted Hom bifunctor. -/
@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem bifunctor_obj_obj (n : ℤ) (X : Cᵒᵖ) (Y : C) :
    ((bifunctor n).obj X).obj Y = ShiftedHom.addCommGrp X.unop Y n := rfl

/-- The source action of the bifunctor is the canonical source-variable functor. -/
@[simp, stacks 0G1X, stacks 0G1Z]
theorem bifunctor_map_app_source (n : ℤ) {X X' : Cᵒᵖ} (f : X ⟶ X') (Y : C) :
    ((bifunctor n).map f).app Y = (sourceFunctor Y n).map f := rfl

/-- Mixed naturality of shifted Hom in its source and target variables. -/
@[reassoc, stacks 0G1X, stacks 0G1Z]
theorem bifunctor_map_naturality (n : ℤ) {X X' : Cᵒᵖ} (f : X ⟶ X')
    {Y Z : C} (g : Y ⟶ Z) :
    ((bifunctor n).map f).app Y ≫ (targetFunctor X'.unop n).map g =
      (targetFunctor X.unop n).map g ≫ ((bifunctor n).map f).app Z := sorry

/-- The elementary mixed square for precomposition and postcomposition. -/
@[reassoc, stacks 0G1X, stacks 0G1Z]
theorem precomp_postcomp {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℤ) :
    ShiftedHom.precomp f Y n ≫ ShiftedHom.postcomp X g n =
      ShiftedHom.postcomp X' g n ≫ ShiftedHom.precomp f Y' n := sorry

end CategoryTheory.ShiftedHom.AddCommGrp

end
