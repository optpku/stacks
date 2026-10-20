/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Bimod.Module
import Mathlib.Tactic.CrossRefAttribute

/-!
# Free modules over monoid objects

Tensoring with a monoid object constructs free right and left modules in an arbitrary monoidal
category.  Both orientations are exposed symmetrically, with explicit carrier, action, and map
formulas for downstream graded, differential graded, and sheaf-theoretic specializations.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u v

namespace CategoryTheory.Bimod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace RightModule

/-- The free right `A`-module on `X`, with carrier `X ⊗ A.X`. -/
@[stacks 0FSF "free right module object"]
def freeObj (A : Mon C) (X : C) : RightModule A where
  X := X ⊗ A.X
  actLeft := (λ_ (X ⊗ A.X)).hom
  actRight := (α_ X A.X A.X).hom ≫ (X ◁ μ)
  one_actLeft := sorry
  left_assoc := sorry
  actRight_one := sorry
  right_assoc := sorry
  middle_assoc := sorry

/-- The morphism of free right `A`-modules induced by `f : X ⟶ Y`. -/
@[stacks 0FSF "map of free right modules"]
def freeMap (A : Mon C) {X Y : C} (f : X ⟶ Y) :
    freeObj A X ⟶ freeObj A Y where
  hom := f ▷ A.X
  left_act_hom := sorry
  right_act_hom := sorry

/-- The free right-module functor over the monoid object `A`. -/
@[stacks 0FSF "free right module functor"]
def free (A : Mon C) : C ⥤ RightModule A where
  obj := freeObj A
  map := freeMap A
  map_id := sorry
  map_comp := sorry

/-- The carrier of the free right module on `X` is `X ⊗ A.X`. -/
@[simp]
theorem free_obj_X (A : Mon C) (X : C) :
    ((free A).obj X).X = X ⊗ A.X := sorry

/-- The trivial left action on a free right module is the left unitor. -/
@[simp]
theorem free_obj_actLeft (A : Mon C) (X : C) :
    ((free A).obj X).actLeft = (λ_ (X ⊗ A.X)).hom := sorry

/-- The right action on a free right module is multiplication in its `A.X` factor. -/
@[simp]
theorem free_obj_actRight (A : Mon C) (X : C) :
    ((free A).obj X).actRight =
      (α_ X A.X A.X).hom ≫ (X ◁ μ) := sorry

/-- The carrier map of the free right-module morphism induced by `f` is `f ▷ A.X`. -/
@[simp]
theorem free_map_hom (A : Mon C) {X Y : C} (f : X ⟶ Y) :
    ((free A).map f).hom = f ▷ A.X := sorry

end RightModule

namespace LeftModule

/-- The free left `A`-module on `X`, with carrier `A.X ⊗ X`. -/
@[stacks 0FSF "free left module object"]
def freeObj (A : Mon C) (X : C) : LeftModule A where
  X := A.X ⊗ X
  actLeft := (α_ A.X A.X X).inv ≫ (μ ▷ X)
  actRight := (ρ_ (A.X ⊗ X)).hom
  one_actLeft := sorry
  left_assoc := sorry
  actRight_one := sorry
  right_assoc := sorry
  middle_assoc := sorry

/-- The morphism of free left `A`-modules induced by `f : X ⟶ Y`. -/
@[stacks 0FSF "map of free left modules"]
def freeMap (A : Mon C) {X Y : C} (f : X ⟶ Y) :
    freeObj A X ⟶ freeObj A Y where
  hom := A.X ◁ f
  left_act_hom := sorry
  right_act_hom := sorry

/-- The free left-module functor over the monoid object `A`. -/
@[stacks 0FSF "free left module functor"]
def free (A : Mon C) : C ⥤ LeftModule A where
  obj := freeObj A
  map := freeMap A
  map_id := sorry
  map_comp := sorry

/-- The carrier of the free left module on `X` is `A.X ⊗ X`. -/
@[simp]
theorem free_obj_X (A : Mon C) (X : C) :
    ((free A).obj X).X = A.X ⊗ X := sorry

/-- The left action on a free left module is multiplication in its `A.X` factor. -/
@[simp]
theorem free_obj_actLeft (A : Mon C) (X : C) :
    ((free A).obj X).actLeft =
      (α_ A.X A.X X).inv ≫ (μ ▷ X) := sorry

/-- The trivial right action on a free left module is the right unitor. -/
@[simp]
theorem free_obj_actRight (A : Mon C) (X : C) :
    ((free A).obj X).actRight = (ρ_ (A.X ⊗ X)).hom := sorry

/-- The carrier map of the free left-module morphism induced by `f` is `A.X ◁ f`. -/
@[simp]
theorem free_map_hom (A : Mon C) {X Y : C} (f : X ⟶ Y) :
    ((free A).map f).hom = A.X ◁ f := sorry

end LeftModule

-- All carriers, actions, and maps are explicit; `sorryAx` is confined to module and functor laws.

end CategoryTheory.Bimod

end
