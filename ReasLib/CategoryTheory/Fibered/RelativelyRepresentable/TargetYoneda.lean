/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange

/-!
# Target-Hom functors of 1-morphisms of groupoid fibrations

A 1-morphism `F : X ⟶ Y` of categories fibred in groupoids determines, for each
object `y` of `Y`, the functor on the opposite total category of `X` sending `x`
to the type of morphisms `(toFunctor F).obj x ⟶ y`. Relative representability of
`F` is equivalent to representability of every such functor.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Opposite
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids

variable {X Y : Groupoids C}

/-- The functor `X.totalᵒᵖ ⥤ Type vS` sending `x` to the type of morphisms
`(toFunctor F).obj x ⟶ y` in the total category of `Y`. -/
abbrev targetYoneda (F : X ⟶ Y) (y : Y.total) : X.totalᵒᵖ ⥤ Type vS :=
  (toFunctor F).op ⋙ yoneda.obj y

/-- Evaluating `targetYoneda F y` at `op x` recovers the hom-type
`(toFunctor F).obj x ⟶ y`. -/
theorem targetYoneda_obj (F : X ⟶ Y) (y : Y.total) (x : X.total) :
    (targetYoneda F y).obj (op x) = ((toFunctor F).obj x ⟶ y) :=
  rfl

/-- A 1-morphism has representable target-Hom functors when for every object of
the target total category, the associated `targetYoneda` functor is representable. -/
def targetYoneda.representable (F : X ⟶ Y) : Prop :=
  ∀ y : Y.total, (targetYoneda F y).IsRepresentable

/-- The target-Hom representability predicate holds exactly when the target-Hom
presheaf is representable for every object of the target total category. -/
theorem targetYoneda.representable_iff (F : X ⟶ Y) :
    targetYoneda.representable F ↔
      ∀ y : Y.total, (targetYoneda F y).IsRepresentable :=
  Iff.rfl

/-- A 1-morphism of categories fibred in groupoids is relatively representable if
and only if every target-Hom functor `targetYoneda F y` is representable. -/
theorem relativelyRepresentable.iff_targetYoneda (F : X ⟶ Y) :
    relativelyRepresentable F ↔ targetYoneda.representable F :=
  sorry

/-- Relative representability implies representability of every target-Hom functor. -/
theorem relativelyRepresentable.targetYoneda {F : X ⟶ Y}
    (hF : relativelyRepresentable F) : targetYoneda.representable F :=
  (relativelyRepresentable.iff_targetYoneda F).mp hF

/-- Representability of every target-Hom functor implies relative representability. -/
theorem relativelyRepresentable.of_targetYoneda {F : X ⟶ Y}
    (hF : targetYoneda.representable F) : relativelyRepresentable F :=
  (relativelyRepresentable.iff_targetYoneda F).mpr hF

end FiberedCategoryOver.Groupoids

end CategoryTheory
