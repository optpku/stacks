/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Thickening.Over

/-- Postcomposition along `g : X ⟶ Y` rebases a thickening over `X` to a thickening over
`Y`, without changing its underlying thickening of schemes. -/
def map {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Thickening.Over X ⥤ Thickening.Over Y :=
  MorphismProperty.Comma.lift
    (MorphismProperty.Arrow.forget
        (MorphismProperty.inverseImage (@IsThickening)
          (CategoryTheory.Over.forget X)) ⊤ ⊤ ⋙
      (CategoryTheory.Over.map g).mapArrow)
    (fun T ↦ T.prop) (fun f ↦ f.prop_hom_left) (fun f ↦ f.prop_hom_right)

/-- The closed-part object of a rebased thickening is obtained by postcomposition. -/
theorem map_obj_left {X Y : Scheme.{u}} (g : X ⟶ Y) (T : Thickening.Over X) :
    ((map g).obj T).left = (CategoryTheory.Over.map g).obj T.left := sorry

/-- The ambient object of a rebased thickening is obtained by postcomposition. -/
theorem map_obj_right {X Y : Scheme.{u}} (g : X ⟶ Y) (T : Thickening.Over X) :
    ((map g).obj T).right = (CategoryTheory.Over.map g).obj T.right := sorry

/-- The defining arrow of a rebased thickening is the postcomposition image of the original
defining arrow. -/
theorem map_obj_hom {X Y : Scheme.{u}} (g : X ⟶ Y) (T : Thickening.Over X) :
    ((map g).obj T).hom = (CategoryTheory.Over.map g).map T.hom := sorry

/-- Rebasing preserves the first-order property of the underlying thickening. -/
instance instIsFirstOrderThickeningMapObj {X Y : Scheme.{u}} (g : X ⟶ Y)
    (T : Thickening.Over X)
    [IsFirstOrderThickening ((CategoryTheory.Over.forget X).map T.hom)] :
    IsFirstOrderThickening
      ((CategoryTheory.Over.forget Y).map ((map g).obj T).hom) := sorry

end AlgebraicGeometry.Thickening.Over
