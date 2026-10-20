/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.Composition.Whiskering

/-!
# Interchange maps for two-sided augmented whiskering

The two orders of horizontally composing maps between precomposed and postcomposed augmentations
define canonical morphisms between the corresponding two-sided whiskerings.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SimplicialObject
open CategoryTheory.Functor

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]

namespace SimplicialObject.Augmented

namespace whisker

namespace interchange

namespace leftRight

/-- The degreewise endpoint using the normalized left point and the right simplicial map. -/
@[stacks 0G5R "left/right horizontal-composite component"]
def app {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : postcompose G ε ⟶ postcompose G' ε)
    (β : precompose F ε ⟶ precompose F' ε)
    (Δ : SimplexCategoryᵒᵖ) :
    (whisker F G ε).left.obj Δ ⟶ (whisker F' G' ε).left.obj Δ :=
  precompose.point β ◫ α.left.app Δ

/-- The left/right degreewise endpoint is natural in the simplex. -/
@[stacks 0G5R "naturality of left/right horizontal composition"]
theorem naturality {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : postcompose G ε ⟶ postcompose G' ε)
    (β : precompose F ε ⟶ precompose F' ε)
    {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') :
    (whisker F G ε).left.map θ ≫ app α β Δ' =
      app α β Δ ≫ (whisker F' G' ε).left.map θ := sorry

/-- The simplicial component of the left/right interchange endpoint. -/
@[stacks 0G5R "left/right horizontal-composite simplicial map"]
def left {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : postcompose G ε ⟶ postcompose G' ε)
    (β : precompose F ε ⟶ precompose F' ε) :
    (whisker F G ε).left ⟶ (whisker F' G' ε).left where
  app := app α β
  naturality := fun {_ _} θ ↦ naturality α β θ

/-- The point component of the left/right interchange endpoint. -/
@[stacks 0G5R "point component of left/right interchange"]
def rightMap {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : postcompose G ε ⟶ postcompose G' ε)
    (β : precompose F ε ⟶ precompose F' ε) :
    (whisker F G ε).right ⟶ (whisker F' G' ε).right :=
  precompose.point β ◫ α.right

/-- The left/right endpoint respects the augmentations. -/
@[stacks 0G5R "augmentation law for left/right interchange"]
theorem w {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : postcompose G ε ⟶ postcompose G' ε)
    (β : precompose F ε ⟶ precompose F' ε) :
    left α β ≫ (whisker F' G' ε).hom =
      (whisker F G ε).hom ≫
        (SimplicialObject.const (A ⥤ B)).map (rightMap α β) := sorry

end leftRight

/-- The complete augmented endpoint using the normalized left point and right simplicial map. -/
@[stacks 0G5R "left/right interchange morphism of augmented simplicial objects"]
def leftRight {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : postcompose G ε ⟶ postcompose G' ε)
    (β : precompose F ε ⟶ precompose F' ε) :
    whisker F G ε ⟶ whisker F' G' ε where
  left := leftRight.left α β
  right := leftRight.rightMap α β
  w := leftRight.w α β

namespace leftRight

/-- The left projection of the left/right interchange morphism is its degreewise endpoint. -/
@[simp, stacks 0G5R "left projection of left/right interchange"]
theorem left_app {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : postcompose G ε ⟶ postcompose G' ε)
    (β : precompose F ε ⟶ precompose F' ε) (Δ : SimplexCategoryᵒᵖ) :
    (interchange.leftRight α β).left.app Δ =
      precompose.point β ◫ α.left.app Δ := sorry

/-- The right projection of the left/right interchange morphism is horizontal composition. -/
@[simp, stacks 0G5R "right projection of left/right interchange"]
theorem right {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : postcompose G ε ⟶ postcompose G' ε)
    (β : precompose F ε ⟶ precompose F' ε) :
    (interchange.leftRight α β).right = precompose.point β ◫ α.right := sorry

/-- The normalized point of the left/right endpoint is the horizontal composite of points. -/
@[simp, stacks 0G5R "normalized point of left/right interchange"]
theorem point {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : postcompose G ε ⟶ postcompose G' ε)
    (β : precompose F ε ⟶ precompose F' ε) :
    whisker.point (interchange.leftRight α β) =
      precompose.point β ◫ postcompose.point α := sorry

end leftRight

namespace rightLeft

/-- The degreewise endpoint using the left simplicial map and normalized right point. -/
@[stacks 0G5R "right/left horizontal-composite component"]
def app {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : postcompose G ε ⟶ postcompose G' ε)
    (β : precompose F ε ⟶ precompose F' ε)
    (Δ : SimplexCategoryᵒᵖ) :
    (whisker F G ε).left.obj Δ ⟶ (whisker F' G' ε).left.obj Δ :=
  (Functor.associator F (X.obj Δ) G).inv ≫
    (β.left.app Δ ◫ postcompose.point α) ≫
    (Functor.associator F' (X.obj Δ) G').hom

/-- The right/left degreewise endpoint is natural in the simplex. -/
@[stacks 0G5R "naturality of right/left horizontal composition"]
theorem naturality {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : postcompose G ε ⟶ postcompose G' ε)
    (β : precompose F ε ⟶ precompose F' ε)
    {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') :
    (whisker F G ε).left.map θ ≫ app α β Δ' =
      app α β Δ ≫ (whisker F' G' ε).left.map θ := sorry

/-- The simplicial component of the right/left interchange endpoint. -/
@[stacks 0G5R "right/left horizontal-composite simplicial map"]
def left {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : postcompose G ε ⟶ postcompose G' ε)
    (β : precompose F ε ⟶ precompose F' ε) :
    (whisker F G ε).left ⟶ (whisker F' G' ε).left where
  app := app α β
  naturality := fun {_ _} θ ↦ naturality α β θ

/-- The point component of the right/left interchange endpoint. -/
@[stacks 0G5R "point component of right/left interchange"]
def rightMap {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : postcompose G ε ⟶ postcompose G' ε)
    (β : precompose F ε ⟶ precompose F' ε) :
    (whisker F G ε).right ⟶ (whisker F' G' ε).right :=
  (Functor.associator F (𝟭 C) G).inv ≫
    (β.right ◫ postcompose.point α) ≫
    (Functor.associator F' (𝟭 C) G').hom

/-- The right/left endpoint respects the augmentations. -/
@[stacks 0G5R "augmentation law for right/left interchange"]
theorem w {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : postcompose G ε ⟶ postcompose G' ε)
    (β : precompose F ε ⟶ precompose F' ε) :
    left α β ≫ (whisker F' G' ε).hom =
      (whisker F G ε).hom ≫
        (SimplicialObject.const (A ⥤ B)).map (rightMap α β) := sorry

end rightLeft

/-- The complete augmented endpoint using the left simplicial map and normalized right point. -/
@[stacks 0G5R "right/left interchange morphism of augmented simplicial objects"]
def rightLeft {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : postcompose G ε ⟶ postcompose G' ε)
    (β : precompose F ε ⟶ precompose F' ε) :
    whisker F G ε ⟶ whisker F' G' ε where
  left := rightLeft.left α β
  right := rightLeft.rightMap α β
  w := rightLeft.w α β

namespace rightLeft

/-- The left projection of the right/left interchange morphism is its degreewise endpoint. -/
@[simp, stacks 0G5R "left projection of right/left interchange"]
theorem left_app {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : postcompose G ε ⟶ postcompose G' ε)
    (β : precompose F ε ⟶ precompose F' ε) (Δ : SimplexCategoryᵒᵖ) :
    (interchange.rightLeft α β).left.app Δ =
      (Functor.associator F (X.obj Δ) G).inv ≫
        (β.left.app Δ ◫ postcompose.point α) ≫
        (Functor.associator F' (X.obj Δ) G').hom := sorry

/-- The right projection of the right/left interchange morphism is horizontal composition. -/
@[simp, stacks 0G5R "right projection of right/left interchange"]
theorem right {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : postcompose G ε ⟶ postcompose G' ε)
    (β : precompose F ε ⟶ precompose F' ε) :
    (interchange.rightLeft α β).right =
      (Functor.associator F (𝟭 C) G).inv ≫
        (β.right ◫ postcompose.point α) ≫
        (Functor.associator F' (𝟭 C) G').hom := sorry

/-- The normalized point of the right/left endpoint is the horizontal composite of points. -/
@[simp, stacks 0G5R "normalized point of right/left interchange"]
theorem point {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : postcompose G ε ⟶ postcompose G' ε)
    (β : precompose F ε ⟶ precompose F' ε) :
    whisker.point (interchange.rightLeft α β) =
      precompose.point β ◫ postcompose.point α := sorry

end rightLeft

end interchange

end whisker

end SimplicialObject.Augmented

end CategoryTheory
