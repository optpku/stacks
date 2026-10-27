/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.Center.Whiskering
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The category center acting on augmented simplicial objects

A central endomorphism acts simultaneously on every degree of an augmented simplicial object and
on its augmentation point.  This file bundles that construction first as an endomorphism of one
augmented object and then as a monoid homomorphism into the center of the augmented-object
category.
-/

@[expose] public section

open CategoryTheory

universe u v uC vC

namespace CategoryTheory.CatCenter

variable {D : Type u} [Category.{v} D]

/-- The square expressing that a central endomorphism commutes with the augmentation map. -/
@[stacks 0G5S "the category center preserves an augmentation"]
theorem augmentedApp.commSq (z : CatCenter D)
    (Q : SimplicialObject.Augmented D) :
    CommSq
      (Functor.whiskerLeft Q.left z)
      Q.hom Q.hom
      ((SimplicialObject.const D).map (z.app Q.right)) := by
  refine ⟨?_⟩
  ext n
  exact (z.naturality (Q.hom.app n)).symm

/-- The endomorphism of an augmented simplicial object induced by a central endomorphism of its
ambient category. -/
@[stacks 0G5S "the category center acting on an augmented simplicial object"]
def augmentedApp (z : CatCenter D) (Q : SimplicialObject.Augmented D) : Q ⟶ Q where
  left := Functor.whiskerLeft Q.left z
  right := z.app Q.right
  w := (augmentedApp.commSq z Q).w

/-- The simplicial component of the center action is degreewise application of the central
endomorphism. -/
@[simp, stacks 0G5S "simplicial component of the augmented center action"]
theorem augmentedApp.left (z : CatCenter D) (Q : SimplicialObject.Augmented D) :
    (augmentedApp z Q).left = Functor.whiskerLeft Q.left z := rfl

/-- The augmentation-point component of the center action is the component of the central
endomorphism at that point. -/
@[simp, stacks 0G5S "point component of the augmented center action"]
theorem augmentedApp.right (z : CatCenter D) (Q : SimplicialObject.Augmented D) :
    (augmentedApp z Q).right = z.app Q.right := rfl

variable {C : Type uC} [Category.{vC} C]

/-- Right-whiskering a central endomorphism by every simplicial degree commutes with any
augmentation to the identity endofunctor. -/
@[stacks 0G5S "right-whiskering the center preserves an endofunctor augmentation"]
theorem whiskerRight.commSq (z : CatCenter C) {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)) :
    CommSq
      (Functor.whiskerLeft X (whiskerRight C z)) ε ε
      ((SimplicialObject.const (C ⥤ C)).map z) := by
  refine ⟨?_⟩
  ext n A
  exact (ε.app n).naturality (z.app A)

/-- Left-whiskering a central endomorphism by every simplicial degree commutes with any
augmentation to the identity endofunctor. -/
@[stacks 0G5S "left-whiskering the center preserves an endofunctor augmentation"]
theorem whiskerLeft.commSq (z : CatCenter C) {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)) :
    CommSq
      (Functor.whiskerLeft X (whiskerLeft C z)) ε ε
      ((SimplicialObject.const (C ⥤ C)).map z) := by
  refine ⟨?_⟩
  ext n A
  exact (z.naturality ((ε.app n).app A)).symm

/-- The center action is natural in the augmented simplicial object. -/
@[stacks 0G5S "naturality of the augmented center action"]
theorem augmentedApp.naturality (z : CatCenter D)
    {Q R : SimplicialObject.Augmented D} (f : Q ⟶ R) :
    f ≫ augmentedApp z R = augmentedApp z Q ≫ f := by
  apply SimplicialObject.Augmented.hom_ext
  · show (f ≫ augmentedApp z R).left = (augmentedApp z Q ≫ f).left
    ext n
    exact z.naturality (f.left.app n)
  · show (f ≫ augmentedApp z R).right = (augmentedApp z Q ≫ f).right
    exact z.naturality f.right

/-- A central endomorphism of `D` induces a central endomorphism of the category of augmented
simplicial objects in `D`. -/
@[stacks 0G5S "lifting the category center to augmented simplicial objects"]
def augmentedMap (z : CatCenter D) :
    CatCenter (SimplicialObject.Augmented D) where
  app Q := augmentedApp z Q
  naturality _ _ f := augmentedApp.naturality z f

/-- The lifted identity central endomorphism is the identity. -/
@[simp]
theorem augmentedMap.one : augmentedMap (1 : CatCenter D) = 1 := by
  apply CatCenter.ext
  intro Q
  exact SimplicialObject.Augmented.hom_ext _ _ rfl rfl

/-- Lifting central endomorphisms preserves multiplication. -/
@[simp]
theorem augmentedMap.mul (z w : CatCenter D) :
    augmentedMap (z * w) = augmentedMap z * augmentedMap w := by
  apply CatCenter.ext
  intro Q
  exact SimplicialObject.Augmented.hom_ext _ _ rfl rfl

/-- The center action on augmented simplicial objects, bundled as a monoid homomorphism between
category centers. -/
@[stacks 0G5S "center action on the category of augmented simplicial objects"]
def augmented :
    CatCenter D →* CatCenter (SimplicialObject.Augmented D) where
  toFun := augmentedMap
  map_one' := augmentedMap.one
  map_mul' := augmentedMap.mul

/-- Evaluating the bundled center action at an augmented object gives `augmentedApp`. -/
@[simp]
theorem augmented_app (z : CatCenter D) (Q : SimplicialObject.Augmented D) :
    (augmented z).app Q = augmentedApp z Q := rfl

end CategoryTheory.CatCenter
