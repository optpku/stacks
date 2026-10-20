/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Pointwise evaluation of augmented simplicial functors

Functor-valued augmented simplicial objects and their morphisms can be evaluated functorially at
objects of the source category.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SimplicialObject
open CategoryTheory.Functor

universe v₁ u₁ v₂ u₂

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]

namespace SimplicialObject.Augmented

namespace Pointwise

variable (X : SimplicialObject.Augmented (A ⥤ B))

/-- Evaluate a functor-valued augmented simplicial object at `a`. -/
@[stacks 0G5N "pointwise evaluation of an augmented simplicial functor"]
def obj (a : A) : SimplicialObject.Augmented B where
  left := X.left.flip.obj a
  right := X.right.obj a
  hom := NatTrans.flipApp X.hom a

/-- Functoriality in the evaluation object is compatible with the augmentation. -/
@[stacks 0G5N "naturality of pointwise augmented evaluation"]
theorem map_w {a a' : A} (f : a ⟶ a') :
    X.left.flip.map f ≫ (obj X a').hom =
      (obj X a).hom ≫ (SimplicialObject.const B).map (X.right.map f) := sorry

/-- The morphism of evaluated augmented simplicial objects induced by `f`. -/
@[stacks 0G5N "pointwise augmented evaluation map"]
def map {a a' : A} (f : a ⟶ a') : obj X a ⟶ obj X a' where
  left := X.left.flip.map f
  right := X.right.map f
  w := map_w X f

/-- Pointwise augmented evaluation preserves identity morphisms. -/
@[stacks 0G5N "pointwise evaluation preserves identities"]
theorem map_id (a : A) : map X (𝟙 a) = 𝟙 (obj X a) := sorry

/-- Pointwise augmented evaluation preserves composition. -/
@[stacks 0G5N "pointwise evaluation preserves composition"]
theorem map_comp {a₀ a₁ a₂ : A} (f : a₀ ⟶ a₁) (g : a₁ ⟶ a₂) :
    map X (f ≫ g) = map X f ≫ map X g := sorry

end Pointwise

/-- A functor-valued augmented simplicial object evaluated functorially in its input.

This is the augmented analogue of `Functor.flip`: it packages all point evaluations and the
maps between them into a single functor. -/
@[stacks 0G5N "functorial pointwise evaluation of an augmented simplicial functor"]
def pointwise (X : SimplicialObject.Augmented (A ⥤ B)) :
    A ⥤ SimplicialObject.Augmented B where
  obj := Pointwise.obj X
  map := Pointwise.map X
  map_id := Pointwise.map_id X
  map_comp := Pointwise.map_comp X

/-- The simplicial component of pointwise augmented evaluation. -/
@[simp, stacks 0G5N "simplicial component of pointwise augmented evaluation"]
theorem pointwise.obj_left (X : SimplicialObject.Augmented (A ⥤ B)) (a : A) :
    ((pointwise X).obj a).left = X.left.flip.obj a := sorry

/-- The augmentation point of pointwise augmented evaluation. -/
@[simp, stacks 0G5N "augmentation point of pointwise augmented evaluation"]
theorem pointwise.obj_right (X : SimplicialObject.Augmented (A ⥤ B)) (a : A) :
    ((pointwise X).obj a).right = X.right.obj a := sorry

/-- The augmentation map of pointwise evaluation is obtained by flipping the original map. -/
@[simp, stacks 0G5N "augmentation map of pointwise evaluation"]
theorem pointwise.obj_hom (X : SimplicialObject.Augmented (A ⥤ B)) (a : A) :
    ((pointwise X).obj a).hom = NatTrans.flipApp X.hom a := sorry

/-- The simplicial component of a pointwise evaluation map is objectwise functoriality. -/
@[simp, stacks 0G5N "simplicial component of a pointwise evaluation map"]
theorem pointwise.map_left_app (X : SimplicialObject.Augmented (A ⥤ B))
    {a a' : A} (f : a ⟶ a') (Δ : SimplexCategoryᵒᵖ) :
    ((pointwise X).map f).left.app Δ = (X.left.obj Δ).map f := sorry

/-- The point component of a pointwise evaluation map is the map of the augmented point. -/
@[simp, stacks 0G5N "point component of a pointwise evaluation map"]
theorem pointwise.map_right (X : SimplicialObject.Augmented (A ⥤ B))
    {a a' : A} (f : a ⟶ a') :
    ((pointwise X).map f).right = X.right.map f := sorry

/-- An augmented natural transformation is compatible with pointwise evaluation at `a`. -/
@[stacks 0G5N "pointwise component compatibility for augmented maps"]
theorem Pointwise.component_w {X Y : SimplicialObject.Augmented (A ⥤ B)}
    (f : X ⟶ Y) (a : A) :
    NatTrans.flipApp f.left a ≫ (Pointwise.obj Y a).hom =
      (Pointwise.obj X a).hom ≫
        (SimplicialObject.const B).map (f.right.app a) := sorry

/-- Evaluate a morphism of functor-valued augmented simplicial objects at `a`. -/
@[stacks 0G5N "pointwise component of an augmented map"]
def Pointwise.component {X Y : SimplicialObject.Augmented (A ⥤ B)}
    (f : X ⟶ Y) (a : A) : Pointwise.obj X a ⟶ Pointwise.obj Y a where
  left := NatTrans.flipApp f.left a
  right := f.right.app a
  w := Pointwise.component_w f a

/-- Evaluated components of an augmented natural transformation are natural in the input. -/
@[stacks 0G5N "naturality of pointwise augmented-map components"]
theorem Pointwise.component_naturality
    {X Y : SimplicialObject.Augmented (A ⥤ B)} (f : X ⟶ Y)
    {a a' : A} (g : a ⟶ a') :
    Pointwise.map X g ≫ Pointwise.component f a' =
      Pointwise.component f a ≫ Pointwise.map Y g := sorry

/-- Pointwise evaluation of a morphism of functor-valued augmented simplicial objects. -/
@[stacks 0G5N "pointwise natural transformation of augmented objects"]
def Pointwise.hom {X Y : SimplicialObject.Augmented (A ⥤ B)} (f : X ⟶ Y) :
    pointwise X ⟶ pointwise Y where
  app a := Pointwise.component f a
  naturality := fun {_ _} g ↦ Pointwise.component_naturality f g

/-- The components of `Pointwise.hom` are the corresponding pointwise augmented maps. -/
@[simp, stacks 0G5N "components of pointwise augmented natural transformations"]
theorem Pointwise.hom_app {X Y : SimplicialObject.Augmented (A ⥤ B)}
    (f : X ⟶ Y) (a : A) :
    (Pointwise.hom f).app a = Pointwise.component f a := sorry

/-- Pointwise evaluation sends identity augmented maps to identity natural transformations. -/
@[simp, stacks 0G5N "pointwise evaluation sends identities to identities"]
theorem Pointwise.hom_id (X : SimplicialObject.Augmented (A ⥤ B)) :
    Pointwise.hom (𝟙 X) = 𝟙 (pointwise X) := sorry

/-- Pointwise evaluation preserves composition of augmented maps. -/
@[simp, stacks 0G5N "pointwise evaluation preserves augmented composition"]
theorem Pointwise.hom_comp
    {X Y Z : SimplicialObject.Augmented (A ⥤ B)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Pointwise.hom (f ≫ g) = Pointwise.hom f ≫ Pointwise.hom g := sorry

/-- Pointwise evaluation as a functor from functor-valued augmented simplicial objects. -/
@[stacks 0G5N "functorial pointwise evaluation of augmented objects"]
def pointwiseFunctor :
    SimplicialObject.Augmented (A ⥤ B) ⥤ A ⥤ SimplicialObject.Augmented B where
  obj X := pointwise X
  map f := Pointwise.hom f
  map_id := Pointwise.hom_id
  map_comp := Pointwise.hom_comp

end SimplicialObject.Augmented

end CategoryTheory
