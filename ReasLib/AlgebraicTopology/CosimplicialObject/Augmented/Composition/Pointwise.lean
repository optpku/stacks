module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Pointwise evaluation of augmented cosimplicial objects

This leaf owns functorial pointwise evaluation for augmented cosimplicial objects valued in a
functor category.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.CosimplicialObject
open CategoryTheory.Functor

universe v₁ u₁ v₂ u₂

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]

namespace CosimplicialObject.Augmented

namespace Pointwise

variable (X : CosimplicialObject.Augmented (A ⥤ B))

/-- Evaluate a functor-valued augmented cosimplicial object at `a`. -/
@[stacks 0G5N "pointwise evaluation of an augmented cosimplicial functor"]
def obj (a : A) : CosimplicialObject.Augmented B where
  left := X.left.obj a
  right := X.right.flip.obj a
  hom := NatTrans.flipApp X.hom a

/-- Functoriality in the evaluation object is compatible with the coaugmentation. -/
@[stacks 0G5N "naturality of pointwise cosimplicial evaluation"]
theorem map_w {a a' : A} (f : a ⟶ a') :
    (CosimplicialObject.const B).map (X.left.map f) ≫ (obj X a').hom =
      (obj X a).hom ≫ X.right.flip.map f := sorry

/-- The morphism of evaluated augmented cosimplicial objects induced by `f`. -/
@[stacks 0G5N "pointwise augmented cosimplicial evaluation map"]
def map {a a' : A} (f : a ⟶ a') : obj X a ⟶ obj X a' where
  left := X.left.map f
  right := X.right.flip.map f
  w := map_w X f

/-- Pointwise augmented cosimplicial evaluation preserves identity morphisms. -/
@[stacks 0G5N "pointwise cosimplicial evaluation preserves identities"]
theorem map_id (a : A) : map X (𝟙 a) = 𝟙 (obj X a) := sorry

/-- Pointwise augmented cosimplicial evaluation preserves composition. -/
@[stacks 0G5N "pointwise cosimplicial evaluation preserves composition"]
theorem map_comp {a₀ a₁ a₂ : A} (f : a₀ ⟶ a₁) (g : a₁ ⟶ a₂) :
    map X (f ≫ g) = map X f ≫ map X g := sorry

end Pointwise

/-- A functor-valued augmented cosimplicial object evaluated functorially in its input.

This is the augmented cosimplicial analogue of `Functor.flip`: it packages all point
evaluations and the maps between them into a single functor. -/
@[stacks 0G5N "functorial pointwise evaluation of an augmented cosimplicial functor"]
def pointwise (X : CosimplicialObject.Augmented (A ⥤ B)) :
    A ⥤ CosimplicialObject.Augmented B where
  obj := Pointwise.obj X
  map := Pointwise.map X
  map_id := Pointwise.map_id X
  map_comp := Pointwise.map_comp X

/-- The point of a pointwise evaluation is evaluation of the original point. -/
@[simp, stacks 0G5N "point object of augmented cosimplicial evaluation"]
theorem pointwise.obj_left (X : CosimplicialObject.Augmented (A ⥤ B)) (a : A) :
    ((pointwise X).obj a).left = X.left.obj a := sorry

/-- The cosimplicial component of pointwise evaluation is the flipped objectwise functor. -/
@[simp, stacks 0G5N "cosimplicial object of pointwise augmented evaluation"]
theorem pointwise.obj_right (X : CosimplicialObject.Augmented (A ⥤ B)) (a : A) :
    ((pointwise X).obj a).right = X.right.flip.obj a := sorry

/-- The coaugmentation of pointwise evaluation is the flipped component of the original map. -/
@[simp, stacks 0G5N "coaugmentation of pointwise augmented evaluation"]
theorem pointwise.obj_hom (X : CosimplicialObject.Augmented (A ⥤ B)) (a : A) :
    ((pointwise X).obj a).hom = NatTrans.flipApp X.hom a := sorry

/-- The point component of a pointwise evaluation map is the map of the augmented point. -/
@[simp, stacks 0G5N "point map of pointwise augmented cosimplicial evaluation"]
theorem pointwise.map_left (X : CosimplicialObject.Augmented (A ⥤ B))
    {a a' : A} (f : a ⟶ a') :
    ((pointwise X).map f).left = X.left.map f := sorry

/-- The cosimplicial component of a pointwise evaluation map is objectwise functoriality. -/
@[simp, stacks 0G5N "cosimplicial map of pointwise augmented evaluation"]
theorem pointwise.map_right_app (X : CosimplicialObject.Augmented (A ⥤ B))
    {a a' : A} (f : a ⟶ a') (Δ : SimplexCategory) :
    ((pointwise X).map f).right.app Δ = (X.right.obj Δ).map f := sorry

/-- An augmented natural transformation is compatible with pointwise evaluation. -/
@[stacks 0G5N "pointwise component compatibility for augmented cosimplicial maps"]
theorem Pointwise.component_w {X Y : CosimplicialObject.Augmented (A ⥤ B)}
    (f : X ⟶ Y) (a : A) :
    (CosimplicialObject.const B).map (f.left.app a) ≫ (Pointwise.obj Y a).hom =
      (Pointwise.obj X a).hom ≫ NatTrans.flipApp f.right a := sorry

/-- Evaluate a morphism of functor-valued augmented cosimplicial objects at `a`. -/
@[stacks 0G5N "pointwise component of an augmented cosimplicial map"]
def Pointwise.component {X Y : CosimplicialObject.Augmented (A ⥤ B)}
    (f : X ⟶ Y) (a : A) : Pointwise.obj X a ⟶ Pointwise.obj Y a where
  left := f.left.app a
  right := NatTrans.flipApp f.right a
  w := Pointwise.component_w f a

/-- Evaluated components of an augmented cosimplicial transformation are natural in the input. -/
@[stacks 0G5N "naturality of pointwise augmented cosimplicial components"]
theorem Pointwise.component_naturality
    {X Y : CosimplicialObject.Augmented (A ⥤ B)} (f : X ⟶ Y)
    {a a' : A} (g : a ⟶ a') :
    Pointwise.map X g ≫ Pointwise.component f a' =
      Pointwise.component f a ≫ Pointwise.map Y g := sorry

/-- Pointwise evaluation of a morphism of augmented cosimplicial objects. -/
@[stacks 0G5N "pointwise natural transformation of augmented cosimplicial objects"]
def Pointwise.hom {X Y : CosimplicialObject.Augmented (A ⥤ B)} (f : X ⟶ Y) :
    pointwise X ⟶ pointwise Y where
  app a := Pointwise.component f a
  naturality := fun {_ _} g ↦ Pointwise.component_naturality f g

/-- The components of an evaluated augmented transformation are its pointwise maps. -/
@[simp, stacks 0G5N "components of pointwise augmented cosimplicial transformations"]
theorem Pointwise.hom_app {X Y : CosimplicialObject.Augmented (A ⥤ B)}
    (f : X ⟶ Y) (a : A) :
    (Pointwise.hom f).app a = Pointwise.component f a := sorry

/-- Pointwise evaluation sends identity augmented maps to identity transformations. -/
@[simp, stacks 0G5N "pointwise cosimplicial evaluation sends identities to identities"]
theorem Pointwise.hom_id (X : CosimplicialObject.Augmented (A ⥤ B)) :
    Pointwise.hom (𝟙 X) = 𝟙 (pointwise X) := sorry

/-- Pointwise evaluation preserves composition of augmented maps. -/
@[simp, stacks 0G5N "pointwise cosimplicial evaluation preserves augmented composition"]
theorem Pointwise.hom_comp {X Y Z : CosimplicialObject.Augmented (A ⥤ B)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Pointwise.hom (f ≫ g) = Pointwise.hom f ≫ Pointwise.hom g := sorry

/-- Pointwise evaluation as a functor on functor-valued augmented cosimplicial objects. -/
@[stacks 0G5N "functorial pointwise evaluation of augmented cosimplicial objects"]
def pointwiseFunctor :
    CosimplicialObject.Augmented (A ⥤ B) ⥤ A ⥤ CosimplicialObject.Augmented B where
  obj X := pointwise X
  map f := Pointwise.hom f
  map_id := Pointwise.hom_id
  map_comp := Pointwise.hom_comp

end CosimplicialObject.Augmented

end CategoryTheory
