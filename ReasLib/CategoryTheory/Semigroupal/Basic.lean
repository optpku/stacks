/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Monoidal.Category

@[expose] public section

universe v u

namespace CategoryTheory

/-- A category with a tensor bifunctor and a coherent associator, with no chosen unit. -/
class SemigroupalCategory (C : Type u) [Category.{v} C] where
  /-- The tensor product bifunctor. -/
  tensor : C × C ⥤ C
  /-- The associator from the left-associated to the right-associated tensor product. -/
  associator :
    ∀ X Y Z : C, tensor.obj (tensor.obj (X, Y), Z) ≅ tensor.obj (X, tensor.obj (Y, Z))
  /-- Naturality of the associator in all three variables. -/
  associator_naturality :
    ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (first : X₁ ⟶ Y₁) (second : X₂ ⟶ Y₂) (third : X₃ ⟶ Y₃),
      tensor.map ⟨tensor.map ⟨first, second⟩, third⟩ ≫ (associator Y₁ Y₂ Y₃).hom =
        (associator X₁ X₂ X₃).hom ≫ tensor.map ⟨first, tensor.map ⟨second, third⟩⟩
  /-- The pentagon identity for the associator. -/
  pentagon :
    ∀ W X Y Z : C,
      tensor.map ⟨(associator W X Y).hom, 𝟙 Z⟩ ≫
          (associator W (tensor.obj (X, Y)) Z).hom ≫
          tensor.map ⟨𝟙 W, (associator X Y Z).hom⟩ =
        (associator (tensor.obj (W, X)) Y Z).hom ≫
          (associator W X (tensor.obj (Y, Z))).hom

namespace SemigroupalCategory

/-- The coherent tensor structure obtained by forgetting the unit of a monoidal category. -/
@[reducible] def ofMonoidal (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    SemigroupalCategory C where
  tensor := MonoidalCategory.tensor C
  associator := MonoidalCategory.associator
  associator_naturality := MonoidalCategory.associator_naturality
  pentagon W X Y Z := by
    simpa only [MonoidalCategory.tensor,
      MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
      MonoidalCategory.pentagon W X Y Z

/-- A monoidal category has its canonical unit-free coherent tensor structure. -/
instance instSemigroupalCategory {C : Type u} [Category.{v} C] [MonoidalCategory C] :
    SemigroupalCategory C := ofMonoidal C

variable {C : Type u} [Category.{v} C] [SemigroupalCategory C]

/-- The tensor product of two objects. -/
abbrev tensorObj (X Y : C) : C :=
  tensor.obj (X, Y)

/-- The tensor product of objects is the object map of the tensor bifunctor. -/
theorem tensorObj_def (X Y : C) : tensorObj X Y = tensor.obj (X, Y) := rfl

/-- The tensor product of two morphisms is their image under the tensor bifunctor. -/
def tensorHom {X₁ Y₁ X₂ Y₂ : C} (first : X₁ ⟶ Y₁) (second : X₂ ⟶ Y₂) :
    tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ :=
  tensor.map ⟨first, second⟩

/-- Tensoring morphisms agrees with the morphism map of the tensor bifunctor. -/
theorem tensorHom_def {X₁ Y₁ X₂ Y₂ : C} (first : X₁ ⟶ Y₁) (second : X₂ ⟶ Y₂) :
    tensorHom first second = tensor.map ⟨first, second⟩ := rfl

/-- The tensor product of two isomorphisms is their image under the tensor bifunctor. -/
def tensorIso {X₁ Y₁ X₂ Y₂ : C} (first : X₁ ≅ Y₁) (second : X₂ ≅ Y₂) :
    tensorObj X₁ X₂ ≅ tensorObj Y₁ Y₂ :=
  tensor.mapIso (Iso.prod first second)

/-- The forward morphism of a tensor product of isomorphisms tensors their forward maps. -/
theorem tensorIso_hom {X₁ Y₁ X₂ Y₂ : C} (first : X₁ ≅ Y₁) (second : X₂ ≅ Y₂) :
    (tensorIso first second).hom = tensorHom first.hom second.hom := rfl

/-- Tensoring a morphism on the left by an object. -/
abbrev whiskerLeft (X : C) {Y₁ Y₂ : C} (morphism : Y₁ ⟶ Y₂) :
    tensorObj X Y₁ ⟶ tensorObj X Y₂ :=
  tensor.map ⟨𝟙 X, morphism⟩

/-- Left whiskering is the tensor of an identity with the given morphism. -/
theorem whiskerLeft_def (X : C) {Y₁ Y₂ : C} (morphism : Y₁ ⟶ Y₂) :
    whiskerLeft X morphism = tensor.map ⟨𝟙 X, morphism⟩ := rfl

/-- Tensoring a morphism on the right by an object. -/
abbrev whiskerRight {X₁ X₂ : C} (morphism : X₁ ⟶ X₂) (Y : C) :
    tensorObj X₁ Y ⟶ tensorObj X₂ Y :=
  tensor.map ⟨morphism, 𝟙 Y⟩

/-- Right whiskering is the tensor of the given morphism with an identity. -/
theorem whiskerRight_def {X₁ X₂ : C} (morphism : X₁ ⟶ X₂) (Y : C) :
    whiskerRight morphism Y = tensor.map ⟨morphism, 𝟙 Y⟩ := rfl

/-- Tensoring on the left with a fixed object. -/
abbrev tensorLeft (X : C) : C ⥤ C :=
  (Functor.curryObj tensor).obj X

/-- Left tensoring evaluates as the tensor bifunctor on objects. -/
theorem tensorLeft_obj (X Y : C) : (tensorLeft X).obj Y = tensorObj X Y := rfl

/-- Tensoring on the right with a fixed object. -/
abbrev tensorRight (X : C) : C ⥤ C :=
  (Functor.curryObj tensor).flip.obj X

/-- Right tensoring evaluates as the tensor bifunctor on objects. -/
theorem tensorRight_obj (X Y : C) : (tensorRight X).obj Y = tensorObj Y X := rfl

/-- Tensoring an isomorphism on the left by an object. -/
def whiskerLeftIso (X : C) {Y Z : C} (iso : Y ≅ Z) : tensorObj X Y ≅ tensorObj X Z :=
  (tensorLeft X).mapIso iso

/-- The forward morphism of left iso-whiskering is left whiskering. -/
theorem whiskerLeftIso_hom (X : C) {Y Z : C} (iso : Y ≅ Z) :
    (whiskerLeftIso X iso).hom = whiskerLeft X iso.hom := rfl

/-- Tensoring an isomorphism on the right by an object. -/
def whiskerRightIso {X Y : C} (iso : X ≅ Y) (Z : C) : tensorObj X Z ≅ tensorObj Y Z :=
  (tensorRight Z).mapIso iso

/-- The forward morphism of right iso-whiskering is right whiskering. -/
theorem whiskerRightIso_hom {X Y : C} (iso : X ≅ Y) (Z : C) :
    (whiskerRightIso iso Z).hom = whiskerRight iso.hom Z := rfl

end SemigroupalCategory

end CategoryTheory
