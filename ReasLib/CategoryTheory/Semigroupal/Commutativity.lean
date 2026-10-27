/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Semigroupal.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

@[expose] public section

namespace CategoryTheory.SemigroupalCategory

universe u v

/-- A chosen natural involutive commutativity constraint on a unit-free tensor category.
Compatibility with the associator is a separate property. -/
structure CommutativityConstraint (C : Type u) [Category.{v} C]
    [SemigroupalCategory C] where
  /-- The component isomorphisms interchanging the two tensor factors. -/
  braiding : ∀ X Y : C, tensorObj X Y ≅ tensorObj Y X
  /-- Naturality in both tensor factors. -/
  naturality : ∀ {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
    tensorHom f g ≫ (braiding Y₁ Y₂).hom = (braiding X₁ X₂).hom ≫ tensorHom g f
  /-- Interchanging the factors twice is the identity. -/
  symmetry : ∀ X Y : C,
    (braiding X Y).hom ≫ (braiding Y X).hom = 𝟙 (tensorObj X Y)

namespace CommutativityConstraint

section Semigroupal

variable {C : Type u} [Category.{v} C] [SemigroupalCategory C]

/-- A commutativity constraint is natural and involutive. -/
theorem spec (ψ : CommutativityConstraint C) :
    (∀ {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
      tensorHom f g ≫ (ψ.braiding Y₁ Y₂).hom =
        (ψ.braiding X₁ X₂).hom ≫ tensorHom g f) ∧
    (∀ X Y : C,
      (ψ.braiding X Y).hom ≫ (ψ.braiding Y X).hom = 𝟙 (tensorObj X Y)) := sorry

/-- A commutativity constraint is compatible with the associator when the
inverse-associator hexagon commutes for every triple of objects. -/
def IsCompatible (ψ : CommutativityConstraint C) : Prop :=
  ∀ X Y Z : C,
    (associator X Y Z).inv ≫ (ψ.braiding (tensorObj X Y) Z).hom ≫
        (associator Z X Y).inv =
      whiskerLeft X (ψ.braiding Y Z).hom ≫ (associator X Z Y).inv ≫
        whiskerRight (ψ.braiding X Z).hom Y

/-- A commutativity constraint is compatible with the associator if and only if
the inverse-associator hexagon commutes for all objects. -/
theorem isCompatible_iff (ψ : CommutativityConstraint C) :
    ψ.IsCompatible ↔ ∀ X Y Z : C,
      (associator X Y Z).inv ≫ (ψ.braiding (tensorObj X Y) Z).hom ≫
          (associator Z X Y).inv =
        whiskerLeft X (ψ.braiding Y Z).hom ≫ (associator X Z Y).inv ≫
          whiskerRight (ψ.braiding X Z).hom Y := sorry

/-- Apply compatibility at three objects to obtain the hexagon equality. -/
theorem hexagon (ψ : CommutativityConstraint C) (h : ψ.IsCompatible) (X Y Z : C) :
    (associator X Y Z).inv ≫ (ψ.braiding (tensorObj X Y) Z).hom ≫
        (associator Z X Y).inv =
      whiskerLeft X (ψ.braiding Y Z).hom ≫ (associator X Z Y).inv ≫
        whiskerRight (ψ.braiding X Z).hom Y := sorry

end Semigroupal

section Symmetric

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- Forget the unit of a symmetric monoidal category and retain its given braiding. -/
def ofSymmetric : CommutativityConstraint C where
  braiding := fun X Y ↦ BraidedCategory.braiding X Y
  naturality := sorry
  symmetry := sorry

/-- The commutativity constraint obtained from a symmetric monoidal category
has exactly its original braiding components. -/
theorem ofSymmetric_braiding (X Y : C) :
    (ofSymmetric C).braiding X Y = BraidedCategory.braiding X Y := sorry

/-- The braiding of a symmetric monoidal category is compatible with its associator. -/
theorem ofSymmetric_isCompatible : (ofSymmetric C).IsCompatible := sorry

end Symmetric

end CommutativityConstraint

end CategoryTheory.SemigroupalCategory
