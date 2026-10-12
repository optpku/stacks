/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Relative.Maps
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Basic.Comparisons
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative inertia maps of stacks

The forgetful map, identity section, relative-to-absolute comparison, and square-induced map,
with direct computations on their ambient fibered-category morphisms.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.relativeInertia

variable {X Y : StackOver.{u, v, max w vS, vS} J}

/-- Forget the selected relative automorphism from bundled relative inertia. -/
@[stacks 042H "stack relative-inertia structure map"]
def forget (F : X ⟶ Y) : relativeInertia F ⟶ X :=
  Hom.lift (FiberedCategoryOver.RelativeInertia.forget (Hom.toMor F))

/-- The ambient fibered morphism is neutral relative-inertia forgetting. -/
@[simp, stacks 042H "underlying stack relative-inertia forgetful morphism"]
theorem forget.hom (F : X ⟶ Y) :
    (forget F).hom =
      FiberedCategoryOver.RelativeInertia.forget (Hom.toMor F) := sorry

/-- Equip every source object with its identity relative automorphism. -/
@[stacks 04Z3 "stack relative-inertia neutral section"]
def identitySection (F : X ⟶ Y) : X ⟶ relativeInertia F :=
  Hom.lift (FiberedCategoryOver.RelativeInertia.identitySection (Hom.toMor F))

/-- The ambient fibered morphism is the canonical neutral section. -/
@[simp, stacks 04Z3 "underlying stack relative-inertia identity section"]
theorem identitySection.hom (F : X ⟶ Y) :
    (identitySection F).hom =
      FiberedCategoryOver.RelativeInertia.identitySection (Hom.toMor F) := sorry

/-- Retain the selected relative automorphism as an absolute automorphism. -/
@[stacks 04Z5 "stack relative-to-absolute inertia comparison"]
def toInertia (F : X ⟶ Y) : relativeInertia F ⟶ inertia X :=
  Hom.lift (FiberedCategoryOver.RelativeInertia.toInertia (Hom.toMor F))

/-- The ambient fibered morphism is the canonical neutral relative-to-absolute comparison. -/
@[simp, stacks 04Z5 "underlying stack relative-to-absolute inertia map"]
theorem toInertia.hom (F : X ⟶ Y) :
    (toInertia F).hom =
      FiberedCategoryOver.RelativeInertia.toInertia (Hom.toMor F) := sorry

/-- An invertibly commuting square of stack morphisms induces a map on relative inertia. -/
@[stacks 04Z4 "stack relative-inertia square map"]
def map
    {X₁ X₁' X₂ X₂' : StackOver.{u, v, max w vS, vS} J}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    relativeInertia F₁ ⟶ relativeInertia F₂ :=
  Hom.lift (FiberedCategoryOver.RelativeInertia.map
    (Hom.toMor G) (Hom.toMor G')
    (Bicategory.InducedBicategory.Iso.toAmbient comm))

/-- The ambient fibered morphism is the neutral square-induced relative-inertia map. -/
@[simp, stacks 04Z4 "underlying stack relative-inertia square map"]
theorem map.hom
    {X₁ X₁' X₂ X₂' : StackOver.{u, v, max w vS, vS} J}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    (map G G' comm).hom =
      FiberedCategoryOver.RelativeInertia.map
        (Hom.toMor G) (Hom.toMor G')
        (Bicategory.InducedBicategory.Iso.toAmbient comm) := sorry

/-- The relative identity section is a right inverse to relative-inertia forgetting. -/
@[simp, stacks 04Z3 "stack relative-inertia identity-section round trip"]
theorem identitySection.comp_forget (F : X ⟶ Y) :
    identitySection F ≫ forget F = 𝟙 X := sorry

/-- A relative-inertia square map commutes with forgetting to the source side. -/
@[simp, stacks 04Z4 "stack relative-inertia square forgetful compatibility"]
theorem map.comp_forget
    {X₁ X₁' X₂ X₂' : StackOver.{u, v, max w vS, vS} J}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    map G G' comm ≫ forget F₂ = forget F₁ ≫ G := sorry

/-- Relative identity sections are compatible with maps induced by invertible squares. -/
@[simp, stacks 04Z4 "stack relative-inertia square identity compatibility"]
theorem identitySection.comp_map
    {X₁ X₁' X₂ X₂' : StackOver.{u, v, max w vS, vS} J}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    identitySection F₁ ≫ map G G' comm = G ≫ identitySection F₂ := sorry

end StackOver.relativeInertia

end CategoryTheory
