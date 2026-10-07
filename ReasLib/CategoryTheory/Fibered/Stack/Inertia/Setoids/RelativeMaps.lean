module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Equivalence
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Groupoids.RelativeMaps
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Setoids.Comparisons
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative inertia maps of setoid stacks

Structure maps, square functoriality, and the relative-inertia equivalence, with normalized
readouts at both the groupoid-stack and setoid-fibred levels.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Setoids.relativeInertia

variable {X Y : StackOver.Setoids.{u, v, max w vS, vS} J}

/-- Forget the selected relative automorphism from bundled setoid-stack relative inertia. -/
@[stacks 042H "setoid-stack relative-inertia structure map"]
def forget (F : X ⟶ Y) : relativeInertia F ⟶ X :=
  Hom.lift (StackOver.Groupoids.relativeInertia.forget (Hom.toGroupoidsMor F))

/-- The underlying groupoid-stack morphism is neutral relative-inertia forgetting. -/
@[simp, stacks 042H "setoid-stack relative-inertia structure-map readout"]
theorem forget.hom (F : X ⟶ Y) :
    (forget F).hom =
      StackOver.Groupoids.relativeInertia.forget (Hom.toGroupoidsMor F) := sorry

/-- The setoid-fibred morphism is neutral relative-inertia forgetting. -/
@[simp, stacks 042H "setoid-fibred relative-inertia structure-map readout"]
theorem forget.toSetoidsMor (F : X ⟶ Y) :
    Hom.toSetoidsMor (forget F) =
      FiberedCategoryOver.Setoids.RelativeInertia.forget (Hom.toSetoidsMor F) := sorry

/-- Equip every source object with its identity relative automorphism. -/
@[stacks 04Z3 "setoid-stack relative-inertia neutral section"]
def identitySection (F : X ⟶ Y) : X ⟶ relativeInertia F :=
  Hom.lift (StackOver.Groupoids.relativeInertia.identitySection
    (Hom.toGroupoidsMor F))

/-- The underlying groupoid-stack morphism is the neutral relative identity section. -/
@[simp, stacks 04Z3 "setoid-stack relative-inertia neutral-section readout"]
theorem identitySection.hom (F : X ⟶ Y) :
    (identitySection F).hom =
      StackOver.Groupoids.relativeInertia.identitySection
        (Hom.toGroupoidsMor F) := sorry

/-- The setoid-fibred morphism is the neutral relative identity section. -/
@[simp, stacks 04Z3 "setoid-fibred relative-inertia neutral-section readout"]
theorem identitySection.toSetoidsMor (F : X ⟶ Y) :
    Hom.toSetoidsMor (identitySection F) =
      FiberedCategoryOver.Setoids.RelativeInertia.identitySection
        (Hom.toSetoidsMor F) := sorry

/-- Retain a selected relative automorphism as an absolute automorphism. -/
@[stacks 04Z5 "setoid-stack relative-to-absolute inertia comparison"]
def toInertia (F : X ⟶ Y) : relativeInertia F ⟶ inertia X :=
  Hom.lift (StackOver.Groupoids.relativeInertia.toInertia
    (Hom.toGroupoidsMor F))

/-- The underlying groupoid-stack morphism is the neutral relative-to-absolute comparison. -/
@[simp, stacks 04Z5 "setoid-stack relative-to-absolute inertia comparison readout"]
theorem toInertia.hom (F : X ⟶ Y) :
    (toInertia F).hom =
      StackOver.Groupoids.relativeInertia.toInertia (Hom.toGroupoidsMor F) := sorry

/-- The setoid-fibred morphism is the neutral relative-to-absolute comparison. -/
@[simp, stacks 04Z5 "setoid-fibred relative-to-absolute inertia comparison readout"]
theorem toInertia.toSetoidsMor (F : X ⟶ Y) :
    Hom.toSetoidsMor (toInertia F) =
      FiberedCategoryOver.Setoids.RelativeInertia.toInertia
        (Hom.toSetoidsMor F) := sorry

/-- An invertibly commuting square of setoid-stack morphisms induces a map on relative
inertia. -/
@[stacks 04Z4 "setoid-stack relative-inertia square map"]
def map
    {X₁ X₁' X₂ X₂' : StackOver.Setoids.{u, v, max w vS, vS} J}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    relativeInertia F₁ ⟶ relativeInertia F₂ :=
  Hom.lift (StackOver.Groupoids.relativeInertia.map
    (Hom.toGroupoidsMor G) (Hom.toGroupoidsMor G')
    (Bicategory.InducedBicategory.Iso.toAmbient comm))

/-- The underlying groupoid-stack morphism is the square-induced relative-inertia map. -/
@[simp, stacks 04Z4 "setoid-stack square-induced relative-inertia map readout"]
theorem map.hom
    {X₁ X₁' X₂ X₂' : StackOver.Setoids.{u, v, max w vS, vS} J}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    (map G G' comm).hom =
      StackOver.Groupoids.relativeInertia.map
        (Hom.toGroupoidsMor G) (Hom.toGroupoidsMor G')
        (Bicategory.InducedBicategory.Iso.toAmbient comm) := sorry

/-- The setoid-fibred morphism is the canonical map of the underlying invertible square. -/
@[simp, stacks 04Z4 "setoid-fibred square-induced relative-inertia map readout"]
theorem map.toSetoidsMor
    {X₁ X₁' X₂ X₂' : StackOver.Setoids.{u, v, max w vS, vS} J}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    Hom.toSetoidsMor (map G G' comm) =
      FiberedCategoryOver.Setoids.RelativeInertia.map
        (Hom.toSetoidsMor G) (Hom.toSetoidsMor G')
        (Hom.toSetoidsMor.compIso F₁ G' ≪≫
          Hom.toSetoidsMorIso comm ≪≫
          (Hom.toSetoidsMor.compIso G F₂).symm) := sorry

/-- The setoid-stack relative identity section is a right inverse to forgetting. -/
@[simp, stacks 04Z3 "setoid-stack relative-inertia section/forget readout"]
theorem identitySection.comp_forget (F : X ⟶ Y) :
    identitySection F ≫ forget F = 𝟙 X := sorry

/-- Thin fibres make relative-inertia forgetting a left inverse to the identity section. -/
@[simp, stacks 04Z3 "setoid-stack relative-inertia forget/section readout"]
theorem forget.comp_identitySection (F : X ⟶ Y) :
    forget F ≫ identitySection F = 𝟙 (relativeInertia F) := sorry

/-- Relative inertia of a setoid-stack morphism is canonically equivalent to its source. -/
@[stacks 04Z3 "setoid-stack relative-inertia equivalence"]
def forget.equivalence (F : X ⟶ Y) : relativeInertia F ≌ X :=
  ObjectProperty.FullSubbicategory.equivalenceOfAmbient
    (ObjectProperty.FullSubbicategory.equivalenceOfAmbient
      (ObjectProperty.FullSubbicategory.equivalenceOfAmbient
        (BasedCategory.RelativeInertia.forget.equivalenceOf
          (Hom.toBasedFunctor F) X.2)))

/-- The forward morphism of the relative-inertia equivalence is forgetting. -/
@[simp, stacks 04Z3 "setoid-stack relative-inertia equivalence forward readout"]
theorem forget.equivalence.hom (F : X ⟶ Y) :
    (forget.equivalence F).hom = forget F := sorry

/-- The inverse morphism of the relative-inertia equivalence is the identity section. -/
@[simp, stacks 04Z3 "setoid-stack relative-inertia equivalence inverse readout"]
theorem forget.equivalence.inv (F : X ⟶ Y) :
    (forget.equivalence F).inv = identitySection F := sorry

/-- A relative-inertia square map commutes with forgetting to its source. -/
@[simp, stacks 04Z4 "setoid-stack square-induced map/forget compatibility"]
theorem map.comp_forget
    {X₁ X₁' X₂ X₂' : StackOver.Setoids.{u, v, max w vS, vS} J}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    map G G' comm ≫ forget F₂ = forget F₁ ≫ G := sorry

/-- Relative identity sections are compatible with square-induced maps. -/
@[simp, stacks 04Z4 "setoid-stack square-induced map/section compatibility"]
theorem identitySection.comp_map
    {X₁ X₁' X₂ X₂' : StackOver.Setoids.{u, v, max w vS, vS} J}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    identitySection F₁ ≫ map G G' comm = G ≫ identitySection F₂ := sorry

end StackOver.Setoids.relativeInertia

end CategoryTheory
