module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Equivalence
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.RelativeFunctoriality
public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.Iso
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Sets.Comparisons
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Setoids.RelativeMaps
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative inertia maps for stacks in sets

The concrete maps are lifted from the neutral setoid-stack construction. Computation rules
expose them directly at the setoid-stack and based-category levels. The separate owner equations
relate the resulting objects to the neutral set-fibred model when transport is required.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open BasedCategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Sets

/-- Forget the selected relative automorphism from a morphism of stacks in sets. -/
@[stacks 042H "set-stack relative-inertia structure map"]
def relativeInertia.forget
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    relativeInertia F ⟶ X :=
  Hom.lift (StackOver.Setoids.relativeInertia.forget (Hom.toSetoidsMor F))

/-- The underlying setoid-stack morphism is neutral relative-inertia forgetting. -/
@[simp]
theorem relativeInertia.forget.hom
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    (relativeInertia.forget F).hom =
      StackOver.Setoids.relativeInertia.forget (Hom.toSetoidsMor F) := sorry

/-- Forgetting to set-fibred categories recovers neutral relative-inertia forgetting directly. -/
@[simp, stacks 042H "underlying set-fibred relative-inertia forgetful morphism"]
theorem relativeInertia.forget.toSets
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    Hom.toSetsMor (relativeInertia.forget F) =
      FiberedCategoryOver.Sets.RelativeInertia.forget (Hom.toSetsMor F) := sorry

/-- The based functor underlying relative-inertia forgetting is the neutral forgetful map. -/
@[simp]
theorem relativeInertia.forget.toBasedFunctor
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    Hom.toBasedFunctor (relativeInertia.forget F) =
      BasedCategory.RelativeInertia.forget (Hom.toBasedFunctor F) := sorry

/-- Equip every source object with its identity relative automorphism. -/
@[stacks 04Z3 "set-stack relative-inertia neutral section"]
def relativeInertia.identitySection
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    X ⟶ relativeInertia F :=
  Hom.lift (StackOver.Setoids.relativeInertia.identitySection
    (Hom.toSetoidsMor F))

/-- The underlying setoid-stack morphism is the neutral relative identity section. -/
@[simp]
theorem relativeInertia.identitySection.hom
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    (relativeInertia.identitySection F).hom =
      StackOver.Setoids.relativeInertia.identitySection
        (Hom.toSetoidsMor F) := sorry

/-- Forgetting to set-fibred categories recovers the neutral relative identity section after
the canonical identification of relative-inertia targets. -/
@[simp, stacks 04Z3 "underlying set-fibred relative-inertia identity section"]
theorem relativeInertia.identitySection.toSets
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    Hom.toSetsMor (relativeInertia.identitySection F) ≫
        eqToHom (relativeInertia.toSets F) =
      FiberedCategoryOver.Sets.RelativeInertia.identitySection (Hom.toSetsMor F) := sorry

/-- The based functor underlying the relative identity section is the neutral section. -/
@[simp]
theorem relativeInertia.identitySection.toBasedFunctor
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    Hom.toBasedFunctor (relativeInertia.identitySection F) =
      BasedCategory.RelativeInertia.identitySection
        (Hom.toBasedFunctor F) := sorry

/-- Retain a relative automorphism as an absolute automorphism. -/
@[stacks 04Z5 "set-stack relative-to-absolute inertia comparison"]
def relativeInertia.toInertia
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    relativeInertia F ⟶ inertia X :=
  Hom.lift (StackOver.Setoids.relativeInertia.toInertia
    (Hom.toSetoidsMor F))

/-- The underlying setoid-stack morphism is the neutral relative-to-absolute comparison. -/
@[simp]
theorem relativeInertia.toInertia.hom
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    (relativeInertia.toInertia F).hom =
      StackOver.Setoids.relativeInertia.toInertia (Hom.toSetoidsMor F) := sorry

/-- Forgetting to set-fibred categories recovers the neutral relative-to-absolute inertia map
directly. -/
@[simp, stacks 04Z5 "underlying set-fibred relative-to-absolute inertia map"]
theorem relativeInertia.toInertia.toSets
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    Hom.toSetsMor (relativeInertia.toInertia F) =
      FiberedCategoryOver.Sets.RelativeInertia.toInertia (Hom.toSetsMor F) := sorry

/-- An invertibly commuting square of set-stack morphisms induces a map on relative inertia. -/
@[stacks 04Z4 "set-stack relative-inertia square map"]
def relativeInertia.map
    {X₁ X₁' X₂ X₂' : StackOver.Sets.{u, v, max w vS, vS} J}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    relativeInertia F₁ ⟶ relativeInertia F₂ :=
  Hom.lift (StackOver.Setoids.relativeInertia.map
    (Hom.toSetoidsMor G) (Hom.toSetoidsMor G')
    (Bicategory.InducedBicategory.Iso.toAmbient comm))

/-- The underlying setoid-stack morphism is the square-induced relative-inertia map. -/
@[simp]
theorem relativeInertia.map.hom
    {X₁ X₁' X₂ X₂' : StackOver.Sets.{u, v, max w vS, vS} J}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    (relativeInertia.map G G' comm).hom =
      StackOver.Setoids.relativeInertia.map
        (Hom.toSetoidsMor G) (Hom.toSetoidsMor G')
        (Bicategory.InducedBicategory.Iso.toAmbient comm) := sorry

/-- The based functor underlying the relative-inertia square map is the neutral square-induced
map of based categories. -/
@[simp, stacks 04Z4 "based relative-inertia square map"]
theorem relativeInertia.map.toBasedFunctor
    {X₁ X₁' X₂ X₂' : StackOver.Sets.{u, v, max w vS, vS} J}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    Hom.toBasedFunctor (relativeInertia.map G G' comm) =
      BasedCategory.RelativeInertia.map
        (Hom.toBasedFunctor G) (Hom.toBasedFunctor G')
        (Hom.toBasedFunctorIso comm) := sorry

/-- The set-stack relative identity section is a right inverse to forgetting. -/
@[simp]
theorem relativeInertia.identitySection.comp_forget
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    relativeInertia.identitySection F ≫ relativeInertia.forget F = 𝟙 X := sorry

/-- Discrete fibres make relative-inertia forgetting a left inverse to the identity section. -/
@[simp]
theorem relativeInertia.forget.comp_identitySection
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    relativeInertia.forget F ≫ relativeInertia.identitySection F =
      𝟙 (relativeInertia F) := sorry

/-- Relative inertia of a set-stack morphism is canonically equivalent to its source. -/
@[stacks 04Z3 "set-stack relative-inertia equivalence"]
def relativeInertia.forget.equivalence
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    relativeInertia F ≌ X :=
  ObjectProperty.FullSubbicategory.equivalenceOfAmbient
    (StackOver.Setoids.relativeInertia.forget.equivalence (Hom.toSetoidsMor F))

/-- A relative-inertia square map commutes with forgetting to its source. -/
@[simp]
theorem relativeInertia.map.comp_forget
    {X₁ X₁' X₂ X₂' : StackOver.Sets.{u, v, max w vS, vS} J}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    relativeInertia.map G G' comm ≫ relativeInertia.forget F₂ =
      relativeInertia.forget F₁ ≫ G := sorry

/-- Relative identity sections are compatible with square-induced maps. -/
@[simp]
theorem relativeInertia.identitySection.comp_map
    {X₁ X₁' X₂ X₂' : StackOver.Sets.{u, v, max w vS, vS} J}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    relativeInertia.identitySection F₁ ≫ relativeInertia.map G G' comm =
      G ≫ relativeInertia.identitySection F₂ := sorry

end StackOver.Sets

end CategoryTheory
