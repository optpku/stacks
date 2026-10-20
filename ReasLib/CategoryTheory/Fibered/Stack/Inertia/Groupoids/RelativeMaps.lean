module

public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Groupoids.Comparisons
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative inertia maps of groupoid stacks

Structure maps and square functoriality for relative inertia, with computations directly on the
underlying groupoid-fibred morphisms.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Groupoids.relativeInertia

variable {X Y : StackOver.Groupoids.{u, v, max w vS, vS} J}

/-- Forget the selected relative automorphism from bundled groupoid relative inertia. -/
@[stacks 042H "groupoid-stack relative-inertia structure map"]
def forget (F : X ⟶ Y) : relativeInertia F ⟶ X :=
  Hom.lift (FiberedCategoryOver.Groupoids.RelativeInertia.forget (Hom.toGroupoidsMor F))

/-- The underlying groupoid-fibred morphism is neutral relative-inertia forgetting. -/
@[simp, stacks 042H "underlying relative-inertia forgetful morphism"]
theorem forget.hom (F : X ⟶ Y) :
    (forget F).hom =
      FiberedCategoryOver.Groupoids.RelativeInertia.forget (Hom.toGroupoidsMor F) := sorry

/-- The based functor underlying relative-inertia forgetting is the neutral based forgetful
map. -/
@[simp, stacks 042H "based relative-inertia forgetful morphism"]
theorem forget.toBasedFunctor (F : X ⟶ Y) :
    Hom.toBasedFunctor (forget F) =
      BasedCategory.RelativeInertia.forget (Hom.toBasedFunctor F) := sorry

/-- Equip every source object with its identity relative automorphism. -/
@[stacks 04Z3 "groupoid-stack relative-inertia neutral section"]
def identitySection (F : X ⟶ Y) : X ⟶ relativeInertia F :=
  Hom.lift (FiberedCategoryOver.Groupoids.RelativeInertia.identitySection
    (Hom.toGroupoidsMor F))

/-- The underlying groupoid-fibred morphism is the canonical neutral section. -/
@[simp, stacks 04Z3 "underlying relative-inertia identity section"]
theorem identitySection.hom (F : X ⟶ Y) :
    (identitySection F).hom =
      FiberedCategoryOver.Groupoids.RelativeInertia.identitySection
        (Hom.toGroupoidsMor F) := sorry

/-- The based functor underlying the relative identity section is the neutral based section. -/
@[simp, stacks 04Z3 "based relative-inertia identity section"]
theorem identitySection.toBasedFunctor (F : X ⟶ Y) :
    Hom.toBasedFunctor (identitySection F) =
      BasedCategory.RelativeInertia.identitySection (Hom.toBasedFunctor F) := sorry

/-- Retain a selected relative automorphism as an absolute automorphism. -/
@[stacks 04Z5 "groupoid-stack relative-to-absolute inertia comparison"]
def toInertia (F : X ⟶ Y) : relativeInertia F ⟶ inertia X :=
  Hom.lift (FiberedCategoryOver.Groupoids.RelativeInertia.toInertia
    (Hom.toGroupoidsMor F))

/-- The underlying groupoid-fibred morphism is the neutral relative-to-absolute comparison. -/
@[simp, stacks 04Z5 "underlying relative-to-absolute inertia map"]
theorem toInertia.hom (F : X ⟶ Y) :
    (toInertia F).hom =
      FiberedCategoryOver.Groupoids.RelativeInertia.toInertia
        (Hom.toGroupoidsMor F) := sorry

/-- The based functor underlying the relative-to-absolute comparison is the neutral based
comparison. -/
@[simp, stacks 04Z5 "based relative-to-absolute inertia map"]
theorem toInertia.toBasedFunctor (F : X ⟶ Y) :
    Hom.toBasedFunctor (toInertia F) =
      BasedCategory.RelativeInertia.toInertia (Hom.toBasedFunctor F) := sorry

/-- An invertibly commuting square of groupoid-stack morphisms induces a map on relative
inertia. -/
@[stacks 04Z4 "groupoid-stack relative-inertia square map"]
def map
    {X₁ X₁' X₂ X₂' : StackOver.Groupoids.{u, v, max w vS, vS} J}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    relativeInertia F₁ ⟶ relativeInertia F₂ :=
  Hom.lift (FiberedCategoryOver.Groupoids.RelativeInertia.map
    (Hom.toGroupoidsMor G) (Hom.toGroupoidsMor G')
    (Bicategory.InducedBicategory.Iso.toAmbient comm))

/-- The underlying groupoid-fibred morphism is the neutral square-induced map. -/
@[simp, stacks 04Z4 "underlying relative-inertia square map"]
theorem map.hom
    {X₁ X₁' X₂ X₂' : StackOver.Groupoids.{u, v, max w vS, vS} J}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    (map G G' comm).hom =
      FiberedCategoryOver.Groupoids.RelativeInertia.map
        (Hom.toGroupoidsMor G) (Hom.toGroupoidsMor G')
        (Bicategory.InducedBicategory.Iso.toAmbient comm) := sorry

/-- The based functor underlying the relative-inertia square map is the neutral square-induced
map of based categories. -/
@[simp, stacks 04Z4 "based relative-inertia square map"]
theorem map.toBasedFunctor
    {X₁ X₁' X₂ X₂' : StackOver.Groupoids.{u, v, max w vS, vS} J}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    Hom.toBasedFunctor (map G G' comm) =
      BasedCategory.RelativeInertia.map
        (Hom.toBasedFunctor G) (Hom.toBasedFunctor G')
        (Hom.toBasedFunctorIso comm) := sorry

/-- The groupoid-stack relative identity section is a right inverse to forgetting. -/
@[simp, stacks 04Z3 "groupoid-stack relative-inertia identity-section round trip"]
theorem identitySection.comp_forget (F : X ⟶ Y) :
    identitySection F ≫ forget F = 𝟙 X := sorry

/-- A relative-inertia square map commutes with forgetting to its source. -/
@[simp, stacks 04Z4 "groupoid-stack relative-inertia square forgetful compatibility"]
theorem map.comp_forget
    {X₁ X₁' X₂ X₂' : StackOver.Groupoids.{u, v, max w vS, vS} J}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    map G G' comm ≫ forget F₂ = forget F₁ ≫ G := sorry

/-- Relative identity sections are compatible with square-induced maps. -/
@[simp, stacks 04Z4 "groupoid-stack relative-inertia square identity compatibility"]
theorem identitySection.comp_map
    {X₁ X₁' X₂ X₂' : StackOver.Groupoids.{u, v, max w vS, vS} J}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    identitySection F₁ ≫ map G G' comm = G ≫ identitySection F₂ := sorry

end StackOver.Groupoids.relativeInertia

end CategoryTheory
