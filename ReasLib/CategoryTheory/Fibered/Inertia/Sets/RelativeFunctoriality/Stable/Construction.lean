module

public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.RelativeFunctoriality.Map.Construction
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Equivalence
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Equivalence.Construction
public import ReasLib.CategoryTheory.Fibered.Setoids.FromSets
import Mathlib.Tactic.CrossRefAttribute

/-! Stable-universe set-fibred relative inertia. -/

@[expose] public section

universe u v vS w

namespace CategoryTheory
open BasedCategory BasedFunctor
namespace FiberedCategoryOver.Sets
open scoped Bicategory
variable {C : Type u} [Category.{v} C]
namespace RelativeInertia
variable {X Y : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C}

/-- Forget the selected relative automorphism. -/
@[stacks 042H "set-fibred relative-inertia structure map"]
def forget (F : X ⟶ Y) : FiberedCategoryOver.Sets.relativeInertia F ⟶ X :=
  FiberedCategoryOver.Sets.ofBasedFunctor
    (BasedCategory.RelativeInertia.forget
      (FiberedCategoryOver.Sets.toBasedFunctor F))

/-- Equip every source object with its identity relative automorphism. -/
@[stacks 04Z3 "set-fibred relative-inertia neutral section"]
def identitySection (F : X ⟶ Y) :
    X ⟶ FiberedCategoryOver.Sets.relativeInertia F :=
  FiberedCategoryOver.Sets.ofBasedFunctor
    (BasedCategory.RelativeInertia.identitySection
      (FiberedCategoryOver.Sets.toBasedFunctor F))

/-- Relative inertia of a set-fibred morphism is canonically equivalent to its source. -/
@[stacks 04Z3 "set-fibred relative-inertia equivalence"]
def forget.equivalence (F : X ⟶ Y) :
    FiberedCategoryOver.Sets.relativeInertia F ≌ X :=
  ObjectProperty.FullSubbicategory.equivalenceOfAmbient
    (BasedCategory.RelativeInertia.forget.equivalenceOf
      (FiberedCategoryOver.Sets.toBasedFunctor F)
      (BasedCategory.isFiberedInSets.le_isFiberedInSetoids X.toBasedCategory X.2))

end RelativeInertia
end FiberedCategoryOver.Sets
end CategoryTheory
