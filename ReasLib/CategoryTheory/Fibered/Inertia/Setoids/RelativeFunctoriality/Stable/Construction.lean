module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.RelativeFunctoriality.Map.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Equivalence.Construction
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-! Stable-universe setoid-fibred relative inertia. -/

@[expose] public section

universe u v vS w

namespace CategoryTheory
open BasedCategory BasedFunctor
namespace FiberedCategoryOver.Setoids
open scoped Bicategory
variable {C : Type u} [Category.{v} C]
namespace RelativeInertia
variable {X Y : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C}

/-- Forget the selected relative automorphism. For a morphism between categories fibred in
setoids, this remains a morphism in the same stable-universe owner. -/
@[stacks 042H "setoid-fibred relative-inertia structure map"]
def forget (F : X ⟶ Y) :
    FiberedCategoryOver.Setoids.relativeInertia F ⟶ X :=
  FiberedCategoryOver.Setoids.ofBasedFunctor
    (BasedCategory.RelativeInertia.forget
      (FiberedCategoryOver.Setoids.toBasedFunctor F))

/-- Equip every source object with the identity relative automorphism. -/
@[stacks 04Z3 "setoid-fibred relative-inertia neutral section"]
def identitySection (F : X ⟶ Y) :
    X ⟶ FiberedCategoryOver.Setoids.relativeInertia F :=
  FiberedCategoryOver.Setoids.ofBasedFunctor
    (BasedCategory.RelativeInertia.identitySection
      (FiberedCategoryOver.Setoids.toBasedFunctor F))

/- Axiom audit: the non-Prop data of `forget`, `identitySection`, and
`forget.equivalence` are inherited from the neutral based relative-inertia maps. Thinness is
used only in the theorem identifying the other composite with the identity. -/

/-- Relative inertia of a morphism between categories fibred in setoids is canonically
equivalent to its source. This is the relative generalization of triviality of absolute inertia
for setoid-valued fibres. -/
@[stacks 04Z3 "setoid-fibred relative-inertia equivalence"]
def forget.equivalence (F : X ⟶ Y) :
    FiberedCategoryOver.Setoids.relativeInertia F ≌ X :=
  ObjectProperty.FullSubbicategory.equivalenceOfAmbient
    (BasedCategory.RelativeInertia.forget.equivalenceOf
      (FiberedCategoryOver.Setoids.toBasedFunctor F) X.2)

end RelativeInertia
end FiberedCategoryOver.Setoids
end CategoryTheory
