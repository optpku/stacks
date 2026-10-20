/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.RelativeFunctoriality.Map.Construction
import Mathlib.Tactic.CrossRefAttribute

/-! Stable-universe groupoid-fibred relative inertia. -/

@[expose] public section

universe u v vS w

namespace CategoryTheory
open BasedCategory BasedFunctor
namespace FiberedCategoryOver.Groupoids
open scoped Bicategory
variable {C : Type u} [Category.{v} C]
namespace RelativeInertia
variable {X Y : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C}

/-- Forget the selected relative automorphism. For a morphism between categories fibred in
groupoids, this remains a morphism in the same stable-universe owner. -/
@[stacks 042H "groupoid-fibred relative-inertia structure map"]
def forget (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.relativeInertia F ⟶ X :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    (BasedCategory.RelativeInertia.forget
      (FiberedCategoryOver.Groupoids.toBasedFunctor F))

/-- Equip every source object with the identity relative automorphism. -/
@[stacks 04Z3 "groupoid-fibred relative-inertia neutral section"]
def identitySection (F : X ⟶ Y) :
    X ⟶ FiberedCategoryOver.Groupoids.relativeInertia F :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    (BasedCategory.RelativeInertia.identitySection
      (FiberedCategoryOver.Groupoids.toBasedFunctor F))

/- Axiom audit: the non-Prop data of `forget` and `identitySection` are inherited from the
neutral based relative-inertia maps. No uniqueness of relative automorphisms is assumed, so only
the section-retraction composite below is exposed. -/

end RelativeInertia
end FiberedCategoryOver.Groupoids
end CategoryTheory
