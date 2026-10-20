/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Square.Routes.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphism computations for routes in the relative-inertia square

This leaf records the action on morphisms of the three canonical routes. Object and
automorphism formulas are kept in `Routes.ObjectComputations`.
-/

@[expose] public section

universe u v uX vX uY vY

namespace CategoryTheory
namespace BasedCategory

open BasedNatIso BasedNatTrans
open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

namespace RelativeInertia
namespace Square

/-- The target projection applies `F` to the underlying morphism of a relative-inertia
morphism. -/
@[simp, stacks 04Z6 "relative-inertia square target-route morphism computation"]
theorem toTarget.map
    (F : X ⥤ᵇ Y) {Z Z' : CategoryTheory.RelativeInertia F.toFunctor} (f : Z ⟶ Z') :
    (toTarget F).toFunctor.map f =
      F.toFunctor.map (CategoryTheory.RelativeInertia.hom f) := sorry

/-- The target route applies `F` to the underlying morphism of a relative-inertia
morphism. -/
@[simp, stacks 04Z6 "relative-inertia square target-route underlying morphism"]
theorem viaTarget.hom
    (F : X ⥤ᵇ Y) {Z Z' : CategoryTheory.RelativeInertia F.toFunctor} (f : Z ⟶ Z') :
    CategoryTheory.RelativeInertia.hom ((viaTarget F).toFunctor.map f) =
      F.toFunctor.map (CategoryTheory.RelativeInertia.hom f) := sorry

/-- The source route applies `F` to the underlying morphism of a relative-inertia
morphism. -/
@[simp, stacks 04Z6 "relative-inertia square source-route underlying morphism"]
theorem viaSource.hom
    (F : X ⥤ᵇ Y) {Z Z' : CategoryTheory.RelativeInertia F.toFunctor} (f : Z ⟶ Z') :
    CategoryTheory.RelativeInertia.hom ((viaSource F).toFunctor.map f) =
      F.toFunctor.map (CategoryTheory.RelativeInertia.hom f) := sorry

end Square
end RelativeInertia
end BasedCategory
end CategoryTheory
