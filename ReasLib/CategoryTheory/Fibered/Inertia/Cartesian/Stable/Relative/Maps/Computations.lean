/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Relative.Maps.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Relative.Computations

/-!
# Computations for stable cartesian relative-inertia maps

This leaf exposes based and total projections together with object, automorphism, and arrow
formulas for the relative-inertia forgetful map and identity section.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, max w vS, vS} C}

/-- Forgetting the fibred structure from the relative-inertia structure map recovers the
canonical based forgetful map. -/
@[simp, stacks 042H "cartesian relative-inertia forgetful based readout"]
theorem forget.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedFunctor (forget F) =
      BasedCategory.RelativeInertia.forget
        (FiberedCategoryOver.toBasedFunctor F) := sorry

/-- The total functor of cartesian relative-inertia forgetting is the neutral forgetful functor. -/
@[simp, stacks 042H "cartesian relative-inertia forgetful total readout"]
theorem forget.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toFunctor (forget F) =
      CategoryTheory.RelativeInertia.forget
        (FiberedCategoryOver.toFunctor F) := sorry

/-- Forgetting a relative-inertia object returns its underlying source object. -/
@[simp, stacks 042H "cartesian relative-inertia forgetful object readout"]
theorem forget.obj
    (F : X ⟶ Y) (A : (FiberedCategoryOver.relativeInertia F).total) :
    (FiberedCategoryOver.toFunctor (forget F)).obj A = A.obj := sorry

/-- Forgetting a relative-inertia morphism returns its underlying source arrow. -/
@[simp, stacks 042H "cartesian relative-inertia forgetful arrow readout"]
theorem forget.map
    (F : X ⟶ Y) {A B : (FiberedCategoryOver.relativeInertia F).total} (f : A ⟶ B) :
    (FiberedCategoryOver.toFunctor (forget F)).map f =
      CategoryTheory.RelativeInertia.hom f := sorry

/-- Forgetting the fibred structure from the relative identity section recovers the canonical
based section. -/
@[simp, stacks 04Z3 "cartesian relative-inertia identity-section based readout"]
theorem identitySection.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedFunctor (identitySection F) =
      BasedCategory.RelativeInertia.identitySection
        (FiberedCategoryOver.toBasedFunctor F) := sorry

/-- The total functor of the cartesian relative identity section is the neutral section. -/
@[simp, stacks 04Z3 "cartesian relative-inertia identity-section total readout"]
theorem identitySection.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toFunctor (identitySection F) =
      CategoryTheory.RelativeInertia.identitySection
        (FiberedCategoryOver.toFunctor F) := sorry

/-- The relative identity section retains each source object. -/
@[simp, stacks 04Z3 "cartesian relative-inertia identity-section object readout"]
theorem identitySection.obj (F : X ⟶ Y) (x : X.total) :
    ((FiberedCategoryOver.toFunctor (identitySection F)).obj x).obj = x := sorry

/-- The relative identity section selects the identity automorphism. -/
@[simp, stacks 04Z3 "cartesian relative-inertia identity-section automorphism readout"]
theorem identitySection.aut (F : X ⟶ Y) (x : X.total) :
    ((FiberedCategoryOver.toFunctor (identitySection F)).obj x).aut = 1 := sorry

/-- The relative identity section retains the arrow underlying each morphism. -/
@[simp, stacks 04Z3 "cartesian relative-inertia identity-section arrow readout"]
theorem identitySection.hom
    (F : X ⟶ Y) {x y : X.total} (f : x ⟶ y) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.toFunctor (identitySection F)).map f) = f := sorry

end FiberedCategoryOver.RelativeInertia

end CategoryTheory
