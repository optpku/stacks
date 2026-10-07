module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Objects.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Setoid-fibred inertia object computations

This leaf exposes the neutral based-category, total-category, and projection
readouts for bundled setoid-fibred inertia objects.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.Setoids

open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Setoids.{u, v, w, vS} C}

/-- Forgetting the setoid-fibration owner from relative inertia recovers the neutral based
construction. -/
@[simp, stacks 034I "relative inertia setoid-fibration owner computation"]
theorem relativeInertia.toBasedCategory (F : X ⟶ Y) :
    (relativeInertia F).toBasedCategory =
      BasedCategory.relativeInertia (toBasedFunctor F) := sorry

/-- The total category of setoid-fibred relative inertia is the neutral relative-inertia
category. -/
@[simp, stacks 034I "relative inertia setoid-fibration total category"]
theorem relativeInertia.total (F : X ⟶ Y) :
    (relativeInertia F).total =
      CategoryTheory.RelativeInertia (toFunctor F) := sorry

/-- The projection of setoid-fibred relative inertia is the neutral relative-inertia
projection. -/
@[simp, stacks 034I "relative inertia setoid-fibration projection"]
theorem relativeInertia.p (F : X ⟶ Y) :
    (relativeInertia F).p =
      CategoryTheory.RelativeInertia.projection (toFunctor F) X.p := sorry

/-- The setoid-fibred relative-inertia projection sends an object to the base of its underlying
object. -/
@[simp, stacks 034I "relative inertia setoid-fibration projection on objects"]
theorem relativeInertia.p.obj (F : X ⟶ Y) (A : (relativeInertia F).total) :
    (relativeInertia F).p.obj A = X.p.obj A.obj := sorry

/-- The setoid-fibred relative-inertia projection sends an arrow to the base of its underlying
inertia arrow. -/
@[simp, stacks 034I "relative inertia setoid-fibration projection on arrows"]
theorem relativeInertia.p.map (F : X ⟶ Y)
    {A B : (relativeInertia F).total} (φ : A ⟶ B) :
    (relativeInertia F).p.map φ = X.p.map (CategoryTheory.RelativeInertia.hom φ) := sorry

/-- Forgetting the setoid-fibre refinement from relative inertia recovers the general fibred
relative-inertia owner applied to the forgotten morphism. -/
@[simp, stacks 034I "relative inertia setoid-fibration forgetful computation"]
theorem relativeInertia.toFibered (F : X ⟶ Y) :
    (FiberedCategoryOver.Setoids.toFibered C).obj (relativeInertia F) =
      FiberedCategoryOver.relativeInertia
        ((FiberedCategoryOver.Setoids.toFibered C).map F) := sorry

/-- Forgetting the setoid-fibration owner from absolute inertia recovers neutral based
inertia. -/
@[simp, stacks 034I "absolute inertia setoid-fibration owner computation"]
theorem inertia.toBasedCategory
    (X : FiberedCategoryOver.Setoids.{u, v, w, vS} C) :
    (inertia X).toBasedCategory =
      BasedCategory.inertia X.toBasedCategory := sorry

/-- The total category of setoid-fibred absolute inertia is the category of vertical
automorphisms in the source. -/
@[simp, stacks 034I "absolute inertia setoid-fibration total category"]
theorem inertia.total
    (X : FiberedCategoryOver.Setoids.{u, v, w, vS} C) :
    (inertia X).total = CategoryTheory.RelativeInertia X.p := sorry

/-- The projection of setoid-fibred absolute inertia is the neutral self-relative-inertia
projection. -/
@[simp, stacks 034I "absolute inertia setoid-fibration projection"]
theorem inertia.p
    (X : FiberedCategoryOver.Setoids.{u, v, w, vS} C) :
    (inertia X).p =
      CategoryTheory.RelativeInertia.projection X.p X.p := sorry

/-- The setoid-fibred absolute-inertia projection sends an object to the base of its underlying
object. -/
@[simp, stacks 034I "absolute inertia setoid-fibration projection on objects"]
theorem inertia.p.obj
    (X : FiberedCategoryOver.Setoids.{u, v, w, vS} C)
    (A : (inertia X).total) :
    (inertia X).p.obj A = X.p.obj A.obj := sorry

/-- The setoid-fibred absolute-inertia projection sends an arrow to the base of its underlying
inertia arrow. -/
@[simp, stacks 034I "absolute inertia setoid-fibration projection on arrows"]
theorem inertia.p.map
    (X : FiberedCategoryOver.Setoids.{u, v, w, vS} C)
    {A B : (inertia X).total} (φ : A ⟶ B) :
    (inertia X).p.map φ = X.p.map (CategoryTheory.RelativeInertia.hom φ) := sorry

/-- Forgetting the setoid-fibre refinement from absolute inertia recovers the general fibred
absolute-inertia owner. -/
@[simp, stacks 034I "absolute inertia setoid-fibration forgetful computation"]
theorem inertia.toFibered
    (X : FiberedCategoryOver.Setoids.{u, v, w, vS} C) :
    (FiberedCategoryOver.Setoids.toFibered C).obj (inertia X) =
      FiberedCategoryOver.inertia
        ((FiberedCategoryOver.Setoids.toFibered C).obj X) := sorry

end FiberedCategoryOver.Setoids

end CategoryTheory
