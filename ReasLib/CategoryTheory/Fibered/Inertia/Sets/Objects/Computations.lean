/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.Objects.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Set-fibred inertia object computations

This leaf exposes the neutral based-category, total-category, and projection
readouts for bundled set-fibred inertia objects.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Sets

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Sets.{u, v, w, vS} C}

/-- Forgetting the set-fibration owner from relative inertia recovers neutral based relative
inertia. -/
@[simp, stacks 034I "relative inertia set-fibration owner computation"]
theorem relativeInertia.toBasedCategory (F : X ⟶ Y) :
    (relativeInertia F).toBasedCategory =
      BasedCategory.relativeInertia (toBasedFunctor F) := sorry

/-- The total category of set-fibred relative inertia is the neutral relative-inertia
category. -/
@[simp, stacks 034I "relative inertia set-fibration total category"]
theorem relativeInertia.total (F : X ⟶ Y) :
    (relativeInertia F).total = RelativeInertia (toFunctor F) := sorry

/-- The projection of set-fibred relative inertia is the neutral relative-inertia projection. -/
@[simp, stacks 034I "relative inertia set-fibration projection"]
theorem relativeInertia.p (F : X ⟶ Y) :
    (relativeInertia F).p =
      RelativeInertia.projection (toFunctor F) X.p := sorry

/-- The set-fibred relative-inertia projection sends an object to the base of its underlying
object. -/
@[simp, stacks 034I "relative inertia set-fibration projection on objects"]
theorem relativeInertia.p.obj (F : X ⟶ Y) (A : (relativeInertia F).total) :
    (relativeInertia F).p.obj A = X.p.obj A.obj := sorry

/-- The set-fibred relative-inertia projection sends an arrow to the base of its underlying
inertia arrow. -/
@[simp, stacks 034I "relative inertia set-fibration projection on arrows"]
theorem relativeInertia.p.map (F : X ⟶ Y)
    {A B : (relativeInertia F).total} (φ : A ⟶ B) :
    (relativeInertia F).p.map φ = X.p.map (CategoryTheory.RelativeInertia.hom φ) := sorry

/-- Forgetting the set-fibration owner from absolute inertia recovers neutral based inertia. -/
@[simp, stacks 034I "absolute inertia set-fibration owner computation"]
theorem inertia.toBasedCategory
    (X : FiberedCategoryOver.Sets.{u, v, w, vS} C) :
    (inertia X).toBasedCategory = BasedCategory.inertia X.toBasedCategory := sorry

/-- The total category of set-fibred absolute inertia is the category of vertical
automorphisms. -/
@[simp, stacks 034I "absolute inertia set-fibration total category"]
theorem inertia.total (X : FiberedCategoryOver.Sets.{u, v, w, vS} C) :
    (inertia X).total = RelativeInertia X.p := sorry

/-- The projection of set-fibred absolute inertia is the neutral self-relative-inertia
projection. -/
@[simp, stacks 034I "absolute inertia set-fibration projection"]
theorem inertia.p (X : FiberedCategoryOver.Sets.{u, v, w, vS} C) :
    (inertia X).p = RelativeInertia.projection X.p X.p := sorry

/-- The set-fibred absolute-inertia projection sends an object to the base of its underlying
object. -/
@[simp, stacks 034I "absolute inertia set-fibration projection on objects"]
theorem inertia.p.obj
    (X : FiberedCategoryOver.Sets.{u, v, w, vS} C)
    (A : (inertia X).total) :
    (inertia X).p.obj A = X.p.obj A.obj := sorry

/-- The set-fibred absolute-inertia projection sends an arrow to the base of its underlying
inertia arrow. -/
@[simp, stacks 034I "absolute inertia set-fibration projection on arrows"]
theorem inertia.p.map
    (X : FiberedCategoryOver.Sets.{u, v, w, vS} C)
    {A B : (inertia X).total} (φ : A ⟶ B) :
    (inertia X).p.map φ = X.p.map (CategoryTheory.RelativeInertia.hom φ) := sorry

end FiberedCategoryOver.Sets

end CategoryTheory
