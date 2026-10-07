module

public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Objects.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibred inertia object computations

This module exposes the canonical total-category, projection, and based-owner
readouts for bundled inertia objects.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

/-- The total category of bundled relative inertia is the neutral relative-inertia category. -/
@[simp, stacks 034I "fibred relative-inertia total category"]
theorem relativeInertia.total (F : X ⟶ Y) :
    (relativeInertia F).total = CategoryTheory.RelativeInertia (toFunctor F) := sorry
/- Proof strategy: unfold `relativeInertia` and `FiberedCategoryOver.ofFunctor`. -/

/-- The bundled relative-inertia projection is the neutral relative-inertia projection. -/
@[simp, stacks 034I "fibred relative-inertia projection"]
theorem relativeInertia.p (F : X ⟶ Y) :
    (relativeInertia F).p =
      CategoryTheory.RelativeInertia.projection (toFunctor F) X.p := sorry
/- Proof strategy: unfold `relativeInertia` and use `FiberedCategoryOver.ofFunctor.p`. -/

/-- The bundled relative-inertia projection sends an object to the base of its underlying object. -/
@[simp, stacks 034I "fibred relative-inertia projection on objects"]
theorem relativeInertia.p.obj (F : X ⟶ Y) (A : (relativeInertia F).total) :
    (relativeInertia F).p.obj A = X.p.obj A.obj := sorry
/- Proof strategy: rewrite `relativeInertia.p` and apply
`CategoryTheory.RelativeInertia.projection.obj`. -/

/-- The bundled relative-inertia projection sends an arrow to the base of its underlying inertia
arrow. -/
@[simp, stacks 034I "fibred relative-inertia projection on arrows"]
theorem relativeInertia.p.map (F : X ⟶ Y) {A B : (relativeInertia F).total} (φ : A ⟶ B) :
    (relativeInertia F).p.map φ = X.p.map (CategoryTheory.RelativeInertia.hom φ) := sorry
/- Proof strategy: rewrite `relativeInertia.p` and apply
`CategoryTheory.RelativeInertia.projection.map`. -/

/-- Forgetting the fibred structure on relative inertia recovers its canonical based-category
packaging. -/
@[simp, stacks 034I "fibred relative-inertia based owner"]
theorem relativeInertia.toBasedCategory (F : X ⟶ Y) :
    (relativeInertia F).toBasedCategory =
      BasedCategory.relativeInertia (toBasedFunctor F) := sorry
/- Proof strategy: apply `BasedCategory.ext`; the total category, category structure, and
projection are the same neutral relative-inertia data. -/

/-- Forgetting the fibred structure on absolute inertia recovers its canonical based-category
packaging. -/
@[simp, stacks 034I "fibred absolute-inertia based owner"]
theorem inertia.toBasedCategory (X : FiberedCategoryOver.{u, v, w, vS} C) :
    (inertia X).toBasedCategory =
      BasedCategory.inertia X.toBasedCategory := sorry
/- Proof strategy: apply `BasedCategory.ext`; both objects use the same total category, category
structure, and projection. -/

/-- The total category of fibred absolute inertia is the self-relative-inertia category of the
projection, so only vertical automorphisms occur. -/
@[simp, stacks 034I "fibred absolute-inertia total category"]
theorem inertia.total (X : FiberedCategoryOver.{u, v, w, vS} C) :
    (inertia X).total = CategoryTheory.RelativeInertia X.p := sorry
/- Proof strategy: combine `inertia.toBasedCategory` with `BasedCategory.inertia.obj`. -/

/-- The projection of fibred absolute inertia is the neutral self-relative-inertia projection. -/
@[simp, stacks 034I "fibred absolute-inertia projection"]
theorem inertia.p (X : FiberedCategoryOver.{u, v, w, vS} C) :
    (inertia X).p =
      CategoryTheory.RelativeInertia.projection X.p X.p := sorry
/- Proof strategy: combine `inertia.toBasedCategory` with `BasedCategory.inertia.p`. -/

/-- The bundled absolute-inertia projection sends an object to the base of its underlying object. -/
@[simp, stacks 034I "fibred absolute-inertia projection on objects"]
theorem inertia.p.obj (X : FiberedCategoryOver.{u, v, w, vS} C)
    (A : (inertia X).total) :
    (inertia X).p.obj A = X.p.obj A.obj := sorry
/- Proof strategy: rewrite `inertia.p` and apply
`CategoryTheory.RelativeInertia.projection.obj`. -/

/-- The bundled absolute-inertia projection sends an arrow to the base of its underlying inertia
arrow. -/
@[simp, stacks 034I "fibred absolute-inertia projection on arrows"]
theorem inertia.p.map (X : FiberedCategoryOver.{u, v, w, vS} C)
    {A B : (inertia X).total} (φ : A ⟶ B) :
    (inertia X).p.map φ = X.p.map (CategoryTheory.RelativeInertia.hom φ) := sorry
/- Proof strategy: rewrite `inertia.p` and apply
`CategoryTheory.RelativeInertia.projection.map`. -/

end FiberedCategoryOver
end CategoryTheory
