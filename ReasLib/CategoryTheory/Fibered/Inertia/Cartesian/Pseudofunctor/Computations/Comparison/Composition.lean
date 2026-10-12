/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Computations.Action
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Absolute.Comparisons.Composition

/-!
# Composition comparison computations for fibred inertia

This leaf identifies the ordinary pseudofunctor composition comparison with its canonical
cartesian owner and exposes both directions down to underlying total-category arrows.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

/-- The ordinary composition comparison is the canonical lifted composition isomorphism. -/
@[simp]
theorem pseudofunctor.mapComp
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    (pseudofunctor C).mapComp F G = mapCompIso F G := sorry

/-- The forward composition comparison of fibred inertia is the underlying based cell. -/
@[simp]
theorem pseudofunctor.mapComp.hom.toBasedNatTrans
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    FiberedCategoryOver.toBasedNatTrans ((pseudofunctor C).mapComp F G).hom =
      (BasedCategory.Inertia.mapCompIso
        (FiberedCategoryOver.toBasedFunctor F)
        (FiberedCategoryOver.toBasedFunctor G)).hom := sorry

/-- The inverse composition comparison of fibred inertia is the underlying based cell. -/
@[simp]
theorem pseudofunctor.mapComp.inv.toBasedNatTrans
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    FiberedCategoryOver.toBasedNatTrans ((pseudofunctor C).mapComp F G).inv =
      (BasedCategory.Inertia.mapCompIso
        (FiberedCategoryOver.toBasedFunctor F)
        (FiberedCategoryOver.toBasedFunctor G)).inv := sorry

/-- The forward composition comparison component is the canonical neutral component. -/
@[simp]
theorem pseudofunctor.mapComp.hom.app
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.toNatTrans ((pseudofunctor C).mapComp F G).hom).app A =
      (BasedCategory.Inertia.mapCompIso.app
        (FiberedCategoryOver.toBasedFunctor F)
        (FiberedCategoryOver.toBasedFunctor G) A).hom := sorry

/-- The inverse composition comparison component is the canonical neutral component. -/
@[simp]
theorem pseudofunctor.mapComp.inv.app
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.toNatTrans ((pseudofunctor C).mapComp F G).inv).app A =
      (BasedCategory.Inertia.mapCompIso.app
        (FiberedCategoryOver.toBasedFunctor F)
        (FiberedCategoryOver.toBasedFunctor G) A).inv := sorry

/-- The total-category arrow underlying a forward packaged composition component is an
identity. -/
@[simp]
theorem pseudofunctor.mapComp.hom.app.underlying
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z)
    (A : (FiberedCategoryOver.inertia X).total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans ((pseudofunctor C).mapComp F G).hom).app A) =
      𝟙 (((BasedCategory.Inertia.map
        (FiberedCategoryOver.toBasedFunctor F) ⋙
          BasedCategory.Inertia.map
            (FiberedCategoryOver.toBasedFunctor G)).obj A).obj) := sorry

/-- The total-category arrow underlying an inverse packaged composition component is an
identity. -/
@[simp]
theorem pseudofunctor.mapComp.inv.app.underlying
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z)
    (A : (FiberedCategoryOver.inertia X).total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans ((pseudofunctor C).mapComp F G).inv).app A) =
      𝟙 (((BasedCategory.Inertia.map
        (FiberedCategoryOver.toBasedFunctor F) ⋙
          BasedCategory.Inertia.map
            (FiberedCategoryOver.toBasedFunctor G)).obj A).obj) := sorry

end FiberedCategoryOver.Inertia

end CategoryTheory
