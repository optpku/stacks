/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Computations.Action
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Absolute.Comparisons.Identity

/-!
# Identity comparison computations for fibred inertia

This leaf identifies the ordinary pseudofunctor identity comparison with its canonical
cartesian owner and exposes both directions down to underlying total-category arrows.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Inertia

variable {C : Type u} [Category.{v} C]

/-- The ordinary identity comparison is the canonical lifted identity isomorphism. -/
@[simp]
theorem pseudofunctor.mapId
    (X : FiberedCategoryOver.{u, v, w, vS} C) :
    (pseudofunctor C).mapId X = mapIdIso X := sorry

/-- The forward identity comparison of fibred inertia is the underlying based comparison cell. -/
@[simp]
theorem pseudofunctor.mapId.hom.toBasedNatTrans
    (X : FiberedCategoryOver.{u, v, w, vS} C) :
    FiberedCategoryOver.toBasedNatTrans ((pseudofunctor C).mapId X).hom =
      (BasedCategory.Inertia.mapIdIso X.toBasedCategory).hom := sorry

/-- The inverse identity comparison of fibred inertia is the underlying based comparison cell. -/
@[simp]
theorem pseudofunctor.mapId.inv.toBasedNatTrans
    (X : FiberedCategoryOver.{u, v, w, vS} C) :
    FiberedCategoryOver.toBasedNatTrans ((pseudofunctor C).mapId X).inv =
      (BasedCategory.Inertia.mapIdIso X.toBasedCategory).inv := sorry

/-- The forward identity comparison component is the canonical neutral identity component. -/
@[simp]
theorem pseudofunctor.mapId.hom.app
    (X : FiberedCategoryOver.{u, v, w, vS} C)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.toNatTrans ((pseudofunctor C).mapId X).hom).app A =
      (BasedCategory.Inertia.mapIdIso.app X.toBasedCategory A).hom := sorry

/-- The inverse identity comparison component is the canonical neutral identity component. -/
@[simp]
theorem pseudofunctor.mapId.inv.app
    (X : FiberedCategoryOver.{u, v, w, vS} C)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.toNatTrans ((pseudofunctor C).mapId X).inv).app A =
      (BasedCategory.Inertia.mapIdIso.app X.toBasedCategory A).inv := sorry

/-- The total-category arrow underlying a forward packaged identity component is an identity. -/
@[simp]
theorem pseudofunctor.mapId.hom.app.underlying
    (X : FiberedCategoryOver.{u, v, w, vS} C)
    (A : (FiberedCategoryOver.inertia X).total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans ((pseudofunctor C).mapId X).hom).app A) =
      𝟙 A.obj := sorry

/-- The total-category arrow underlying an inverse packaged identity component is an identity. -/
@[simp]
theorem pseudofunctor.mapId.inv.app.underlying
    (X : FiberedCategoryOver.{u, v, w, vS} C)
    (A : (FiberedCategoryOver.inertia X).total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans ((pseudofunctor C).mapId X).inv).app A) =
      𝟙 A.obj := sorry

end FiberedCategoryOver.Inertia

end CategoryTheory
