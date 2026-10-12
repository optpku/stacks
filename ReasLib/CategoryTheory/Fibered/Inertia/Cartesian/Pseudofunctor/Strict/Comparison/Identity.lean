/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Strict.Action
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Absolute.Comparisons.Identity

/-!
# Identity comparison computations for strict fibred inertia

This leaf identifies the strict identity comparison with its canonical cartesian owner and
exposes both directions down to underlying total-category arrows.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Inertia

variable {C : Type u} [Category.{v} C]

/-- The strict identity comparison is the canonical lifted identity isomorphism. -/
@[simp]
theorem strictPseudofunctor.mapId
    (X : FiberedCategoryOver.{u, v, w, vS} C) :
    (strictPseudofunctor C).mapId X = mapIdIso X := sorry

/-- The forward strict identity comparison is the neutral based identity comparison. -/
@[simp]
theorem strictPseudofunctor.mapId.hom.toBasedNatTrans
    (X : FiberedCategoryOver.{u, v, w, vS} C) :
    FiberedCategoryOver.toBasedNatTrans ((strictPseudofunctor C).mapId X).hom =
      (BasedCategory.Inertia.mapIdIso X.toBasedCategory).hom := sorry

/-- The inverse strict identity comparison is the neutral based identity comparison. -/
@[simp]
theorem strictPseudofunctor.mapId.inv.toBasedNatTrans
    (X : FiberedCategoryOver.{u, v, w, vS} C) :
    FiberedCategoryOver.toBasedNatTrans ((strictPseudofunctor C).mapId X).inv =
      (BasedCategory.Inertia.mapIdIso X.toBasedCategory).inv := sorry

/-- The forward strict identity comparison component is the canonical neutral component. -/
@[simp]
theorem strictPseudofunctor.mapId.hom.app
    (X : FiberedCategoryOver.{u, v, w, vS} C)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.toNatTrans ((strictPseudofunctor C).mapId X).hom).app A =
      (BasedCategory.Inertia.mapIdIso.app X.toBasedCategory A).hom := sorry

/-- The inverse strict identity comparison component is the canonical neutral component. -/
@[simp]
theorem strictPseudofunctor.mapId.inv.app
    (X : FiberedCategoryOver.{u, v, w, vS} C)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.toNatTrans ((strictPseudofunctor C).mapId X).inv).app A =
      (BasedCategory.Inertia.mapIdIso.app X.toBasedCategory A).inv := sorry

/-- The total-category arrow underlying a forward strict identity component is an identity. -/
@[simp]
theorem strictPseudofunctor.mapId.hom.app.underlying
    (X : FiberedCategoryOver.{u, v, w, vS} C)
    (A : (FiberedCategoryOver.inertia X).total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans
          ((strictPseudofunctor C).mapId X).hom).app A) =
      𝟙 A.obj := sorry

/-- The total-category arrow underlying an inverse strict identity component is an identity. -/
@[simp]
theorem strictPseudofunctor.mapId.inv.app.underlying
    (X : FiberedCategoryOver.{u, v, w, vS} C)
    (A : (FiberedCategoryOver.inertia X).total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans
          ((strictPseudofunctor C).mapId X).inv).app A) =
      𝟙 A.obj := sorry

end FiberedCategoryOver.Inertia

end CategoryTheory
