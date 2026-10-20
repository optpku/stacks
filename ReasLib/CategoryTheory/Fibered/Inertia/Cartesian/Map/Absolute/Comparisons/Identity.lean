/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Absolute.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Comparison.Identity
import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity comparison for cartesian absolute inertia

This leaf owns the fibred identity comparison and its based, component, and underlying-arrow
readouts. Composition comparison is provided by the sibling `Composition` leaf.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Inertia

variable {C : Type u} [Category.{v} C]

/-- The explicit based identity comparison lifts canonically to an isomorphism of fibred inertia
morphisms. -/
def mapIdIso (X : FiberedCategoryOver.{u, v, w, vS} C) :
    map (𝟙 X) ≅ 𝟙 (FiberedCategoryOver.inertia X) :=
  FiberedCategoryOver.BasedFunctorIso.lift
    (BasedCategory.Inertia.mapIdIso X.toBasedCategory)

namespace mapIdIso

/-- Forgetting the forward fibred identity-comparison cell recovers the explicit based comparison. -/
@[simp]
theorem hom.toBasedNatTrans
    (X : FiberedCategoryOver.{u, v, w, vS} C) :
    FiberedCategoryOver.toBasedNatTrans (mapIdIso X).hom =
      (BasedCategory.Inertia.mapIdIso X.toBasedCategory).hom := sorry

/-- Forgetting the inverse fibred identity-comparison cell recovers the explicit based comparison. -/
@[simp]
theorem inv.toBasedNatTrans
    (X : FiberedCategoryOver.{u, v, w, vS} C) :
    FiberedCategoryOver.toBasedNatTrans (mapIdIso X).inv =
      (BasedCategory.Inertia.mapIdIso X.toBasedCategory).inv := sorry

/-- The forward component of the fibred identity comparison is the explicit based component. -/
@[simp]
theorem hom.app
    (X : FiberedCategoryOver.{u, v, w, vS} C)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.toNatTrans (mapIdIso X).hom).app A =
      (BasedCategory.Inertia.mapIdIso.app X.toBasedCategory A).hom := sorry

/-- The inverse component of the fibred identity comparison is the explicit based component. -/
@[simp]
theorem inv.app
    (X : FiberedCategoryOver.{u, v, w, vS} C)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.toNatTrans (mapIdIso X).inv).app A =
      (BasedCategory.Inertia.mapIdIso.app X.toBasedCategory A).inv := sorry

/-- Every forward fibred identity-comparison component lies over the identity of its base
object. -/
theorem hom.app.isHomLift
    (X : FiberedCategoryOver.{u, v, w, vS} C)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.inertia X).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.inertia X).p.obj A))
      ((FiberedCategoryOver.toNatTrans (mapIdIso X).hom).app A) := sorry

/-- Every inverse fibred identity-comparison component lies over the identity of its base
object. -/
theorem inv.app.isHomLift
    (X : FiberedCategoryOver.{u, v, w, vS} C)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.inertia X).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.inertia X).p.obj A))
      ((FiberedCategoryOver.toNatTrans (mapIdIso X).inv).app A) := sorry

/-- The total-category arrow underlying a forward identity-comparison component is an identity. -/
@[simp]
theorem hom.app.underlying
    (X : FiberedCategoryOver.{u, v, w, vS} C)
    (A : (FiberedCategoryOver.inertia X).total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans (mapIdIso X).hom).app A) =
      𝟙 A.obj := sorry

/-- The total-category arrow underlying an inverse identity-comparison component is an identity. -/
@[simp]
theorem inv.app.underlying
    (X : FiberedCategoryOver.{u, v, w, vS} C)
    (A : (FiberedCategoryOver.inertia X).total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans (mapIdIso X).inv).app A) =
      𝟙 A.obj := sorry

end mapIdIso

end FiberedCategoryOver.Inertia

end CategoryTheory
