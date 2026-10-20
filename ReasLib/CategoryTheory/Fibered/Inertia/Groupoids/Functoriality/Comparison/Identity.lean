module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Functoriality.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Comparison.Identity
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso

/-!
# Identity comparison for typed groupoid-fibred inertia

The comparison itself is owned by the induced-bicategory constructor applied
to the neutral based comparison.  This leaf provides the typed owner and its
component-level readouts.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Groupoids.Inertia

variable {C : Type u} [Category.{v} C]

/-- The identity comparison for the typed groupoid-fibred inertia action. -/
def mapIdIso (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) :
    map (𝟙 X) ≅ 𝟙 (inertia X) :=
  Bicategory.InducedBicategory.isoMk
    (BasedCategory.Inertia.mapIdIso X.toBasedCategory)

namespace mapIdIso

/-- The ambient forward identity-comparison cell is the neutral based one. -/
@[simp]
theorem hom.toBasedNatTrans
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) :
    FiberedCategoryOver.Groupoids.toBasedNatTrans (mapIdIso X).hom =
      (BasedCategory.Inertia.mapIdIso X.toBasedCategory).hom := sorry

/-- The ambient inverse identity-comparison cell is the neutral based one. -/
@[simp]
theorem inv.toBasedNatTrans
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) :
    FiberedCategoryOver.Groupoids.toBasedNatTrans (mapIdIso X).inv =
      (BasedCategory.Inertia.mapIdIso X.toBasedCategory).inv := sorry

/-- The forward identity-comparison component is the neutral component. -/
@[simp]
theorem hom.app
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C)
    (A : X.inertia.total) :
    (FiberedCategoryOver.Groupoids.toNatTrans (mapIdIso X).hom).app A =
      (BasedCategory.Inertia.mapIdIso.app X.toBasedCategory A).hom := sorry

/-- The inverse identity-comparison component is the neutral component. -/
@[simp]
theorem inv.app
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C)
    (A : X.inertia.total) :
    (FiberedCategoryOver.Groupoids.toNatTrans (mapIdIso X).inv).app A =
      (BasedCategory.Inertia.mapIdIso.app X.toBasedCategory A).inv := sorry

/-- Every forward groupoid-fibred identity-comparison component lies over the identity of its
base object. -/
theorem hom.app.isHomLift
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C)
    (A : X.inertia.total) :
    X.inertia.p.IsHomLift (𝟙 (X.inertia.p.obj A))
      ((FiberedCategoryOver.Groupoids.toNatTrans (mapIdIso X).hom).app A) := sorry

/-- Every inverse groupoid-fibred identity-comparison component lies over the identity of its
base object. -/
theorem inv.app.isHomLift
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C)
    (A : X.inertia.total) :
    X.inertia.p.IsHomLift (𝟙 (X.inertia.p.obj A))
      ((FiberedCategoryOver.Groupoids.toNatTrans (mapIdIso X).inv).app A) := sorry

/-- The underlying arrow of a forward identity-comparison component is an identity. -/
@[simp]
theorem hom.app.underlying
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C)
    (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Groupoids.toNatTrans (mapIdIso X).hom).app A) =
      𝟙 A.obj := sorry

/-- The underlying arrow of an inverse identity-comparison component is an identity. -/
@[simp]
theorem inv.app.underlying
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C)
    (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Groupoids.toNatTrans (mapIdIso X).inv).app A) =
      𝟙 A.obj := sorry

end mapIdIso

end FiberedCategoryOver.Groupoids.Inertia

end CategoryTheory
