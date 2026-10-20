module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.StrongTrans.IdentitySection.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Maps.Computations
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso

/-!
# Computations for the stable cartesian-inertia identity section

This leaf exposes the object component and ambient based-natural-transformation projections of
the identity-section strong transformation.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Inertia.identitySection.strongTrans

variable {C : Type u} [Category.{v} C]

/-- The object component of the strong identity-section transformation is the bundled identity
section. -/
@[simp]
theorem app (X : FiberedCategoryOver.{u, v, max w vS, vS} C) :
    (FiberedCategoryOver.Inertia.identitySection.strongTrans C).app X =
      FiberedCategoryOver.Inertia.identitySection X := sorry

/-- Forgetting cartesian preservation from strong identity-section naturality gives the ambient
naturality isomorphism. -/
@[simp]
theorem naturality.toBasedFunctorIso
    {X Y : FiberedCategoryOver.{u, v, max w vS, vS} C} (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedFunctorIso
        ((FiberedCategoryOver.Inertia.identitySection.strongTrans C).naturality F) =
      Bicategory.InducedBicategory.Iso.toAmbient
        ((FiberedCategoryOver.Inertia.objectLift.identitySection.strongTrans C).naturality F) := sorry

/-- The forward based natural transformation of strong identity-section naturality is the
forward cell of its ambient isomorphism. -/
@[simp]
theorem naturality.hom.toBasedNatTrans
    {X Y : FiberedCategoryOver.{u, v, max w vS, vS} C} (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedNatTrans
        ((FiberedCategoryOver.Inertia.identitySection.strongTrans C).naturality F).hom =
      (Bicategory.InducedBicategory.Iso.toAmbient
        ((FiberedCategoryOver.Inertia.objectLift.identitySection.strongTrans C).naturality F)).hom := sorry

/-- The inverse based natural transformation of strong identity-section naturality is the inverse
cell of its ambient isomorphism. -/
@[simp]
theorem naturality.inv.toBasedNatTrans
    {X Y : FiberedCategoryOver.{u, v, max w vS, vS} C} (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedNatTrans
        ((FiberedCategoryOver.Inertia.identitySection.strongTrans C).naturality F).inv =
      (Bicategory.InducedBicategory.Iso.toAmbient
        ((FiberedCategoryOver.Inertia.objectLift.identitySection.strongTrans C).naturality F)).inv := sorry

end FiberedCategoryOver.Inertia.identitySection.strongTrans

end CategoryTheory
