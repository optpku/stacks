/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.StrongTrans.Forget.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Maps.Computations
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso

/-!
# Computations for the stable cartesian-inertia forgetful transformation

This leaf exposes the object component and the ambient based-natural-transformation
projections of the forgetful strong transformation.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Inertia.forget.strongTrans

variable {C : Type u} [Category.{v} C]

/-- The object component of the strong forgetful transformation is the bundled forgetful
morphism. -/
@[simp]
theorem app (X : FiberedCategoryOver.{u, v, max w vS, vS} C) :
    (FiberedCategoryOver.Inertia.forget.strongTrans C).app X =
      FiberedCategoryOver.Inertia.forget X := sorry

/-- Forgetting cartesian preservation from strong forgetful naturality gives the ambient
naturality isomorphism. -/
@[simp]
theorem naturality.toBasedFunctorIso
    {X Y : FiberedCategoryOver.{u, v, max w vS, vS} C} (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedFunctorIso
        ((FiberedCategoryOver.Inertia.forget.strongTrans C).naturality F) =
      Bicategory.InducedBicategory.Iso.toAmbient
        ((FiberedCategoryOver.Inertia.objectLift.forget.strongTrans C).naturality F) := sorry

/-- The forward based natural transformation of strong forgetful naturality is the forward
cell of its ambient isomorphism. -/
@[simp]
theorem naturality.hom.toBasedNatTrans
    {X Y : FiberedCategoryOver.{u, v, max w vS, vS} C} (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedNatTrans
        ((FiberedCategoryOver.Inertia.forget.strongTrans C).naturality F).hom =
      (Bicategory.InducedBicategory.Iso.toAmbient
        ((FiberedCategoryOver.Inertia.objectLift.forget.strongTrans C).naturality F)).hom := sorry

/-- The inverse based natural transformation of strong forgetful naturality is the inverse
cell of its ambient isomorphism. -/
@[simp]
theorem naturality.inv.toBasedNatTrans
    {X Y : FiberedCategoryOver.{u, v, max w vS, vS} C} (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedNatTrans
        ((FiberedCategoryOver.Inertia.forget.strongTrans C).naturality F).inv =
      (Bicategory.InducedBicategory.Iso.toAmbient
        ((FiberedCategoryOver.Inertia.objectLift.forget.strongTrans C).naturality F)).inv := sorry

end FiberedCategoryOver.Inertia.forget.strongTrans

end CategoryTheory
