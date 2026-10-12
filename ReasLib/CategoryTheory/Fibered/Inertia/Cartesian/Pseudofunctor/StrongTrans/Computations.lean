/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.StrongTrans.Construction

/-!
# Computations for object-level strong transformations of cartesian inertia

This module exposes the ambient components and naturality isomorphisms of the
canonical forgetful and identity-section lifts.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory.FiberedCategoryOver.Inertia.objectLift

open BasedCategory BasedFunctor
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace forget.strongTrans

/-- The ambient based functor underlying an object-lifted forgetful component is neutral
based-inertia forgetting. -/
@[simp]
theorem app.toAmbient
    (X : FiberedCategoryOver.{u, v, max w vS, vS} C) :
    ((forget.strongTrans.{u, v, vS, w} C).app X).hom =
      BasedCategory.Inertia.forget X.toBasedCategory := sorry

/-- Naturality of the object-level forgetful transformation is the ambient naturality
isomorphism lifted through the fibred-object property. -/
@[simp]
theorem naturality
    {X Y : FiberedCategoryOver.{u, v, max w vS, vS} C} (F : X ⟶ Y) :
    (forget.strongTrans.{u, v, vS, w} C).naturality F =
      Bicategory.InducedBicategory.isoMk
        ((forget.basedStrongTrans.{u, v, vS, w} C).naturality F) := sorry

/-- Forgetting the object-property wrapper on object-level naturality recovers the
canonical based naturality isomorphism. -/
@[simp]
theorem naturality.toAmbient
    {X Y : FiberedCategoryOver.{u, v, max w vS, vS} C} (F : X ⟶ Y) :
    Bicategory.InducedBicategory.Iso.toAmbient
        ((forget.strongTrans.{u, v, vS, w} C).naturality F) =
      (forget.basedStrongTrans.{u, v, vS, w} C).naturality F := sorry

end forget.strongTrans

namespace identitySection.strongTrans

/-- The ambient based functor underlying an object-lifted identity-section component is the
neutral based-inertia identity section. -/
@[simp]
theorem app.toAmbient
    (X : FiberedCategoryOver.{u, v, max w vS, vS} C) :
    ((identitySection.strongTrans.{u, v, vS, w} C).app X).hom =
      BasedCategory.Inertia.identitySection X.toBasedCategory := sorry

/-- Naturality of the object-level identity section is the ambient naturality isomorphism
lifted through the fibred-object property. -/
@[simp]
theorem naturality
    {X Y : FiberedCategoryOver.{u, v, max w vS, vS} C} (F : X ⟶ Y) :
    (identitySection.strongTrans.{u, v, vS, w} C).naturality F =
      Bicategory.InducedBicategory.isoMk
        ((identitySection.basedStrongTrans.{u, v, vS, w} C).naturality F) := sorry

/-- Forgetting the object-property wrapper on object-level naturality recovers the
canonical based naturality isomorphism. -/
@[simp]
theorem naturality.toAmbient
    {X Y : FiberedCategoryOver.{u, v, max w vS, vS} C} (F : X ⟶ Y) :
    Bicategory.InducedBicategory.Iso.toAmbient
        ((identitySection.strongTrans.{u, v, vS, w} C).naturality F) =
      (identitySection.basedStrongTrans.{u, v, vS, w} C).naturality F := sorry

end identitySection.strongTrans

end CategoryTheory.FiberedCategoryOver.Inertia.objectLift
