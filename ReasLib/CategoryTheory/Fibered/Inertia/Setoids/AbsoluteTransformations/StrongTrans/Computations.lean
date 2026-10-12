/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.AbsoluteTransformations.StrongTrans.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.StrongTrans.Forget.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.StrongTrans.IdentitySection.Computations

/-!
# Strong transformation computations for setoid-fibred inertia

Component, naturality, equivalence, and inverse-transformation readouts.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.Setoids

open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace Inertia

namespace forget.strongTrans

/-- The component of the strong setoid-inertia forgetful transformation is the typed
forgetful morphism. -/
@[simp] theorem app (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) :
    (forget.strongTrans C).app X = forget X := sorry

/-- The naturality isomorphism of the strong forgetful transformation is the full-subbicategory
lift of the explicit based naturality isomorphism. -/
@[simp] theorem naturality {X Y : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C} (F : X ⟶ Y) :
    (forget.strongTrans C).naturality F =
      Bicategory.InducedBicategory.isoMk
        (BasedCategory.Inertia.forget.naturalityIso
          (FiberedCategoryOver.Setoids.toBasedFunctor F)) := sorry

/-- The forward objectwise naturality component is the neutral based-inertia forgetful
comparison. -/
@[simp]
theorem naturality.hom.app
    {X Y : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (A : (FiberedCategoryOver.Setoids.inertia X).total) :
    ((forget.strongTrans C).naturality F).hom.hom.toNatTrans.app A =
      (BasedCategory.Inertia.forget.naturalityIso.component
        (FiberedCategoryOver.Setoids.toBasedFunctor F) A).hom := sorry

/-- The inverse objectwise naturality component is the inverse neutral based-inertia
forgetful comparison. -/
@[simp]
theorem naturality.inv.app
    {X Y : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (A : (FiberedCategoryOver.Setoids.inertia X).total) :
    ((forget.strongTrans C).naturality F).inv.hom.toNatTrans.app A =
      (BasedCategory.Inertia.forget.naturalityIso.component
        (FiberedCategoryOver.Setoids.toBasedFunctor F) A).inv := sorry

/-- The forward objectwise naturality component has identity underlying arrow. -/
@[simp]
theorem naturality.hom.app.underlying
    {X Y : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (A : (FiberedCategoryOver.Setoids.inertia X).total) :
    ((forget.strongTrans C).naturality F).hom.hom.toNatTrans.app A =
      𝟙 ((FiberedCategoryOver.Setoids.toBasedFunctor F).toFunctor.obj A.obj) := sorry

/-- The inverse objectwise naturality component has identity underlying arrow. -/
@[simp]
theorem naturality.inv.app.underlying
    {X Y : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (A : (FiberedCategoryOver.Setoids.inertia X).total) :
    ((forget.strongTrans C).naturality F).inv.hom.toNatTrans.app A =
      𝟙 ((FiberedCategoryOver.Setoids.toBasedFunctor F).toFunctor.obj A.obj) := sorry

/-- The forward objectwise naturality component lies over the identity of the base. -/
theorem naturality.hom.app.isHomLift
    {X Y : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (A : (FiberedCategoryOver.Setoids.inertia X).total) :
    Y.p.IsHomLift (𝟙 ((FiberedCategoryOver.Setoids.inertia X).p.obj A))
      (((forget.strongTrans C).naturality F).hom.hom.toNatTrans.app A) := sorry

/-- The inverse objectwise naturality component lies over the identity of the base. -/
theorem naturality.inv.app.isHomLift
    {X Y : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (A : (FiberedCategoryOver.Setoids.inertia X).total) :
    Y.p.IsHomLift (𝟙 ((FiberedCategoryOver.Setoids.inertia X).p.obj A))
      (((forget.strongTrans C).naturality F).inv.hom.toNatTrans.app A) := sorry

end forget.strongTrans

namespace forget.pointwiseEquivalence

/-- Evaluating the pointwise-equivalence data gives the canonical objectwise inertia
equivalence. -/
@[simp] theorem app (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) :
    (forget.pointwiseEquivalence C).app X = forget.equivalence X := sorry

end forget.pointwiseEquivalence

namespace forget.pseudofunctorEquivalence

/-- The forward strong transformation is inertia forgetting. -/
@[simp] theorem hom :
    (forget.pseudofunctorEquivalence.{u, v, vS, w} C).hom =
      forget.strongTrans.{u, v, vS, w} C := sorry

/-- The forward component is the bundled inertia-forgetful morphism. -/
@[simp] theorem hom.app (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) :
    (forget.pseudofunctorEquivalence C).hom.app X = forget X := sorry

/-- The inverse component is the identity-automorphism section. -/
@[simp] theorem inv.app (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) :
    (forget.pseudofunctorEquivalence C).inv.app X = identitySection X := sorry

/-- Evaluating the pseudofunctor equivalence gives the canonical objectwise inertia
equivalence. -/
@[simp] theorem app (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) :
    (forget.pseudofunctorEquivalence C).app X = forget.equivalence X := sorry

end forget.pseudofunctorEquivalence

namespace identitySection.strongTrans

/-- The component of the inverse strong transformation is the bundled identity section. -/
@[simp] theorem app (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) :
    (identitySection.strongTrans C).app X = identitySection X := sorry

/-- The inverse strong transformation uses the full-subbicategory lift of the explicit
identity-section naturality isomorphism. -/
@[simp] theorem naturality {X Y : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C} (F : X ⟶ Y) :
    (identitySection.strongTrans C).naturality F =
      Bicategory.InducedBicategory.isoMk
        (BasedCategory.Inertia.identitySection.naturalityIso
          (FiberedCategoryOver.Setoids.toBasedFunctor F)) := sorry

/-- The forward objectwise naturality component is the neutral based-inertia
identity-section comparison. -/
@[simp]
theorem naturality.hom.app
    {X Y : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (x : X.total) :
    ((identitySection.strongTrans C).naturality F).hom.hom.toNatTrans.app x =
      (BasedCategory.Inertia.identitySection.naturalityIso.component
        (FiberedCategoryOver.Setoids.toBasedFunctor F) x).hom := sorry

/-- The inverse objectwise naturality component is the inverse neutral based-inertia
identity-section comparison. -/
@[simp]
theorem naturality.inv.app
    {X Y : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (x : X.total) :
    ((identitySection.strongTrans C).naturality F).inv.hom.toNatTrans.app x =
      (BasedCategory.Inertia.identitySection.naturalityIso.component
        (FiberedCategoryOver.Setoids.toBasedFunctor F) x).inv := sorry

/-- The forward objectwise identity-section naturality component has identity underlying
arrow. -/
@[simp]
theorem naturality.hom.app.underlying
    {X Y : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (x : X.total) :
    CategoryTheory.RelativeInertia.hom
        (((identitySection.strongTrans C).naturality F).hom.hom.toNatTrans.app x) =
      𝟙 ((FiberedCategoryOver.Setoids.toBasedFunctor F).toFunctor.obj x) := sorry

/-- The inverse objectwise identity-section naturality component has identity underlying
arrow. -/
@[simp]
theorem naturality.inv.app.underlying
    {X Y : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (x : X.total) :
    CategoryTheory.RelativeInertia.hom
        (((identitySection.strongTrans C).naturality F).inv.hom.toNatTrans.app x) =
      𝟙 ((FiberedCategoryOver.Setoids.toBasedFunctor F).toFunctor.obj x) := sorry

/-- The forward objectwise identity-section naturality component lies over the identity of
the base. -/
theorem naturality.hom.app.isHomLift
    {X Y : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (x : X.total) :
    (FiberedCategoryOver.Setoids.inertia Y).p.IsHomLift (𝟙 (X.p.obj x))
      (((identitySection.strongTrans C).naturality F).hom.hom.toNatTrans.app x) := sorry

/-- The inverse objectwise identity-section naturality component lies over the identity of
the base. -/
theorem naturality.inv.app.isHomLift
    {X Y : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (x : X.total) :
    (FiberedCategoryOver.Setoids.inertia Y).p.IsHomLift (𝟙 (X.p.obj x))
      (((identitySection.strongTrans C).naturality F).inv.hom.toNatTrans.app x) := sorry

/-- The restricted neutral identity section is the inverse transformation in the canonical
setoid-inertia pseudofunctor equivalence. -/
@[stacks 04Z3 "setoid-inertia identity section as inverse transformation"]
theorem eq_inv :
    identitySection.strongTrans.{u, v, vS, w} C =
      (forget.pseudofunctorEquivalence.{u, v, vS, w} C).inv := sorry

end identitySection.strongTrans

end Inertia

end FiberedCategoryOver.Setoids

end CategoryTheory
