module

public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.AbsoluteTransformations.StrongTrans.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.StrongTrans.Forget.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.StrongTrans.IdentitySection.Computations

/-!
# Strong transformation computations for set-fibred inertia

Component, naturality, equivalence, and inverse-transformation readouts.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory Pseudofunctor.StrongTrans

namespace FiberedCategoryOver.Sets.Inertia

variable {C : Type u} [Category.{v} C]

namespace forget.strongTrans

/-- The component of set-fibred inertia forgetting is the concrete forgetful morphism. -/
@[simp] theorem app (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) :
    (forget.strongTrans C).app X = forget X := sorry

/-- The naturality isomorphism of set-fibred inertia forgetting is the full-subbicategory lift
of the explicit based naturality isomorphism. -/
@[simp] theorem naturality {X Y : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C} (F : X ⟶ Y) :
    (forget.strongTrans C).naturality F =
      Bicategory.InducedBicategory.isoMk
        (BasedCategory.Inertia.forget.naturalityIso
          (FiberedCategoryOver.Sets.toBasedFunctor F)) := sorry

/-- The forward objectwise naturality component is the neutral based-inertia forgetful
comparison. -/
@[simp]
theorem naturality.hom.app
    {X Y : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (A : (FiberedCategoryOver.Sets.inertia X).total) :
    ((forget.strongTrans C).naturality F).hom.hom.toNatTrans.app A =
      (BasedCategory.Inertia.forget.naturalityIso.component
        (FiberedCategoryOver.Sets.toBasedFunctor F) A).hom := sorry

/-- The inverse objectwise naturality component is the inverse neutral based-inertia
forgetful comparison. -/
@[simp]
theorem naturality.inv.app
    {X Y : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (A : (FiberedCategoryOver.Sets.inertia X).total) :
    ((forget.strongTrans C).naturality F).inv.hom.toNatTrans.app A =
      (BasedCategory.Inertia.forget.naturalityIso.component
        (FiberedCategoryOver.Sets.toBasedFunctor F) A).inv := sorry

/-- The forward objectwise naturality component has identity underlying arrow. -/
@[simp]
theorem naturality.hom.app.underlying
    {X Y : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (A : (FiberedCategoryOver.Sets.inertia X).total) :
    ((forget.strongTrans C).naturality F).hom.hom.toNatTrans.app A =
      𝟙 ((FiberedCategoryOver.Sets.toBasedFunctor F).toFunctor.obj A.obj) := sorry

/-- The inverse objectwise naturality component has identity underlying arrow. -/
@[simp]
theorem naturality.inv.app.underlying
    {X Y : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (A : (FiberedCategoryOver.Sets.inertia X).total) :
    ((forget.strongTrans C).naturality F).inv.hom.toNatTrans.app A =
      𝟙 ((FiberedCategoryOver.Sets.toBasedFunctor F).toFunctor.obj A.obj) := sorry

/-- The forward objectwise naturality component lies over the identity of the base. -/
theorem naturality.hom.app.isHomLift
    {X Y : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (A : (FiberedCategoryOver.Sets.inertia X).total) :
    Y.p.IsHomLift (𝟙 ((FiberedCategoryOver.Sets.inertia X).p.obj A))
      (((forget.strongTrans C).naturality F).hom.hom.toNatTrans.app A) := sorry

/-- The inverse objectwise naturality component lies over the identity of the base. -/
theorem naturality.inv.app.isHomLift
    {X Y : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (A : (FiberedCategoryOver.Sets.inertia X).total) :
    Y.p.IsHomLift (𝟙 ((FiberedCategoryOver.Sets.inertia X).p.obj A))
      (((forget.strongTrans C).naturality F).inv.hom.toNatTrans.app A) := sorry

end forget.strongTrans

/-- Evaluating the pointwise-equivalence data gives the canonical inertia equivalence. -/
@[simp]
theorem forget.pointwiseEquivalence.app
    (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) :
    (forget.pointwiseEquivalence C).app X = forget.equivalence X := sorry

/-- The forward strong transformation of the pseudofunctor equivalence is inertia forgetting. -/
@[simp]
theorem forget.pseudofunctorEquivalence.hom :
    (forget.pseudofunctorEquivalence.{u, v, vS, w} C).hom =
      forget.strongTrans.{u, v, vS, w} C := sorry

/-- The forward component of the pseudofunctor equivalence is inertia forgetting. -/
@[simp]
theorem forget.pseudofunctorEquivalence.hom.app
    (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) :
    (forget.pseudofunctorEquivalence C).hom.app X = forget X := sorry

/-- The inverse component of the pseudofunctor equivalence is the identity section. -/
@[simp]
theorem forget.pseudofunctorEquivalence.inv.app
    (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) :
    (forget.pseudofunctorEquivalence C).inv.app X = identitySection X := sorry

/-- Evaluating the pseudofunctor equivalence gives the canonical objectwise inertia
equivalence. -/
@[simp]
theorem forget.pseudofunctorEquivalence.app
    (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) :
    (forget.pseudofunctorEquivalence C).app X = forget.equivalence X := sorry

namespace identitySection.strongTrans

/-- The component of the identity-section strong transformation is the concrete identity
section. -/
@[simp] theorem app (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) :
    (identitySection.strongTrans C).app X = identitySection X := sorry

/-- The identity-section naturality isomorphism is the full-subbicategory lift of the explicit
based naturality isomorphism. -/
@[simp] theorem naturality {X Y : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C} (F : X ⟶ Y) :
    (identitySection.strongTrans C).naturality F =
      Bicategory.InducedBicategory.isoMk
        (BasedCategory.Inertia.identitySection.naturalityIso
          (FiberedCategoryOver.Sets.toBasedFunctor F)) := sorry

/-- The forward objectwise naturality component is the neutral based-inertia
identity-section comparison. -/
@[simp]
theorem naturality.hom.app
    {X Y : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (x : X.total) :
    ((identitySection.strongTrans C).naturality F).hom.hom.toNatTrans.app x =
      (BasedCategory.Inertia.identitySection.naturalityIso.component
        (FiberedCategoryOver.Sets.toBasedFunctor F) x).hom := sorry

/-- The inverse objectwise naturality component is the inverse neutral based-inertia
identity-section comparison. -/
@[simp]
theorem naturality.inv.app
    {X Y : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (x : X.total) :
    ((identitySection.strongTrans C).naturality F).inv.hom.toNatTrans.app x =
      (BasedCategory.Inertia.identitySection.naturalityIso.component
        (FiberedCategoryOver.Sets.toBasedFunctor F) x).inv := sorry

/-- The forward objectwise identity-section naturality component has identity underlying
arrow. -/
@[simp]
theorem naturality.hom.app.underlying
    {X Y : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (x : X.total) :
    CategoryTheory.RelativeInertia.hom
        (((identitySection.strongTrans C).naturality F).hom.hom.toNatTrans.app x) =
      𝟙 ((FiberedCategoryOver.Sets.toBasedFunctor F).toFunctor.obj x) := sorry

/-- The inverse objectwise identity-section naturality component has identity underlying
arrow. -/
@[simp]
theorem naturality.inv.app.underlying
    {X Y : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (x : X.total) :
    CategoryTheory.RelativeInertia.hom
        (((identitySection.strongTrans C).naturality F).inv.hom.toNatTrans.app x) =
      𝟙 ((FiberedCategoryOver.Sets.toBasedFunctor F).toFunctor.obj x) := sorry

/-- The forward objectwise identity-section naturality component lies over the identity of
the base. -/
theorem naturality.hom.app.isHomLift
    {X Y : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (x : X.total) :
    (FiberedCategoryOver.Sets.inertia Y).p.IsHomLift (𝟙 (X.p.obj x))
      (((identitySection.strongTrans C).naturality F).hom.hom.toNatTrans.app x) := sorry

/-- The inverse objectwise identity-section naturality component lies over the identity of
the base. -/
theorem naturality.inv.app.isHomLift
    {X Y : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (x : X.total) :
    (FiberedCategoryOver.Sets.inertia Y).p.IsHomLift (𝟙 (X.p.obj x))
      (((identitySection.strongTrans C).naturality F).inv.hom.toNatTrans.app x) := sorry

/-- The identity section is the inverse transformation in the canonical set-fibred inertia
pseudofunctor equivalence. -/
theorem eq_inv :
    identitySection.strongTrans.{u, v, vS, w} C =
      (forget.pseudofunctorEquivalence.{u, v, vS, w} C).inv := sorry

end identitySection.strongTrans

end FiberedCategoryOver.Sets.Inertia

end CategoryTheory
