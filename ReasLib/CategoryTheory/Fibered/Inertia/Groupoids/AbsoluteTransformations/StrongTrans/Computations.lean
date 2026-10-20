module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.StrongTrans.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.StrongTrans.Forget.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.StrongTrans.IdentitySection.Computations

/-!
# Strong transformation computations for groupoid-fibred inertia

Component and naturality readouts for the forgetful and identity-section strong transformations.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.Groupoids

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace Inertia

variable {X Y : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C}

namespace forget.strongTrans

/-- The component of the strong groupoid-inertia forgetful transformation is the typed
forgetful morphism. -/
@[simp]
theorem app (X : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C) :
    (forget.strongTrans C).app X = forget X := sorry

/-- The naturality isomorphism of the strong forgetful transformation is the full-subbicategory
lift of the explicit based naturality isomorphism. -/
@[simp]
theorem naturality
    {X Y : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) :
    (forget.strongTrans C).naturality F =
      Bicategory.InducedBicategory.isoMk
        (BasedCategory.Inertia.forget.naturalityIso
          (FiberedCategoryOver.Groupoids.toBasedFunctor F)) := sorry

/-- The forward objectwise naturality component is the neutral based-inertia forgetful
comparison. -/
@[simp]
theorem naturality.hom.app
    {X Y : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (A : (FiberedCategoryOver.Groupoids.inertia X).total) :
    ((forget.strongTrans C).naturality F).hom.hom.toNatTrans.app A =
      (BasedCategory.Inertia.forget.naturalityIso.component
        (FiberedCategoryOver.Groupoids.toBasedFunctor F) A).hom := sorry

/-- The inverse objectwise naturality component is the inverse neutral based-inertia
forgetful comparison. -/
@[simp]
theorem naturality.inv.app
    {X Y : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (A : (FiberedCategoryOver.Groupoids.inertia X).total) :
    ((forget.strongTrans C).naturality F).inv.hom.toNatTrans.app A =
      (BasedCategory.Inertia.forget.naturalityIso.component
        (FiberedCategoryOver.Groupoids.toBasedFunctor F) A).inv := sorry

/-- The forward objectwise naturality component has identity underlying arrow. -/
@[simp]
theorem naturality.hom.app.underlying
    {X Y : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (A : (FiberedCategoryOver.Groupoids.inertia X).total) :
    ((forget.strongTrans C).naturality F).hom.hom.toNatTrans.app A =
      𝟙 ((FiberedCategoryOver.Groupoids.toBasedFunctor F).toFunctor.obj A.obj) := sorry

/-- The inverse objectwise naturality component has identity underlying arrow. -/
@[simp]
theorem naturality.inv.app.underlying
    {X Y : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (A : (FiberedCategoryOver.Groupoids.inertia X).total) :
    ((forget.strongTrans C).naturality F).inv.hom.toNatTrans.app A =
      𝟙 ((FiberedCategoryOver.Groupoids.toBasedFunctor F).toFunctor.obj A.obj) := sorry

/-- The forward objectwise naturality component lies over the identity of the base. -/
theorem naturality.hom.app.isHomLift
    {X Y : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (A : (FiberedCategoryOver.Groupoids.inertia X).total) :
    Y.p.IsHomLift (𝟙 ((FiberedCategoryOver.Groupoids.inertia X).p.obj A))
      (((forget.strongTrans C).naturality F).hom.hom.toNatTrans.app A) := sorry

/-- The inverse objectwise naturality component lies over the identity of the base. -/
theorem naturality.inv.app.isHomLift
    {X Y : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (A : (FiberedCategoryOver.Groupoids.inertia X).total) :
    Y.p.IsHomLift (𝟙 ((FiberedCategoryOver.Groupoids.inertia X).p.obj A))
      (((forget.strongTrans C).naturality F).inv.hom.toNatTrans.app A) := sorry

end forget.strongTrans

namespace identitySection.strongTrans

/-- The component of the strong identity-section transformation is the typed identity
section. -/
@[simp]
theorem app (X : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C) :
    (identitySection.strongTrans C).app X = identitySection X := sorry

/-- The naturality isomorphism of the strong identity-section transformation is the
full-subbicategory lift of the explicit based naturality isomorphism. -/
@[simp]
theorem naturality
    {X Y : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) :
    (identitySection.strongTrans C).naturality F =
      Bicategory.InducedBicategory.isoMk
        (BasedCategory.Inertia.identitySection.naturalityIso
          (FiberedCategoryOver.Groupoids.toBasedFunctor F)) := sorry

/-- The forward objectwise naturality component is the neutral based-inertia
identity-section comparison. -/
@[simp]
theorem naturality.hom.app
    {X Y : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (x : X.total) :
    ((identitySection.strongTrans C).naturality F).hom.hom.toNatTrans.app x =
      (BasedCategory.Inertia.identitySection.naturalityIso.component
        (FiberedCategoryOver.Groupoids.toBasedFunctor F) x).hom := sorry

/-- The inverse objectwise naturality component is the inverse neutral based-inertia
identity-section comparison. -/
@[simp]
theorem naturality.inv.app
    {X Y : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (x : X.total) :
    ((identitySection.strongTrans C).naturality F).inv.hom.toNatTrans.app x =
      (BasedCategory.Inertia.identitySection.naturalityIso.component
        (FiberedCategoryOver.Groupoids.toBasedFunctor F) x).inv := sorry

/-- The forward objectwise identity-section naturality component has identity underlying
arrow. -/
@[simp]
theorem naturality.hom.app.underlying
    {X Y : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (x : X.total) :
    CategoryTheory.RelativeInertia.hom
        (((identitySection.strongTrans C).naturality F).hom.hom.toNatTrans.app x) =
      𝟙 ((FiberedCategoryOver.Groupoids.toBasedFunctor F).toFunctor.obj x) := sorry

/-- The inverse objectwise identity-section naturality component has identity underlying
arrow. -/
@[simp]
theorem naturality.inv.app.underlying
    {X Y : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (x : X.total) :
    CategoryTheory.RelativeInertia.hom
        (((identitySection.strongTrans C).naturality F).inv.hom.toNatTrans.app x) =
      𝟙 ((FiberedCategoryOver.Groupoids.toBasedFunctor F).toFunctor.obj x) := sorry

/-- The forward objectwise identity-section naturality component lies over the identity of
the base. -/
theorem naturality.hom.app.isHomLift
    {X Y : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (x : X.total) :
    (FiberedCategoryOver.Groupoids.inertia Y).p.IsHomLift (𝟙 (X.p.obj x))
      (((identitySection.strongTrans C).naturality F).hom.hom.toNatTrans.app x) := sorry

/-- The inverse objectwise identity-section naturality component lies over the identity of
the base. -/
theorem naturality.inv.app.isHomLift
    {X Y : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C}
    (F : X ⟶ Y) (x : X.total) :
    (FiberedCategoryOver.Groupoids.inertia Y).p.IsHomLift (𝟙 (X.p.obj x))
      (((identitySection.strongTrans C).naturality F).inv.hom.toNatTrans.app x) := sorry

end identitySection.strongTrans

end Inertia

end FiberedCategoryOver.Groupoids

end CategoryTheory
