module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsolutePseudofunctor.Computations.Action
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Functoriality.Comparison.Identity

/-! # Identity comparison computations for groupoid-fibred inertia -/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Groupoids.Inertia

variable {C : Type u} [Category.{v} C]

namespace strictPseudofunctor

/-- The strict identity comparison is the direct typed inertia comparison. -/
@[simp] theorem mapId (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) :
    (strictPseudofunctor C).mapId X = Inertia.mapIdIso X := sorry

/-- The forward strict identity-comparison cell forgets to the neutral based comparison. -/
@[simp] theorem mapId.hom.toBasedNatTrans
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) :
    FiberedCategoryOver.Groupoids.toBasedNatTrans ((strictPseudofunctor C).mapId X).hom =
      (BasedCategory.Inertia.mapIdIso X.toBasedCategory).hom := sorry

/-- The inverse strict identity-comparison cell forgets to the neutral based comparison. -/
@[simp] theorem mapId.inv.toBasedNatTrans
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) :
    FiberedCategoryOver.Groupoids.toBasedNatTrans ((strictPseudofunctor C).mapId X).inv =
      (BasedCategory.Inertia.mapIdIso X.toBasedCategory).inv := sorry

/-- The forward strict identity-comparison component is the neutral component. -/
@[simp] theorem mapId.hom.app
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) (A : X.inertia.total) :
    (FiberedCategoryOver.Groupoids.toNatTrans
        ((strictPseudofunctor C).mapId X).hom).app A =
      (BasedCategory.Inertia.mapIdIso.app X.toBasedCategory A).hom := sorry

/-- The inverse strict identity-comparison component is the neutral component. -/
@[simp] theorem mapId.inv.app
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) (A : X.inertia.total) :
    (FiberedCategoryOver.Groupoids.toNatTrans
        ((strictPseudofunctor C).mapId X).inv).app A =
      (BasedCategory.Inertia.mapIdIso.app X.toBasedCategory A).inv := sorry

/-- The underlying arrow of a forward strict identity component is an identity. -/
@[simp] theorem mapId.hom.app.underlying
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Groupoids.toNatTrans
          ((strictPseudofunctor C).mapId X).hom).app A) =
      𝟙 A.obj := sorry

/-- The underlying arrow of an inverse strict identity component is an identity. -/
@[simp] theorem mapId.inv.app.underlying
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Groupoids.toNatTrans
          ((strictPseudofunctor C).mapId X).inv).app A) =
      𝟙 A.obj := sorry

end strictPseudofunctor

namespace pseudofunctor

/-- The ordinary identity comparison is the direct typed inertia comparison. -/
@[simp] theorem mapId (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) :
    (pseudofunctor C).mapId X = Inertia.mapIdIso X := sorry

/-- The forward ordinary identity-comparison cell forgets to the neutral based comparison. -/
@[simp] theorem mapId.hom.toBasedNatTrans
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) :
    FiberedCategoryOver.Groupoids.toBasedNatTrans ((pseudofunctor C).mapId X).hom =
      (BasedCategory.Inertia.mapIdIso X.toBasedCategory).hom := sorry

/-- The inverse ordinary identity-comparison cell forgets to the neutral based comparison. -/
@[simp] theorem mapId.inv.toBasedNatTrans
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) :
    FiberedCategoryOver.Groupoids.toBasedNatTrans ((pseudofunctor C).mapId X).inv =
      (BasedCategory.Inertia.mapIdIso X.toBasedCategory).inv := sorry

/-- The forward ordinary identity-comparison component is the neutral component. -/
@[simp] theorem mapId.hom.app
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) (A : X.inertia.total) :
    (FiberedCategoryOver.Groupoids.toNatTrans ((pseudofunctor C).mapId X).hom).app A =
      (BasedCategory.Inertia.mapIdIso.app X.toBasedCategory A).hom := sorry

/-- The inverse ordinary identity-comparison component is the neutral component. -/
@[simp] theorem mapId.inv.app
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) (A : X.inertia.total) :
    (FiberedCategoryOver.Groupoids.toNatTrans ((pseudofunctor C).mapId X).inv).app A =
      (BasedCategory.Inertia.mapIdIso.app X.toBasedCategory A).inv := sorry

/-- The underlying arrow of a forward ordinary identity component is an identity. -/
@[simp] theorem mapId.hom.app.underlying
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Groupoids.toNatTrans
          ((pseudofunctor C).mapId X).hom).app A) =
      𝟙 A.obj := sorry

/-- The underlying arrow of an inverse ordinary identity component is an identity. -/
@[simp] theorem mapId.inv.app.underlying
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Groupoids.toNatTrans
          ((pseudofunctor C).mapId X).inv).app A) =
      𝟙 A.obj := sorry

end pseudofunctor

end FiberedCategoryOver.Groupoids.Inertia

end CategoryTheory
