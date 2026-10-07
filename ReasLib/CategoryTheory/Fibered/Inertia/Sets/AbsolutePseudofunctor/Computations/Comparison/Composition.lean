module

public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.AbsolutePseudofunctor.Computations.Action
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.Functoriality.Comparison.Composition

/-! # Composition comparison computations for set-fibred inertia -/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Sets.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Sets.{u, v, w, vS} C}

namespace strictPseudofunctor

/-- The strict composition comparison is the direct typed inertia comparison. -/
@[simp] theorem mapComp {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    (strictPseudofunctor C).mapComp F G = Inertia.mapCompIso F G := sorry

/-- The forward strict composition-comparison cell forgets to the neutral based comparison. -/
@[simp] theorem mapComp.hom.toBasedNatTrans
    {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    FiberedCategoryOver.Sets.toBasedNatTrans
        ((strictPseudofunctor C).mapComp F G).hom =
      (BasedCategory.Inertia.mapCompIso
        (FiberedCategoryOver.Sets.toBasedFunctor F)
        (FiberedCategoryOver.Sets.toBasedFunctor G)).hom := sorry

/-- The inverse strict composition-comparison cell forgets to the neutral based comparison. -/
@[simp] theorem mapComp.inv.toBasedNatTrans
    {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    FiberedCategoryOver.Sets.toBasedNatTrans
        ((strictPseudofunctor C).mapComp F G).inv =
      (BasedCategory.Inertia.mapCompIso
        (FiberedCategoryOver.Sets.toBasedFunctor F)
        (FiberedCategoryOver.Sets.toBasedFunctor G)).inv := sorry

/-- The forward strict composition-comparison component is the neutral component. -/
@[simp] theorem mapComp.hom.app
    {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    (FiberedCategoryOver.Sets.toNatTrans
        ((strictPseudofunctor C).mapComp F G).hom).app A =
      (BasedCategory.Inertia.mapCompIso.app
        (FiberedCategoryOver.Sets.toBasedFunctor F)
        (FiberedCategoryOver.Sets.toBasedFunctor G) A).hom := sorry

/-- The inverse strict composition-comparison component is the neutral component. -/
@[simp] theorem mapComp.inv.app
    {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    (FiberedCategoryOver.Sets.toNatTrans
        ((strictPseudofunctor C).mapComp F G).inv).app A =
      (BasedCategory.Inertia.mapCompIso.app
        (FiberedCategoryOver.Sets.toBasedFunctor F)
        (FiberedCategoryOver.Sets.toBasedFunctor G) A).inv := sorry

/-- The underlying arrow of a forward strict composition component is an identity. -/
@[simp] theorem mapComp.hom.app.underlying
    {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Sets.toNatTrans
          ((strictPseudofunctor C).mapComp F G).hom).app A) =
      𝟙 (((BasedCategory.Inertia.map
        (FiberedCategoryOver.Sets.toBasedFunctor F)).comp
          (BasedCategory.Inertia.map
            (FiberedCategoryOver.Sets.toBasedFunctor G))).obj A).obj := sorry

/-- The underlying arrow of an inverse strict composition component is an identity. -/
@[simp] theorem mapComp.inv.app.underlying
    {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Sets.toNatTrans
          ((strictPseudofunctor C).mapComp F G).inv).app A) =
      𝟙 (((BasedCategory.Inertia.map
        (FiberedCategoryOver.Sets.toBasedFunctor F)).comp
          (BasedCategory.Inertia.map
            (FiberedCategoryOver.Sets.toBasedFunctor G))).obj A).obj := sorry

end strictPseudofunctor

namespace pseudofunctor

/-- The ordinary composition comparison is the direct typed inertia comparison. -/
@[simp] theorem mapComp {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    (pseudofunctor C).mapComp F G = Inertia.mapCompIso F G := sorry

/-- The forward ordinary composition-comparison cell forgets to the neutral based comparison. -/
@[simp] theorem mapComp.hom.toBasedNatTrans
    {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    FiberedCategoryOver.Sets.toBasedNatTrans ((pseudofunctor C).mapComp F G).hom =
      (BasedCategory.Inertia.mapCompIso
        (FiberedCategoryOver.Sets.toBasedFunctor F)
        (FiberedCategoryOver.Sets.toBasedFunctor G)).hom := sorry

/-- The inverse ordinary composition-comparison cell forgets to the neutral based comparison. -/
@[simp] theorem mapComp.inv.toBasedNatTrans
    {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    FiberedCategoryOver.Sets.toBasedNatTrans ((pseudofunctor C).mapComp F G).inv =
      (BasedCategory.Inertia.mapCompIso
        (FiberedCategoryOver.Sets.toBasedFunctor F)
        (FiberedCategoryOver.Sets.toBasedFunctor G)).inv := sorry

/-- The forward ordinary composition-comparison component is the neutral component. -/
@[simp] theorem mapComp.hom.app
    {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    (FiberedCategoryOver.Sets.toNatTrans
        ((pseudofunctor C).mapComp F G).hom).app A =
      (BasedCategory.Inertia.mapCompIso.app
        (FiberedCategoryOver.Sets.toBasedFunctor F)
        (FiberedCategoryOver.Sets.toBasedFunctor G) A).hom := sorry

/-- The inverse ordinary composition-comparison component is the neutral component. -/
@[simp] theorem mapComp.inv.app
    {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    (FiberedCategoryOver.Sets.toNatTrans
        ((pseudofunctor C).mapComp F G).inv).app A =
      (BasedCategory.Inertia.mapCompIso.app
        (FiberedCategoryOver.Sets.toBasedFunctor F)
        (FiberedCategoryOver.Sets.toBasedFunctor G) A).inv := sorry

/-- The underlying arrow of a forward ordinary composition component is an identity. -/
@[simp] theorem mapComp.hom.app.underlying
    {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Sets.toNatTrans
          ((pseudofunctor C).mapComp F G).hom).app A) =
      𝟙 (((BasedCategory.Inertia.map
        (FiberedCategoryOver.Sets.toBasedFunctor F)).comp
          (BasedCategory.Inertia.map
            (FiberedCategoryOver.Sets.toBasedFunctor G))).obj A).obj := sorry

/-- The underlying arrow of an inverse ordinary composition component is an identity. -/
@[simp] theorem mapComp.inv.app.underlying
    {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Sets.toNatTrans
          ((pseudofunctor C).mapComp F G).inv).app A) =
      𝟙 (((BasedCategory.Inertia.map
        (FiberedCategoryOver.Sets.toBasedFunctor F)).comp
          (BasedCategory.Inertia.map
            (FiberedCategoryOver.Sets.toBasedFunctor G))).obj A).obj := sorry

end pseudofunctor

end FiberedCategoryOver.Sets.Inertia

end CategoryTheory
