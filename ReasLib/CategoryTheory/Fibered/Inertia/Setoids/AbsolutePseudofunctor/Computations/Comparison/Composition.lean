/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.AbsolutePseudofunctor.Computations.Action
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Functoriality.Comparison.Composition

/-! # Composition comparison computations for setoid-fibred inertia -/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Setoids.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Setoids.{u, v, w, vS} C}

namespace strictPseudofunctor

/-- The strict composition comparison is the direct typed inertia comparison. -/
@[simp] theorem mapComp {Z : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    (strictPseudofunctor C).mapComp F G = Inertia.mapCompIso F G := sorry

/-- The forward strict composition-comparison cell forgets to the neutral based comparison. -/
@[simp] theorem mapComp.hom.toBasedNatTrans
    {Z : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    FiberedCategoryOver.Setoids.toBasedNatTrans
        ((strictPseudofunctor C).mapComp F G).hom =
      (BasedCategory.Inertia.mapCompIso
        (FiberedCategoryOver.Setoids.toBasedFunctor F)
        (FiberedCategoryOver.Setoids.toBasedFunctor G)).hom := sorry

/-- The inverse strict composition-comparison cell forgets to the neutral based comparison. -/
@[simp] theorem mapComp.inv.toBasedNatTrans
    {Z : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    FiberedCategoryOver.Setoids.toBasedNatTrans
        ((strictPseudofunctor C).mapComp F G).inv =
      (BasedCategory.Inertia.mapCompIso
        (FiberedCategoryOver.Setoids.toBasedFunctor F)
        (FiberedCategoryOver.Setoids.toBasedFunctor G)).inv := sorry

/-- The forward strict composition-comparison component is the neutral component. -/
@[simp] theorem mapComp.hom.app
    {Z : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    (FiberedCategoryOver.Setoids.toNatTrans
        ((strictPseudofunctor C).mapComp F G).hom).app A =
      (BasedCategory.Inertia.mapCompIso.app
        (FiberedCategoryOver.Setoids.toBasedFunctor F)
        (FiberedCategoryOver.Setoids.toBasedFunctor G) A).hom := sorry

/-- The inverse strict composition-comparison component is the neutral component. -/
@[simp] theorem mapComp.inv.app
    {Z : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    (FiberedCategoryOver.Setoids.toNatTrans
        ((strictPseudofunctor C).mapComp F G).inv).app A =
      (BasedCategory.Inertia.mapCompIso.app
        (FiberedCategoryOver.Setoids.toBasedFunctor F)
        (FiberedCategoryOver.Setoids.toBasedFunctor G) A).inv := sorry

/-- The underlying arrow of a forward strict composition component is an identity. -/
@[simp] theorem mapComp.hom.app.underlying
    {Z : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Setoids.toNatTrans
          ((strictPseudofunctor C).mapComp F G).hom).app A) =
      𝟙 (((BasedCategory.Inertia.map
        (FiberedCategoryOver.Setoids.toBasedFunctor F)).comp
          (BasedCategory.Inertia.map
            (FiberedCategoryOver.Setoids.toBasedFunctor G))).obj A).obj := sorry

/-- The underlying arrow of an inverse strict composition component is an identity. -/
@[simp] theorem mapComp.inv.app.underlying
    {Z : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Setoids.toNatTrans
          ((strictPseudofunctor C).mapComp F G).inv).app A) =
      𝟙 (((BasedCategory.Inertia.map
        (FiberedCategoryOver.Setoids.toBasedFunctor F)).comp
          (BasedCategory.Inertia.map
            (FiberedCategoryOver.Setoids.toBasedFunctor G))).obj A).obj := sorry

end strictPseudofunctor

namespace pseudofunctor

/-- The ordinary composition comparison is the direct typed inertia comparison. -/
@[simp] theorem mapComp {Z : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    (pseudofunctor C).mapComp F G = Inertia.mapCompIso F G := sorry

/-- The forward ordinary composition-comparison cell forgets to the neutral based comparison. -/
@[simp] theorem mapComp.hom.toBasedNatTrans
    {Z : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    FiberedCategoryOver.Setoids.toBasedNatTrans ((pseudofunctor C).mapComp F G).hom =
      (BasedCategory.Inertia.mapCompIso
        (FiberedCategoryOver.Setoids.toBasedFunctor F)
        (FiberedCategoryOver.Setoids.toBasedFunctor G)).hom := sorry

/-- The inverse ordinary composition-comparison cell forgets to the neutral based comparison. -/
@[simp] theorem mapComp.inv.toBasedNatTrans
    {Z : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    FiberedCategoryOver.Setoids.toBasedNatTrans ((pseudofunctor C).mapComp F G).inv =
      (BasedCategory.Inertia.mapCompIso
        (FiberedCategoryOver.Setoids.toBasedFunctor F)
        (FiberedCategoryOver.Setoids.toBasedFunctor G)).inv := sorry

/-- The forward ordinary composition-comparison component is the neutral component. -/
@[simp] theorem mapComp.hom.app
    {Z : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    (FiberedCategoryOver.Setoids.toNatTrans
        ((pseudofunctor C).mapComp F G).hom).app A =
      (BasedCategory.Inertia.mapCompIso.app
        (FiberedCategoryOver.Setoids.toBasedFunctor F)
        (FiberedCategoryOver.Setoids.toBasedFunctor G) A).hom := sorry

/-- The inverse ordinary composition-comparison component is the neutral component. -/
@[simp] theorem mapComp.inv.app
    {Z : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    (FiberedCategoryOver.Setoids.toNatTrans
        ((pseudofunctor C).mapComp F G).inv).app A =
      (BasedCategory.Inertia.mapCompIso.app
        (FiberedCategoryOver.Setoids.toBasedFunctor F)
        (FiberedCategoryOver.Setoids.toBasedFunctor G) A).inv := sorry

/-- The underlying arrow of a forward ordinary composition component is an identity. -/
@[simp] theorem mapComp.hom.app.underlying
    {Z : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Setoids.toNatTrans
          ((pseudofunctor C).mapComp F G).hom).app A) =
      𝟙 (((BasedCategory.Inertia.map
        (FiberedCategoryOver.Setoids.toBasedFunctor F)).comp
          (BasedCategory.Inertia.map
            (FiberedCategoryOver.Setoids.toBasedFunctor G))).obj A).obj := sorry

/-- The underlying arrow of an inverse ordinary composition component is an identity. -/
@[simp] theorem mapComp.inv.app.underlying
    {Z : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Setoids.toNatTrans
          ((pseudofunctor C).mapComp F G).inv).app A) =
      𝟙 (((BasedCategory.Inertia.map
        (FiberedCategoryOver.Setoids.toBasedFunctor F)).comp
          (BasedCategory.Inertia.map
            (FiberedCategoryOver.Setoids.toBasedFunctor G))).obj A).obj := sorry

end pseudofunctor

end FiberedCategoryOver.Setoids.Inertia

end CategoryTheory
