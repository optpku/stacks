module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Functoriality.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Comparison.Composition
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso

/-!
# Composition comparison for typed groupoid-fibred inertia

The typed composition comparison is the induced-bicategory lift of the
neutral based comparison.  Component formulas are kept here so clients do
not need to unfold either constructor.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Groupoids.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}

/-- The composition comparison for typed groupoid-fibred inertia. -/
def mapCompIso {Z : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    map (F ≫ G) ≅ map F ≫ map G :=
  Bicategory.InducedBicategory.isoMk
    (BasedCategory.Inertia.mapCompIso
      (FiberedCategoryOver.Groupoids.toBasedFunctor F)
      (FiberedCategoryOver.Groupoids.toBasedFunctor G))

namespace mapCompIso

/-- The ambient forward composition-comparison cell is the neutral one. -/
@[simp]
theorem hom.toBasedNatTrans {Z : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    FiberedCategoryOver.Groupoids.toBasedNatTrans (mapCompIso F G).hom =
      (BasedCategory.Inertia.mapCompIso
        (FiberedCategoryOver.Groupoids.toBasedFunctor F)
        (FiberedCategoryOver.Groupoids.toBasedFunctor G)).hom := sorry

/-- The ambient inverse composition-comparison cell is the neutral one. -/
@[simp]
theorem inv.toBasedNatTrans {Z : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    FiberedCategoryOver.Groupoids.toBasedNatTrans (mapCompIso F G).inv =
      (BasedCategory.Inertia.mapCompIso
        (FiberedCategoryOver.Groupoids.toBasedFunctor F)
        (FiberedCategoryOver.Groupoids.toBasedFunctor G)).inv := sorry

/-- The forward composition-comparison component is the neutral component. -/
@[simp]
theorem hom.app {Z : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    (FiberedCategoryOver.Groupoids.toNatTrans (mapCompIso F G).hom).app A =
      (BasedCategory.Inertia.mapCompIso.app
        (FiberedCategoryOver.Groupoids.toBasedFunctor F)
        (FiberedCategoryOver.Groupoids.toBasedFunctor G) A).hom := sorry

/-- The inverse composition-comparison component is the neutral component. -/
@[simp]
theorem inv.app {Z : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    (FiberedCategoryOver.Groupoids.toNatTrans (mapCompIso F G).inv).app A =
      (BasedCategory.Inertia.mapCompIso.app
        (FiberedCategoryOver.Groupoids.toBasedFunctor F)
        (FiberedCategoryOver.Groupoids.toBasedFunctor G) A).inv := sorry

/-- Every forward groupoid-fibred composition-comparison component lies over the identity of its
source base object. -/
theorem hom.app.isHomLift {Z : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    Z.inertia.p.IsHomLift (𝟙 (X.inertia.p.obj A))
      ((FiberedCategoryOver.Groupoids.toNatTrans (mapCompIso F G).hom).app A) := sorry

/-- Every inverse groupoid-fibred composition-comparison component lies over the identity of its
source base object. -/
theorem inv.app.isHomLift {Z : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    Z.inertia.p.IsHomLift (𝟙 (X.inertia.p.obj A))
      ((FiberedCategoryOver.Groupoids.toNatTrans (mapCompIso F G).inv).app A) := sorry

/-- The underlying arrow of a forward composition-comparison component is an identity. -/
@[simp]
theorem hom.app.underlying {Z : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Groupoids.toNatTrans (mapCompIso F G).hom).app A) =
      𝟙 (((BasedCategory.Inertia.map
        (FiberedCategoryOver.Groupoids.toBasedFunctor F)).comp
          (BasedCategory.Inertia.map
            (FiberedCategoryOver.Groupoids.toBasedFunctor G))).obj A).obj := sorry

/-- The underlying arrow of an inverse composition-comparison component is an identity. -/
@[simp]
theorem inv.app.underlying {Z : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Groupoids.toNatTrans (mapCompIso F G).inv).app A) =
      𝟙 (((BasedCategory.Inertia.map
        (FiberedCategoryOver.Groupoids.toBasedFunctor F)).comp
          (BasedCategory.Inertia.map
            (FiberedCategoryOver.Groupoids.toBasedFunctor G))).obj A).obj := sorry

end mapCompIso

end FiberedCategoryOver.Groupoids.Inertia

end CategoryTheory
