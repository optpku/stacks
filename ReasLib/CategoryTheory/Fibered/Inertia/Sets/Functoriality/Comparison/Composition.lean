module

public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.Functoriality.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Comparison.Composition
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso

/-!
# Composition comparison for typed set-fibred inertia

The comparison is the induced-bicategory lift of the neutral based composition
comparison. Component formulas keep downstream code independent of constructors.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Sets.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Sets.{u, v, w, vS} C}

/-- The composition comparison for typed set-fibred inertia. -/
def mapCompIso {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    map (F ≫ G) ≅ map F ≫ map G :=
  Bicategory.InducedBicategory.isoMk
    (BasedCategory.Inertia.mapCompIso
      (FiberedCategoryOver.Sets.toBasedFunctor F)
      (FiberedCategoryOver.Sets.toBasedFunctor G))

namespace mapCompIso

/-- The ambient forward composition-comparison cell is the neutral one. -/
@[simp]
theorem hom.toBasedNatTrans {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    FiberedCategoryOver.Sets.toBasedNatTrans (mapCompIso F G).hom =
      (BasedCategory.Inertia.mapCompIso
        (FiberedCategoryOver.Sets.toBasedFunctor F)
        (FiberedCategoryOver.Sets.toBasedFunctor G)).hom := sorry

/-- The ambient inverse composition-comparison cell is the neutral one. -/
@[simp]
theorem inv.toBasedNatTrans {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    FiberedCategoryOver.Sets.toBasedNatTrans (mapCompIso F G).inv =
      (BasedCategory.Inertia.mapCompIso
        (FiberedCategoryOver.Sets.toBasedFunctor F)
        (FiberedCategoryOver.Sets.toBasedFunctor G)).inv := sorry

/-- The forward composition-comparison component is the neutral component. -/
@[simp]
theorem hom.app {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    (FiberedCategoryOver.Sets.toNatTrans (mapCompIso F G).hom).app A =
      (BasedCategory.Inertia.mapCompIso.app
        (FiberedCategoryOver.Sets.toBasedFunctor F)
        (FiberedCategoryOver.Sets.toBasedFunctor G) A).hom := sorry

/-- The inverse composition-comparison component is the neutral component. -/
@[simp]
theorem inv.app {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    (FiberedCategoryOver.Sets.toNatTrans (mapCompIso F G).inv).app A =
      (BasedCategory.Inertia.mapCompIso.app
        (FiberedCategoryOver.Sets.toBasedFunctor F)
        (FiberedCategoryOver.Sets.toBasedFunctor G) A).inv := sorry

/-- Every forward set-fibred composition-comparison component lies over the identity of its source
base object. -/
theorem hom.app.isHomLift {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    Z.inertia.p.IsHomLift (𝟙 (X.inertia.p.obj A))
      ((FiberedCategoryOver.Sets.toNatTrans (mapCompIso F G).hom).app A) := sorry

/-- Every inverse set-fibred composition-comparison component lies over the identity of its source
base object. -/
theorem inv.app.isHomLift {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    Z.inertia.p.IsHomLift (𝟙 (X.inertia.p.obj A))
      ((FiberedCategoryOver.Sets.toNatTrans (mapCompIso F G).inv).app A) := sorry

/-- The underlying arrow of a forward composition-comparison component is an identity. -/
@[simp]
theorem hom.app.underlying {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Sets.toNatTrans (mapCompIso F G).hom).app A) =
      𝟙 (((BasedCategory.Inertia.map
        (FiberedCategoryOver.Sets.toBasedFunctor F)).comp
          (BasedCategory.Inertia.map
            (FiberedCategoryOver.Sets.toBasedFunctor G))).obj A).obj := sorry

/-- The underlying arrow of an inverse composition-comparison component is an identity. -/
@[simp]
theorem inv.app.underlying {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Sets.toNatTrans (mapCompIso F G).inv).app A) =
      𝟙 (((BasedCategory.Inertia.map
        (FiberedCategoryOver.Sets.toBasedFunctor F)).comp
          (BasedCategory.Inertia.map
            (FiberedCategoryOver.Sets.toBasedFunctor G))).obj A).obj := sorry

end mapCompIso

end FiberedCategoryOver.Sets.Inertia

end CategoryTheory
