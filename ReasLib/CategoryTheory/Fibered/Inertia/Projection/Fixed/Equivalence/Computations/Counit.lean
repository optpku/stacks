module

public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Fixed.Equivalence.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Counit.Computations
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso

/-!
# Counit computations for the fibred relative-inertia equivalence

This leaf exposes the counit and its base, first, and second projections.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.RelativeInertia

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, max w (max u v), v} C}

/-- The based projection of the forward counit cell of the canonical relative-inertia equivalence is
the explicit comparison counit. -/
@[simp]
theorem diagonalComparisonEquivalence.counit.hom (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedNatTrans
        ((RelativeInertia.diagonalComparisonEquivalence F).counit.hom) =
      (BasedFunctor.RelativeInertia.diagonalComparison.counitIso
        (FiberedCategoryOver.toBasedFunctor F)).hom := sorry

/-- The based projection of the inverse counit cell of the canonical relative-inertia equivalence is
the inverse explicit comparison counit. -/
@[simp]
theorem diagonalComparisonEquivalence.counit.inv (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedNatTrans
        ((RelativeInertia.diagonalComparisonEquivalence F).counit.inv) =
      (BasedFunctor.RelativeInertia.diagonalComparison.counitIso
        (FiberedCategoryOver.toBasedFunctor F)).inv := sorry

/-- The forward counit component of the fibred relative-inertia comparison equivalence is the
explicit based comparison-counit component. -/
@[simp]
theorem diagonalComparisonEquivalence.counit.app.hom
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))) :
    (FiberedCategoryOver.toNatTrans
      ((RelativeInertia.diagonalComparisonEquivalence F).counit.hom)).app P =
      (BasedFunctor.RelativeInertia.diagonalComparison.counitIso.app
        (FiberedCategoryOver.toBasedFunctor F) P).hom := sorry

/-- The inverse counit component of the fibred relative-inertia comparison equivalence is the
inverse explicit based comparison-counit component. -/
@[simp]
theorem diagonalComparisonEquivalence.counit.app.inv
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))) :
    (FiberedCategoryOver.toNatTrans
      ((RelativeInertia.diagonalComparisonEquivalence F).counit.inv)).app P =
      (BasedFunctor.RelativeInertia.diagonalComparison.counitIso.app
        (FiberedCategoryOver.toBasedFunctor F) P).inv := sorry

/-- The forward fibred comparison-counit components are natural in morphisms of the fixed
self-two-fibre-product. -/
@[reassoc]
theorem diagonalComparisonEquivalence.counit.naturality
    (F : X ⟶ Y)
    {P Q : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))}
    (φ : P ⟶ Q) :
    (FiberedCategoryOver.toFunctor
        ((RelativeInertia.diagonalComparisonEquivalence F).inv ≫
          (RelativeInertia.diagonalComparisonEquivalence F).hom)).map φ ≫
        (FiberedCategoryOver.toNatTrans
          ((RelativeInertia.diagonalComparisonEquivalence F).counit.hom)).app Q =
      (FiberedCategoryOver.toNatTrans
          ((RelativeInertia.diagonalComparisonEquivalence F).counit.hom)).app P ≫ φ := sorry

/-- The inverse fibred comparison-counit components satisfy the reverse naturality equation. -/
@[reassoc]
theorem diagonalComparisonEquivalence.counit.invNaturality
    (F : X ⟶ Y)
    {P Q : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))}
    (φ : P ⟶ Q) :
    (FiberedCategoryOver.toNatTrans
        ((RelativeInertia.diagonalComparisonEquivalence F).counit.inv)).app P ≫
        (FiberedCategoryOver.toFunctor
          ((RelativeInertia.diagonalComparisonEquivalence F).inv ≫
            (RelativeInertia.diagonalComparisonEquivalence F).hom)).map φ =
      φ ≫ (FiberedCategoryOver.toNatTrans
        ((RelativeInertia.diagonalComparisonEquivalence F).counit.inv)).app Q := sorry

/-- Every forward fibred comparison-counit component is vertical over its base object. -/
theorem diagonalComparisonEquivalence.counit.app.hom.isHomLift
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))) :
    (FiberedCategoryOver.p (LocallyInduced.TwoFibreProduct.apex
        (RelativeInertia.relativeDiagonal F)
        (RelativeInertia.relativeDiagonal F))).IsHomLift
      (𝟙 ((FiberedCategoryOver.p (LocallyInduced.TwoFibreProduct.apex
        (RelativeInertia.relativeDiagonal F)
        (RelativeInertia.relativeDiagonal F))).obj P))
      ((FiberedCategoryOver.toNatTrans
        ((RelativeInertia.diagonalComparisonEquivalence F).counit.hom)).app P) := sorry

/-- Every inverse fibred comparison-counit component is vertical over its base object. -/
theorem diagonalComparisonEquivalence.counit.app.inv.isHomLift
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))) :
    (FiberedCategoryOver.p (LocallyInduced.TwoFibreProduct.apex
        (RelativeInertia.relativeDiagonal F)
        (RelativeInertia.relativeDiagonal F))).IsHomLift
      (𝟙 ((FiberedCategoryOver.p (LocallyInduced.TwoFibreProduct.apex
        (RelativeInertia.relativeDiagonal F)
        (RelativeInertia.relativeDiagonal F))).obj P))
      ((FiberedCategoryOver.toNatTrans
        ((RelativeInertia.diagonalComparisonEquivalence F).counit.inv)).app P) := sorry

/-- The base projection of the forward fibred counit component is the neutral counit base
component. -/
@[simp]
theorem diagonalComparisonEquivalence.counit.app.base.hom
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))) :
    BasedCategory.PseudoPullback.baseMap
        ((FiberedCategoryOver.toNatTrans
          ((RelativeInertia.diagonalComparisonEquivalence F).counit.hom)).app P) =
      (BasedFunctor.RelativeInertia.diagonalComparison.counitIso.app.baseIso
        (FiberedCategoryOver.toBasedFunctor F) P).hom := sorry

/-- The first projection of the forward fibred counit component is the neutral counit first
component. -/
@[simp]
theorem diagonalComparisonEquivalence.counit.app.fst.hom
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))) :
    BasedCategory.PseudoPullback.fstMap
        ((FiberedCategoryOver.toNatTrans
          ((RelativeInertia.diagonalComparisonEquivalence F).counit.hom)).app P) =
      (BasedFunctor.RelativeInertia.diagonalComparison.counitIso.app.fstIso
        (FiberedCategoryOver.toBasedFunctor F) P).hom := sorry

/-- The second projection of the forward fibred counit component is the neutral counit second
component. -/
@[simp]
theorem diagonalComparisonEquivalence.counit.app.snd.hom
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))) :
    BasedCategory.PseudoPullback.sndMap
        ((FiberedCategoryOver.toNatTrans
          ((RelativeInertia.diagonalComparisonEquivalence F).counit.hom)).app P) =
      (BasedFunctor.RelativeInertia.diagonalComparison.counitIso.app.sndIso
        (FiberedCategoryOver.toBasedFunctor F) P).hom := sorry

/-- The base projection of the inverse fibred counit component is the neutral inverse counit
base component. -/
@[simp]
theorem diagonalComparisonEquivalence.counit.app.base.inv
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))) :
    BasedCategory.PseudoPullback.baseMap
        ((FiberedCategoryOver.toNatTrans
          ((RelativeInertia.diagonalComparisonEquivalence F).counit.inv)).app P) =
      (BasedFunctor.RelativeInertia.diagonalComparison.counitIso.app.baseIso
        (FiberedCategoryOver.toBasedFunctor F) P).inv := sorry

/-- The first projection of the inverse fibred counit component is the neutral inverse counit
first component. -/
@[simp]
theorem diagonalComparisonEquivalence.counit.app.fst.inv
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))) :
    BasedCategory.PseudoPullback.fstMap
        ((FiberedCategoryOver.toNatTrans
          ((RelativeInertia.diagonalComparisonEquivalence F).counit.inv)).app P) =
      (BasedFunctor.RelativeInertia.diagonalComparison.counitIso.app.fstIso
        (FiberedCategoryOver.toBasedFunctor F) P).inv := sorry

/-- The second projection of the inverse fibred counit component is the neutral inverse counit
second component. -/
@[simp]
theorem diagonalComparisonEquivalence.counit.app.snd.inv
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))) :
    BasedCategory.PseudoPullback.sndMap
        ((FiberedCategoryOver.toNatTrans
          ((RelativeInertia.diagonalComparisonEquivalence F).counit.inv)).app P) =
      (BasedFunctor.RelativeInertia.diagonalComparison.counitIso.app.sndIso
        (FiberedCategoryOver.toBasedFunctor F) P).inv := sorry

end FiberedCategoryOver.RelativeInertia
end CategoryTheory
