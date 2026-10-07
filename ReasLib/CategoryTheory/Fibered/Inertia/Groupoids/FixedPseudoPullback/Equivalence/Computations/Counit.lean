module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.FixedPseudoPullback.Equivalence.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Counit.Computations
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso

/-!
# Counit computations for the groupoid-fibred relative-inertia equivalence

This leaf exposes the counit and its base, first, and second projections.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.Groupoids.RelativeInertia

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {X Y :
  FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}

/-- The based projection of the forward counit cell of the groupoid-fibration relative-inertia
equivalence is the explicit comparison counit. -/
@[simp]
theorem diagonalComparisonEquivalence.counit.hom (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toBasedNatTrans
        ((diagonalComparisonEquivalence F).counit.hom) =
      (BasedFunctor.RelativeInertia.diagonalComparison.counitIso
        (FiberedCategoryOver.Groupoids.toBasedFunctor F)).hom := sorry

/-- The based projection of the inverse counit cell of the groupoid-fibration relative-inertia
equivalence is the inverse explicit comparison counit. -/
@[simp]
theorem diagonalComparisonEquivalence.counit.inv (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toBasedNatTrans
        ((diagonalComparisonEquivalence F).counit.inv) =
      (BasedFunctor.RelativeInertia.diagonalComparison.counitIso
        (FiberedCategoryOver.Groupoids.toBasedFunctor F)).inv := sorry

/-- The forward counit component of the groupoid-fibred relative-inertia comparison equivalence
is the explicit based comparison-counit component. -/
@[simp]
theorem diagonalComparisonEquivalence.counit.app.hom
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))) :
    (FiberedCategoryOver.Groupoids.toNatTrans
      ((diagonalComparisonEquivalence F).counit.hom)).app P =
      (BasedFunctor.RelativeInertia.diagonalComparison.counitIso.app
        (FiberedCategoryOver.Groupoids.toBasedFunctor F) P).hom := sorry

/-- The inverse counit component of the groupoid-fibred relative-inertia comparison equivalence is
the inverse explicit based comparison-counit component. -/
@[simp]
theorem diagonalComparisonEquivalence.counit.app.inv
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))) :
    (FiberedCategoryOver.Groupoids.toNatTrans
      ((diagonalComparisonEquivalence F).counit.inv)).app P =
      (BasedFunctor.RelativeInertia.diagonalComparison.counitIso.app
        (FiberedCategoryOver.Groupoids.toBasedFunctor F) P).inv := sorry

/-- The forward groupoid-fibred comparison-counit components are natural in morphisms of the
fixed self-two-fibre-product. -/
@[reassoc]
theorem diagonalComparisonEquivalence.counit.naturality
    (F : X ⟶ Y)
    {P Q : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))}
    (φ : P ⟶ Q) :
    (FiberedCategoryOver.Groupoids.toFunctor
        ((diagonalComparisonEquivalence F).inv ≫
          (diagonalComparisonEquivalence F).hom)).map φ ≫
        (FiberedCategoryOver.Groupoids.toNatTrans
          ((diagonalComparisonEquivalence F).counit.hom)).app Q =
      (FiberedCategoryOver.Groupoids.toNatTrans
          ((diagonalComparisonEquivalence F).counit.hom)).app P ≫ φ := sorry

/-- The inverse groupoid-fibred comparison-counit components satisfy the reverse naturality
equation. -/
@[reassoc]
theorem diagonalComparisonEquivalence.counit.invNaturality
    (F : X ⟶ Y)
    {P Q : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))}
    (φ : P ⟶ Q) :
    (FiberedCategoryOver.Groupoids.toNatTrans
        ((diagonalComparisonEquivalence F).counit.inv)).app P ≫
        (FiberedCategoryOver.Groupoids.toFunctor
          ((diagonalComparisonEquivalence F).inv ≫
            (diagonalComparisonEquivalence F).hom)).map φ =
      φ ≫ (FiberedCategoryOver.Groupoids.toNatTrans
        ((diagonalComparisonEquivalence F).counit.inv)).app Q := sorry

/-- Every forward groupoid-fibred comparison-counit component is vertical over its base
object. -/
theorem diagonalComparisonEquivalence.counit.app.hom.isHomLift
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))) :
    (FiberedCategoryOver.Groupoids.p (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))).IsHomLift
      (𝟙 ((FiberedCategoryOver.Groupoids.p (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))).obj P))
      ((FiberedCategoryOver.Groupoids.toNatTrans
        ((diagonalComparisonEquivalence F).counit.hom)).app P) := sorry

/-- Every inverse groupoid-fibred comparison-counit component is vertical over its base
object. -/
theorem diagonalComparisonEquivalence.counit.app.inv.isHomLift
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))) :
    (FiberedCategoryOver.Groupoids.p (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))).IsHomLift
      (𝟙 ((FiberedCategoryOver.Groupoids.p (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))).obj P))
      ((FiberedCategoryOver.Groupoids.toNatTrans
        ((diagonalComparisonEquivalence F).counit.inv)).app P) := sorry

/-- The base projection of the forward groupoid-fibred counit component is the neutral counit
base component. -/
@[simp]
theorem diagonalComparisonEquivalence.counit.app.base.hom
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))) :
    BasedCategory.PseudoPullback.baseMap
        ((FiberedCategoryOver.Groupoids.toNatTrans
          ((diagonalComparisonEquivalence F).counit.hom)).app P) =
      (BasedFunctor.RelativeInertia.diagonalComparison.counitIso.app.baseIso
        (FiberedCategoryOver.Groupoids.toBasedFunctor F) P).hom := sorry

/-- The first projection of the forward groupoid-fibred counit component is the neutral first
counit component. -/
@[simp]
theorem diagonalComparisonEquivalence.counit.app.fst.hom
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))) :
    BasedCategory.PseudoPullback.fstMap
        ((FiberedCategoryOver.Groupoids.toNatTrans
          ((diagonalComparisonEquivalence F).counit.hom)).app P) =
      (BasedFunctor.RelativeInertia.diagonalComparison.counitIso.app.fstIso
        (FiberedCategoryOver.Groupoids.toBasedFunctor F) P).hom := sorry

/-- The second projection of the forward groupoid-fibred counit component is the neutral second
counit component. -/
@[simp]
theorem diagonalComparisonEquivalence.counit.app.snd.hom
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))) :
    BasedCategory.PseudoPullback.sndMap
        ((FiberedCategoryOver.Groupoids.toNatTrans
          ((diagonalComparisonEquivalence F).counit.hom)).app P) =
      (BasedFunctor.RelativeInertia.diagonalComparison.counitIso.app.sndIso
        (FiberedCategoryOver.Groupoids.toBasedFunctor F) P).hom := sorry

/-- The base projection of the inverse groupoid-fibred counit component is the neutral inverse
counit base component. -/
@[simp]
theorem diagonalComparisonEquivalence.counit.app.base.inv
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))) :
    BasedCategory.PseudoPullback.baseMap
        ((FiberedCategoryOver.Groupoids.toNatTrans
          ((diagonalComparisonEquivalence F).counit.inv)).app P) =
      (BasedFunctor.RelativeInertia.diagonalComparison.counitIso.app.baseIso
        (FiberedCategoryOver.Groupoids.toBasedFunctor F) P).inv := sorry

/-- The first projection of the inverse groupoid-fibred counit component is the neutral inverse
first counit component. -/
@[simp]
theorem diagonalComparisonEquivalence.counit.app.fst.inv
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))) :
    BasedCategory.PseudoPullback.fstMap
        ((FiberedCategoryOver.Groupoids.toNatTrans
          ((diagonalComparisonEquivalence F).counit.inv)).app P) =
      (BasedFunctor.RelativeInertia.diagonalComparison.counitIso.app.fstIso
        (FiberedCategoryOver.Groupoids.toBasedFunctor F) P).inv := sorry

/-- The second projection of the inverse groupoid-fibred counit component is the neutral inverse
second counit component. -/
@[simp]
theorem diagonalComparisonEquivalence.counit.app.snd.inv
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))) :
    BasedCategory.PseudoPullback.sndMap
        ((FiberedCategoryOver.Groupoids.toNatTrans
          ((diagonalComparisonEquivalence F).counit.inv)).app P) =
      (BasedFunctor.RelativeInertia.diagonalComparison.counitIso.app.sndIso
        (FiberedCategoryOver.Groupoids.toBasedFunctor F) P).inv := sorry

end FiberedCategoryOver.Groupoids.RelativeInertia
end CategoryTheory
