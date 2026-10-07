module

public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Fixed.Equivalence.Construction
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso

/-!
# Unit computations for the fibred relative-inertia equivalence

This leaf exposes the adjusted unit and its total-category components.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.RelativeInertia

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, max w (max u v), v} C}

/-- The based projection of the forward unit cell of the canonical relative-inertia equivalence is
the canonical adjustment of the explicit based unit against the explicit based counit. -/
@[simp]
theorem diagonalComparisonEquivalence.unit.hom (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedNatTrans
        ((RelativeInertia.diagonalComparisonEquivalence F).unit.hom) =
      (Bicategory.Equivalence.adjointifyUnit
        (BasedFunctor.RelativeInertia.diagonalComparison.unitIso
          (FiberedCategoryOver.toBasedFunctor F))
        (BasedFunctor.RelativeInertia.diagonalComparison.counitIso
          (FiberedCategoryOver.toBasedFunctor F))).hom := sorry

/-- The based projection of the inverse unit cell of the canonical relative-inertia equivalence is
the inverse of the canonical adjusted unit. -/
@[simp]
theorem diagonalComparisonEquivalence.unit.inv (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedNatTrans
        ((RelativeInertia.diagonalComparisonEquivalence F).unit.inv) =
      (Bicategory.Equivalence.adjointifyUnit
        (BasedFunctor.RelativeInertia.diagonalComparison.unitIso
          (FiberedCategoryOver.toBasedFunctor F))
        (BasedFunctor.RelativeInertia.diagonalComparison.counitIso
          (FiberedCategoryOver.toBasedFunctor F))).inv := sorry

/-- The forward total-category component of the fibred comparison unit is the component of the
canonical adjusted based unit. -/
@[simp]
theorem diagonalComparisonEquivalence.unit.app.hom
    (F : X ⟶ Y) (A : FiberedCategoryOver.total (relativeInertia F)) :
    (FiberedCategoryOver.toNatTrans
      ((RelativeInertia.diagonalComparisonEquivalence F).unit.hom)).app A =
      (BasedNatIso.toNatIso
        (Bicategory.Equivalence.adjointifyUnit
          (BasedFunctor.RelativeInertia.diagonalComparison.unitIso
            (FiberedCategoryOver.toBasedFunctor F))
          (BasedFunctor.RelativeInertia.diagonalComparison.counitIso
            (FiberedCategoryOver.toBasedFunctor F)))).hom.app A := sorry

/-- The inverse total-category component of the fibred comparison unit is the component of the
inverse canonical adjusted based unit. -/
@[simp]
theorem diagonalComparisonEquivalence.unit.app.inv
    (F : X ⟶ Y) (A : FiberedCategoryOver.total (relativeInertia F)) :
    (FiberedCategoryOver.toNatTrans
      ((RelativeInertia.diagonalComparisonEquivalence F).unit.inv)).app A =
      (BasedNatIso.toNatIso
        (Bicategory.Equivalence.adjointifyUnit
          (BasedFunctor.RelativeInertia.diagonalComparison.unitIso
            (FiberedCategoryOver.toBasedFunctor F))
          (BasedFunctor.RelativeInertia.diagonalComparison.counitIso
            (FiberedCategoryOver.toBasedFunctor F)))).inv.app A := sorry

/-- The forward fibred comparison-unit components are natural in morphisms of the fixed
relative-inertia category. -/
@[reassoc]
theorem diagonalComparisonEquivalence.unit.naturality
    (F : X ⟶ Y)
    {A B : FiberedCategoryOver.total (relativeInertia F)}
    (φ : A ⟶ B) :
    φ ≫ (FiberedCategoryOver.toNatTrans
        ((RelativeInertia.diagonalComparisonEquivalence F).unit.hom)).app B =
      (FiberedCategoryOver.toNatTrans
          ((RelativeInertia.diagonalComparisonEquivalence F).unit.hom)).app A ≫
        (FiberedCategoryOver.toFunctor
          ((RelativeInertia.diagonalComparisonEquivalence F).hom ≫
            (RelativeInertia.diagonalComparisonEquivalence F).inv)).map φ := sorry

/-- The inverse fibred comparison-unit components satisfy the reverse naturality equation. -/
@[reassoc]
theorem diagonalComparisonEquivalence.unit.invNaturality
    (F : X ⟶ Y)
    {A B : FiberedCategoryOver.total (relativeInertia F)}
    (φ : A ⟶ B) :
    (FiberedCategoryOver.toNatTrans
        ((RelativeInertia.diagonalComparisonEquivalence F).unit.inv)).app A ≫ φ =
      (FiberedCategoryOver.toFunctor
          ((RelativeInertia.diagonalComparisonEquivalence F).hom ≫
            (RelativeInertia.diagonalComparisonEquivalence F).inv)).map φ ≫
        (FiberedCategoryOver.toNatTrans
          ((RelativeInertia.diagonalComparisonEquivalence F).unit.inv)).app B := sorry

/-- Every forward fibred comparison-unit component is vertical over its base object. -/
theorem diagonalComparisonEquivalence.unit.app.hom.isHomLift
    (F : X ⟶ Y) (A : FiberedCategoryOver.total (relativeInertia F)) :
    (relativeInertia F).p.IsHomLift
      (𝟙 ((relativeInertia F).p.obj A))
      ((FiberedCategoryOver.toNatTrans
        ((RelativeInertia.diagonalComparisonEquivalence F).unit.hom)).app A) := sorry

/-- Every inverse fibred comparison-unit component is vertical over its base object. -/
theorem diagonalComparisonEquivalence.unit.app.inv.isHomLift
    (F : X ⟶ Y) (A : FiberedCategoryOver.total (relativeInertia F)) :
    (relativeInertia F).p.IsHomLift
      (𝟙 ((relativeInertia F).p.obj A))
      ((FiberedCategoryOver.toNatTrans
        ((RelativeInertia.diagonalComparisonEquivalence F).unit.inv)).app A) := sorry

/-- The underlying arrow of a forward fibred comparison-unit component is an identity. -/
@[simp]
theorem diagonalComparisonEquivalence.unit.app.underlying.hom
    (F : X ⟶ Y) (A : FiberedCategoryOver.total (relativeInertia F)) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans
          ((RelativeInertia.diagonalComparisonEquivalence F).unit.hom)).app A) =
      𝟙 A.obj := sorry

/-- The underlying arrow of an inverse fibred comparison-unit component is an identity. -/
@[simp]
theorem diagonalComparisonEquivalence.unit.app.underlying.inv
    (F : X ⟶ Y) (A : FiberedCategoryOver.total (relativeInertia F)) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans
          ((RelativeInertia.diagonalComparisonEquivalence F).unit.inv)).app A) =
      𝟙 A.obj := sorry

end FiberedCategoryOver.RelativeInertia
end CategoryTheory
