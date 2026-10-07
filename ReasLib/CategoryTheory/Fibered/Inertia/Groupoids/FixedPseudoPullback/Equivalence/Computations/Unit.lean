module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.FixedPseudoPullback.Equivalence.Construction
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso

/-!
# Unit computations for the groupoid-fibred relative-inertia equivalence

This leaf exposes the adjusted unit and its total-category components.
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

/-- The based projection of the forward unit cell of the groupoid-fibration relative-inertia
equivalence is the canonical adjustment of the explicit unit against the explicit counit. -/
@[simp]
theorem diagonalComparisonEquivalence.unit.hom (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toBasedNatTrans
        ((diagonalComparisonEquivalence F).unit.hom) =
      (Bicategory.Equivalence.adjointifyUnit
        (BasedFunctor.RelativeInertia.diagonalComparison.unitIso
          (FiberedCategoryOver.Groupoids.toBasedFunctor F))
        (BasedFunctor.RelativeInertia.diagonalComparison.counitIso
          (FiberedCategoryOver.Groupoids.toBasedFunctor F))).hom := sorry

/-- The based projection of the inverse unit cell of the groupoid-fibration relative-inertia
equivalence is the inverse canonical adjusted unit. -/
@[simp]
theorem diagonalComparisonEquivalence.unit.inv (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toBasedNatTrans
        ((diagonalComparisonEquivalence F).unit.inv) =
      (Bicategory.Equivalence.adjointifyUnit
        (BasedFunctor.RelativeInertia.diagonalComparison.unitIso
          (FiberedCategoryOver.Groupoids.toBasedFunctor F))
        (BasedFunctor.RelativeInertia.diagonalComparison.counitIso
          (FiberedCategoryOver.Groupoids.toBasedFunctor F))).inv := sorry

/-- The forward total-category component of the groupoid-fibred comparison unit is the component
of the canonical adjusted based unit. -/
@[simp]
theorem diagonalComparisonEquivalence.unit.app.hom
    (F : X ⟶ Y)
    (A : FiberedCategoryOver.Groupoids.total (relativeInertia F)) :
    (FiberedCategoryOver.Groupoids.toNatTrans
      ((diagonalComparisonEquivalence F).unit.hom)).app A =
      (BasedNatIso.toNatIso
        (Bicategory.Equivalence.adjointifyUnit
          (BasedFunctor.RelativeInertia.diagonalComparison.unitIso
            (FiberedCategoryOver.Groupoids.toBasedFunctor F))
          (BasedFunctor.RelativeInertia.diagonalComparison.counitIso
            (FiberedCategoryOver.Groupoids.toBasedFunctor F)))).hom.app A := sorry

/-- The inverse total-category component of the groupoid-fibred comparison unit is the component
of the inverse canonical adjusted unit. -/
@[simp]
theorem diagonalComparisonEquivalence.unit.app.inv
    (F : X ⟶ Y)
    (A : FiberedCategoryOver.Groupoids.total (relativeInertia F)) :
    (FiberedCategoryOver.Groupoids.toNatTrans
      ((diagonalComparisonEquivalence F).unit.inv)).app A =
      (BasedNatIso.toNatIso
        (Bicategory.Equivalence.adjointifyUnit
          (BasedFunctor.RelativeInertia.diagonalComparison.unitIso
            (FiberedCategoryOver.Groupoids.toBasedFunctor F))
          (BasedFunctor.RelativeInertia.diagonalComparison.counitIso
            (FiberedCategoryOver.Groupoids.toBasedFunctor F)))).inv.app A := sorry

/-- The forward groupoid-fibred comparison-unit components are natural in morphisms of the
fixed relative-inertia category. -/
@[reassoc]
theorem diagonalComparisonEquivalence.unit.naturality
    (F : X ⟶ Y)
    {A B : FiberedCategoryOver.Groupoids.total (relativeInertia F)}
    (φ : A ⟶ B) :
    φ ≫ (FiberedCategoryOver.Groupoids.toNatTrans
        ((diagonalComparisonEquivalence F).unit.hom)).app B =
      (FiberedCategoryOver.Groupoids.toNatTrans
          ((diagonalComparisonEquivalence F).unit.hom)).app A ≫
        (FiberedCategoryOver.Groupoids.toFunctor
          ((diagonalComparisonEquivalence F).hom ≫
            (diagonalComparisonEquivalence F).inv)).map φ := sorry

/-- The inverse groupoid-fibred comparison-unit components satisfy the reverse naturality
equation. -/
@[reassoc]
theorem diagonalComparisonEquivalence.unit.invNaturality
    (F : X ⟶ Y)
    {A B : FiberedCategoryOver.Groupoids.total (relativeInertia F)}
    (φ : A ⟶ B) :
    (FiberedCategoryOver.Groupoids.toNatTrans
        ((diagonalComparisonEquivalence F).unit.inv)).app A ≫ φ =
      (FiberedCategoryOver.Groupoids.toFunctor
          ((diagonalComparisonEquivalence F).hom ≫
            (diagonalComparisonEquivalence F).inv)).map φ ≫
        (FiberedCategoryOver.Groupoids.toNatTrans
          ((diagonalComparisonEquivalence F).unit.inv)).app B := sorry

/-- Every forward groupoid-fibred comparison-unit component is vertical over its base object. -/
theorem diagonalComparisonEquivalence.unit.app.hom.isHomLift
    (F : X ⟶ Y)
    (A : FiberedCategoryOver.Groupoids.total (relativeInertia F)) :
    (relativeInertia F).p.IsHomLift
      (𝟙 ((relativeInertia F).p.obj A))
      ((FiberedCategoryOver.Groupoids.toNatTrans
        ((diagonalComparisonEquivalence F).unit.hom)).app A) := sorry

/-- Every inverse groupoid-fibred comparison-unit component is vertical over its base object. -/
theorem diagonalComparisonEquivalence.unit.app.inv.isHomLift
    (F : X ⟶ Y)
    (A : FiberedCategoryOver.Groupoids.total (relativeInertia F)) :
    (relativeInertia F).p.IsHomLift
      (𝟙 ((relativeInertia F).p.obj A))
      ((FiberedCategoryOver.Groupoids.toNatTrans
        ((diagonalComparisonEquivalence F).unit.inv)).app A) := sorry

/-- The underlying arrow of a forward groupoid-fibred comparison-unit component is an identity. -/
@[simp]
theorem diagonalComparisonEquivalence.unit.app.underlying.hom
    (F : X ⟶ Y) (A : FiberedCategoryOver.Groupoids.total (relativeInertia F)) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.Groupoids.toNatTrans
          ((diagonalComparisonEquivalence F).unit.hom)).app A) =
      𝟙 A.obj := sorry

/-- The underlying arrow of an inverse groupoid-fibred comparison-unit component is an identity. -/
@[simp]
theorem diagonalComparisonEquivalence.unit.app.underlying.inv
    (F : X ⟶ Y) (A : FiberedCategoryOver.Groupoids.total (relativeInertia F)) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.Groupoids.toNatTrans
          ((diagonalComparisonEquivalence F).unit.inv)).app A) =
      𝟙 A.obj := sorry

end FiberedCategoryOver.Groupoids.RelativeInertia
end CategoryTheory
