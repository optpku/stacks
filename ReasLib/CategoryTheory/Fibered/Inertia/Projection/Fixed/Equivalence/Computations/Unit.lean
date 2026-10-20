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
theorem diagonalComparisonEquivalence.unit.naturality
    (F : X ⟶ Y)
    {A B : FiberedCategoryOver.total (relativeInertia F)}
    (φ : A ⟶ B) :
    let H := FiberedCategoryOver.toFunctor
      ((RelativeInertia.diagonalComparisonEquivalence F).hom ≫ (RelativeInertia.diagonalComparisonEquivalence F).inv)
    let η : 𝟭 (FiberedCategoryOver.total (relativeInertia F)) ⟶ H :=
      FiberedCategoryOver.toNatTrans ((RelativeInertia.diagonalComparisonEquivalence F).unit.hom)
    φ ≫ η.app B = η.app A ≫ H.map φ := sorry

/-- The forward unit naturality equation after postcomposition, with the original public
parenthesization retained. -/
theorem diagonalComparisonEquivalence.unit.naturality_assoc
    (F : X ⟶ Y) {A B : FiberedCategoryOver.total (relativeInertia F)} (φ : A ⟶ B)
    {Z : FiberedCategoryOver.total (relativeInertia F)}
    (h : (FiberedCategoryOver.toFunctor
      ((RelativeInertia.diagonalComparisonEquivalence F).hom ≫ (RelativeInertia.diagonalComparisonEquivalence F).inv)).obj B ⟶ Z) :
    let H := FiberedCategoryOver.toFunctor
      ((RelativeInertia.diagonalComparisonEquivalence F).hom ≫ (RelativeInertia.diagonalComparisonEquivalence F).inv)
    let η : 𝟭 (FiberedCategoryOver.total (relativeInertia F)) ⟶ H :=
      FiberedCategoryOver.toNatTrans ((RelativeInertia.diagonalComparisonEquivalence F).unit.hom)
    φ ≫ (η.app B ≫ h) = (η.app A ≫ H.map φ) ≫ h := by
  dsimp only
  rw [← Category.assoc]
  exact congrArg (fun k => k ≫ h) (diagonalComparisonEquivalence.unit.naturality F φ)


/-- The inverse fibred comparison-unit components satisfy the reverse naturality equation. -/
theorem diagonalComparisonEquivalence.unit.invNaturality
    (F : X ⟶ Y)
    {A B : FiberedCategoryOver.total (relativeInertia F)}
    (φ : A ⟶ B) :
    let H := FiberedCategoryOver.toFunctor
      ((RelativeInertia.diagonalComparisonEquivalence F).hom ≫ (RelativeInertia.diagonalComparisonEquivalence F).inv)
    let η : H ⟶ 𝟭 (FiberedCategoryOver.total (relativeInertia F)) :=
      FiberedCategoryOver.toNatTrans ((RelativeInertia.diagonalComparisonEquivalence F).unit.inv)
    η.app A ≫ φ = H.map φ ≫ η.app B := sorry

/-- The inverse unit naturality equation after postcomposition, with the original public
parenthesization retained. -/
theorem diagonalComparisonEquivalence.unit.invNaturality_assoc
    (F : X ⟶ Y) {A B : FiberedCategoryOver.total (relativeInertia F)} (φ : A ⟶ B)
    {Z : FiberedCategoryOver.total (relativeInertia F)} (h : B ⟶ Z) :
    let H := FiberedCategoryOver.toFunctor
      ((RelativeInertia.diagonalComparisonEquivalence F).hom ≫ (RelativeInertia.diagonalComparisonEquivalence F).inv)
    let η : H ⟶ 𝟭 (FiberedCategoryOver.total (relativeInertia F)) :=
      FiberedCategoryOver.toNatTrans ((RelativeInertia.diagonalComparisonEquivalence F).unit.inv)
    η.app A ≫ (φ ≫ h) = (H.map φ ≫ η.app B) ≫ h := by
  dsimp only
  rw [← Category.assoc]
  exact congrArg (fun k => k ≫ h) (diagonalComparisonEquivalence.unit.invNaturality F φ)


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
