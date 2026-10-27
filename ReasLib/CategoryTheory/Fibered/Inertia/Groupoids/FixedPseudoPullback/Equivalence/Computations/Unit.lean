/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
          (FiberedCategoryOver.Groupoids.toBasedFunctor F))).hom := rfl

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
          (FiberedCategoryOver.Groupoids.toBasedFunctor F))).inv := rfl

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
            (FiberedCategoryOver.Groupoids.toBasedFunctor F)))).hom.app A := rfl

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
            (FiberedCategoryOver.Groupoids.toBasedFunctor F)))).inv.app A := rfl

/-- The forward groupoid-fibred comparison-unit components are natural in morphisms of the
fixed relative-inertia category. -/
theorem diagonalComparisonEquivalence.unit.naturality
    (F : X ⟶ Y)
    {A B : FiberedCategoryOver.Groupoids.total (relativeInertia F)}
    (φ : A ⟶ B) :
    let H := FiberedCategoryOver.Groupoids.toFunctor
      ((diagonalComparisonEquivalence F).hom ≫ (diagonalComparisonEquivalence F).inv)
    let η : 𝟭 (FiberedCategoryOver.Groupoids.total (relativeInertia F)) ⟶ H :=
      FiberedCategoryOver.Groupoids.toNatTrans ((diagonalComparisonEquivalence F).unit.hom)
    φ ≫ η.app B = η.app A ≫ H.map φ := by
  let η : 𝟭 (FiberedCategoryOver.Groupoids.total (relativeInertia F)) ⟶ _ :=
    FiberedCategoryOver.Groupoids.toNatTrans ((diagonalComparisonEquivalence F).unit.hom)
  exact η.naturality φ

/-- The forward unit naturality equation after postcomposition, with the original public
parenthesization retained. -/
theorem diagonalComparisonEquivalence.unit.naturality_assoc
    (F : X ⟶ Y) {A B : FiberedCategoryOver.Groupoids.total (relativeInertia F)} (φ : A ⟶ B)
    {Z : FiberedCategoryOver.Groupoids.total (relativeInertia F)}
    (h : (FiberedCategoryOver.Groupoids.toFunctor
      ((diagonalComparisonEquivalence F).hom ≫ (diagonalComparisonEquivalence F).inv)).obj B ⟶ Z) :
    let H := FiberedCategoryOver.Groupoids.toFunctor
      ((diagonalComparisonEquivalence F).hom ≫ (diagonalComparisonEquivalence F).inv)
    let η : 𝟭 (FiberedCategoryOver.Groupoids.total (relativeInertia F)) ⟶ H :=
      FiberedCategoryOver.Groupoids.toNatTrans ((diagonalComparisonEquivalence F).unit.hom)
    φ ≫ (η.app B ≫ h) = (η.app A ≫ H.map φ) ≫ h := by
  dsimp only
  rw [← Category.assoc]
  exact congrArg (fun k => k ≫ h) (diagonalComparisonEquivalence.unit.naturality F φ)


/-- The inverse groupoid-fibred comparison-unit components satisfy the reverse naturality
equation. -/
theorem diagonalComparisonEquivalence.unit.invNaturality
    (F : X ⟶ Y)
    {A B : FiberedCategoryOver.Groupoids.total (relativeInertia F)}
    (φ : A ⟶ B) :
    let H := FiberedCategoryOver.Groupoids.toFunctor
      ((diagonalComparisonEquivalence F).hom ≫ (diagonalComparisonEquivalence F).inv)
    let η : H ⟶ 𝟭 (FiberedCategoryOver.Groupoids.total (relativeInertia F)) :=
      FiberedCategoryOver.Groupoids.toNatTrans ((diagonalComparisonEquivalence F).unit.inv)
    η.app A ≫ φ = H.map φ ≫ η.app B := by
  let η : _ ⟶ 𝟭 (FiberedCategoryOver.Groupoids.total (relativeInertia F)) :=
    FiberedCategoryOver.Groupoids.toNatTrans ((diagonalComparisonEquivalence F).unit.inv)
  exact (η.naturality φ).symm

/-- The inverse unit naturality equation after postcomposition, with the original public
parenthesization retained. -/
theorem diagonalComparisonEquivalence.unit.invNaturality_assoc
    (F : X ⟶ Y) {A B : FiberedCategoryOver.Groupoids.total (relativeInertia F)} (φ : A ⟶ B)
    {Z : FiberedCategoryOver.Groupoids.total (relativeInertia F)} (h : B ⟶ Z) :
    let H := FiberedCategoryOver.Groupoids.toFunctor
      ((diagonalComparisonEquivalence F).hom ≫ (diagonalComparisonEquivalence F).inv)
    let η : H ⟶ 𝟭 (FiberedCategoryOver.Groupoids.total (relativeInertia F)) :=
      FiberedCategoryOver.Groupoids.toNatTrans ((diagonalComparisonEquivalence F).unit.inv)
    η.app A ≫ (φ ≫ h) = (H.map φ ≫ η.app B) ≫ h := by
  dsimp only
  rw [← Category.assoc]
  exact congrArg (fun k => k ≫ h) (diagonalComparisonEquivalence.unit.invNaturality F φ)


/-- Every forward groupoid-fibred comparison-unit component is vertical over its base object. -/
theorem diagonalComparisonEquivalence.unit.app.hom.isHomLift
    (F : X ⟶ Y)
    (A : FiberedCategoryOver.Groupoids.total (relativeInertia F)) :
    (relativeInertia F).p.IsHomLift
      (𝟙 ((relativeInertia F).p.obj A))
      ((FiberedCategoryOver.Groupoids.toNatTrans
        ((diagonalComparisonEquivalence F).unit.hom)).app A) := by
  exact (FiberedCategoryOver.Groupoids.toBasedNatTrans
    ((diagonalComparisonEquivalence F).unit.hom)).isHomLift' A

/-- Every inverse groupoid-fibred comparison-unit component is vertical over its base object. -/
theorem diagonalComparisonEquivalence.unit.app.inv.isHomLift
    (F : X ⟶ Y)
    (A : FiberedCategoryOver.Groupoids.total (relativeInertia F)) :
    (relativeInertia F).p.IsHomLift
      (𝟙 ((relativeInertia F).p.obj A))
      ((FiberedCategoryOver.Groupoids.toNatTrans
        ((diagonalComparisonEquivalence F).unit.inv)).app A) := by
  exact (FiberedCategoryOver.Groupoids.toBasedNatTrans
    ((diagonalComparisonEquivalence F).unit.inv)).isHomLift' A

/-- The underlying arrow of a forward groupoid-fibred comparison-unit component is an identity. -/
@[simp]
theorem diagonalComparisonEquivalence.unit.app.underlying.hom
    (F : X ⟶ Y) (A : FiberedCategoryOver.Groupoids.total (relativeInertia F)) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.Groupoids.toNatTrans
          ((diagonalComparisonEquivalence F).unit.hom)).app A) =
      𝟙 A.obj := by
  -- The explicit unit, coherence cells, and first counit components are identities.
  change (𝟙 A.obj ≫
    ((𝟙 A.obj ≫ ((𝟙 A.obj ≫ (𝟙 A.obj ≫ 𝟙 A.obj)) ≫ 𝟙 A.obj)) ≫
      𝟙 A.obj)) = 𝟙 A.obj
  simp only [Category.id_comp]

/-- The underlying arrow of an inverse groupoid-fibred comparison-unit component is an identity. -/
@[simp]
theorem diagonalComparisonEquivalence.unit.app.underlying.inv
    (F : X ⟶ Y) (A : FiberedCategoryOver.Groupoids.total (relativeInertia F)) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.Groupoids.toNatTrans
          ((diagonalComparisonEquivalence F).unit.inv)).app A) =
      𝟙 A.obj := by
  have h := congrArg
    (fun η => CategoryTheory.RelativeInertia.hom
      ((FiberedCategoryOver.Groupoids.toNatTrans η).app A))
    (diagonalComparisonEquivalence F).unit.hom_inv_id
  change CategoryTheory.RelativeInertia.hom
      ((FiberedCategoryOver.Groupoids.toNatTrans
        ((diagonalComparisonEquivalence F).unit.hom)).app A) ≫
    CategoryTheory.RelativeInertia.hom
      ((FiberedCategoryOver.Groupoids.toNatTrans
        ((diagonalComparisonEquivalence F).unit.inv)).app A) = 𝟙 A.obj at h
  rw [diagonalComparisonEquivalence.unit.app.underlying.hom] at h
  exact (Category.id_comp _).symm.trans h

end FiberedCategoryOver.Groupoids.RelativeInertia
end CategoryTheory
