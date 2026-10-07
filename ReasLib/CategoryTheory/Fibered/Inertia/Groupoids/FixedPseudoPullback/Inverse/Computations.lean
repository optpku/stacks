module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.FixedPseudoPullback.Inverse.Construction

/-!
# Fixed groupoid-fibred relative-inertia comparison inverse computations

Object, automorphism, and morphism projections of the explicit inverse to the
fixed relative-inertia comparison.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.Groupoids.RelativeInertia

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

section FixedPseudoPullbackOwner

variable {X Y :
  FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}

/-- The recovered relative-inertia object lies over the base object of the fixed
self-two-fibre-product object. -/
@[simp]
theorem diagonalComparison.inverse.obj.base
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))) :
    X.p.obj
        ((FiberedCategoryOver.Groupoids.toFunctor
          (diagonalComparison.inverse F)).obj P).obj =
      BasedCategory.PseudoPullback.baseObj P := sorry

/-- The underlying object recovered by the groupoid-fibred comparison inverse is the first
object projection. -/
@[simp]
theorem diagonalComparison.inverse.obj.underlying
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))) :
    ((FiberedCategoryOver.Groupoids.toFunctor (diagonalComparison.inverse F)).obj P).obj =
      BasedCategory.PseudoPullback.fstObj P := sorry

/-- The automorphism recovered by the groupoid-fibred comparison inverse is the explicit
neutral comparison automorphism. -/
@[simp]
theorem diagonalComparison.inverse.obj.aut
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))) :
    ((FiberedCategoryOver.Groupoids.toFunctor (diagonalComparison.inverse F)).obj P).aut =
      BasedFunctor.RelativeInertia.diagonalComparison.inverse.aut
        (FiberedCategoryOver.Groupoids.toBasedFunctor F) P := sorry

/-- The first structural component of the fixed groupoid-fibred inverse has the neutral first
projection formula. This named boundary keeps downstream calculations at the groupoid owner
namespace. -/
@[simp]
theorem diagonalComparison.inverse.fstIso.hom
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))) :
    (BasedFunctor.RelativeInertia.diagonalComparison.inverse.fstIso
      (FiberedCategoryOver.Groupoids.toBasedFunctor F) P).hom =
      BasedCategory.PseudoPullback.fstMap
        (BasedFunctor.RelativeInertia.diagonalComparison.inverse.innerIso
          (FiberedCategoryOver.Groupoids.toBasedFunctor F) P).hom := sorry

/-- The inverse of the first structural component of the fixed groupoid-fibred inverse has the
neutral first projection formula. -/
@[simp]
theorem diagonalComparison.inverse.fstIso.inv
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))) :
    (BasedFunctor.RelativeInertia.diagonalComparison.inverse.fstIso
      (FiberedCategoryOver.Groupoids.toBasedFunctor F) P).inv =
      BasedCategory.PseudoPullback.fstMap
        (BasedFunctor.RelativeInertia.diagonalComparison.inverse.innerIso
          (FiberedCategoryOver.Groupoids.toBasedFunctor F) P).inv := sorry

/-- The second structural component of the fixed groupoid-fibred inverse has the neutral second
projection formula. -/
@[simp]
theorem diagonalComparison.inverse.sndIso.hom
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))) :
    (BasedFunctor.RelativeInertia.diagonalComparison.inverse.sndIso
      (FiberedCategoryOver.Groupoids.toBasedFunctor F) P).hom =
      BasedCategory.PseudoPullback.sndMap
        (BasedFunctor.RelativeInertia.diagonalComparison.inverse.innerIso
          (FiberedCategoryOver.Groupoids.toBasedFunctor F) P).hom := sorry

/-- The inverse of the second structural component of the fixed groupoid-fibred inverse has the
neutral second projection formula. -/
@[simp]
theorem diagonalComparison.inverse.sndIso.inv
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))) :
    (BasedFunctor.RelativeInertia.diagonalComparison.inverse.sndIso
      (FiberedCategoryOver.Groupoids.toBasedFunctor F) P).inv =
      BasedCategory.PseudoPullback.sndMap
        (BasedFunctor.RelativeInertia.diagonalComparison.inverse.innerIso
          (FiberedCategoryOver.Groupoids.toBasedFunctor F) P).inv := sorry

/-- The forward arrow of the recovered automorphism is the first structural component followed
by the inverse second structural component. -/
@[simp]
theorem diagonalComparison.inverse.aut.hom
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))) :
    ((FiberedCategoryOver.Groupoids.toFunctor
      (diagonalComparison.inverse F)).obj P).aut.hom =
      (BasedFunctor.RelativeInertia.diagonalComparison.inverse.fstIso
        (FiberedCategoryOver.Groupoids.toBasedFunctor F) P).hom ≫
        (BasedFunctor.RelativeInertia.diagonalComparison.inverse.sndIso
          (FiberedCategoryOver.Groupoids.toBasedFunctor F) P).inv := sorry

/-- The inverse arrow of the recovered automorphism is the second structural component followed
by the inverse first structural component. -/
@[simp]
theorem diagonalComparison.inverse.aut.inv
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))) :
    ((FiberedCategoryOver.Groupoids.toFunctor
      (diagonalComparison.inverse F)).obj P).aut.inv =
      (BasedFunctor.RelativeInertia.diagonalComparison.inverse.sndIso
        (FiberedCategoryOver.Groupoids.toBasedFunctor F) P).hom ≫
        (BasedFunctor.RelativeInertia.diagonalComparison.inverse.fstIso
          (FiberedCategoryOver.Groupoids.toBasedFunctor F) P).inv := sorry

/-- The underlying arrow recovered by the groupoid-fibred comparison inverse is the first
morphism projection. -/
@[simp]
theorem diagonalComparison.inverse.map.hom
    (F : X ⟶ Y)
    {P Q : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))}
    (φ : P ⟶ Q) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.Groupoids.toFunctor (diagonalComparison.inverse F)).map φ) =
      BasedCategory.PseudoPullback.fstMap φ := sorry

/-- The recovered groupoid-fibred automorphisms intertwine every morphism in
the fixed self-two-fibre-product. -/
@[reassoc]
theorem diagonalComparison.inverse.map.naturality
    (F : X ⟶ Y)
    {P Q : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))}
    (φ : P ⟶ Q) :
    ((FiberedCategoryOver.Groupoids.toFunctor
      (diagonalComparison.inverse F)).obj P).aut.hom ≫
        BasedCategory.PseudoPullback.fstMap φ =
      BasedCategory.PseudoPullback.fstMap φ ≫
        ((FiberedCategoryOver.Groupoids.toFunctor
          (diagonalComparison.inverse F)).obj Q).aut.hom := sorry

/-- The inverse recovered groupoid-fibred automorphisms satisfy the reverse
intertwining equation for every morphism in the fixed self-two-fibre-product. -/
@[reassoc]
theorem diagonalComparison.inverse.map.invNaturality
    (F : X ⟶ Y)
    {P Q : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))}
    (φ : P ⟶ Q) :
    ((FiberedCategoryOver.Groupoids.toFunctor
      (diagonalComparison.inverse F)).obj P).aut.inv ≫
        BasedCategory.PseudoPullback.fstMap φ =
      BasedCategory.PseudoPullback.fstMap φ ≫
        ((FiberedCategoryOver.Groupoids.toFunctor
          (diagonalComparison.inverse F)).obj Q).aut.inv := sorry

/-- The recovered relative-inertia morphism lies over the common base map of the fixed
self-two-fibre-product morphism, transported through the canonical first-component base
isomorphisms. -/
@[simp]
theorem diagonalComparison.inverse.map.base
    (F : X ⟶ Y)
    {P Q : FiberedCategoryOver.Groupoids.total
      (CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F))}
    (φ : P ⟶ Q) :
    X.p.map
        (CategoryTheory.RelativeInertia.hom
          ((FiberedCategoryOver.Groupoids.toFunctor
            (diagonalComparison.inverse F)).map φ)) =
      (BasedCategory.PseudoPullback.fstBaseIso P).hom ≫
        BasedCategory.PseudoPullback.baseMap φ ≫
        (BasedCategory.PseudoPullback.fstBaseIso Q).inv := sorry

end FixedPseudoPullbackOwner

end FiberedCategoryOver.Groupoids.RelativeInertia

end CategoryTheory
