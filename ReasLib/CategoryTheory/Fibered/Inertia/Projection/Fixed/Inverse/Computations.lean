module

public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Fixed.Inverse.Construction

/-!
# Fibred relative-inertia comparison inverse computations

Object, automorphism, and morphism readouts for the fixed fibred-category comparison inverse.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.RelativeInertia

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

section FixedOwner

variable {X Y :
  FiberedCategoryOver.{u, v, max w (max u v), v} C}

/-- The recovered relative-inertia object lies over the base object of the fixed
self-two-fibre-product object. -/
@[simp]
theorem diagonalComparison.inverse.obj.base
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))) :
    X.p.obj
        ((FiberedCategoryOver.toFunctor (RelativeInertia.diagonalComparison.inverse F)).obj P).obj =
      BasedCategory.PseudoPullback.baseObj P := sorry

/-- The underlying object recovered by the fibred comparison inverse is the first object
projection. -/
@[simp]
theorem diagonalComparison.inverse.obj.underlying
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))) :
    ((FiberedCategoryOver.toFunctor (RelativeInertia.diagonalComparison.inverse F)).obj P).obj =
      BasedCategory.PseudoPullback.fstObj P := sorry

/-- The automorphism recovered by the fibred comparison inverse is the explicit neutral
comparison automorphism. -/
@[simp]
theorem diagonalComparison.inverse.obj.aut
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))) :
    ((FiberedCategoryOver.toFunctor (RelativeInertia.diagonalComparison.inverse F)).obj P).aut =
      BasedFunctor.RelativeInertia.diagonalComparison.inverse.aut
        (FiberedCategoryOver.toBasedFunctor F) P := sorry

/-- The first structural component of the fixed fibred inverse has the neutral first projection
formula. This named boundary keeps downstream calculations at the fibred owner namespace. -/
@[simp]
theorem diagonalComparison.inverse.fstIso.hom
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))) :
    (BasedFunctor.RelativeInertia.diagonalComparison.inverse.fstIso
      (FiberedCategoryOver.toBasedFunctor F) P).hom =
      BasedCategory.PseudoPullback.fstMap
        (BasedFunctor.RelativeInertia.diagonalComparison.inverse.innerIso
          (FiberedCategoryOver.toBasedFunctor F) P).hom := sorry

/-- The inverse of the first structural component of the fixed fibred inverse has the neutral
first projection formula. -/
@[simp]
theorem diagonalComparison.inverse.fstIso.inv
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))) :
    (BasedFunctor.RelativeInertia.diagonalComparison.inverse.fstIso
      (FiberedCategoryOver.toBasedFunctor F) P).inv =
      BasedCategory.PseudoPullback.fstMap
        (BasedFunctor.RelativeInertia.diagonalComparison.inverse.innerIso
          (FiberedCategoryOver.toBasedFunctor F) P).inv := sorry

/-- The second structural component of the fixed fibred inverse has the neutral second projection
formula. -/
@[simp]
theorem diagonalComparison.inverse.sndIso.hom
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))) :
    (BasedFunctor.RelativeInertia.diagonalComparison.inverse.sndIso
      (FiberedCategoryOver.toBasedFunctor F) P).hom =
      BasedCategory.PseudoPullback.sndMap
        (BasedFunctor.RelativeInertia.diagonalComparison.inverse.innerIso
          (FiberedCategoryOver.toBasedFunctor F) P).hom := sorry

/-- The inverse of the second structural component of the fixed fibred inverse has the neutral
second projection formula. -/
@[simp]
theorem diagonalComparison.inverse.sndIso.inv
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))) :
    (BasedFunctor.RelativeInertia.diagonalComparison.inverse.sndIso
      (FiberedCategoryOver.toBasedFunctor F) P).inv =
      BasedCategory.PseudoPullback.sndMap
        (BasedFunctor.RelativeInertia.diagonalComparison.inverse.innerIso
          (FiberedCategoryOver.toBasedFunctor F) P).inv := sorry

/-- The forward arrow of the recovered automorphism is the first structural component followed
by the inverse second structural component. -/
@[simp]
theorem diagonalComparison.inverse.aut.hom
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))) :
    ((FiberedCategoryOver.toFunctor (RelativeInertia.diagonalComparison.inverse F)).obj P).aut.hom =
      (BasedFunctor.RelativeInertia.diagonalComparison.inverse.fstIso
        (FiberedCategoryOver.toBasedFunctor F) P).hom ≫
        (BasedFunctor.RelativeInertia.diagonalComparison.inverse.sndIso
          (FiberedCategoryOver.toBasedFunctor F) P).inv := sorry

/-- The inverse arrow of the recovered automorphism is the second structural component followed
by the inverse first structural component. -/
@[simp]
theorem diagonalComparison.inverse.aut.inv
    (F : X ⟶ Y)
    (P : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))) :
    ((FiberedCategoryOver.toFunctor (RelativeInertia.diagonalComparison.inverse F)).obj P).aut.inv =
      (BasedFunctor.RelativeInertia.diagonalComparison.inverse.sndIso
        (FiberedCategoryOver.toBasedFunctor F) P).hom ≫
        (BasedFunctor.RelativeInertia.diagonalComparison.inverse.fstIso
          (FiberedCategoryOver.toBasedFunctor F) P).inv := sorry

/-- The underlying arrow recovered by the fibred comparison inverse is the first morphism
projection. -/
@[simp]
theorem diagonalComparison.inverse.map.hom
    (F : X ⟶ Y)
    {P Q : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))}
    (φ : P ⟶ Q) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.toFunctor (RelativeInertia.diagonalComparison.inverse F)).map φ) =
      BasedCategory.PseudoPullback.fstMap φ := sorry

/-- The recovered automorphisms intertwine every morphism in the fixed
self-two-fibre-product. -/
@[reassoc]
theorem diagonalComparison.inverse.map.naturality
    (F : X ⟶ Y)
    {P Q : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))}
    (φ : P ⟶ Q) :
    ((FiberedCategoryOver.toFunctor
      (RelativeInertia.diagonalComparison.inverse F)).obj P).aut.hom ≫
        BasedCategory.PseudoPullback.fstMap φ =
      BasedCategory.PseudoPullback.fstMap φ ≫
        ((FiberedCategoryOver.toFunctor
          (RelativeInertia.diagonalComparison.inverse F)).obj Q).aut.hom := sorry

/-- The inverse recovered automorphisms satisfy the reverse intertwining
equation for every morphism in the fixed self-two-fibre-product. -/
@[reassoc]
theorem diagonalComparison.inverse.map.invNaturality
    (F : X ⟶ Y)
    {P Q : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))}
    (φ : P ⟶ Q) :
    ((FiberedCategoryOver.toFunctor
      (RelativeInertia.diagonalComparison.inverse F)).obj P).aut.inv ≫
        BasedCategory.PseudoPullback.fstMap φ =
      BasedCategory.PseudoPullback.fstMap φ ≫
        ((FiberedCategoryOver.toFunctor
          (RelativeInertia.diagonalComparison.inverse F)).obj Q).aut.inv := sorry

/-- The recovered relative-inertia morphism lies over the common base map of the fixed
self-two-fibre-product morphism, transported through the canonical first-component base
isomorphisms. -/
@[simp]
theorem diagonalComparison.inverse.map.base
    (F : X ⟶ Y)
    {P Q : FiberedCategoryOver.total (LocallyInduced.TwoFibreProduct.apex
      (RelativeInertia.relativeDiagonal F)
      (RelativeInertia.relativeDiagonal F))}
    (φ : P ⟶ Q) :
    X.p.map
        (CategoryTheory.RelativeInertia.hom
          ((FiberedCategoryOver.toFunctor
            (RelativeInertia.diagonalComparison.inverse F)).map φ)) =
      (BasedCategory.PseudoPullback.fstBaseIso P).hom ≫
        BasedCategory.PseudoPullback.baseMap φ ≫
        (BasedCategory.PseudoPullback.fstBaseIso Q).inv := sorry

end FixedOwner

end FiberedCategoryOver.RelativeInertia
end CategoryTheory
