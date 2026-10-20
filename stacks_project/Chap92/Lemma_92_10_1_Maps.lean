module

public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Functoriality
public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Frobenius

/-!
# Standard polynomial resolutions and their functoriality maps

The shared polynomial-resolution owners provide the underlying simplicial ring, maps induced
by coefficient-changing commutative squares, and the Frobenius specialization.
-/

open CategoryTheory
open CategoryTheory.CommRingCat.Under.PolynomialResolution

universe u

#check (CategoryTheory.CommRingCat.Under.PolynomialResolution.standardSimplicial :
  (A : CommRingCat.{u}) → (B : Under A) → SimplicialObject CommRingCat.{u})

#check (CategoryTheory.CommRingCat.Under.PolynomialResolution.functorialityMap :
  {A A' : CommRingCat.{u}} → {B : Under A} → {B' : Under A'} →
    (α : A ⟶ A') → (β : B.right ⟶ B'.right) →
      (h_comm : α ≫ B'.hom = B.hom ≫ β) →
        ((evaluation A).obj B).left ⟶ ((evaluation A').obj B').left ⋙ Under.map α)
