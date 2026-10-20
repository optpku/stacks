module

public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Functoriality
public import ReasLib.Algebra.CharP.Frobenius
public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy

/-!
# Frobenius on standard polynomial resolutions

For a prime vanishing in the base ring, the Frobenius square induces a map of standard
polynomial resolutions. This map is simplicially homotopic to degreewise Frobenius; both
maps take values in the resolution restricted along base Frobenius.
-/

@[expose] public section

open CommRingCat.Under.FreeAlgebra
open CategoryTheory
open Opposite
open Under

universe u

noncomputable section

namespace CategoryTheory.CommRingCat.Under.PolynomialResolution

namespace Frobenius

variable (p : ℕ) [Fact p.Prime]

/-- The prime `p` vanishes in every algebra over a ring in which `p` vanishes. -/
theorem algebra_prime_eq_zero {A : CommRingCat.{u}} (hp : (p : A) = 0) (B : Under A) :
    (p : B.right) = 0 := sorry

/-- The prime `p` vanishes in every standard-resolution term over a ring in which `p` vanishes. -/
theorem standardSimplicial_prime_eq_zero {A : CommRingCat.{u}} (hp : (p : A) = 0)
    (B : Under A) (n : SimplexCategoryᵒᵖ) :
    (p : (standardSimplicial A B).obj n) = 0 := sorry

/-- The Frobenius endomorphism of a commutative ring in which the prime `p` vanishes. -/
def hom {A : CommRingCat.{u}} (hp : (p : A) = 0) : A ⟶ A :=
  CommRingCat.ofHom (RingHom.frobeniusOfPrime p hp)

/-- The Frobenius morphism of a ring sends `x` to `x ^ p`. -/
theorem hom_apply {A : CommRingCat.{u}} (hp : (p : A) = 0) (x : A) :
    (hom p hp).hom x = x ^ p := sorry

/-- The Frobenius endomorphism of the resolved algebra. -/
def homResolved {A : CommRingCat.{u}} (hp : (p : A) = 0) (B : Under A) :
    B.right ⟶ B.right :=
  hom p (algebra_prime_eq_zero p hp B)

/-- The resolved Frobenius morphism sends `x` to `x ^ p`. -/
theorem homResolved_apply {A : CommRingCat.{u}} (hp : (p : A) = 0) (B : Under A)
    (x : B.right) :
    (homResolved p hp B).hom x = x ^ p := sorry

/-- The Frobenius maps of `A` and `B` form a commutative square with the structure map. -/
theorem w {A : CommRingCat.{u}} (hp : (p : A) = 0) (B : Under A) :
    hom p hp ≫ B.hom = B.hom ≫ homResolved p hp B := sorry

/-- Frobenius of an `A`-algebra, as a morphism to the restriction along `F_A`. -/
def underHom {A : CommRingCat.{u}} (hp : (p : A) = 0) (B : Under A) :
    B ⟶ (Under.map (hom p hp)).obj B :=
  Under.homMk (homResolved p hp B) (w p hp B).symm

/-- The underlying ring map of `underHom` is resolved Frobenius. -/
theorem underHom_right {A : CommRingCat.{u}} (hp : (p : A) = 0) (B : Under A) :
    (underHom p hp B).right = homResolved p hp B := sorry

/-- The map of standard resolutions induced by the Frobenius square of `A ⟶ B`. -/
def functoriality {A : CommRingCat.{u}} (hp : (p : A) = 0) (B : Under A) :
    ((evaluation A).obj B).left ⟶
      ((evaluation A).obj B).left ⋙ Under.map (hom p hp) :=
  functorialityMap (hom p hp) (homResolved p hp B) (w p hp B)

/-- Components of the Frobenius functoriality map are iterate maps along the Frobenius square. -/
theorem functoriality_app {A : CommRingCat.{u}} (hp : (p : A) = 0) (B : Under A)
    (n : SimplexCategoryᵒᵖ) :
    (functoriality p hp B).app n =
      iterateHom (hom p hp) (homResolved p hp B) (w p hp B) (n.unop.len + 1) := sorry

/-- Underlying ring components of Frobenius functoriality are the iterate ring maps. -/
theorem functoriality_app_right {A : CommRingCat.{u}} (hp : (p : A) = 0) (B : Under A)
    (n : SimplexCategoryᵒᵖ) :
    ((functoriality p hp B).app n).right =
      iterateRightHom (hom p hp) (homResolved p hp B) (n.unop.len + 1) := sorry

/-- Frobenius functoriality commutes with the standard augmentations through `F_B`. -/
theorem functoriality_augmentation {A : CommRingCat.{u}} (hp : (p : A) = 0) (B : Under A)
    (n : SimplexCategoryᵒᵖ) :
    CommSq ((functoriality p hp B).app n) (((evaluation A).obj B).hom.app n)
      ((Under.map (hom p hp)).map (((evaluation A).obj B).hom.app n))
      (underHom p hp B) := sorry

/-- The Frobenius morphism of the standard resolution, given by Frobenius on each term. -/
def degreewise {A : CommRingCat.{u}} (hp : (p : A) = 0) (B : Under A) :
    ((evaluation A).obj B).left ⟶
      ((evaluation A).obj B).left ⋙ Under.map (hom p hp) where
  app n := underHom p hp (((evaluation A).obj B).left.obj n)
  naturality _ _ _ := sorry

/-- A component of degreewise Frobenius is Frobenius of that standard-resolution term. -/
theorem degreewise_app {A : CommRingCat.{u}} (hp : (p : A) = 0) (B : Under A)
    (n : SimplexCategoryᵒᵖ) :
    (degreewise p hp B).app n = underHom p hp (((evaluation A).obj B).left.obj n) := sorry

/-- The underlying ring map of a degreewise Frobenius component is Frobenius of that term. -/
theorem degreewise_app_right {A : CommRingCat.{u}} (hp : (p : A) = 0) (B : Under A)
    (n : SimplexCategoryᵒᵖ) :
    ((degreewise p hp B).app n).right =
      hom p (algebra_prime_eq_zero p hp (((evaluation A).obj B).left.obj n)) := sorry

/-- Degreewise Frobenius sends an element of a standard-resolution term to its `p`-th power. -/
theorem degreewise_apply {A : CommRingCat.{u}} (hp : (p : A) = 0) (B : Under A)
    (n : SimplexCategoryᵒᵖ) (x : (((evaluation A).obj B).left.obj n).right) :
    ((degreewise p hp B).app n).right.hom x = x ^ p := sorry

/-- Degreewise Frobenius commutes with the standard augmentations through `F_B`. -/
theorem degreewise_augmentation {A : CommRingCat.{u}} (hp : (p : A) = 0) (B : Under A)
    (n : SimplexCategoryᵒᵖ) :
    CommSq ((degreewise p hp B).app n) (((evaluation A).obj B).hom.app n)
      ((Under.map (hom p hp)).map (((evaluation A).obj B).hom.app n))
      (underHom p hp B) := sorry

/-- For a prime vanishing in the base ring, the standard-resolution map induced by the
Frobenius square is simplicially homotopic to Frobenius on each resolution term. -/
theorem functoriality_homotopic_degreewise
    (p : ℕ) [Fact p.Prime] {A : CommRingCat.{u}} (hp : (p : A) = 0) (B : Under A) :
    SimplicialObject.Homotopic (functoriality p hp B) (degreewise p hp B) := sorry

end Frobenius

end CategoryTheory.CommRingCat.Under.PolynomialResolution
