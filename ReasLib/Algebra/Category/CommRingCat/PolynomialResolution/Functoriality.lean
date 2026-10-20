/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Construction
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.CategoryTheory.CommSq

/-!
# Functoriality of standard polynomial resolutions

A commutative square of rings induces a map between their standard polynomial resolutions,
with the target restricted along the coefficient map. Its components are recursively defined
maps of iterated free algebras.
-/

@[expose] public section

open CommRingCat.Under.FreeAlgebra
open CategoryTheory
open Opposite
open Under

universe u

noncomputable section

namespace CategoryTheory.CommRingCat.Under.PolynomialResolution

/-- The standard resolution of `B` over `A`, viewed as a simplicial object of commutative rings. -/
abbrev standardSimplicial (A : CommRingCat.{u}) (B : Under A) :
    SimplicialObject CommRingCat.{u} :=
  ((evaluation A).obj B).left ⋙ Under.forget A

/-- Degree `n` of `standardSimplicial` is the underlying ring of the corresponding standard term. -/
theorem standardSimplicial_obj (A : CommRingCat.{u}) (B : Under A)
    (n : SimplexCategoryᵒᵖ) :
    (standardSimplicial A B).obj n =
      (((evaluation A).obj B).left.obj n).right := sorry

/-- The polynomial ring map induced by a coefficient homomorphism and a variable map. -/
def mvPolynomialRingHom {R S : Type u} [CommRing R] [CommRing S] {E F : Type u}
    (α : R →+* S) (φ : E → F) :
    MvPolynomial E R →+* MvPolynomial F S :=
  (AlgHom.toRingHom
      (MvPolynomial.rename φ : MvPolynomial E S →ₐ[S] MvPolynomial F S)).comp
    (MvPolynomial.map α)

/-- Unfolding of `mvPolynomialRingHom` as coefficient change followed by renaming. -/
theorem mvPolynomialRingHom_eq {R S : Type u} [CommRing R] [CommRing S] {E F : Type u}
    (α : R →+* S) (φ : E → F) :
    mvPolynomialRingHom α φ =
      (AlgHom.toRingHom
          (MvPolynomial.rename φ : MvPolynomial E S →ₐ[S] MvPolynomial F S)).comp
        (MvPolynomial.map α) := sorry

/-- The polynomial coefficient-and-rename map preserves structure maps after restriction along
the coefficient homomorphism. -/
theorem mvPolynomialHom_w {A A' : CommRingCat.{u}} {E F : Type u}
    (α : A ⟶ A') (φ : E → F) :
    (polynomial A E).hom ≫ CommRingCat.ofHom (mvPolynomialRingHom α.hom φ) =
      ((Under.map α).obj (polynomial A' F)).hom := sorry

/-- The map of polynomial algebras over a coefficient homomorphism, as a morphism in `Under A`. -/
def mvPolynomialHom {A A' : CommRingCat.{u}} {E F : Type u}
    (α : A ⟶ A') (φ : E → F) :
    polynomial A E ⟶ (Under.map α).obj (polynomial A' F) :=
  Under.homMk (CommRingCat.ofHom (mvPolynomialRingHom α.hom φ)) (mvPolynomialHom_w α φ)

/-- The underlying ring map of `mvPolynomialHom` is `mvPolynomialRingHom`. -/
theorem mvPolynomialHom_right {A A' : CommRingCat.{u}} {E F : Type u}
    (α : A ⟶ A') (φ : E → F) :
    (mvPolynomialHom α φ).right = CommRingCat.ofHom (mvPolynomialRingHom α.hom φ) := sorry

/-- The map of categorical free algebras induced by a coefficient map and a variable map. -/
def freeAlgebraRightHom {A A' : CommRingCat.{u}} {E F : Type u}
    (α : A ⟶ A') (φ : E → F) :
    (algebraic A E).right ⟶ (algebraic A' F).right :=
  (toPolynomial A E).right ≫
    CommRingCat.ofHom (mvPolynomialRingHom α.hom φ) ≫
    (fromPolynomial A' F).right

/-- Unfolding of `freeAlgebraRightHom` through the polynomial model. -/
theorem freeAlgebraRightHom_eq {A A' : CommRingCat.{u}} {E F : Type u}
    (α : A ⟶ A') (φ : E → F) :
    freeAlgebraRightHom α φ =
      (toPolynomial A E).right ≫
        CommRingCat.ofHom (mvPolynomialRingHom α.hom φ) ≫
        (fromPolynomial A' F).right := sorry

/-- The free-algebra map over a coefficient homomorphism, as a morphism in `Under A`. -/
def freeAlgebraHom {A A' : CommRingCat.{u}} {E F : Type u}
    (α : A ⟶ A') (φ : E → F) :
    algebraic A E ⟶ (Under.map α).obj (algebraic A' F) :=
  toPolynomial A E ≫ mvPolynomialHom α φ ≫ (Under.map α).map (fromPolynomial A' F)

/-- The underlying ring map of `freeAlgebraHom` is `freeAlgebraRightHom`. -/
theorem freeAlgebraHom_right {A A' : CommRingCat.{u}} {E F : Type u}
    (α : A ⟶ A') (φ : E → F) :
    (freeAlgebraHom α φ).right = freeAlgebraRightHom α φ := sorry

/-- The ring map of iterated polynomial-algebra resolutions induced by a map of under-objects
changing both the base ring and the resolved algebra. -/
def iterateRightHom {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right) :
    (n : ℕ) →
      ((Endofunctor.iterate (functor A) n).obj B).right ⟶
        ((Endofunctor.iterate (functor A') n).obj B').right
  | 0 => β
  | n + 1 =>
      freeAlgebraRightHom α
        ((forget CommRingCat).map (iterateRightHom α β n))

/-- The zeroth iterate ring map is the given map of resolved algebras. -/
theorem iterateRightHom_zero {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right) :
    iterateRightHom α β 0 = β := sorry

/-- The successor iterate ring map applies `freeAlgebraRightHom` to the previous iterate. -/
theorem iterateRightHom_succ {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right) (n : ℕ) :
    iterateRightHom α β (n + 1) =
      freeAlgebraRightHom α
        ((forget CommRingCat).map (iterateRightHom α β n)) := sorry

/-- The iterated polynomial-algebra map over a commutative square, as a morphism in `Under A`. -/
def iterateHom {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (h_comm : α ≫ B'.hom = B.hom ≫ β) :
    (n : ℕ) →
      (Endofunctor.iterate (functor A) n).obj B ⟶
        (Under.map α).obj ((Endofunctor.iterate (functor A') n).obj B')
  | 0 => Under.homMk β h_comm.symm
  | n + 1 =>
      freeAlgebraHom α ((carrier A).map (iterateHom α β h_comm n))

/-- The zeroth iterate in `Under A` is the given algebra map, using the commutative square. -/
theorem iterateHom_zero {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (h_comm : α ≫ B'.hom = B.hom ≫ β) :
    iterateHom α β h_comm 0 = Under.homMk β h_comm.symm := sorry

/-- The successor iterate in `Under A` applies `freeAlgebraHom` to the previous iterate. -/
theorem iterateHom_succ {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (h_comm : α ≫ B'.hom = B.hom ≫ β) (n : ℕ) :
    iterateHom α β h_comm (n + 1) =
      freeAlgebraHom α ((carrier A).map (iterateHom α β h_comm n)) := sorry

/-- The underlying ring map of `iterateHom` is `iterateRightHom`. -/
theorem iterateHom_right {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (h_comm : α ≫ B'.hom = B.hom ≫ β) (n : ℕ) :
    (iterateHom α β h_comm n).right = iterateRightHom α β n := sorry

/-- The map of standard resolutions, as simplicial objects of `Under A`, induced by a
commutative square of ring maps. -/
def functorialityMap {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (h_comm : α ≫ B'.hom = B.hom ≫ β) :
    ((evaluation A).obj B).left ⟶
      ((evaluation A').obj B').left ⋙ Under.map α where
  app n := iterateHom α β h_comm (n.unop.len + 1)
  naturality _ _ _ := sorry

/-- Components of `functorialityMap` are the corresponding iterate maps in `Under A`. -/
theorem functorialityMap_app {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (h_comm : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    (functorialityMap α β h_comm).app n = iterateHom α β h_comm (n.unop.len + 1) := sorry

/-- Underlying ring components of `functorialityMap` are the corresponding iterate ring maps. -/
theorem functorialityMap_app_right {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (h_comm : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    ((functorialityMap α β h_comm).app n).right =
      iterateRightHom α β (n.unop.len + 1) := sorry

/-- `functorialityMap` is compatible with the standard augmentations through the given algebra
map. -/
theorem functorialityMap_augmentation {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (h_comm : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    CommSq ((functorialityMap α β h_comm).app n) (((evaluation A).obj B).hom.app n)
      ((Under.map α).map (((evaluation A').obj B').hom.app n))
      (Under.homMk β h_comm.symm) := sorry

end CategoryTheory.CommRingCat.Under.PolynomialResolution
