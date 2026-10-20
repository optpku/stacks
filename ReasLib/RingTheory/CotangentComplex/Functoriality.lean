/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Basic
public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Functoriality
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# Functoriality of cotangent complexes

Commutative squares of ring maps induce scalar-extended maps of the standard
cotangent complexes.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicTopology
open HomologicalComplex
open scoped Simplicial ZeroObject

universe u

noncomputable section

namespace Algebra.CotangentComplex

open CommRingCat.Under.CotangentComplex

/-- The ring map of standard polynomial-resolution terms induced by a map of
under-objects changing both the base ring and the resolved algebra. -/
def standardTermRightHom {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right) (n : SimplexCategoryᵒᵖ) :
    (standardTerm A B n).right ⟶ (standardTerm A' B' n).right :=
  CategoryTheory.CommRingCat.Under.PolynomialResolution.iterateRightHom α β (n.unop.len + 1)

/-- Structure maps of standard-resolution terms form a commutative square with the
induced termwise ring maps. -/
theorem standardTermRightHom_square {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (hα : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    α ≫ (standardTerm A' B' n).hom =
      (standardTerm A B n).hom ≫ standardTermRightHom α β n :=
  sorry

/-- Augmentations of standard-resolution terms form a commutative square with the
induced termwise ring maps. -/
theorem standardTermRightHom_comp_augmentation {A A' : CommRingCat.{u}}
    {B : Under A} {B' : Under A'} (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (hα : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    β.hom.comp (standardAugmentation A B n).hom =
      (standardAugmentation A' B' n).hom.comp (standardTermRightHom α β n).hom :=
  sorry

/-- The map of relative Kähler differentials of standard-resolution terms induced by a
commutative square of under-objects. -/
def standardDifferentialsMap {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (hα : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    CommRingCat.KaehlerDifferential (standardTerm A B n).hom ⟶
      (ModuleCat.restrictScalars (standardTermRightHom α β n).hom).obj
        (CommRingCat.KaehlerDifferential (standardTerm A' B' n).hom) :=
  CommRingCat.KaehlerDifferential.map (standardTermRightHom_square α β hα n)

/-- Unfolding of `standardDifferentialsMap` as `CommRingCat.KaehlerDifferential.map`
of the standard-term structure-map square. -/
theorem standardDifferentialsMap_eq {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (hα : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    standardDifferentialsMap α β hα n =
      CommRingCat.KaehlerDifferential.map (standardTermRightHom_square α β hα n) :=
  rfl

/-- The `B`-module comparison underlying a square map of simplicial cotangent terms,
before extension of scalars along the target ring map. -/
def standardBModuleMap {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (hα : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    (simplicialModule A B).obj n ⟶
      (ModuleCat.restrictScalars β.hom).obj ((simplicialModule A' B').obj n) :=
  ((ModuleCat.extendRestrictScalarsAdj (standardAugmentation A B n).hom).homEquiv _ _).symm
    (standardDifferentialsMap α β hα n ≫
      (ModuleCat.restrictScalars (standardTermRightHom α β n).hom).map
        ((ModuleCat.extendRestrictScalarsAdj (standardAugmentation A' B' n).hom).unit.app _) ≫
      (ModuleCat.restrictScalarsComp' (standardTermRightHom α β n).hom
          (standardAugmentation A' B' n).hom
          (β.hom.comp (standardAugmentation A B n).hom)
          (standardTermRightHom_comp_augmentation α β hα n)).inv.app _)

/-- Degreewise map of polynomial-resolution simplicial modules after extending scalars
along the target ring map of a commutative square. -/
def simplicialMap {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (hα : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    (ModuleCat.extendScalars β.hom).obj ((simplicialModule A B).obj n) ⟶
      (simplicialModule A' B').obj n :=
  ((ModuleCat.extendRestrictScalarsAdj β.hom).homEquiv _ _).symm
    (standardBModuleMap α β hα n)

/-- Unfolding of `simplicialMap` through the extension-restriction adjunction. -/
theorem simplicialMap_eq {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (hα : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    simplicialMap α β hα n =
      ((ModuleCat.extendRestrictScalarsAdj β.hom).homEquiv _ _).symm
        (standardBModuleMap α β hα n) :=
  rfl

/-- Degreewise map of polynomial-resolution simplicial modules induced by a
commutative square of ring homomorphisms. -/
def simplicialMap_ringHom {R S R' S' : Type u}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (f' : R' →+* S') (α : R →+* R') (β : S →+* S')
    (hcomm : f'.comp α = β.comp f) (n : SimplexCategoryᵒᵖ) :
    (ModuleCat.extendScalars β).obj
        ((simplicialModule (CommRingCat.of R) (Under.mk (CommRingCat.ofHom f))).obj n) ⟶
      (simplicialModule (CommRingCat.of R') (Under.mk (CommRingCat.ofHom f'))).obj n :=
  @simplicialMap (CommRingCat.of R) (CommRingCat.of R')
    (Under.mk (CommRingCat.ofHom f)) (Under.mk (CommRingCat.ofHom f'))
    (CommRingCat.ofHom α) (CommRingCat.ofHom β)
    (congrArg CommRingCat.ofHom hcomm) n

/-- The cochain map of André-Quillen cotangent complexes induced by a commutative
square of ring homomorphisms. -/
def map {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (f' : R' →+* S') (α : R →+* R') (β : S →+* S')
    (hcomm : f'.comp α = β.comp f) :
    ((ModuleCat.extendScalars β).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (RingHom.cotangentComplex f) ⟶
      RingHom.cotangentComplex f' where
  f i :=
    match h : ComplexShape.embeddingDownNat.r i with
    | some n =>
        (ModuleCat.extendScalars β).map
            (extendXIso
              ((alternatingFaceMapComplex (ModuleCat.{u} S)).obj
                (simplicialModule (CommRingCat.of R) (Under.mk (CommRingCat.ofHom f))))
              ComplexShape.embeddingDownNat
              (ComplexShape.embeddingDownNat.f_eq_of_r_eq_some h)).hom ≫
          simplicialMap_ringHom f f' α β hcomm (op ⦋n⦌) ≫
          (extendXIso
              ((alternatingFaceMapComplex (ModuleCat.{u} S')).obj
                (simplicialModule (CommRingCat.of R') (Under.mk (CommRingCat.ofHom f'))))
              ComplexShape.embeddingDownNat
              (ComplexShape.embeddingDownNat.f_eq_of_r_eq_some h)).inv
    | none => 0
  comm' := sorry

/-- Unfolding of `simplicialMap_ringHom` as `simplicialMap` of the corresponding
morphisms in `CommRingCat`. -/
theorem simplicialMap_ringHom_eq {R S R' S' : Type u}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (f' : R' →+* S') (α : R →+* R') (β : S →+* S')
    (hcomm : f'.comp α = β.comp f) (n : SimplexCategoryᵒᵖ) :
    simplicialMap_ringHom f f' α β hcomm n =
      @simplicialMap (CommRingCat.of R) (CommRingCat.of R')
        (Under.mk (CommRingCat.ofHom f)) (Under.mk (CommRingCat.ofHom f'))
        (CommRingCat.ofHom α) (CommRingCat.ofHom β)
        (congrArg CommRingCat.ofHom hcomm) n :=
  rfl

/-- A square map of cotangent complexes vanishes in strictly positive cohomological
degrees. -/
theorem map_zero_of_pos {R S R' S' : Type u}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (f' : R' →+* S') (α : R →+* R') (β : S →+* S')
    (hcomm : f'.comp α = β.comp f) {n : ℤ} (hn : 0 < n) :
    (map f f' α β hcomm).f n = 0 :=
  sorry

end Algebra.CotangentComplex

