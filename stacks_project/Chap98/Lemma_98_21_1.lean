/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Lifts
public import stacks_project.Chap94.Definition_94_12_1_Representable
import StacksCheckRecall

/-!
# Functoriality of categories of lifts

A morphism of categories fibred in groupoids and a commutative square of
algebras induce a functor on categories of lifts, compatible with composition.
-/

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Functor
open FiberedCategoryOver.Groupoids (fiberFunctor)
open FiberedCategoryOver.Groupoids renaming liftFunctor → cfgLiftFunctor
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

universe u

/- Lemma 98.21.1. A commutative square of S-algebras and a connecting fibre
morphism induce the canonical functor on categories of outgoing lifts. -/
@[stacks 07Y7] #check (AlgebraicGeometry.GroupoidsOver.liftFunctor :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (F : X ⟶ Y)
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (fB : B' ⟶ B) (hfB : Spec.map fB ≫ σB' = σB)
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (u : A' ⟶ B') (hu : Spec.map u ≫ σA' = σB')
    (sq : CommSq fA u v fB)
    (x : X.p.Fiber (Over.mk σA)) (y : Y.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj Y.p (specOverHom v hv)
      ((fiberFunctor F (Over.mk σA)).obj x) ⟶ y),
    liftCat x fA hfA ⥤ liftCat y fB hfB)

#check (AlgebraicGeometry.GroupoidsOver.liftFunctor_comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (F : X ⟶ Y) (G : Y ⟶ Z)
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (fB : B' ⟶ B) (hfB : Spec.map fB ≫ σB' = σB)
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (u : A' ⟶ B') (hu : Spec.map u ≫ σA' = σB')
    (sq : CommSq fA u v fB)
    (x : X.p.Fiber (Over.mk σA)) (y : Y.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj Y.p (specOverHom v hv)
      ((fiberFunctor F (Over.mk σA)).obj x) ⟶ y),
    liftFunctor (F ≫ G) fA hfA fB hfB v hv u hu sq x
        ((fiberFunctor G (Over.mk σB)).obj y)
        (cfgLiftFunctor.connect F G (specOverHom v hv) φ) ≅
      liftFunctor F fA hfA fB hfB v hv u hu sq x y φ ⋙
        cfgLiftFunctor.onId G (specOverHom fB hfB) y)
