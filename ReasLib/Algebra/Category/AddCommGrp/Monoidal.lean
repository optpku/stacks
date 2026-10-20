/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Monoidal.Preadditive

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe w

namespace AddCommGrpCat

/-- Modules over the universe-lifted integers are equivalent to additive commutative groups. -/
def integerModuleEquivalence : ModuleCat.{w} (ULift.{w} ℤ) ≌ AddCommGrpCat.{w} :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (ULift.ringEquiv : ULift.{w} ℤ ≃+* ℤ).symm).trans
      (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).asEquivalence

/-- The integer tensor product on additive commutative groups, transported from modules. -/
instance tensorMonoidalCategory : MonoidalCategory AddCommGrpCat.{w} :=
  CategoryTheory.Monoidal.transport integerModuleEquivalence

/-- Integer tensor product is additive in each variable. -/
instance tensorMonoidalPreadditive : MonoidalPreadditive AddCommGrpCat.{w} :=
  sorry

/-- The tensor product of additive groups is the underlying additive group of module tensor. -/
def tensorObjIso (A B : AddCommGrpCat.{w}) :
    A ⊗ B ≅ integerModuleEquivalence.functor.obj
      (integerModuleEquivalence.inverse.obj A ⊗ integerModuleEquivalence.inverse.obj B) :=
  Iso.refl _

/-- The unit of integer tensor product is the additive group of universe-lifted integers. -/
def tensorUnitIsoInteger : 𝟙_ AddCommGrpCat.{w} ≅ AddCommGrpCat.of (ULift.{w} ℤ) :=
  Iso.refl _

end AddCommGrpCat
