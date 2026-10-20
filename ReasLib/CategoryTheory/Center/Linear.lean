/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Scalar units in the center of a linear category

This leaf constructs the central action of a scalar in a linear category and lifts scalar units to
units of the categorical center.  The construction only needs a semiring, so it is independent of
additive inverses and of complexes.

@stack 0194
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace CategoryTheory.Linear

variable (R : Type w) [Semiring R]
variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- Scalar multiplication by `r` is natural in the object of a linear category. -/
@[stacks 0194 "linear scalar central naturality"]
theorem scalarCenter_naturality [Linear R C] (r : R) {X Y : C} (f : X ⟶ Y) :
    f ≫ (r • 𝟙 Y) = (r • 𝟙 X) ≫ f := sorry

/-- A scalar acts as a central endomorphism of the identity functor of a linear category. -/
@[stacks 0194 "linear scalar in the categorical center"]
def scalarCenter [Linear R C] (r : R) : CatCenter C where
  app X := r • 𝟙 X
  naturality _ _ f := scalarCenter_naturality R C r f

/-- The central scalar construction preserves zero. -/
@[stacks 0194 "linear scalar center zero law"]
theorem scalarCenter_zero [Linear R C] :
    scalarCenter R C 0 = 0 := sorry

/-- The central scalar construction preserves one. -/
@[stacks 0194 "linear scalar center one law"]
theorem scalarCenter_one [Linear R C] :
    scalarCenter R C 1 = 1 := sorry

/-- The central scalar construction preserves addition. -/
@[stacks 0194 "linear scalar center addition law"]
theorem scalarCenter_add [Linear R C] (r s : R) :
    scalarCenter R C (r + s) = scalarCenter R C r + scalarCenter R C s := sorry

/-- The central scalar construction preserves multiplication. -/
@[stacks 0194 "linear scalar center multiplication law"]
theorem scalarCenter_mul [Linear R C] (r s : R) :
    scalarCenter R C (r * s) = scalarCenter R C r * scalarCenter R C s := sorry

/-- The semiring homomorphism from the scalar semiring to the categorical center. -/
@[stacks 0194 "linear scalar semiring homomorphism to the categorical center"]
def scalarCenterHom [Linear R C] : R →+* CatCenter C where
  toFun := scalarCenter R C
  map_zero' := scalarCenter_zero R C
  map_one' := scalarCenter_one R C
  map_add' := scalarCenter_add R C
  map_mul' := scalarCenter_mul R C

/-- The canonical map from scalar units to units of the center of an `R`-linear category. -/
@[stacks 0194 "linear scalar units in the categorical center"]
def toCatCenterUnits [Linear R C] : Rˣ →* (CatCenter C)ˣ :=
  Units.map (scalarCenterHom R C).toMonoidHom

/-- The component of the central action of `r` at `X` is `r • 𝟙 X`. -/
@[simp, stacks 0194 "linear scalar center component"]
theorem scalarCenter_app [Linear R C] (r : R) (X : C) :
    (scalarCenter R C r).app X = r • 𝟙 X := sorry

/-- Acting by the central scalar associated to `r` is the original scalar action by `r`. -/
@[simp, stacks 0194 "linear scalar center action"]
theorem scalarCenter_smul [Linear R C] (r : R) {X Y : C} (f : X ⟶ Y) :
    scalarCenter R C r • f = r • f := sorry

/-- The underlying central endomorphism of a scalar unit is its central scalar action. -/
@[simp, stacks 0194 "linear scalar unit underlying center element"]
theorem toCatCenterUnits_apply [Linear R C] (ε : Rˣ) :
    (toCatCenterUnits R C ε : CatCenter C) = scalarCenter R C ε := sorry

/-- Acting by the central unit associated to `ε` is the original scalar action by `ε`. -/
@[simp, stacks 0194 "linear scalar unit action"]
theorem toCatCenterUnits_smul [Linear R C] (ε : Rˣ) {X Y : C} (f : X ⟶ Y) :
    (toCatCenterUnits R C ε : CatCenter C) • f = (ε : R) • f := sorry

/-- Over a ring, the ReasLib scalar action is the canonical Mathlib center map. -/
@[simp, stacks 0194 "scalar center bridge to Mathlib"]
theorem scalarCenter_eq_toCatCenter (S : Type w) [Ring S]
    (C : Type u) [Category.{v} C] [Preadditive C] [Linear S C] (r : S) :
    scalarCenter S C r = CategoryTheory.Linear.toCatCenter S C r := sorry

/-- The ReasLib scalar homomorphism agrees with the canonical center homomorphism. -/
@[simp, stacks 0194 "scalar center homomorphism bridge"]
theorem scalarCenterHom_eq_toCatCenter (S : Type w) [Ring S]
    (C : Type u) [Category.{v} C] [Preadditive C] [Linear S C] :
    scalarCenterHom S C = CategoryTheory.Linear.toCatCenter S C := sorry

/-- Units transported through the scalar center use the canonical center map. -/
@[simp, stacks 0194 "scalar center units bridge"]
theorem toCatCenterUnits_eq (S : Type w) [Ring S]
    (C : Type u) [Category.{v} C] [Preadditive C] [Linear S C] :
    toCatCenterUnits S C =
      Units.map (CategoryTheory.Linear.toCatCenter S C).toMonoidHom := sorry

end CategoryTheory.Linear
