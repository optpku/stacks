/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Homology

/-!
# Multiplication on cohomology of a cochain DGA

This leaf owns the graded multiplication and its functoriality for every cohomological degree.
The degree-zero ring and algebra instances live in `HomologyZero.lean`, which imports this more
general layer.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace CochainDGAlgebra

variable {R : Type u} [CommRing R]

/-- The successor selected by the cochain shape raises the sum of two degrees by one. -/
theorem up_next_add (n m : ℤ) :
    (ComplexShape.up ℤ).next (n + m) = n + m + 1 := sorry

/-- The product of two cochain-DGA cycles is again a cycle. -/
theorem d_mul_cycles_eq_zero (A : CochainDGAlgebra.{u, v} R) (n m : ℤ)
    (x : A.cycles n) (y : A.cycles m) :
    ((forget₂ (ModuleCat.{v} R) Ab).map
      (A.toCochainComplex.d (n + m) (n + m + 1)))
        (A.mul n m (A.iCycles n x) (A.iCycles m y)) = 0 := sorry

/-- Multiplication of cycles, bundled in the canonical cycle object. -/
@[stacks 09S8 "multiplication of cochain-DGA cycles"]
noncomputable def cyclesMul (A : CochainDGAlgebra.{u, v} R) (n m : ℤ)
    (x : A.cycles n) (y : A.cycles m) : A.cycles (n + m) :=
  A.toCochainComplex.cyclesMk
    (A.mul n m (A.iCycles n x) (A.iCycles m y)) (n + m + 1)
      (up_next_add n m) (A.d_mul_cycles_eq_zero n m x y)

/-- The underlying value of multiplication on cohomology classes. -/
@[stacks 09S8 "multiplication value on cochain-DGA cohomology"]
noncomputable def homologyMulValue (A : CochainDGAlgebra.{u, v} R) (n m : ℤ)
    (x : A.homology n) (y : A.homology m) : A.homology (n + m) :=
  A.homologyπ (n + m)
    (A.cyclesMul n m (A.homologyCycle n x) (A.homologyCycle m y))

/-- Cohomology multiplication is additive in its right input. -/
theorem homologyMulValue_add_right (A : CochainDGAlgebra.{u, v} R) (n m : ℤ)
    (x : A.homology n) (y z : A.homology m) :
    A.homologyMulValue n m x (y + z) =
      A.homologyMulValue n m x y + A.homologyMulValue n m x z := sorry

/-- Cohomology multiplication is linear in its right input. -/
theorem homologyMulValue_smul_right (A : CochainDGAlgebra.{u, v} R) (n m : ℤ)
    (r : R) (x : A.homology n) (y : A.homology m) :
    A.homologyMulValue n m x (r • y) = r • A.homologyMulValue n m x y := sorry

/-- Cohomology multiplication is additive in its left input. -/
theorem homologyMulValue_add_left (A : CochainDGAlgebra.{u, v} R) (n m : ℤ)
    (x y : A.homology n) (z : A.homology m) :
    A.homologyMulValue n m (x + y) z =
      A.homologyMulValue n m x z + A.homologyMulValue n m y z := sorry

/-- Cohomology multiplication is linear in its left input. -/
theorem homologyMulValue_smul_left (A : CochainDGAlgebra.{u, v} R) (n m : ℤ)
    (r : R) (x : A.homology n) (y : A.homology m) :
    A.homologyMulValue n m (r • x) y = r • A.homologyMulValue n m x y := sorry

/-- Multiplication by a fixed cohomology class, linear in the right input. -/
@[stacks 09S8 "right-linear cochain-DGA cohomology multiplication"]
noncomputable def homologyMulRight (A : CochainDGAlgebra.{u, v} R) (n m : ℤ)
    (x : A.homology n) : A.homology m →ₗ[R] A.homology (n + m) where
  toFun := A.homologyMulValue n m x
  map_add' := A.homologyMulValue_add_right n m x
  map_smul' := fun r y ↦ A.homologyMulValue_smul_right n m r x y

/-- Right multiplication on cohomology is additive in its left input. -/
theorem homologyMulRight_add (A : CochainDGAlgebra.{u, v} R) (n m : ℤ)
    (x y : A.homology n) :
    A.homologyMulRight n m (x + y) =
      A.homologyMulRight n m x + A.homologyMulRight n m y := sorry

/-- Right multiplication on cohomology is linear in its left input. -/
theorem homologyMulRight_smul (A : CochainDGAlgebra.{u, v} R) (n m : ℤ)
    (r : R) (x : A.homology n) :
    A.homologyMulRight n m (r • x) = r • A.homologyMulRight n m x := sorry

/-- The homogeneous bilinear multiplication on cochain-DGA cohomology. -/
@[stacks 09S8 "multiplication on cochain-DGA cohomology"]
noncomputable def homologyMul (A : CochainDGAlgebra.{u, v} R) (n m : ℤ) :
    A.homology n →ₗ[R] A.homology m →ₗ[R] A.homology (n + m) where
  toFun := A.homologyMulRight n m
  map_add' := A.homologyMulRight_add n m
  map_smul' := A.homologyMulRight_smul n m

/-- On specified cycle classes, cohomology multiplication is represented by the DGA product. -/
@[simp, stacks 09S8 "cycle formula for cochain-DGA cohomology multiplication"]
theorem homologyMul_homologyπ (A : CochainDGAlgebra.{u, v} R) (n m : ℤ)
    (x : A.cycles n) (y : A.cycles m) :
    A.homologyMul n m (A.homologyπ n x) (A.homologyπ m y) =
      A.homologyπ (n + m) (A.cyclesMul n m x y) := sorry

/-- The chosen cycle representatives in `homologyMulValue` may be replaced by any representatives
of the same cohomology classes. -/
@[stacks 09S8 "independence of cochain-DGA cohomology multiplication representatives"]
theorem homologyMulValue_eq_of_rep (A : CochainDGAlgebra.{u, v} R) (n m : ℤ)
    (x : A.homology n) (y : A.homology m) (x' : A.cycles n) (y' : A.cycles m)
    (hx : A.homologyπ n x' = x) (hy : A.homologyπ m y' = y) :
    A.homologyMulValue n m x y =
      A.homologyπ (n + m) (A.cyclesMul n m x' y') := sorry

namespace Hom

variable {A B C : CochainDGAlgebra.{u, v} R}

/-- The canonical linear map on cohomology induced by a cochain-DGA homomorphism. -/
noncomputable def homologyLinearMap (f : Hom A B) (n : ℤ) :
    A.homology n →ₗ[R] B.homology n :=
  (HomologicalComplex.homologyMap f.toCochainMap n).hom

/-- The induced map sends a cycle class to the class of the mapped cycle. -/
@[simp]
theorem homologyLinearMap_homologyπ (f : Hom A B) (n : ℤ) (x : A.cycles n) :
    f.homologyLinearMap n (A.homologyπ n x) =
      B.homologyπ n (HomologicalComplex.cyclesMap f.toCochainMap n x) := sorry

/-- The identity cochain-DGA map induces the identity on cohomology. -/
@[simp]
theorem homologyLinearMap_id (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    (id A).homologyLinearMap n = LinearMap.id := sorry

/-- Cohomology maps preserve composition of cochain-DGA homomorphisms. -/
@[simp]
theorem homologyLinearMap_comp (g : Hom B C) (f : Hom A B) (n : ℤ) :
    (comp g f).homologyLinearMap n =
      (g.homologyLinearMap n).comp (f.homologyLinearMap n) := sorry

/-- The induced cohomology map preserves homogeneous multiplication. -/
@[simp]
theorem homologyLinearMap_mul (f : Hom A B) (n m : ℤ)
    (x : A.homology n) (y : A.homology m) :
    f.homologyLinearMap (n + m) (A.homologyMul n m x y) =
      B.homologyMul n m (f.homologyLinearMap n x) (f.homologyLinearMap m y) := sorry

end Hom

end CochainDGAlgebra
