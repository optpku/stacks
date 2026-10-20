/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Ring.MinimalAxioms
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Homology
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Homology.Multiplication

/-!
# Zeroth Cohomology Algebra of a Cochain DGA

The canonical Mathlib homology object in degree zero inherits the ordinary, generally
noncommutative, algebra structure of cohomology.  Multiplication is constructed from chosen cycle
representatives, while the public cycle-class formula records independence of that choice.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace CochainDGAlgebra

variable {R : Type u} [CommRing R]

/-- The differential of the cochain-DGA unit is zero. -/
theorem d_one_zero (A : CochainDGAlgebra.{u, v} R) :
    ((forget₂ (ModuleCat.{v} R) Ab).map (A.toCochainComplex.d 0 1)) A.one = 0 := sorry

/-- The successor of degree zero in the cochain shape is degree one. -/
theorem up_next_zero : (ComplexShape.up ℤ).next 0 = 1 := sorry

/-- The unit of a cochain DGA as a canonical degree-zero cycle. -/
@[stacks 09S8 "unit cycle of a cochain DGA"]
noncomputable def oneCycle (A : CochainDGAlgebra.{u, v} R) : A.cycles 0 :=
  A.toCochainComplex.cyclesMk A.one 1 up_next_zero A.d_one_zero

/-- The unit class in degree-zero cohomology. -/
@[stacks 09S8 "unit in zeroth cochain-DGA cohomology"]
noncomputable def homologyOne (A : CochainDGAlgebra.{u, v} R) : A.homology 0 :=
  A.homologyπ 0 A.oneCycle

/-- The unit class is the class represented by the canonical unit cycle. -/
@[simp]
theorem homologyπ_oneCycle (A : CochainDGAlgebra.{u, v} R) :
    A.homologyπ 0 A.oneCycle = A.homologyOne := rfl

/-- The canonical zeroth cohomology algebra carrier of a cochain DGA. -/
@[stacks 09S8 "zeroth cohomology algebra of a cochain DGA"]
noncomputable abbrev homologyZero (A : CochainDGAlgebra.{u, v} R) : Type v :=
  A.homology 0

/-- Multiplication on zeroth cohomology is the degree-zero cohomology product. -/
@[stacks 09S8 "multiplication on zeroth cochain-DGA cohomology"]
noncomputable instance homologyZeroMul (A : CochainDGAlgebra.{u, v} R) :
    Mul A.homologyZero := ⟨fun x y ↦ A.homologyMul 0 0 x y⟩

/-- The unit on zeroth cohomology is the class of the DGA unit. -/
@[stacks 09S8 "unit on zeroth cochain-DGA cohomology"]
noncomputable instance homologyZeroOne (A : CochainDGAlgebra.{u, v} R) :
    One A.homologyZero := ⟨A.homologyOne⟩

/-- Multiplication on zeroth cohomology is associative. -/
theorem homologyZero_mul_assoc (A : CochainDGAlgebra.{u, v} R)
    (x y z : A.homologyZero) : x * y * z = x * (y * z) := sorry

/-- The zeroth cohomology unit acts on the left. -/
theorem homologyZero_one_mul (A : CochainDGAlgebra.{u, v} R)
    (x : A.homologyZero) : 1 * x = x := sorry

/-- The zeroth cohomology unit acts on the right. -/
theorem homologyZero_mul_one (A : CochainDGAlgebra.{u, v} R)
    (x : A.homologyZero) : x * 1 = x := sorry

/-- Zeroth cohomology multiplication distributes over addition on the right. -/
theorem homologyZero_mul_add (A : CochainDGAlgebra.{u, v} R)
    (x y z : A.homologyZero) : x * (y + z) = x * y + x * z := sorry

/-- Zeroth cohomology multiplication distributes over addition on the left. -/
theorem homologyZero_add_mul (A : CochainDGAlgebra.{u, v} R)
    (x y z : A.homologyZero) : (x + y) * z = x * z + y * z := sorry

/-- The canonical, generally noncommutative, ring structure on `H⁰(A)`. -/
@[stacks 09S8 "ring structure on zeroth cochain-DGA cohomology"]
noncomputable instance homologyZeroRing (A : CochainDGAlgebra.{u, v} R) :
    Ring A.homologyZero :=
  Ring.ofMinimalAxioms add_assoc zero_add neg_add_cancel
    A.homologyZero_mul_assoc A.homologyZero_one_mul A.homologyZero_mul_one
      A.homologyZero_mul_add A.homologyZero_add_mul

/-- Scalar multiplication is compatible with zeroth cohomology multiplication on the left. -/
theorem smul_homologyZero_mul (A : CochainDGAlgebra.{u, v} R)
    (r : R) (x y : A.homologyZero) : (r • x) * y = r • (x * y) := sorry

/-- Scalar multiplication is compatible with zeroth cohomology multiplication on the right. -/
theorem homologyZero_mul_smul (A : CochainDGAlgebra.{u, v} R)
    (r : R) (x y : A.homologyZero) : x * (r • y) = r • (x * y) := sorry

/-- The canonical `R`-algebra structure on zeroth cohomology. -/
@[stacks 09S8 "base algebra structure on zeroth cochain-DGA cohomology"]
noncomputable instance homologyZeroAlgebra (A : CochainDGAlgebra.{u, v} R) :
    Algebra R A.homologyZero where
  smul := fun r x ↦ (inferInstance : SMul R (A.homology 0)).smul r x
  algebraMap :=
    { toFun := fun r ↦ r • A.homologyOne
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry }
  commutes' := sorry
  smul_def' := sorry

/-- The unit of `H⁰(A)` is the cohomology class of the DGA unit. -/
@[simp]
theorem homologyZero_one (A : CochainDGAlgebra.{u, v} R) :
    (1 : A.homologyZero) = A.homologyOne := sorry

/-- Multiplication in `H⁰(A)` is degree-zero cohomology multiplication. -/
@[simp]
theorem homologyZero_mul (A : CochainDGAlgebra.{u, v} R) (x y : A.homologyZero) :
    x * y = A.homologyMul 0 0 x y := sorry

/-- The product of two specified classes in `H⁰(A)` is represented by their cycle product. -/
@[simp, stacks 09S8 "cycle formula for multiplication in zeroth cohomology"]
theorem homologyZero_mul_homologyπ (A : CochainDGAlgebra.{u, v} R)
    (x y : A.cycles 0) :
    A.homologyπ 0 x * A.homologyπ 0 y = A.homologyπ 0 (A.cyclesMul 0 0 x y) := sorry

/-- The structural algebra map sends a scalar to its multiple of the cohomology unit. -/
@[simp]
theorem homologyZero_algebraMap (A : CochainDGAlgebra.{u, v} R) (r : R) :
    algebraMap R A.homologyZero r = r • A.homologyOne := sorry

namespace Hom

variable {A B C : CochainDGAlgebra.{u, v} R}

/-- The induced cohomology map preserves the unit class. -/
@[simp]
theorem homologyLinearMap_one (f : Hom A B) :
    f.homologyLinearMap 0 A.homologyOne = B.homologyOne := sorry

/-- The algebra homomorphism on zeroth cohomology induced by a cochain-DGA homomorphism. -/
@[stacks 09S8 "map on zeroth cochain-DGA cohomology"]
noncomputable def homologyZeroMap (f : Hom A B) :
    A.homologyZero →ₐ[R] B.homologyZero where
  toFun := f.homologyLinearMap 0
  map_zero' := sorry
  map_one' := f.homologyLinearMap_one
  map_add' := sorry
  map_mul' := fun x y ↦ f.homologyLinearMap_mul 0 0 x y
  commutes' := sorry

/-- The zeroth-cohomology algebra map is the canonical map on homology in degree zero. -/
@[simp]
theorem homologyZeroMap_apply (f : Hom A B) (x : A.homologyZero) :
    f.homologyZeroMap x = f.homologyLinearMap 0 x := sorry

/-- The identity cochain-DGA map induces the identity on zeroth cohomology algebras. -/
@[simp]
theorem homologyZeroMap_id (A : CochainDGAlgebra.{u, v} R) :
    (id A).homologyZeroMap = AlgHom.id R A.homologyZero := sorry

/-- Zeroth-cohomology algebra maps preserve composition. -/
@[simp]
theorem homologyZeroMap_comp (g : Hom B C) (f : Hom A B) :
    (comp g f).homologyZeroMap = g.homologyZeroMap.comp f.homologyZeroMap := sorry

end Hom

/-- Zeroth cohomology as a functor from cochain DGAs to ordinary `R`-algebras. -/
@[stacks 09S8 "zeroth cohomology functor for cochain DGAs"]
noncomputable def homologyZeroFunctor (R : Type u) [CommRing R] :
    CochainDGAlgebra.{u, v} R ⥤ AlgCat.{v} R where
  obj A := AlgCat.of R A.homologyZero
  map f := AlgCat.ofHom (Hom.homologyZeroMap f)
  map_id := sorry
  map_comp := sorry

end CochainDGAlgebra
