/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Transport
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.HomologyAlgebra
import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication by a cycle in a chain DGA

A degree-zero cycle acts on the underlying chain complex by right multiplication.  This file
owns that chain map independently of commutativity; comparison with left multiplication on
homology is stated only under strict graded commutativity.
-/

@[expose] public section

noncomputable section

open CategoryTheory HomologicalComplex

universe u v

namespace ChainDGAlgebra.Cycle

variable {R : Type u} [CommRing R]

/-- Right multiplication by a degree-zero element on the degree-`n` component of a chain DGA. -/
def rightMulApp (A : ChainDGAlgebra.{u, v} R) (z : A.X 0) (n : ℤ) :
    A.X n →ₗ[R] A.X n :=
  _root_.ModuleCat.castLinearMap (congrArg A.X (add_zero n)) <|
    (A.mul n 0).flip z

/-- Evaluation of degreewise right multiplication by a cycle. -/
@[simp]
theorem rightMulApp_apply (A : ChainDGAlgebra.{u, v} R) (z : A.X 0)
    (n : ℤ) (x : A.X n) :
    rightMulApp A z n x =
      cast (congrArg (fun i : ℤ ↦ (A.X i : Type v)) (add_zero n))
        (A.mul n 0 x z) := sorry

/-- Degreewise right multiplication by a degree-zero cycle commutes with the differential. -/
theorem rightMulApp_comm (A : ChainDGAlgebra.{u, v} R) (z : A.X 0)
    (hz : A.d 0 z = 0)
    (i j : ℤ) (hij : (ComplexShape.down ℤ).Rel i j) :
    ModuleCat.ofHom (rightMulApp A z i) ≫ A.toChainComplex.d i j =
      A.toChainComplex.d i j ≫ ModuleCat.ofHom (rightMulApp A z j) := sorry

/-- Tag 0GZ6: the chain endomorphism given by right multiplication by a degree-zero cycle. -/
@[stacks 0GZ6 "right multiplication by a degree-zero cycle"]
def rightMul (A : ChainDGAlgebra.{u, v} R) (z : A.X 0) (hz : A.d 0 z = 0) :
    A.toChainComplex ⟶ A.toChainComplex where
  f n := ModuleCat.ofHom (rightMulApp A z n)
  comm' := rightMulApp_comm A z hz

/-- The components of the right-multiplication chain map are the explicit linear maps
`rightMulApp`. -/
@[simp]
theorem rightMul_f (A : ChainDGAlgebra.{u, v} R) (z : A.X 0) (hz : A.d 0 z = 0)
    (n : ℤ) :
    (rightMul A z hz).f n = ModuleCat.ofHom (rightMulApp A z n) := sorry

/-- The underlying homogeneous element of a bundled degree-zero cycle is closed. -/
theorem iCycles_isCycle (A : ChainDGAlgebra.{u, v} R) (z : A.cycles 0) :
    A.d 0 (A.iCycles 0 z) = 0 := sorry

/-- Right multiplication by a bundled degree-zero cycle. -/
@[stacks 0GZ6 "right multiplication by a bundled degree-zero cycle"]
def rightMulCycle (A : ChainDGAlgebra.{u, v} R) (z : A.cycles 0) :
    A.toChainComplex ⟶ A.toChainComplex :=
  rightMul A (A.iCycles 0 z) (iCycles_isCycle A z)

/-- The components of multiplication by a bundled cycle are obtained by multiplying by its
underlying homogeneous element. -/
@[simp]
theorem rightMulCycle_f (A : ChainDGAlgebra.{u, v} R) (z : A.cycles 0) (n : ℤ) :
    (rightMulCycle A z).f n =
      ModuleCat.ofHom (rightMulApp A (A.iCycles 0 z) n) := sorry

/-- The canonical zeroth-homology class represented by a bundled degree-zero cycle. -/
@[stacks 0GZ6 "homology class of a degree-zero cycle"]
def homologyClass (A : ChainDGAlgebra.{u, v} R) (z : A.cycles 0) :
    A.homologyPiece 0 :=
  A.homologyπ 0 z

/-- Left multiplication by the class of a degree-zero cycle on homology in degree `n`. -/
@[stacks 0GZ6 "homology multiplication by a degree-zero cycle"]
def homologyMulAt (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative]
    (z : A.cycles 0) (n : ℕ) :
    A.homologyPiece n →ₗ[R] A.homologyPiece n :=
  (A.homologyNonnegativePart.pieceCast (Nat.zero_add n)).comp <|
    A.homologyMul 0 n (homologyClass A z)

/-- Evaluation of multiplication by the homology class of a degree-zero cycle. -/
@[simp]
theorem homologyMulAt_apply (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative]
    (z : A.cycles 0) (n : ℕ) (x : A.homologyPiece n) :
    homologyMulAt A z n x =
      A.homologyNonnegativePart.pieceCast (Nat.zero_add n)
        (A.homologyMul 0 n (homologyClass A z) x) := sorry

/-- Left multiplication by the class of a degree-zero cycle on zeroth homology. -/
@[stacks 0GZ6 "zeroth-homology multiplication by a degree-zero cycle"]
def homologyMul (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative]
    (z : A.cycles 0) :
    A.homologyPiece 0 →ₗ[R] A.homologyPiece 0 :=
  homologyMulAt A z 0

/-- Evaluation of multiplication by a degree-zero cycle class on zeroth homology. -/
@[simp]
theorem homologyMul_apply (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative]
    (z : A.cycles 0) (x : A.homologyPiece 0) :
    homologyMul A z x = A.homologyMul 0 0 (homologyClass A z) x := sorry

/-- On nonnegative homology of a strictly commutative chain DGA, the map induced by right
multiplication by `z` is left multiplication by the class of `z`. -/
@[stacks 0GZ6 "homology action of a degree-zero cycle"]
theorem homologyMap_eq_mul (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative]
    (z : A.cycles 0) (n : ℕ) :
    HomologicalComplex.homologyMap (rightMulCycle A z) n =
      ModuleCat.ofHom (homologyMulAt A z n) := sorry

end ChainDGAlgebra.Cycle
