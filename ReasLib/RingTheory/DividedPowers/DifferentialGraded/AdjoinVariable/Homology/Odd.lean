/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.AdjoinVariable.Homology.Odd.Cofiber

/-!
# Homology after adjoining an odd variable of degree one

This file exposes the canonical maps in every natural degree of the degree-one adjoining-variable
calculation.  A closed degree-zero element gives a zeroth-homology class, whose multiplication on
`H_n` sits between the homology projection and the map induced by the cell inclusion.  The three
adjacent pairs are obtained from the explicit cofiber short exact sequence.  The degree-zero names
are retained as specializations, where the inclusion is additionally surjective by nonnegativity.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace DividedPowerChainAlgebra

variable {R : Type u} [CommRing R]

namespace Adjoin

/-- The zeroth-homology class of a closed degree-zero element used in a degree-one cell. -/
def degreeZeroClass (A : DividedPowerChainAlgebra.{u, v} R)
    (f : A.toChainDGAlgebra.nonnegativePiece 0) (hf : IsCycle A (1 : ℕ+) f) :
    A.toChainDGAlgebra.homology 0 :=
  ChainDGAlgebra.Cycle.homologyClass A.toChainDGAlgebra (degreeZeroCycle A f hf)

/-- Left multiplication by the zeroth-homology class of the element killed by a degree-one
cell, acting on homology in degree `n`. -/
def degreeZeroClassMulAt (A : DividedPowerChainAlgebra.{u, v} R)
    (f : A.toChainDGAlgebra.nonnegativePiece 0) (hf : IsCycle A (1 : ℕ+) f) (n : ℕ) :
    A.toChainDGAlgebra.homologyPiece n →ₗ[R] A.toChainDGAlgebra.homologyPiece n :=
  ChainDGAlgebra.Cycle.homologyMulAt A.toChainDGAlgebra (degreeZeroCycle A f hf) n

/-- Evaluation of multiplication by a closed degree-zero class on degree-`n` homology. -/
@[simp]
theorem degreeZeroClassMulAt_apply (A : DividedPowerChainAlgebra.{u, v} R)
    (f : A.toChainDGAlgebra.nonnegativePiece 0) (hf : IsCycle A (1 : ℕ+) f) (n : ℕ)
    (x : A.toChainDGAlgebra.homologyPiece n) :
    degreeZeroClassMulAt A f hf n x =
      A.toChainDGAlgebra.homologyNonnegativePart.pieceCast (Nat.zero_add n)
        (A.toChainDGAlgebra.homologyMul 0 n (degreeZeroClass A f hf) x) := sorry

/-- Left multiplication on zeroth homology by the class killed by a degree-one cell. -/
def degreeZeroClassMul (A : DividedPowerChainAlgebra.{u, v} R)
    (f : A.toChainDGAlgebra.nonnegativePiece 0) (hf : IsCycle A (1 : ℕ+) f) :
    A.toChainDGAlgebra.homology 0 →ₗ[R] A.toChainDGAlgebra.homology 0 :=
  ChainDGAlgebra.Cycle.homologyMul A.toChainDGAlgebra (degreeZeroCycle A f hf)

/-- Evaluation of multiplication by the class of the element killed by a degree-one cell. -/
@[simp]
theorem degreeZeroClassMul_apply (A : DividedPowerChainAlgebra.{u, v} R)
    (f : A.toChainDGAlgebra.nonnegativePiece 0) (hf : IsCycle A (1 : ℕ+) f)
    (x : A.toChainDGAlgebra.homology 0) :
    degreeZeroClassMul A f hf x =
      A.toChainDGAlgebra.homologyMul 0 0 (degreeZeroClass A f hf) x := sorry

namespace Odd.Extension

variable {A : DividedPowerChainAlgebra.{u, v} R}
variable {f : A.toChainDGAlgebra.nonnegativePiece 0}

/-- The raw attaching endomorphism agrees with multiplication by the bundled attaching cycle. -/
@[stacks 0GZ6 "odd-cell attaching map as cycle multiplication"]
theorem attachingMap_eq_rightMulCycle (X : Odd.Extension A (1 : ℕ+) f) :
    X.attachingMap =
      ChainDGAlgebra.Cycle.rightMulCycle A.toChainDGAlgebra X.attachingCycle := sorry

/-- The canonical zeroth-homology class of the attaching element of a degree-one odd cell. -/
@[stacks 0GZ6 "odd-cell attaching homology class"]
def attachingClass (X : Odd.Extension A (1 : ℕ+) f) : A.toChainDGAlgebra.homology 0 :=
  ChainDGAlgebra.Cycle.homologyClass A.toChainDGAlgebra X.attachingCycle

/-- Left multiplication by the attaching class of a degree-one odd cell. -/
@[stacks 0GZ6 "odd-cell attaching-class multiplication in each degree"]
def attachingClassMulAt (X : Odd.Extension A (1 : ℕ+) f) (n : ℕ) :
    A.toChainDGAlgebra.homologyPiece n →ₗ[R] A.toChainDGAlgebra.homologyPiece n :=
  ChainDGAlgebra.Cycle.homologyMulAt A.toChainDGAlgebra X.attachingCycle n

/-- Evaluation of multiplication by the attaching class on degree-`n` homology. -/
@[simp]
theorem attachingClassMulAt_apply (X : Odd.Extension A (1 : ℕ+) f) (n : ℕ)
    (x : A.toChainDGAlgebra.homologyPiece n) :
    X.attachingClassMulAt n x =
      A.toChainDGAlgebra.homologyNonnegativePart.pieceCast (Nat.zero_add n)
        (A.toChainDGAlgebra.homologyMul 0 n X.attachingClass x) := sorry

/-- The map induced by the attaching chain endomorphism is multiplication by the attaching class
on nonnegative homology. -/
@[stacks 0GZ6 "odd-cell attaching map on homology"]
theorem homologyMap_attachingMap_eq (X : Odd.Extension A (1 : ℕ+) f) (n : ℕ) :
    HomologicalComplex.homologyMap X.attachingMap n =
      ModuleCat.ofHom (X.attachingClassMulAt n) := sorry

/-- Left multiplication by the attaching class on zeroth homology. -/
@[stacks 0GZ6 "odd-cell attaching-class multiplication on zeroth homology"]
def attachingClassMul (X : Odd.Extension A (1 : ℕ+) f) :
    A.toChainDGAlgebra.homology 0 →ₗ[R] A.toChainDGAlgebra.homology 0 :=
  ChainDGAlgebra.Cycle.homologyMul A.toChainDGAlgebra X.attachingCycle

/-- Evaluation of multiplication by the attaching class of a degree-one odd cell. -/
@[simp]
theorem attachingClassMul_apply (X : Odd.Extension A (1 : ℕ+) f)
    (x : A.toChainDGAlgebra.homology 0) :
    X.attachingClassMul x = A.toChainDGAlgebra.homologyMul 0 0 X.attachingClass x := sorry

/-- The linear map on degree-`n` homology induced by the base inclusion into a degree-one odd
cell. -/
def homologyInclusion (X : Odd.Extension A (1 : ℕ+) f) (n : ℕ) :
    A.toChainDGAlgebra.homologyPiece n →ₗ[R]
      X.algebra.toChainDGAlgebra.homologyPiece n :=
  X.toCell.ι.toChainHom.homologyLinearMap n

/-- Evaluation of the homology map induced by the base inclusion in degree `n`. -/
@[simp]
theorem homologyInclusion_apply (X : Odd.Extension A (1 : ℕ+) f) (n : ℕ)
    (x : A.toChainDGAlgebra.homologyPiece n) :
    X.homologyInclusion n x = X.toCell.ι.toChainHom.homologyLinearMap n x := sorry

/-- The homology projection from degree `n + 1` of a degree-one odd cell to degree `n` of the
base, using the canonical homology identification for the shifted base complex. -/
@[stacks 0GZ6 "degree-one odd-cell homology projection"]
def homologyProjectionSucc (X : Odd.Extension A (1 : ℕ+) f) (n : ℕ) :
    X.algebra.toChainDGAlgebra.homologyPiece (Nat.succ n) →ₗ[R]
      A.toChainDGAlgebra.homologyPiece n :=
  ModuleCat.Hom.hom <|
    HomologicalComplex.homologyMap X.projection (Nat.succ n) ≫
      (ChainComplex.Homology.ShiftSequence.isoOfEq
        A.toChainDGAlgebra.toChainComplex (-1) (Nat.succ n) n
          (ChainComplex.Shift.MinusOne.add_succNat_index n)).inv

/-- The linear map on zeroth homology induced by the base inclusion into a degree-one odd
cell. -/
def homologyZeroInclusion (X : Odd.Extension A (1 : ℕ+) f) :
    A.toChainDGAlgebra.homology 0 →ₗ[R] X.algebra.toChainDGAlgebra.homology 0 :=
  X.homologyInclusion 0

/-- Evaluation of the zeroth-homology map induced by the base inclusion. -/
@[simp]
theorem homologyZeroInclusion_apply (X : Odd.Extension A (1 : ℕ+) f)
    (x : A.toChainDGAlgebra.homology 0) :
    X.homologyZeroInclusion x = X.toCell.ι.toChainHom.homologyLinearMap 0 x := sorry

/-- The inclusion into a degree-one odd cell kills its canonical attaching class. -/
theorem zeroInclusion_attachingClass_eq_zero
    (X : Odd.Extension A (1 : ℕ+) f) :
    X.homologyZeroInclusion X.attachingClass = 0 := sorry

/-- In every natural degree, the cell inclusion kills the image of multiplication by the
attaching class. -/
theorem inclusion_attachingMul_eq_zero
    (X : Odd.Extension A (1 : ℕ+) f) (n : ℕ)
    (x : A.toChainDGAlgebra.homologyPiece n) :
    X.homologyInclusion n (X.attachingClassMulAt n x) = 0 := sorry

/-- In every natural degree, multiplication by the attaching class followed by cell inclusion is
the zero linear map. -/
theorem inclusion_comp_attachingMul
    (X : Odd.Extension A (1 : ℕ+) f) (n : ℕ) :
    X.homologyInclusion n ∘ₗ X.attachingClassMulAt n = 0 := sorry

/-- Lemma 23.12.3 (1) (Tag 0GZ6): in every natural degree `n`, adjoining an odd variable `T` of
degree one with `d T = f` gives an exact segment
`H_n(A) ⟶ H_n(A) ⟶ H_n(A⟨T⟩)`, whose first map is multiplication by `[f]` and whose
second map is induced by the base inclusion. -/
@[stacks 0GZ6 "(1), all-degree adjoining-variable exactness"]
theorem exact_attachingMul_inclusion
    (X : Odd.Extension A (1 : ℕ+) f) (n : ℕ) :
    Function.Exact (X.attachingClassMulAt n) (X.homologyInclusion n) := sorry

/-- Lemma 23.12.3 (1) (Tag 0GZ6): in every natural degree `n`, the homology projection from
degree `n + 1` of the odd cell followed by multiplication by `[f]` is exact. -/
@[stacks 0GZ6 "(1), odd-cell projection-to-attaching exactness"]
theorem exact_projection_attachingMul
    (X : Odd.Extension A (1 : ℕ+) f) (n : ℕ) :
    Function.Exact (X.homologyProjectionSucc n) (X.attachingClassMulAt n) := sorry

/-- Lemma 23.12.3 (1) (Tag 0GZ6): in every positive natural degree, the inclusion-induced map
followed by the odd-cell homology projection is exact. -/
@[stacks 0GZ6 "(1), odd-cell inclusion-to-projection exactness"]
theorem exact_inclusion_projectionSucc
    (X : Odd.Extension A (1 : ℕ+) f) (n : ℕ) :
    Function.Exact (X.homologyInclusion (Nat.succ n))
      (X.homologyProjectionSucc n) := sorry

/-- Lemma 23.12.3 (1) (Tag 0GZ6), degree-zero specialization: multiplication by `[f]` followed by
the inclusion-induced map on zeroth homology is exact. -/
@[stacks 0GZ6 "(1), degree-one adjoining-variable exactness"]
theorem exact_attachingMul_zeroInclusion
    (X : Odd.Extension A (1 : ℕ+) f) :
    Function.Exact X.attachingClassMul X.homologyZeroInclusion := sorry

/-- The map on zeroth homology induced by the base inclusion into a degree-one odd cell is
surjective. -/
@[stacks 0GZ6 "(1), terminal surjectivity"]
theorem homologyZeroInclusion_surjective
    (X : Odd.Extension A (1 : ℕ+) f) :
    Function.Surjective X.homologyZeroInclusion := sorry

end Odd.Extension

end Adjoin

end DividedPowerChainAlgebra
