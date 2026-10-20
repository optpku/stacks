/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.AdjoinVariable.Predifferential.Odd
import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical coefficient model of an odd cell

Every odd one-cell extension is canonically compared with the explicit coefficient model built
from the odd adjoining-variable predifferential.  The resulting coefficient equivalence is
compatible with the base inclusion, generator, differential, and multiplication; it does not use
the unconstrained presentation equivalence stored in an arbitrary extension.
-/

@[expose] public section

noncomputable section

open CategoryTheory HomologicalComplex

universe u v

namespace DividedPowerChainAlgebra.Adjoin.Odd.Extension

variable {R : Type u} [CommRing R]
variable {A : DividedPowerChainAlgebra.{u, v} R} {d : ℕ+}
variable {f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}

/-- The canonical explicit coefficient model associated to an arbitrary odd cell. -/
@[stacks 09PM "canonical explicit model of an odd cell"]
def standardModel (X : Odd.Extension A d f) : Odd.Extension A d f :=
  Odd.extension A d X.degree_odd f X.attaching_isCycle

/-- The degree-`m` component of the canonical comparison with the explicit odd-cell model. -/
def modelPieceIso (X : Odd.Extension A d f) (m : ℕ) :
    X.algebra.toChainDGAlgebra.X (m : ℤ) ≅
      X.standardModel.algebra.toChainDGAlgebra.X (m : ℤ) :=
  (HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.down ℤ) (m : ℤ)).mapIso <|
    Cell.Comparison.chainIso X.toCell X.standardModel.toCell

/-- The canonical coefficient presentation of an arbitrary odd cell, obtained by comparison with
the explicit predifferential model. -/
@[stacks 09PM "canonical coefficient presentation of an odd cell"]
def coefficientEquiv (X : Odd.Extension A d f) (m : ℕ) :
    X.algebra.toChainDGAlgebra.nonnegativePiece m ≃ₗ[R]
      NonnegGradedAlgebra.Adjoin.Odd.Piece
        A.toChainDGAlgebra.nonnegativePart (d : ℕ) m :=
  (X.modelPieceIso m).toLinearEquiv.trans
    (Odd.pieceEquiv A d X.degree_odd f X.attaching_isCycle m)

/-- The constant coefficient of an arbitrary odd-cell element in its canonical presentation. -/
@[stacks 09PM "canonical constant coefficient of an odd cell"]
def baseCoefficient (X : Odd.Extension A d f) (m : ℕ) :
    X.algebra.toChainDGAlgebra.nonnegativePiece m →ₗ[R]
      A.toChainDGAlgebra.nonnegativePiece m :=
  (NonnegGradedAlgebra.Adjoin.Odd.baseProjection
    A.toChainDGAlgebra.nonnegativePart (d : ℕ) m).comp
      (X.coefficientEquiv m).toLinearMap

/-- The coefficient of the odd variable in an arbitrary cell element whenever its degree is at
least the variable degree. -/
@[stacks 09PM "canonical variable coefficient of an odd cell"]
def variableCoefficient (X : Odd.Extension A d f) {m : ℕ} (h : (d : ℕ) ≤ m) :
    X.algebra.toChainDGAlgebra.nonnegativePiece m →ₗ[R]
      A.toChainDGAlgebra.nonnegativePiece (m - (d : ℕ)) :=
  (NonnegGradedAlgebra.Adjoin.Odd.variableProjection
    A.toChainDGAlgebra.nonnegativePart (d : ℕ) h).comp
      (X.coefficientEquiv m).toLinearMap

/-- The actual cell differential expressed in its canonical odd coefficient coordinates. -/
def coeffDifferential (X : Odd.Extension A d f) (m : ℕ+) :
    NonnegGradedAlgebra.Adjoin.Odd.Piece
        A.toChainDGAlgebra.nonnegativePart (d : ℕ) (m : ℕ) →ₗ[R]
      NonnegGradedAlgebra.Adjoin.Odd.Piece
        A.toChainDGAlgebra.nonnegativePart (d : ℕ) ((m : ℕ) - 1) :=
  (X.coefficientEquiv ((m : ℕ) - 1)).toLinearMap.comp <|
    (X.algebra.toChainDGAlgebra.nonnegativeDifferential m).comp
      (X.coefficientEquiv (m : ℕ)).symm.toLinearMap

/-- In successor degree, the canonical transported differential is the explicit odd coefficient
differential. -/
@[simp]
theorem coeffDifferential_succ (X : Odd.Extension A d f) (m : ℕ) :
    X.coeffDifferential ⟨m + 1, Nat.zero_lt_succ m⟩ =
      DividedPowerChainAlgebra.Adjoin.Odd.coefficientDifferential A d f m := sorry

/-- Evaluation of the canonical constant-coefficient projection. -/
@[simp]
theorem baseCoefficient_apply (X : Odd.Extension A d f) (m : ℕ)
    (x : X.algebra.toChainDGAlgebra.nonnegativePiece m) :
    X.baseCoefficient m x =
      NonnegGradedAlgebra.Adjoin.Odd.baseProjection
        A.toChainDGAlgebra.nonnegativePart (d : ℕ) m (X.coefficientEquiv m x) := sorry

/-- Evaluation of the canonical variable-coefficient projection. -/
@[simp]
theorem variableCoefficient_apply (X : Odd.Extension A d f) {m : ℕ}
    (h : (d : ℕ) ≤ m) (x : X.algebra.toChainDGAlgebra.nonnegativePiece m) :
    X.variableCoefficient h x =
      NonnegGradedAlgebra.Adjoin.Odd.variableProjection
        A.toChainDGAlgebra.nonnegativePart (d : ℕ) h (X.coefficientEquiv m x) := sorry

/-- In canonical coefficient coordinates, the base inclusion is the constant coefficient. -/
@[simp]
theorem coefficientEquiv_base (X : Odd.Extension A d f) (m : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePiece m) :
    X.coefficientEquiv m (X.toCell.ι.toChainHom (m : ℤ) x) =
      DividedPowerChainAlgebra.Adjoin.Odd.baseCoeff
        A.toChainDGAlgebra.nonnegativePart (d : ℕ) m x := sorry

/-- In canonical coefficient coordinates, the cell generator is the exponent-one vector. -/
@[simp]
theorem coefficientEquiv_generator (X : Odd.Extension A d f) :
    X.coefficientEquiv d X.toCell.generator =
      DividedPowerChainAlgebra.Adjoin.Odd.generatorCoeff
        A.toChainDGAlgebra.nonnegativePart d := sorry

/-- The canonical coefficient equivalence intertwines the cell differential with the explicit odd
coefficient differential. -/
@[stacks 09PM "canonical odd-cell coefficient differential"]
theorem coefficientEquiv_d (X : Odd.Extension A d f) (m : ℕ)
    (x : X.algebra.toChainDGAlgebra.nonnegativePiece (m + 1)) :
    X.coefficientEquiv m
        (X.algebra.toChainDGAlgebra.nonnegativeDifferential
          ⟨m + 1, Nat.zero_lt_succ m⟩ x) =
      DividedPowerChainAlgebra.Adjoin.Odd.coefficientDifferential A d f m
        (X.coefficientEquiv (m + 1) x) := sorry

/-- The canonical coefficient equivalence preserves homogeneous multiplication. -/
@[stacks 09PM "canonical odd-cell coefficient multiplication"]
theorem coefficientEquiv_mul (X : Odd.Extension A d f) (m n : ℕ)
    (x : X.algebra.toChainDGAlgebra.nonnegativePiece m)
    (y : X.algebra.toChainDGAlgebra.nonnegativePiece n) :
    X.coefficientEquiv (m + n)
        (X.algebra.toChainDGAlgebra.nonnegativeMul x y) =
      GradedMonoid.GMul.mul (X.coefficientEquiv m x) (X.coefficientEquiv n y) := sorry

end DividedPowerChainAlgebra.Adjoin.Odd.Extension
