module

public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.AdjoinVariable.Predifferential.Even
import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical coefficient model of an even cell

Every even one-cell extension is canonically compared with the explicit divided-monomial model
built from the even adjoining-variable predifferential.  Coefficients are therefore derived from
the cell universal property and cannot disagree with multiplication, differential, or the chosen
base and generator.
-/

@[expose] public section

noncomputable section

open CategoryTheory HomologicalComplex

universe u v

namespace DividedPowerChainAlgebra.Adjoin.Even.Extension

variable {R : Type u} [CommRing R]
variable {A : DividedPowerChainAlgebra.{u, v} R} {d : ℕ+}
variable {f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}

/-- The canonical explicit divided-monomial model associated to an arbitrary even cell. -/
@[stacks 09PM "canonical explicit model of an even cell"]
def standardModel (X : Even.Extension A d f) : Even.Extension A d f :=
  Even.extension A d X.degree_even f X.attaching_isCycle

/-- The degree-`m` component of the canonical comparison with the explicit even-cell model. -/
def modelPieceIso (X : Even.Extension A d f) (m : ℕ) :
    X.algebra.toChainDGAlgebra.X (m : ℤ) ≅
      X.standardModel.algebra.toChainDGAlgebra.X (m : ℤ) :=
  (HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.down ℤ) (m : ℤ)).mapIso <|
    Cell.Comparison.chainIso X.toCell X.standardModel.toCell

/-- The canonical divided-monomial coordinates of an arbitrary even cell. -/
@[stacks 09PM "canonical coefficient presentation of an even cell"]
def coefficientEquiv (X : Even.Extension A d f) (m : ℕ) :
    X.algebra.toChainDGAlgebra.nonnegativePiece m ≃ₗ[R]
      NonnegGradedAlgebra.Adjoin.Even.Piece
        A.toChainDGAlgebra.nonnegativePart (d : ℕ) m :=
  (X.modelPieceIso m).toLinearEquiv.trans
    (Even.pieceEquiv A d X.degree_even f X.attaching_isCycle m)

/-- Extract the coefficient of a specified divided monomial from an arbitrary even-cell
element. -/
def coefficient (X : Even.Extension A d f) {m : ℕ}
    (i : {i : ℕ // i * (d : ℕ) ≤ m}) :
    X.algebra.toChainDGAlgebra.nonnegativePiece m →ₗ[R]
      A.toChainDGAlgebra.nonnegativePiece (m - (i : ℕ) * (d : ℕ)) :=
  (DFinsupp.lapply i).comp (X.coefficientEquiv m).toLinearMap

/-- The actual cell differential expressed in its canonical even divided-monomial coordinates. -/
def coeffDifferential (X : Even.Extension A d f) (m : ℕ+) :
    NonnegGradedAlgebra.Adjoin.Even.Piece
        A.toChainDGAlgebra.nonnegativePart (d : ℕ) (m : ℕ) →ₗ[R]
      NonnegGradedAlgebra.Adjoin.Even.Piece
        A.toChainDGAlgebra.nonnegativePart (d : ℕ) ((m : ℕ) - 1) :=
  (X.coefficientEquiv ((m : ℕ) - 1)).toLinearMap.comp <|
    (X.algebra.toChainDGAlgebra.nonnegativeDifferential m).comp
      (X.coefficientEquiv (m : ℕ)).symm.toLinearMap

/-- In successor degree, the canonical transported differential is the explicit even coefficient
differential. -/
@[simp]
theorem coeffDifferential_succ (X : Even.Extension A d f) (m : ℕ) :
    X.coeffDifferential ⟨m + 1, Nat.zero_lt_succ m⟩ =
      DividedPowerChainAlgebra.Adjoin.Even.coefficientDifferential A d f m := sorry

/-- Evaluation of the canonical divided-monomial coefficient projection. -/
@[simp]
theorem coefficient_apply (X : Even.Extension A d f) {m : ℕ}
    (i : {i : ℕ // i * (d : ℕ) ≤ m})
    (x : X.algebra.toChainDGAlgebra.nonnegativePiece m) :
    X.coefficient i x = X.coefficientEquiv m x i := sorry

/-- In canonical coordinates, the base inclusion is the constant coefficient. -/
@[simp]
theorem coefficientEquiv_base (X : Even.Extension A d f) (m : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePiece m) :
    X.coefficientEquiv m (X.toCell.ι.toChainHom (m : ℤ) x) =
      DividedPowerChainAlgebra.Adjoin.Even.baseCoeff
        A.toChainDGAlgebra.nonnegativePart (d : ℕ) m x := sorry

/-- In canonical coordinates, the cell generator is the exponent-one divided monomial. -/
@[simp]
theorem coefficientEquiv_generator (X : Even.Extension A d f) :
    X.coefficientEquiv d X.toCell.generator =
      DividedPowerChainAlgebra.Adjoin.Even.generatorCoeff
        A.toChainDGAlgebra.nonnegativePart d := sorry

/-- The canonical coefficient equivalence intertwines the cell differential with the explicit
even divided-monomial differential. -/
@[stacks 09PM "canonical even-cell coefficient differential"]
theorem coefficientEquiv_d (X : Even.Extension A d f) (m : ℕ)
    (x : X.algebra.toChainDGAlgebra.nonnegativePiece (m + 1)) :
    X.coefficientEquiv m
        (X.algebra.toChainDGAlgebra.nonnegativeDifferential
          ⟨m + 1, Nat.zero_lt_succ m⟩ x) =
      DividedPowerChainAlgebra.Adjoin.Even.coefficientDifferential A d f m
        (X.coefficientEquiv (m + 1) x) := sorry

/-- The canonical coefficient equivalence preserves homogeneous multiplication. -/
@[stacks 09PM "canonical even-cell coefficient multiplication"]
theorem coefficientEquiv_mul (X : Even.Extension A d f) (m n : ℕ)
    (x : X.algebra.toChainDGAlgebra.nonnegativePiece m)
    (y : X.algebra.toChainDGAlgebra.nonnegativePiece n) :
    X.coefficientEquiv (m + n)
        (X.algebra.toChainDGAlgebra.nonnegativeMul x y) =
      GradedMonoid.GMul.mul (X.coefficientEquiv m x) (X.coefficientEquiv n y) := sorry

end DividedPowerChainAlgebra.Adjoin.Even.Extension
