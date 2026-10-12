/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.OfPredifferential
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.Predifferential

/-!
# Divided-power chain algebras from square-zero predifferentials

A divided-power-compatible predifferential on a nonnegatively graded algebra extends by zero to
an integer-graded predifferential.  When it squares to zero, the generic chain-graded construction
produces a chain DGA.  This file adds the divided-power structure without transporting non-Prop
data across an equality of bundled graded algebras: the two divided-power operations are retained
literally, while every law is restated for the reconstructed nonnegative algebra.
-/

@[expose] public section

noncomputable section

open scoped BigOperators DirectSum

universe u v

namespace DividedPowerGradedAlgebra.Predifferential

variable {R : Type u} [CommRing R]
variable {A : DividedPowerGradedAlgebra.{u, v} R}

/-- The chain DGA obtained by applying the generic square-zero predifferential construction to
the extension-by-zero chain grading. -/
def toChainDGAlgebra (d : A.Predifferential) (hd : d.IsSquareZero) :
    ChainDGAlgebra.{u, v} R :=
  ChainGradedAlgebra.Predifferential.toChainDGAlgebra d.toPredifferential hd

namespace ToChain

/-- Multiplication in the reconstructed chain DGA obeys the Koszul commutativity rule inherited
from the original nonnegative graded algebra. -/
theorem mul_comm (d : A.Predifferential) (hd : d.IsSquareZero) {n m : ℤ}
    (x : (d.toChainDGAlgebra hd).X n) (y : (d.toChainDGAlgebra hd).X m) :
    (d.toChainDGAlgebra hd).mul n m x y =
      cast (congrArg (fun i : ℤ ↦ ((d.toChainDGAlgebra hd).X i : Type v)) (add_comm m n))
        (((n * m).negOnePow : R) • (d.toChainDGAlgebra hd).mul m n y x) := sorry

/-- Odd homogeneous elements have square zero in the reconstructed chain DGA. -/
theorem sq_eq_zero_of_odd (d : A.Predifferential) (hd : d.IsSquareZero)
    {n : ℤ} (hn : Odd n) (x : (d.toChainDGAlgebra hd).X n) :
    (d.toChainDGAlgebra hd).mul n n x x = 0 := sorry

/-- The canonical strict graded-commutativity instance on the chain DGA reconstructed from a
divided-power predifferential. -/
noncomputable instance instIsStrictlyCommutative (d : A.Predifferential)
    (hd : d.IsSquareZero) : (d.toChainDGAlgebra hd).IsStrictlyCommutative where
  mul_comm := mul_comm d hd
  sq_eq_zero_of_odd := sq_eq_zero_of_odd d hd

/-- The reconstructed chain DGA is supported in nonnegative degrees. -/
theorem isNonnegative (d : A.Predifferential) (hd : d.IsSquareZero) :
    (d.toChainDGAlgebra hd).IsNonnegative := sorry

end ToChain

/-- The nonnegative graded algebra obtained by restricting the reconstructed chain DGA. -/
noncomputable abbrev toNonnegativeGradedAlgebra
    (d : A.Predifferential) (hd : d.IsSquareZero) : NonnegGradedAlgebra.{u, v} R :=
  (d.toChainDGAlgebra hd).nonnegativePart

namespace ToChain

/-- The total divided-power operation on the reconstructed nonnegative algebra, explicitly
retained from the original divided-power graded algebra. -/
def gamma (d : A.Predifferential) (hd : d.IsSquareZero) :
    ℕ → (d.toNonnegativeGradedAlgebra hd).evenPositivePart →
      (d.toNonnegativeGradedAlgebra hd).evenPart :=
  fun n x ↦ A.gamma.gamma n x

/-- The positive-index divided-power operation on the reconstructed nonnegative algebra,
explicitly retained from the original divided-power graded algebra. -/
def gammaPos (d : A.Predifferential) (hd : d.IsSquareZero) :
    ℕ+ → (d.toNonnegativeGradedAlgebra hd).evenPositivePart →
      (d.toNonnegativeGradedAlgebra hd).evenPositivePart :=
  fun n x ↦ A.gamma.gammaPos n x

/-- Positive divided powers agree with the total operation after inclusion into the even part. -/
theorem gamma_eq_gammaPos (d : A.Predifferential) (hd : d.IsSquareZero)
    (n : ℕ+) (x : (d.toNonnegativeGradedAlgebra hd).evenPositivePart) :
    gamma d hd n x =
      (d.toNonnegativeGradedAlgebra hd).evenPositiveToEven (gammaPos d hd n x) := sorry

/-- The reconstructed divided powers have the prescribed homogeneous degree. -/
theorem gamma_degree (d : A.Predifferential) (hd : d.IsSquareZero)
    (n e : ℕ) (x : (d.toNonnegativeGradedAlgebra hd).piece (2 * (e + 1))) :
    ∃ y : (d.toNonnegativeGradedAlgebra hd).piece (2 * (n * (e + 1))),
      gamma d hd n ((d.toNonnegativeGradedAlgebra hd).evenPositiveHom e x) =
        (d.toNonnegativeGradedAlgebra hd).evenHom (n * (e + 1)) y := sorry

/-- The first reconstructed divided power is the positive-even inclusion. -/
theorem gamma_one (d : A.Predifferential) (hd : d.IsSquareZero)
    (x : (d.toNonnegativeGradedAlgebra hd).evenPositivePart) :
    gamma d hd 1 x = (d.toNonnegativeGradedAlgebra hd).evenPositiveToEven x := sorry

/-- The zeroth reconstructed divided power is the graded unit. -/
theorem gamma_zero (d : A.Predifferential) (hd : d.IsSquareZero)
    (x : (d.toNonnegativeGradedAlgebra hd).evenPositivePart) :
    gamma d hd 0 x = (d.toNonnegativeGradedAlgebra hd).oneEven := sorry

/-- Multiplication of reconstructed divided powers uses the binomial coefficient. -/
theorem gamma_mul (d : A.Predifferential) (hd : d.IsSquareZero)
    (n m : ℕ) (x : (d.toNonnegativeGradedAlgebra hd).evenPositivePart) :
    (d.toNonnegativeGradedAlgebra hd).evenMul (gamma d hd n x) (gamma d hd m x) =
      Nat.choose (n + m) n • gamma d hd (n + m) x := sorry

/-- Reconstructed divided powers intertwine multiplication by an even element with powers. -/
theorem gamma_evenMul (d : A.Predifferential) (hd : d.IsSquareZero)
    (n : ℕ) (x : (d.toNonnegativeGradedAlgebra hd).evenPart)
    (y : (d.toNonnegativeGradedAlgebra hd).evenPositivePart) :
    gamma d hd n ((d.toNonnegativeGradedAlgebra hd).evenMulPositive x y) =
      (d.toNonnegativeGradedAlgebra hd).evenMul
        ((d.toNonnegativeGradedAlgebra hd).evenPow x n) (gamma d hd n y) := sorry

/-- Higher reconstructed divided powers of a product of homogeneous odd elements vanish. -/
theorem gamma_oddMul (d : A.Predifferential) (hd : d.IsSquareZero)
    {n : ℕ} (hn : 1 < n) (i j : ℕ)
    (x : (d.toNonnegativeGradedAlgebra hd).piece (2 * i + 1))
    (y : (d.toNonnegativeGradedAlgebra hd).piece (2 * j + 1)) :
    gamma d hd n ((d.toNonnegativeGradedAlgebra hd).oddMulTerm i j x y) = 0 := sorry

/-- Reconstructed divided powers turn sums into the antidiagonal convolution. -/
theorem gamma_add (d : A.Predifferential) (hd : d.IsSquareZero)
    (n : ℕ) (x y : (d.toNonnegativeGradedAlgebra hd).evenPositivePart) :
    gamma d hd n (x + y) =
      (Finset.antidiagonal n).sum fun ij ↦
        (d.toNonnegativeGradedAlgebra hd).evenMul
          (gamma d hd ij.1 x) (gamma d hd ij.2 y) := sorry

/-- Iterating reconstructed divided powers uses the canonical composition coefficient. -/
theorem gamma_comp (d : A.Predifferential) (hd : d.IsSquareZero)
    (n : ℕ) (m : ℕ+) (x : (d.toNonnegativeGradedAlgebra hd).evenPositivePart) :
    gamma d hd n (gammaPos d hd m x) =
      Nat.uniformBell n m • gamma d hd (n * (m : ℕ)) x := sorry

/-- The divided-power structure on the reconstructed nonnegative algebra. Its two operation
fields are the original operations; only the laws are rebuilt against the new bundled algebra. -/
@[stacks 0GZ4 "divided powers on a chain DGA reconstructed from a predifferential"]
def dividedPowers (d : A.Predifferential) (hd : d.IsSquareZero) :
    NonnegGradedAlgebra.DividedPowers (d.toNonnegativeGradedAlgebra hd) where
  gamma := gamma d hd
  gammaPos := gammaPos d hd
  gamma_eq_gammaPos := gamma_eq_gammaPos d hd
  gamma_degree := gamma_degree d hd
  gamma_one := gamma_one d hd
  gamma_zero := gamma_zero d hd
  gamma_mul := gamma_mul d hd
  gamma_evenMul := gamma_evenMul d hd
  gamma_oddMul := gamma_oddMul d hd
  gamma_add := gamma_add d hd
  gamma_comp := gamma_comp d hd

/-- The reconstructed divided-power structure evaluates by the original total operation. -/
@[simp]
theorem dividedPowers_apply (d : A.Predifferential) (hd : d.IsSquareZero)
    (n : ℕ) (x : (d.toNonnegativeGradedAlgebra hd).evenPositivePart) :
    dividedPowers d hd n x = A.gamma n x := sorry

/-- The positive-index operation of the reconstructed structure is the original one. -/
@[simp]
theorem dividedPowers_gammaPos_apply (d : A.Predifferential) (hd : d.IsSquareZero)
    (n : ℕ+) (x : (d.toNonnegativeGradedAlgebra hd).evenPositivePart) :
    (dividedPowers d hd).gammaPos n x = A.gamma.gammaPos n x := sorry

/-- The differential of a reconstructed positive divided power is multiplication by the
differential of its input. -/
theorem differential_gamma (d : A.Predifferential) (hd : d.IsSquareZero)
    (n : ℕ+) (x : (d.toNonnegativeGradedAlgebra hd).evenPositivePart) :
    (d.toChainDGAlgebra hd).positiveEvenDifferential ((dividedPowers d hd).gammaPos n x) =
      (d.toNonnegativeGradedAlgebra hd).evenMulOdd
        (dividedPowers d hd ((n : ℕ) - 1) x)
        ((d.toChainDGAlgebra hd).positiveEvenDifferential x) := sorry

/-- The canonical compatibility instance between the reconstructed differential and divided
powers. -/
noncomputable instance instIsCompatible (d : A.Predifferential) (hd : d.IsSquareZero) :
    ChainDGAlgebra.DividedPowers.IsCompatible
      (d.toChainDGAlgebra hd) (dividedPowers d hd) where
  differential_gamma := differential_gamma d hd

end ToChain

/-- Tag 0GZ4: a divided-power-compatible square-zero predifferential, assembled as a
nonnegative divided-power chain DGA. -/
@[stacks 0GZ4 "divided-power chain algebra from a square-zero predifferential"]
def toChainAlgebra (d : A.Predifferential) (hd : d.IsSquareZero) :
    DividedPowerChainAlgebra.{u, v} R where
  toChainDGAlgebra := d.toChainDGAlgebra hd
  isStrictlyCommutative := ToChain.instIsStrictlyCommutative d hd
  isNonnegative := ToChain.isNonnegative d hd
  gamma := ToChain.dividedPowers d hd
  compatible := ToChain.instIsCompatible d hd

/-- The chain DGA underlying the assembled divided-power chain algebra is the generic
square-zero reconstruction. -/
@[simp]
theorem toChainAlgebra_toChainDGAlgebra (d : A.Predifferential) (hd : d.IsSquareZero) :
    (d.toChainAlgebra hd).toChainDGAlgebra = d.toChainDGAlgebra hd := sorry

/-- The degree-`n` component of the assembled chain algebra is the original extension-by-zero
component. -/
@[simp]
theorem toChainAlgebra_X (d : A.Predifferential) (hd : d.IsSquareZero) (n : ℤ) :
    (d.toChainAlgebra hd).toChainDGAlgebra.X n = A.toChainGradedAlgebra.X n := sorry

/-- Forgetting the differential of the assembled chain algebra recovers the original
extension-by-zero chain-graded algebra. -/
@[simp]
theorem toChainAlgebra_toChainGradedAlgebra
    (d : A.Predifferential) (hd : d.IsSquareZero) :
    (d.toChainAlgebra hd).toChainDGAlgebra.toChainGradedAlgebra =
      A.toChainGradedAlgebra := sorry

/-- Restricting the assembled chain DGA to nonnegative degrees recovers the original underlying
nonnegative graded algebra. -/
@[simp]
theorem toChainAlgebra_nonnegativePart
    (d : A.Predifferential) (hd : d.IsSquareZero) :
    (d.toChainAlgebra hd).toChainDGAlgebra.nonnegativePart = A.toGradedAlgebra := sorry

/-- Homogeneous multiplication on the reconstructed nonnegative part is the original graded
multiplication. -/
@[simp]
theorem toChainAlgebra_nonnegativeMul (d : A.Predifferential) (hd : d.IsSquareZero)
    (n m : ℕ) (x : A.toGradedAlgebra.piece n) (y : A.toGradedAlgebra.piece m) :
    (d.toChainAlgebra hd).toChainDGAlgebra.nonnegativeMul x y =
      A.toGradedAlgebra.chainMul n m x y := sorry

/-- The divided-power structure of the assembled chain algebra is the explicitly reconstructed
one. -/
@[simp]
theorem toChainAlgebra_gamma (d : A.Predifferential) (hd : d.IsSquareZero) :
    (d.toChainAlgebra hd).gamma = ToChain.dividedPowers d hd := sorry

/-- The assembled chain algebra evaluates divided powers by the original operation. -/
@[simp]
theorem toChainAlgebra_gamma_apply (d : A.Predifferential) (hd : d.IsSquareZero)
    (n : ℕ) (x : A.toGradedAlgebra.evenPositivePart) :
    (d.toChainAlgebra hd).gamma n x = A.gamma n x := sorry

/-- The positive divided-power operation in the assembled chain algebra is the original one. -/
@[simp]
theorem toChainAlgebra_gammaPos_apply (d : A.Predifferential) (hd : d.IsSquareZero)
    (n : ℕ+) (x : A.toGradedAlgebra.evenPositivePart) :
    (d.toChainAlgebra hd).gamma.gammaPos n x = A.gamma.gammaPos n x := sorry

/-- The differential of the assembled chain algebra acts as the original predifferential. -/
@[simp]
theorem toChainAlgebra_d_apply (d : A.Predifferential) (hd : d.IsSquareZero)
    (n : ℤ) (x : A.toChainGradedAlgebra.X n) :
    (d.toChainAlgebra hd).toChainDGAlgebra.d n x = d n x := sorry

/-- The predifferential underlying the assembled chain DGA is the original underlying
predifferential. -/
@[simp]
theorem toChainAlgebra_predifferential (d : A.Predifferential) (hd : d.IsSquareZero) :
    (d.toChainAlgebra hd).toChainDGAlgebra.predifferential = d.toPredifferential := sorry

/-- Forgetting the assembled chain algebra back to a divided-power graded algebra recovers the
original algebra. -/
@[simp]
theorem toChainAlgebra_toGradedAlgebra
    (d : A.Predifferential) (hd : d.IsSquareZero) :
    (d.toChainAlgebra hd).toGradedAlgebra = A := sorry

/-- Passing the assembled chain algebra back to the graded predifferential construction recovers
the original predifferential pointwise. This avoids transporting the bundled derivation across a
propositional equality of graded algebras. -/
@[simp]
theorem toChainAlgebra_toGradedPredifferential_apply
    (d : A.Predifferential) (hd : d.IsSquareZero)
    (n : ℤ) (x : A.toChainGradedAlgebra.X n) :
    (d.toChainAlgebra hd).toGradedPredifferential n x = d n x := sorry

end DividedPowerGradedAlgebra.Predifferential
