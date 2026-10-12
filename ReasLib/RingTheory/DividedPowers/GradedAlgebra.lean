/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.DirectSum.NonnegGradedAlgebra
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Divided powers on nonnegatively graded algebras

This file adds the source-specific divided-power structure carried by the positive even part of a
strictly graded-commutative nonnegative algebra. The parity decomposition and all multiplication
maps are owned by `NonnegGradedAlgebra`; this leaf contains only divided-power data and laws.

The coefficients use the canonical Mathlib forms `Nat.choose` and `Nat.uniformBell`, matching the
corresponding fields of `DividedPowers` on an ordinary commutative ideal.
-/

@[expose] public section

open scoped BigOperators DirectSum

universe u v

namespace NonnegGradedAlgebra

variable {R : Type u} [CommRing R]
variable {A : NonnegGradedAlgebra.{u, v} R}

/-- Definition 23.6.1 (Tag 09PG): divided powers on the positive even part of a strictly
graded-commutative nonnegatively graded algebra. -/
@[stacks 09PG]
structure DividedPowers (A : NonnegGradedAlgebra.{u, v} R) where
  /-- The total family `gamma n : A_even+ → A_even`, including `gamma 0`. -/
  gamma : ℕ → A.evenPositivePart → A.evenPart
  /-- Every positive divided power lands in the positive-even part. -/
  gammaPos : ℕ+ → A.evenPositivePart → A.evenPositivePart
  /-- The positive-index refinement agrees with `gamma` after the canonical inclusion. -/
  gamma_eq_gammaPos (n : ℕ+) (x : A.evenPositivePart) :
    gamma n x = A.evenPositiveToEven (gammaPos n x)
  /-- A homogeneous element of degree `2 * (d + 1)` is sent to degree
  `2 * n * (d + 1)`. -/
  gamma_degree (n d : ℕ) (x : A.piece (2 * (d + 1))) :
    ∃ y : A.piece (2 * (n * (d + 1))),
      gamma n (A.evenPositiveHom d x) = A.evenHom (n * (d + 1)) y
  /-- The first divided power is the positive-even inclusion. -/
  gamma_one (x : A.evenPositivePart) :
    gamma 1 x = A.evenPositiveToEven x
  /-- The zeroth divided power is the graded unit. -/
  gamma_zero (x : A.evenPositivePart) :
    gamma 0 x = A.oneEven
  /-- Multiplying divided powers uses the binomial coefficient. -/
  gamma_mul (n m : ℕ) (x : A.evenPositivePart) :
    A.evenMul (gamma n x) (gamma m x) = Nat.choose (n + m) n • gamma (n + m) x
  /-- Divided powers of an even multiple satisfy `gamma n (x * y) = x ^ n * gamma n y`. -/
  gamma_evenMul (n : ℕ) (x : A.evenPart) (y : A.evenPositivePart) :
    gamma n (A.evenMulPositive x y) = A.evenMul (A.evenPow x n) (gamma n y)
  /-- Higher divided powers of a product of homogeneous odd elements vanish. -/
  gamma_oddMul {n : ℕ} (hn : 1 < n) (i j : ℕ)
      (x : A.piece (2 * i + 1)) (y : A.piece (2 * j + 1)) :
    gamma n (A.oddMulTerm i j x y) = 0
  /-- Divided powers turn sums in the positive-even part into the antidiagonal convolution. -/
  gamma_add (n : ℕ) (x y : A.evenPositivePart) :
    gamma n (x + y) =
      (Finset.antidiagonal n).sum fun ij ↦ A.evenMul (gamma ij.1 x) (gamma ij.2 y)
  /-- Iterated divided powers use the canonical composition coefficient `Nat.uniformBell`. -/
  gamma_comp (n : ℕ) (m : ℕ+) (x : A.evenPositivePart) :
    gamma n (gammaPos m x) = Nat.uniformBell n m • gamma (n * (m : ℕ)) x

namespace DividedPowers

attribute [simp] NonnegGradedAlgebra.DividedPowers.gamma_zero
attribute [simp] NonnegGradedAlgebra.DividedPowers.gamma_one

/-- A graded divided-power structure evaluates to its family `gamma`. -/
instance : CoeFun (NonnegGradedAlgebra.DividedPowers A)
    (fun _ ↦ ℕ → A.evenPositivePart → A.evenPart) where
  coe gamma := gamma.gamma

/-- Coercion to the divided-power family is definitionally its `gamma` field. -/
@[simp]
theorem coe_apply (gamma : NonnegGradedAlgebra.DividedPowers A)
    (n : ℕ) (x : A.evenPositivePart) :
    gamma n x = gamma.gamma n x := sorry

/-- The homogeneous value of `gamma n` on an input of degree `2 * (d + 1)`, obtained by
projecting the total even output to its forced degree `2 * (n * (d + 1))`. -/
def gammaPiece (gamma : NonnegGradedAlgebra.DividedPowers A) (n d : ℕ)
    (x : A.piece (2 * (d + 1))) : A.piece (2 * (n * (d + 1))) :=
  DirectSum.component R ℕ (fun e ↦ A.piece (2 * e)) (n * (d + 1))
    (gamma n (A.evenPositiveHom d x))

/-- The total divided power of a homogeneous input is the inclusion of its explicit
homogeneous value. -/
@[simp]
theorem gamma_eq_evenHom_gammaPiece
    (gamma : NonnegGradedAlgebra.DividedPowers A) (n d : ℕ)
    (x : A.piece (2 * (d + 1))) :
    gamma n (A.evenPositiveHom d x) =
      A.evenHom (n * (d + 1)) (gamma.gammaPiece n d x) := sorry

/-- A homogeneous representative of a divided power is necessarily `gammaPiece`. -/
theorem gammaPiece_eq_of_gamma_eq_evenHom
    (gamma : NonnegGradedAlgebra.DividedPowers A) (n d : ℕ)
    (x : A.piece (2 * (d + 1)))
    {y : A.piece (2 * (n * (d + 1)))}
    (hy : gamma n (A.evenPositiveHom d x) =
      A.evenHom (n * (d + 1)) y) :
    gamma.gammaPiece n d x = y := sorry

/-- A graded divided-power structure is determined by its family of operations. -/
@[ext]
theorem ext (gamma delta : NonnegGradedAlgebra.DividedPowers A)
    (h : ∀ n x, gamma n x = delta n x) : gamma = delta := sorry

/-- Including a positive divided power into the even part recovers the total operation. -/
@[simp]
theorem evenPositiveToEven_gammaPos
    (gamma : NonnegGradedAlgebra.DividedPowers A) (n : ℕ+) (x : A.evenPositivePart) :
    A.evenPositiveToEven (gamma.gammaPos n x) = gamma n x := sorry

/-- The positive-index factorization with an explicit natural-number positivity proof. -/
theorem gamma_eq_gammaPos_nat
    (gamma : NonnegGradedAlgebra.DividedPowers A)
    (n : ℕ) (hn : 0 < n) (x : A.evenPositivePart) :
    gamma n x = A.evenPositiveToEven (gamma.gammaPos ⟨n, hn⟩ x) := sorry

/-- Iterated divided powers with a positive inner index. -/
theorem gamma_comp_nat
    (gamma : NonnegGradedAlgebra.DividedPowers A)
    (n m : ℕ) (hm : 0 < m) (x : A.evenPositivePart) :
    gamma n (gamma.gammaPos ⟨m, hm⟩ x) =
      Nat.uniformBell n m • gamma (n * m) x := sorry

/-- Iterated positive divided powers, viewed in the full even part. -/
theorem gamma_comp_pos
    (gamma : NonnegGradedAlgebra.DividedPowers A)
    (n m : ℕ+) (x : A.evenPositivePart) :
    A.evenPositiveToEven (gamma.gammaPos n (gamma.gammaPos m x)) =
      Nat.uniformBell n m • gamma ((n : ℕ) * (m : ℕ)) x := sorry

end DividedPowers

end NonnegGradedAlgebra
