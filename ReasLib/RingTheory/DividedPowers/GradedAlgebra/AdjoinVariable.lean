/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.GradedAlgebra
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coefficient formulas for adjoining a graded variable

This file provides the reusable data layer behind adjoining one variable to a strictly
graded-commutative nonnegative algebra.  The homogeneous pieces use a degree-bounded shifted
direct sum, so no spurious degree-zero summand appears when a natural-number subtraction would
underflow.

The odd and even namespaces then expose the parity-level coefficient models and the divided-power
formulas.  They deliberately do not manufacture a `NonnegGradedAlgebra` owner: that construction
also needs the full Koszul-signed heterogeneous multiplication on the shifted pieces.  Once that
construction is available, the definitions here are the concrete coefficient data its even and
positive-even parts must realize.

The Stacks snapshot `a04446e57ec1`, Tag 09PI, omits the composition coefficient both in
`gamma_n(T ^ (i))` and in each exponent-distribution factor.  We use
`Nat.uniformBell n i = (n * i)! / ((i!) ^ n * n!)` for `i > 0`, as required by Tag 09PG (7) and the
calculation in Tag 07H5.  In particular `gamma_n(T) = T ^ (n)`, whereas
`gamma_2(T ^ (2)) = 3 • T ^ (4)`.
-/

@[expose] public section

open scoped BigOperators DirectSum

noncomputable section

universe u v w

namespace NonnegGradedAlgebra

variable {R : Type u} [CommRing R]

namespace Adjoin

/-- The degree-`m` direct sum of copies of `A`, shifted by the weights `weight i`.
Only indices whose weight is at most `m` occur, avoiding truncated-subtraction artifacts. -/
abbrev ShiftSum (A : NonnegGradedAlgebra.{u, v} R) {ι : Type w}
    (weight : ι → ℕ) (m : ℕ) : Type (max v w) :=
  Π₀ i : {i : ι // weight i ≤ m}, A.piece (m - weight i)

namespace Odd

variable (A : NonnegGradedAlgebra.{u, v} R)

/-- The homogeneous pieces of the coefficient model `A ⊕ A T` for one variable of degree `d`.
The exponent type `Fin 2` enforces `T ^ 2 = 0`. -/
@[stacks 09PH]
abbrev Piece (d m : ℕ) : Type v :=
  ShiftSum A (fun i : Fin 2 => (i : ℕ) * d) m

/-- Coefficients of the even part of an odd-variable extension, written `x + yT`. -/
abbrev Coeffs : Type v :=
  A.evenPart × A.oddPart

/-- Coefficients of the positive-even part of an odd-variable extension. -/
abbrev PositiveCoeffs : Type v :=
  A.evenPositivePart × A.oddPart

/-- The coefficient-level inclusion of the even part of `A`. -/
def ofEven (x : A.evenPart) : Coeffs A :=
  (x, 0)

/-- The coefficient-level inclusion of the positive-even part of `A`. -/
def ofPositive (x : A.evenPositivePart) : PositiveCoeffs A :=
  (x, 0)

/-- The odd-variable divided-power formula on parity-level coefficients. -/
@[stacks 09PH]
def gamma (gammaA : NonnegGradedAlgebra.DividedPowers A) :
    ℕ → PositiveCoeffs A → Coeffs A
  | 0, _ => ofEven A A.oneEven
  | n + 1, (x, y) =>
      (gammaA (n + 1) x, A.evenMulOdd (gammaA n x) y)

/-- The zeroth odd-variable divided power is the coefficient-level unit. -/
theorem gamma_zero (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (z : PositiveCoeffs A) :
    gamma A gammaA 0 z = ofEven A A.oneEven := by
  rfl

/-- The successor odd-variable divided powers satisfy
`gamma (n + 1) (x + yT) = gammaA (n + 1) x + gammaA n x * yT`. -/
theorem gamma_succ (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (n : ℕ) (x : A.evenPositivePart) (y : A.oddPart) :
    gamma A gammaA (n + 1) (x, y) =
      (gammaA (n + 1) x, A.evenMulOdd (gammaA n x) y) := by
  rfl

/-- The odd-variable coefficient formula restricts to the given divided powers on `A`. -/
theorem gamma_ofPositive (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (n : ℕ) (x : A.evenPositivePart) :
    gamma A gammaA (n + 1) (ofPositive A x) =
      ofEven A (gammaA (n + 1) x) := by
  change (gammaA (n + 1) x, A.evenMulOddDirect (gammaA n x) 0) = _
  rw [map_zero]
  rfl

/-- The two defining equations characterizing the odd-variable coefficient family. -/
structure IsGamma (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (delta : ℕ → PositiveCoeffs A → Coeffs A) : Prop where
  /-- The zeroth operation is the unit. -/
  zero (z : PositiveCoeffs A) : delta 0 z = ofEven A A.oneEven
  /-- Positive operations obey the odd-variable recursion. -/
  succ (n : ℕ) (x : A.evenPositivePart) (y : A.oddPart) :
    delta (n + 1) (x, y) =
      (gammaA (n + 1) x, A.evenMulOdd (gammaA n x) y)

/-- The explicit odd-variable family satisfies its coefficient specification. -/
theorem gamma_isGamma (gammaA : NonnegGradedAlgebra.DividedPowers A) :
    IsGamma A gammaA (gamma A gammaA) := by
  constructor
  · intro z
    rfl
  · intro n x y
    rfl

/-- A family satisfying the odd-variable coefficient specification is the explicit family. -/
theorem IsGamma.eq_gamma {gammaA : NonnegGradedAlgebra.DividedPowers A}
    {delta : ℕ → PositiveCoeffs A → Coeffs A}
    (hdelta : IsGamma A gammaA delta) :
    delta = gamma A gammaA := by
  funext n z
  cases n with
  | zero => exact hdelta.zero z
  | succ n => exact hdelta.succ n z.1 z.2

/-- The odd-variable coefficient specification is equivalent to equality with `gamma`. -/
theorem isGamma_iff (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (delta : ℕ → PositiveCoeffs A → Coeffs A) :
    IsGamma A gammaA delta ↔ delta = gamma A gammaA := by
  constructor
  · intro hdelta
    exact hdelta.eq_gamma
  · intro hdelta
    rw [hdelta]
    exact gamma_isGamma A gammaA

/-- The odd-variable recursion determines a unique coefficient family. -/
@[stacks 09PH]
theorem existsUnique_gamma (gammaA : NonnegGradedAlgebra.DividedPowers A) :
    ∃! delta : ℕ → PositiveCoeffs A → Coeffs A,
      IsGamma A gammaA delta := by
  refine ⟨gamma A gammaA, gamma_isGamma A gammaA, ?_⟩
  intro delta hdelta
  exact hdelta.eq_gamma

end Odd

namespace Even

variable (A : NonnegGradedAlgebra.{u, v} R)

/-- The homogeneous pieces of the coefficient model with divided monomials `T ^ (i)` for a
variable of degree `d`. -/
@[stacks 09PI]
abbrev Piece (d m : ℕ) : Type v :=
  ShiftSum A (fun i : ℕ => i * d) m

/-- Finitely supported coefficients of the divided monomials `T ^ (i)`. -/
abbrev Coeffs : Type v :=
  ℕ →₀ A.evenPart

/-- Positive-even coefficients, with the constant coefficient stored in `A.evenPositivePart`
and all positive divided-monomial coefficients stored without a witness choice.  The product model
inherits its additive and `R`-module structures componentwise. -/
abbrev PositiveCoeffs : Type v :=
  A.evenPositivePart × (ℕ+ →₀ A.evenPart)

namespace PositiveCoeffs

/-- The positive-even constant coefficient. -/
def constant (x : PositiveCoeffs A) : A.evenPositivePart :=
  x.1

/-- The coefficients at positive divided-monomial exponents. -/
def tail (x : PositiveCoeffs A) : ℕ+ →₀ A.evenPart :=
  x.2

end PositiveCoeffs

/-- The canonical embedding of positive natural numbers into natural numbers. -/
def posEmbedding : ℕ+ ↪ ℕ :=
  ⟨fun i => i, Subtype.val_injective⟩

/-- A single divided monomial with the specified coefficient. -/
def monomial (i : ℕ) (x : A.evenPart) : Coeffs A :=
  Finsupp.single i x

/-- The coefficient-level unit. -/
def one : Coeffs A :=
  monomial A 0 A.oneEven

/-- The inclusion of the positive-even part of `A` as the constant coefficient. -/
def ofPositive (x : A.evenPositivePart) : PositiveCoeffs A where
  fst := x
  snd := 0

/-- The positive divided monomial `T ^ (i)`. -/
def tPower (i : ℕ+) : PositiveCoeffs A where
  fst := 0
  snd := Finsupp.single i A.oneEven

/-- Forgetting positivity gives the full finitely supported coefficient family. -/
def PositiveCoeffs.toCoeffs (x : PositiveCoeffs A) : Coeffs A :=
  monomial A 0 (A.evenPositiveToEven x.constant) +
    Finsupp.embDomain posEmbedding x.tail

/-- Forgetting positivity preserves addition. -/
theorem PositiveCoeffs.toCoeffs_add (x y : PositiveCoeffs A) :
    (x + y).toCoeffs A = x.toCoeffs A + y.toCoeffs A := by
  simp [PositiveCoeffs.toCoeffs, PositiveCoeffs.constant, PositiveCoeffs.tail,
    monomial, Finsupp.single_add, Finsupp.embDomain_add, add_add_add_comm]

/-- Forgetting positivity preserves the `R`-module action. -/
theorem PositiveCoeffs.toCoeffs_smul (r : R) (x : PositiveCoeffs A) :
    (r • x).toCoeffs A = r • x.toCoeffs A := by
  have htail : Finsupp.embDomain posEmbedding (r • x.2) =
      r • Finsupp.embDomain posEmbedding x.2 :=
    Finsupp.embDomain_mapRange posEmbedding (fun a : A.evenPart ↦ r • a) x.2 (smul_zero r)
  simp [PositiveCoeffs.toCoeffs, PositiveCoeffs.constant, PositiveCoeffs.tail,
    monomial, Finsupp.single_smul, smul_add, htail]

/-- Multiplication of divided-monomial coefficients, using the canonical binomial coefficient. -/
@[stacks 09PI]
def mul (x y : Coeffs A) : Coeffs A :=
  x.sum fun i xi =>
    y.sum fun j yj =>
      monomial A (i + j) (Nat.choose (i + j) i • A.evenMul xi yj)

/-- Multiplication on individual divided monomials is
`(x T ^ (i)) * (y T ^ (j)) = choose (i + j) i * (xy) T ^ (i + j)`. -/
theorem monomial_mul (i j : ℕ) (x y : A.evenPart) :
    mul A (monomial A i x) (monomial A j y) =
      monomial A (i + j) (Nat.choose (i + j) i • A.evenMul x y) := by
  classical
  simp [mul, monomial, Finsupp.sum_single_index]

/-- Ordered multiplication of a finite list of divided-monomial coefficient families. -/
def listMul : List (Coeffs A) → Coeffs A
  | [] => one A
  | x :: xs => mul A x (listMul xs)

/-- The monomial product indexed by an exponent distribution `e`.

Each block of `e i` copies of the divided monomial `T ^ (i)` contributes
`Nat.uniformBell (e i) i` when taking its divided power.  The subsequent
`listMul` retains the binomial factors between distinct exponents. -/
def distributionTerm (x : ℕ+ →₀ A.evenPart) (e : ℕ+ →₀ ℕ) : Coeffs A :=
  listMul (A := A) <| (e.support.sort (· ≤ ·)).map fun i : ℕ+ =>
    Nat.uniformBell (e i) (i : ℕ) •
      monomial A ((i : ℕ) * e i) (A.evenPow (x i) (e i))

/-- The divided power of a coefficient family supported on positive divided monomials. -/
def tailGamma (n : ℕ) (x : ℕ+ →₀ A.evenPart) : Coeffs A :=
  (Finset.finsuppAntidiag x.support n).sum fun e => distributionTerm A x e

/-- The full even-variable divided-power coefficient formula: split off the constant coefficient,
then convolve its given divided powers with the positive-tail formula. -/
@[stacks 09PI]
def gamma (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (n : ℕ) (x : PositiveCoeffs A) : Coeffs A :=
  (Finset.antidiagonal n).sum fun ab =>
    mul A (monomial A 0 (gammaA ab.1 x.constant)) (tailGamma A ab.2 x.tail)

/-- The positive-tail divided power is the sum over exponent distributions of total weight `n`. -/
theorem tailGamma_apply (n : ℕ) (x : ℕ+ →₀ A.evenPart) :
    tailGamma A n x =
      (Finset.finsuppAntidiag x.support n).sum fun e => distributionTerm A x e := by
  rfl

/-- The full coefficient formula is the antidiagonal convolution of the constant and tail
divided powers. -/
theorem gamma_apply (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (n : ℕ) (x : PositiveCoeffs A) :
    gamma A gammaA n x =
      (Finset.antidiagonal n).sum fun ab =>
        mul A (monomial A 0 (gammaA ab.1 x.constant)) (tailGamma A ab.2 x.tail) := by
  rfl

/-- The even-variable coefficient formula extends the given divided powers on `A`. -/
theorem gamma_ofPositive (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (n : ℕ) (x : A.evenPositivePart) :
    gamma A gammaA n (ofPositive A x) = monomial A 0 (gammaA n x) := sorry

/-- The even-variable coefficient formula sends `T ^ (i)` to
`Nat.uniformBell n i • T ^ (n * i)`. -/
theorem gamma_tPower (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (n : ℕ) (i : ℕ+) :
    gamma A gammaA n (tPower A i) =
      Nat.uniformBell n (i : ℕ) • monomial A (n * (i : ℕ)) A.oneEven := sorry

/-- The first divided monomial has the standard normalization `gamma_n(T) = T ^ (n)`. -/
theorem gamma_tPower_one (gammaA : NonnegGradedAlgebra.DividedPowers A) (n : ℕ) :
    gamma A gammaA n (tPower A 1) = monomial A n A.oneEven := by
  simpa [Nat.uniformBell_one_right] using gamma_tPower A gammaA n 1

/-- A family has the even-variable coefficient specification when it agrees pointwise with the
explicit formula `gamma`. -/
def IsGamma (gammaA : NonnegGradedAlgebra.DividedPowers A)
    (delta : ℕ → PositiveCoeffs A → Coeffs A) : Prop :=
  ∀ n x, delta n x = gamma A gammaA n x

/-- The explicit even-variable coefficient family satisfies its specification. -/
theorem gamma_isGamma (gammaA : NonnegGradedAlgebra.DividedPowers A) :
    IsGamma A gammaA (gamma A gammaA) := by
  intro n x
  rfl

/-- A family with the even-variable coefficient specification is the explicit family. -/
theorem IsGamma.eq_gamma {gammaA : NonnegGradedAlgebra.DividedPowers A}
    {delta : ℕ → PositiveCoeffs A → Coeffs A}
    (hdelta : IsGamma A gammaA delta) :
    delta = gamma A gammaA := by
  exact funext fun n ↦ funext fun x ↦ hdelta n x

/-- The explicit formula determines a unique even-variable coefficient family. -/
@[stacks 09PI]
theorem existsUnique_gamma (gammaA : NonnegGradedAlgebra.DividedPowers A) :
    ∃! delta : ℕ → PositiveCoeffs A → Coeffs A,
      IsGamma A gammaA delta := by
  refine ⟨gamma A gammaA, gamma_isGamma A gammaA, ?_⟩
  intro delta hdelta
  exact hdelta.eq_gamma

end Even

end Adjoin

end NonnegGradedAlgebra
