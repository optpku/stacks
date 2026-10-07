module

public import stacks_project.Chap111.Exercise_111_22_7_Norm
public import ReasLib.RingTheory.Flatness.LocallyFree.Finite
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

/-!
# Exercise 111.22.7

Trace and norm of a finite locally free algebra, the vanishing statement
`π(V(b)) = V(Norm(b))`, base change, product algebras, and the power map
`ℚ[X] → ℚ[Y]`, `X ↦ Y^n`.
-/

@[expose] public section

noncomputable section

universe u v

open Algebra
open Polynomial
open PrimeSpectrum

/- Exercise 111.22.7 (1): Trace_{B/A} and Norm_{B/A} of a finite locally free
A-algebra are `finiteProjectiveTrace` and `finiteProjectiveNorm`. -/
@[stacks 02DV] #check @finiteProjectiveTrace
@[stacks 02DV] #check @finiteProjectiveNorm

namespace Algebra

/-- Exercise 111.22.7 (2): if `π` is `comap (algebraMap A B)` and `V(f)` is
`zeroLocus {f}`, then `π(V(b)) = V(finiteProjectiveNorm A b)`. -/
@[stacks 02DV]
theorem comap_zeroLocus_eq_zeroLocus_finiteProjectiveNorm
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FiniteLocallyFree A B] (b : B) :
    comap (algebraMap A B) '' zeroLocus {b} =
      zeroLocus {finiteProjectiveNorm A b} := sorry

/-- Membership form of `π(V(b)) = V(Norm_{B/A}(b))`. -/
theorem mem_comap_zeroLocus_finiteProjectiveNorm_iff
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FiniteLocallyFree A B] (b : B) (p : PrimeSpectrum A) :
    p ∈ comap (algebraMap A B) '' zeroLocus {b} ↔
      finiteProjectiveNorm A b ∈ p.asIdeal := sorry

end Algebra

/- Exercise 111.22.7 (3): if `i : A → A'` and `B' = A' ⊗[A] B`, then
`i(Norm_{B/A}(b)) = Norm_{B'/A'}(1 ⊗ₜ b)`. -/
@[stacks 02DV] #check @finiteProjectiveNorm_baseChange

/- Exercise 111.22.7 (4): on `B = Fin n → A` with `b = (a_1, …, a_n)`, the
finite-projective norm is `∏ i, a i`. -/
@[stacks 02DV] #check @finiteProjectiveNorm_pi

/-- The relation `Y^n - X` in `R[X][Y]`, so that adjoining a root realises
`R[Y]` as an `R[X]`-algebra via `X ↦ Y^n`. -/
def PolynomialPower.powerRel (R : Type u) [CommRing R] (n : ℕ) :
    Polynomial (Polynomial R) :=
  X ^ n - C (X : Polynomial R)

/-- The `R[X]`-algebra `R[Y]` via `X ↦ Y^n`, as `AdjoinRoot (Y^n - X)`. -/
abbrev PolynomialPower (R : Type u) [CommRing R] (n : ℕ) : Type u :=
  AdjoinRoot (PolynomialPower.powerRel R n)

namespace PolynomialPower

/-- Unfolding of `powerRel`. -/
theorem powerRel_def (R : Type u) [CommRing R] (n : ℕ) :
    powerRel R n = X ^ n - C (X : Polynomial R) := sorry

/-- Evaluation of a polynomial in `Y` at the adjoined root. -/
def ofPolynomial {R : Type u} [CommRing R] (n : ℕ) :
    Polynomial R → PolynomialPower R n :=
  aeval (AdjoinRoot.root (powerRel R n))

/-- `ofPolynomial` evaluates at the adjoined root. -/
theorem ofPolynomial_apply {R : Type u} [CommRing R] (n : ℕ) (p : Polynomial R) :
    ofPolynomial n p = aeval (AdjoinRoot.root (powerRel R n)) p := sorry

/-- The structure map of `PolynomialPower` sends `X` to `Y^n`. -/
theorem algebraMap_X {R : Type u} [CommRing R] (n : ℕ) :
    algebraMap (Polynomial R) (PolynomialPower R n) X =
      AdjoinRoot.root (powerRel R n) ^ n := sorry

/-- For `n ≠ 0`, `R[Y]` is finite locally free over `R[X]` via `X ↦ Y^n`. -/
instance instFiniteLocallyFree {R : Type u} [CommRing R] (n : ℕ) [NeZero n] :
    Module.FiniteLocallyFree (Polynomial R) (PolynomialPower R n) := sorry

/-- Exercise 111.22.7 (5): the finite-projective norm of `Y - Y^3` under
`ℚ[X] → ℚ[Y]`, `X ↦ Y^n`, is `-X * (1 - X)^2` when `n` is even and
`X * (1 - X^2)` when `n` is odd. -/
@[stacks 02DV]
theorem finiteProjectiveNorm_X_sub_X_pow_three {n : ℕ} [NeZero n] :
    finiteProjectiveNorm (Polynomial ℚ) (ofPolynomial n (X - X ^ 3 : Polynomial ℚ)) =
      if Even n then -X * (1 - X) ^ 2 else X * (1 - X ^ 2) := sorry

end PolynomialPower
