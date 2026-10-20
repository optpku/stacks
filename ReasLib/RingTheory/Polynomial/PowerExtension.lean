module

public import ReasLib.RingTheory.Norm.Projective
public import ReasLib.RingTheory.Flatness.LocallyFree.Finite
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Polynomial power extensions

The quotient by the relation `Y^n - X` identifies explicitly with a polynomial ring,
with base generator mapping to the nth power of the polynomial variable.
-/

@[expose] public section

noncomputable section

universe u

open Polynomial

/-- The relation `Y^n - X` in the iterated polynomial ring `R[X][Y]`. -/
def PolynomialPower.powerRel (R : Type u) [CommRing R] (n : ℕ) :
    Polynomial (Polynomial R) :=
  X ^ n - C (X : Polynomial R)

/-- The quotient presentation of the polynomial power extension with relation `Y^n = X`. -/
abbrev PolynomialPower (R : Type u) [CommRing R] (n : ℕ) : Type u :=
  AdjoinRoot (PolynomialPower.powerRel R n)

namespace PolynomialPower

/-- The defining relation of the polynomial power extension is `Y^n - X`. -/
theorem powerRel_def (R : Type u) [CommRing R] (n : ℕ) :
    powerRel R n = X ^ n - C (X : Polynomial R) := rfl

/-- Evaluation at the adjoined root as a homomorphism of algebras over the coefficient ring. -/
def ofPolynomial {R : Type u} [CommRing R] (n : ℕ) :
    Polynomial R →ₐ[R] PolynomialPower R n :=
  aeval (AdjoinRoot.root (powerRel R n))

/-- Evaluation into the power extension is polynomial evaluation at its adjoined root. -/
theorem ofPolynomial_apply {R : Type u} [CommRing R] (n : ℕ) (p : Polynomial R) :
    ofPolynomial n p = aeval (AdjoinRoot.root (powerRel R n)) p := rfl

/-- The base generator maps to the nth power of the adjoined root. -/
theorem algebraMap_X {R : Type u} [CommRing R] (n : ℕ) :
    algebraMap (Polynomial R) (PolynomialPower R n) X =
      AdjoinRoot.root (powerRel R n) ^ n := sorry

/-- Evaluation from the power extension to a polynomial ring sends the root to `X`
and the base generator to `X^n`. -/
def toPolynomial {R : Type u} [CommRing R] (n : ℕ) :
    PolynomialPower R n →ₐ[R] Polynomial R :=
  AdjoinRoot.liftAlgHom (powerRel R n) (aeval (X ^ n : Polynomial R)) X
    (by simp [powerRel])

/-- Evaluation from the power extension sends its adjoined root to the polynomial variable. -/
theorem toPolynomial_root {R : Type u} [CommRing R] (n : ℕ) :
    toPolynomial n (AdjoinRoot.root (powerRel R n)) = (X : Polynomial R) := by
  simp [toPolynomial]

/-- Evaluation from the power extension restricts on the base ring to evaluation at `X^n`. -/
theorem toPolynomial_algebraMap {R : Type u} [CommRing R] (n : ℕ) (p : Polynomial R) :
    toPolynomial n (algebraMap (Polynomial R) (PolynomialPower R n) p) =
      aeval (X ^ n : Polynomial R) p := by
  change toPolynomial n (AdjoinRoot.of (powerRel R n) p) = _
  simp [toPolynomial]

/-- Evaluation into the power extension followed by evaluation back fixes every polynomial. -/
theorem toPolynomial_ofPolynomial {R : Type u} [CommRing R] (n : ℕ) (p : Polynomial R) :
    toPolynomial n (ofPolynomial n p) = p := sorry

/-- Evaluation out of the power extension followed by evaluation back fixes every element. -/
theorem ofPolynomial_toPolynomial {R : Type u} [CommRing R] (n : ℕ)
    (element : PolynomialPower R n) :
    ofPolynomial n (toPolynomial n element) = element := sorry

/-- The explicit algebra equivalence between the power extension and a polynomial ring. -/
def polynomialEquiv {R : Type u} [CommRing R] (n : ℕ) :
    PolynomialPower R n ≃ₐ[R] Polynomial R where
  __ := toPolynomial n
  invFun := ofPolynomial n
  left_inv := ofPolynomial_toPolynomial n
  right_inv := toPolynomial_ofPolynomial n

/-- For nonzero exponents, the polynomial power extension is finite locally free over its base. -/
instance instFiniteLocallyFree {R : Type u} [CommRing R] (n : ℕ) [NeZero n] :
    Module.FiniteLocallyFree (Polynomial R) (PolynomialPower R n) := sorry

/-- The powers of the adjoined root form a basis of the nonzero polynomial power extension. -/
def powerBasis {R : Type u} [CommRing R] (n : ℕ) [NeZero n] :
    PowerBasis (Polynomial R) (PolynomialPower R n) :=
  AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C (X : Polynomial R) (NeZero.ne n))

/-- The nonzero polynomial power extension is finite over its polynomial base ring. -/
instance (priority := 1100) instFinite {R : Type u} [CommRing R] (n : ℕ) [NeZero n] :
    Module.Finite (Polynomial R) (PolynomialPower R n) :=
  Module.Finite.of_basis (powerBasis n).basis

/-- The nonzero polynomial power extension is projective over its polynomial base ring. -/
instance (priority := 1100) instProjective {R : Type u} [CommRing R] (n : ℕ) [NeZero n] :
    Module.Projective (Polynomial R) (PolynomialPower R n) :=
  Module.Projective.of_basis (powerBasis n).basis

/-- Over the rationals, the norm of `Y - Y^3` for the power extension is
`-X * (1 - X)^2` for even exponents and `X * (1 - X^2)` for odd exponents. -/
theorem finiteProjectiveNorm_X_sub_X_pow_three {n : ℕ} [NeZero n] :
    Algebra.finiteProjectiveNorm (Polynomial ℚ)
        (ofPolynomial n (X - X ^ 3 : Polynomial ℚ)) =
      if Even n then -X * (1 - X) ^ 2 else X * (1 - X ^ 2) := sorry

end PolynomialPower
