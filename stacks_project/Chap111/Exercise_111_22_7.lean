module

public import ReasLib.LinearAlgebra.Trace.Projective
public import ReasLib.RingTheory.Norm.Projective
public import ReasLib.RingTheory.Norm.Spectrum
public import ReasLib.RingTheory.Polynomial.PowerExtension
import StacksCheckRecall

/-!
# Exercise 111.22.7

Trace and norm of a finite locally free algebra, the vanishing statement
`π(V(b)) = V(Norm(b))`, base change, product algebras, and the power map
`ℚ[X] → ℚ[Y]`, `X ↦ Y^n`.
-/

@[expose] public section

noncomputable section

universe u v w

open Polynomial PrimeSpectrum
open scoped TensorProduct

/- Exercise 111.22.7 (1): trace is the trace of left multiplication. -/
@[stacks 02DV] #check (Algebra.FiniteProjective.trace :
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Projective A B], B →ₗ[A] A)

/- Exercise 111.22.7 (1): norm is the determinant of left multiplication. -/
@[stacks 02DV] #check (Algebra.finiteProjectiveNorm :
  ∀ (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Projective A B], B → A)

/- Exercise 111.22.7 (2): the spectral image of V(b) is V(Norm(b)). -/
@[stacks 02DV] #check (Algebra.comap_zeroLocus_eq_zeroLocus_finiteProjectiveNorm :
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FiniteLocallyFree A B] (b : B),
    comap (algebraMap A B) '' zeroLocus {b} =
      zeroLocus {Algebra.finiteProjectiveNorm A b})

#check (Algebra.mem_comap_zeroLocus_finiteProjectiveNorm_iff :
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FiniteLocallyFree A B] (b : B) (p : PrimeSpectrum A),
    p ∈ comap (algebraMap A B) '' zeroLocus {b} ↔
      Algebra.finiteProjectiveNorm A b ∈ p.asIdeal)

/- Exercise 111.22.7 (3): norm commutes with arbitrary base change. -/
@[stacks 02DV] #check (Algebra.finiteProjectiveNorm_baseChange :
  ∀ (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Projective A B]
    {A' : Type w} [CommRing A'] [Algebra A A'] (b : B),
    algebraMap A A' (Algebra.finiteProjectiveNorm A b) =
      Algebra.finiteProjectiveNorm A' ((1 : A') ⊗ₜ[A] b))

/- Exercise 111.22.7 (4): the norm of a finite product is the product of its coordinates. -/
@[stacks 02DV] #check (Algebra.finiteProjectiveNorm_pi :
  ∀ (A : Type u) [CommRing A] {n : ℕ} (a : Fin n → A),
    Algebra.finiteProjectiveNorm A a = ∏ i, a i)

/- Exercise 111.22.7 (5): compute the norm of Y - Y³ for X ↦ Yⁿ. -/
@[stacks 02DV] #check (PolynomialPower.finiteProjectiveNorm_X_sub_X_pow_three :
  ∀ {n : ℕ} [NeZero n],
    Algebra.finiteProjectiveNorm (Polynomial ℚ)
        (PolynomialPower.ofPolynomial n (X - X ^ 3 : Polynomial ℚ)) =
      if Even n then -X * (1 - X) ^ 2 else X * (1 - X ^ 2))
