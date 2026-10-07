module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Algebraic sets in affine space

Algebraic sets are zero loci of polynomial ideals. In finitely many variables,
they can be defined by finitely many polynomial equations.
-/

@[expose]
public section

universe u v

namespace MvPolynomial

variable {σ : Type v} {k : Type u} [Field k]

/-- A subset of affine space is algebraic if it is the zero locus of an ideal of
polynomials. -/
def IsAlgebraicSet (Z : Set (σ → k)) : Prop :=
  ∃ I : Ideal (MvPolynomial σ k), Z = zeroLocus k I

/-- A subset of affine space is algebraic if and only if it is the common vanishing
set of a collection of polynomials. -/
theorem isAlgebraicSet_iff (Z : Set (σ → k)) :
    IsAlgebraicSet Z ↔
      ∃ S : Set (MvPolynomial σ k), Z = {x | ∀ p ∈ S, aeval x p = 0} := sorry

/-- The zero locus of an ideal of polynomials is an algebraic set. -/
theorem isAlgebraicSet_zeroLocus (I : Ideal (MvPolynomial σ k)) :
    IsAlgebraicSet (zeroLocus k I) := sorry

namespace IsAlgebraicSet

/-- An algebraic set in finitely many variables over a field is the zero locus
of the ideal spanned by finitely many polynomials. -/
theorem exists_finset_span [Finite σ] {Z : Set (σ → k)}
    (hZ : IsAlgebraicSet Z) :
    ∃ T : Finset (MvPolynomial σ k),
      Z = zeroLocus k (Ideal.span (T : Set (MvPolynomial σ k))) := sorry

/-- An algebraic set in finitely many variables over a field is the common
vanishing set of finitely many polynomials. -/
theorem exists_finset [Finite σ] {Z : Set (σ → k)}
    (hZ : IsAlgebraicSet Z) :
    ∃ T : Finset (MvPolynomial σ k),
      Z = {x | ∀ p ∈ T, aeval x p = 0} := sorry

end IsAlgebraicSet

end MvPolynomial
