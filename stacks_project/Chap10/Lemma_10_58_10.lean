module

public import ReasLib.RingTheory.GradedAlgebra.Quotient
public import ReasLib.RingTheory.MvPolynomial.Hilbert
public import ReasLib.RingTheory.Polynomial.Numerical.Degree
import StacksCheckRecall

/-!
# Hilbert functions of nonzero homogeneous quotients

@stack 00K3

The source Hilbert function is represented directly by the finrank of the mapped homogeneous
piece in the quotient, with value zero in negative degrees. The strict degree predicate already
includes the exceptional eventually-zero case.
-/

@[expose] public section

open Filter

noncomputable section

universe u

namespace MvPolynomial.Hilbert

variable {k : Type u} [Field k] {d : ℕ}

-- The standard polynomial grading is the concrete grading used by every declaration below.
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The degree-`n` piece of `k[X₁, ..., X_d] ⧸ I`, obtained by mapping the standard homogeneous
piece through the quotient map. -/
abbrev QuotientDegreePiece
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin d) k)) (n : ℕ) :
    Submodule k (MvPolynomial (Fin d) k ⧸ I.toIdeal) :=
  GradedAlgebra.Quotient.grading
    (MvPolynomial.homogeneousSubmodule (Fin d) k) I.toIdeal n

/-- The Hilbert function of the homogeneous quotient `k[X₁, ..., X_d] ⧸ I`, extended by zero to
negative degrees. -/
def quotientFunction
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin d) k)) : ℤ → ℤ :=
  fun n ↦ if 0 ≤ n then (Module.finrank k (QuotientDegreePiece I n.toNat) : ℤ) else 0

/-- In a nonnegative degree, `quotientFunction` is the finrank of the corresponding quotient
degree piece. -/
theorem quotientFunction_of_nonneg
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin d) k))
    (n : ℤ) (hn : 0 ≤ n) :
    quotientFunction I n = (Module.finrank k (QuotientDegreePiece I n.toNat) : ℤ) := sorry

/-- In a negative degree, `quotientFunction` is zero. -/
@[simp]
theorem quotientFunction_of_neg
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin d) k))
    {n : ℤ} (hn : n < 0) :
    quotientFunction I n = 0 := sorry

/-- Lemma 10.58.10: if `I` is a nonzero homogeneous ideal of
`k[X₁, ..., X_d]`, the Hilbert function of `k[X₁, ..., X_d] ⧸ I` has degree strictly less than
`d - 1`; when `d = 1`, this means that the function is eventually zero. -/
@[stacks 00K3]
theorem quotientFunction_degreeLT
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin d) k))
    (hI : I ≠ ⊥) :
    IsNumericalPolynomial.degreeLT (quotientFunction I) (d - 1) := sorry

@[stacks 00K3 "graded quotient piece"]
#check @MvPolynomial.Hilbert.QuotientDegreePiece
@[stacks 00K3 "canonical quotient function"]
#check @MvPolynomial.Hilbert.quotientFunction
@[stacks 00K3 "nonnegative-degree value"]
#check @MvPolynomial.Hilbert.quotientFunction_of_nonneg
@[stacks 00K3 "negative-degree value"]
#check @MvPolynomial.Hilbert.quotientFunction_of_neg
@[stacks 00K3 "eventual numerical-polynomial comparison"]
#check @MvPolynomial.Hilbert.quotientFunction_degreeLT
@[stacks 00K3 "numerical-polynomial support"]
#check @IsNumericalPolynomial.degreeLT.isNumericalPolynomial
@[stacks 00K3 "zero-polynomial support"]
#check @IsNumericalPolynomial.degreeLT_zero_iff

#print axioms MvPolynomial.Hilbert.QuotientDegreePiece
#print axioms MvPolynomial.Hilbert.quotientFunction

end MvPolynomial.Hilbert
