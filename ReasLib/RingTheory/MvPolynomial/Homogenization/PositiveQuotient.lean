module

public import ReasLib.RingTheory.GradedAlgebra.Quotient
public import ReasLib.RingTheory.MvPolynomial.Homogenization
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

noncomputable section

universe u

namespace MvPolynomial.Homogenization.HomogenizedIdeal.Positive

variable {R : Type u} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.decomposition
attribute [local instance] MvPolynomial.HomogeneousSubmodule.gradedMonoid

/-- The standard positive-degree shift of the homogenized ideal of an affine ideal. -/
@[stacks 052N "positive shifted homogenized ideal"]
noncomputable abbrev ideal {n : ℕ} (I : Ideal (MvPolynomial (Fin n) R)) :
    Ideal (MvPolynomial (Fin (n + 1)) R) :=
  HomogenizedIdeal.atLeast (R := R) I 1

/-- The quotient grading carried by the positive shifted homogenized ideal. -/
@[stacks 052N "positive shifted homogenized quotient grading"]
noncomputable abbrev grading {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) (d : ℕ) :
    Submodule R (MvPolynomial (Fin (n + 1)) R ⧸ ideal (R := R) I) :=
  GradedAlgebra.Quotient.grading
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (ideal (R := R) I) d

/-- The positive shifted homogenized ideal is homogeneous for the standard polynomial grading. -/
@[stacks 052N "positive shifted homogenized ideal homogeneous"]
theorem ideal_isHomogeneous {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) :
    (ideal (R := R) I).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) := by
  exact HomogenizedIdeal.atLeast_isHomogeneous (R := R) I 1

/-- The positive shifted homogenized ideal remains inside the dehomogenization kernel preimage. -/
@[stacks 052N "positive shifted homogenized ideal dehomogenization bound"]
theorem ideal_le_comap {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) :
    ideal (R := R) I ≤
      Ideal.comap (dehomogenize (R := R) (n := n)) I := by
  exact HomogenizedIdeal.atLeast_le_comap_dehomogenize (R := R) I 1

/-- Every element of the positive shifted ideal has zero constant coefficient. -/
@[stacks 052N "positive shifted ideal constant coefficient"]
theorem constantCoeff_eq_zero_of_mem {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    {q : MvPolynomial (Fin (n + 1)) R}
    (hq : q ∈ ideal (R := R) I) :
    MvPolynomial.constantCoeff q = 0 := sorry

/-- A constant class belongs to the positive shifted ideal exactly when its scalar is zero. -/
@[stacks 052N "positive shifted ideal constant membership"]
theorem mem_C_iff {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) (r : R) :
    MvPolynomial.C r ∈ ideal (R := R) I ↔ r = 0 := sorry

/-- The quotient by the positive shifted homogenized ideal has its canonical graded-algebra
structure.  The homogeneity proof is determined by the ideal, so this instance is reusable. -/
@[stacks 052N "positive shifted homogenized quotient graded algebra"]
noncomputable instance gradedAlgebra {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) :
    GradedAlgebra (grading (R := R) I) :=
  GradedAlgebra.Quotient.gradedAlgebra
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (ideal (R := R) I)
    (ideal_isHomogeneous (R := R) I)

end MvPolynomial.Homogenization.HomogenizedIdeal.Positive

end
