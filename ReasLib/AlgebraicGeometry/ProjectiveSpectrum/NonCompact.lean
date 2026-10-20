module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import ReasLib.RingTheory.MvPolynomial.StandardGrading

@[expose] public section

/-- The projective spectrum of the standard-graded polynomial ring in countably
many variables over the integers is not quasi-compact. -/
theorem not_isCompactSpace_projectiveSpectrum_mvPolynomial_nat_int :
    ¬ CompactSpace (ProjectiveSpectrum (MvPolynomial.standardGrading ℕ ℤ)) :=
  sorry
