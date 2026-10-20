module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial.Newton

/- The chapter compatibility module exposes the canonical Newton polynomial owner. -/
#check (AlgebraicGeometry.ChernPolynomial.Newton.polynomial :
  ℕ+ → MvPolynomial ℕ ℤ)
