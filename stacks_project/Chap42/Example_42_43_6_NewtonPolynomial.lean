/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial.Newton

/- The chapter compatibility module exposes the canonical Newton polynomial owner. -/
#check (AlgebraicGeometry.ChernPolynomial.Newton.polynomial :
  ℕ+ → MvPolynomial ℕ ℤ)
