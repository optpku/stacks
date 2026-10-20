module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.ResidueGalois
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

namespace AlgebraicGeometry.Scheme.GeometricPoint

/-- The geometric point of the rational spectrum induced by the canonical inclusion into
the complex numbers is not algebraic. -/
theorem complex_not_isAlgebraic :
    ¬ (AlgebraicGeometry.Scheme.GeometricPoint.of ℂ
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))).IsAlgebraic := sorry

end AlgebraicGeometry.Scheme.GeometricPoint
