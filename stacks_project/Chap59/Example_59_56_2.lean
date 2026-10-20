module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.Complex
import StacksCheckRecall

/- Example 59.56.2: The geometric point from `Spec ℂ ⟶ Spec ℚ` induced by
the canonical map is not algebraic. -/
@[stacks 03QY] #check
  (AlgebraicGeometry.Scheme.GeometricPoint.complex_not_isAlgebraic :
    ¬ (AlgebraicGeometry.Scheme.GeometricPoint.of ℂ
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))).IsAlgebraic)
