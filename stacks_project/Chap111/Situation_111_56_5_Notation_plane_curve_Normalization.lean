module

public import stacks_project.Chap111.Exercise_111_54_3_Hypersurface
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.PlaneCurve.CanonicalDivisor

/-! # Normalized plane curves and canonical divisors

The shared owners supply the normalization, its standard coordinates, and the
divisor of the canonical differential. The plane hypersurface specializations
remain available to existing chapter consumers.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace.PlaneCurve
open scoped AlgebraicGeometry

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
  (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
  [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]

#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.toVanishing d F hF :
  (abstractCurve d F hF).left ⟶ ProjectiveSpace.Hypersurface.scheme 2 d F hF)

#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.canonicalDivisor_spec d F hF :
  IsZerosPolesDivisor d F hF (canonicalDivisor d F hF))
