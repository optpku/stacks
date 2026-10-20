module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.PlaneCurve.AffineChart

/-! # Affine plane-curve coordinates and differentials

The affine equation and its rational differential are supplied by the shared
plane-curve owner.
-/

@[expose] public section

universe u

variable {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k)

#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.affineEquation F :
  MvPolynomial (Fin 2) k)

#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.affineEquation_eq_dehomogenize F :
  AlgebraicGeometry.ProjectiveSpace.PlaneCurve.affineEquation F =
    MvPolynomial.Homogenization.dehomogenize (n := 2) F)

