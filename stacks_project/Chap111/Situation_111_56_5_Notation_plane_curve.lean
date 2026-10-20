module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.PlaneCurve.CanonicalDivisor
import StacksCheckRecall

/-!
The affine function field uses the nonempty standard chart implicit in the
assertion that the affine quotient is a domain. Homogeneous irreducibility alone
allows the line `F = X 0`, whose dehomogenization is `1`. The condition
`¬ X 0 ∣ F` supplies affine irreducibility through the checked theorem below;
the corresponding domain instance then supplies the fraction field. No lower
bound on the degree is imposed.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace.PlaneCurve
open scoped AlgebraicGeometry

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
  (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
  [Fact (Irreducible F)] (hX0 : ¬ MvPolynomial.X (0 : Fin 3) ∣ F)

#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.irreducible_affineEquation_of_irreducible
  F hF Fact.out hX0 : Irreducible (affineEquation F))

#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.instCurve_planeCurveOver d F hF :
  Curve (planeCurveOver d F hF))

variable [Fact (Irreducible (affineEquation F))]

#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.instIsDomain_affineCoordinateRing F :
  IsDomain (affineCoordinateRing F))

/- Situation 111.56.5 (Notation plane curve) (1) The projective curve is the
canonical homogeneous hypersurface `D = V(F)` in projective two-space. -/
@[stacks 09U0] #check (AlgebraicGeometry.ProjectiveSpace.Hypersurface.scheme 2 d F hF : Scheme)

/- Situation 111.56.5 (Notation plane curve) (2) On the standard chart, with
`x = X 1 / X 0` and `y = X 2 / X 0`, the equation is `f(x, y) = F(1, x, y)`. -/
@[stacks 09U0] #check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.affineEquation F :
  MvPolynomial (Fin 2) k)

/- Situation 111.56.5 (Notation plane curve) (3) The affine function field is
`K = Frac(k[x, y] / (f))`. -/
@[stacks 09U0] #check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.fractionField F : Type u)

/- Situation 111.56.5 (Notation plane curve) (4) The abstract curve is the
normalization of the actual projective hypersurface over `k`. -/
@[stacks 09U0] #check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.abstractCurve d F hF : SchemeOverField k)

#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.standardChartIdent d F hF :
  fractionField F ≃ₐ[k] SchemeOverField.functionFieldCommAlg (abstractCurve d F hF))

#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.standardChartIdent_spec d F hF :
  IsStandardChartIdent d F hF (standardChartIdent d F hF))

/- Situation 111.56.5 (Notation plane curve) (5) The canonical normalization
morphism to `D` is surjective. -/
@[stacks 09U0] #check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.instSurjective_toVanishing d F hF :
  Surjective (toVanishing d F hF))

/- Situation 111.56.5 (Notation plane curve) (6) The canonical map is bijective
on the inverse image of the nonsingular locus of `D`. -/
@[stacks 09U0] #check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.bijOn_regularLocus_toVanishing d F hF :
  Set.BijOn (toVanishing d F hF).base
    ((toVanishing d F hF).base ⁻¹' (ProjectiveSpace.Hypersurface.scheme 2 d F hF).regularLocus)
    (ProjectiveSpace.Hypersurface.scheme 2 d F hF).regularLocus)

/- Situation 111.56.5 (Notation plane curve) (7) If `D` is nonsingular, the
canonical normalization morphism is an isomorphism. -/
@[stacks 09U0] #check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.instIsIso_toVanishing_of_regular d F hF :
  ∀ [Scheme.Regular (ProjectiveSpace.Hypersurface.scheme 2 d F hF)],
    CategoryTheory.IsIso (toVanishing d F hF))

/- Situation 111.56.5 (Notation plane curve) (8) The affine partial derivatives
are `f_x = ∂f/∂x` and `f_y = ∂f/∂y`. -/
@[stacks 09U0] #check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.pderivX F : MvPolynomial (Fin 2) k)

#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.pderivY F : MvPolynomial (Fin 2) k)

/- Situation 111.56.5 (Notation plane curve) (9) The rational differential
is `ω = dx/f_y = -dy/f_x`, with each formula used when its denominator is nonzero. -/
@[stacks 09U0] #check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.canonicalForm F : Ω[fractionField F ⁄ k])

#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.canonicalForm_eq_smul_dX F :
  pderivYFrac F ≠ 0 → canonicalForm F =
    (pderivYFrac F)⁻¹ • KaehlerDifferential.D k (fractionField F) (xFrac F))

#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.canonicalForm_eq_neg_smul_dY F :
  pderivXFrac F ≠ 0 → canonicalForm F =
    -(pderivXFrac F)⁻¹ • KaehlerDifferential.D k (fractionField F) (yFrac F))

#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.canonicalDivisor d F hF :
  WeilDivisor (abstractCurve d F hF).left)

/- Situation 111.56.5 (Notation plane curve) (10) The canonical divisor is the
divisor of zeros and poles of the specified canonical rational differential. -/
@[stacks 09U0] #check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.canonicalDivisor_spec d F hF :
  IsZerosPolesDivisor d F hF (canonicalDivisor d F hF))
