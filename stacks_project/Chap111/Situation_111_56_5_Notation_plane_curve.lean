module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap111.Situation_111_56_5_Notation_plane_curve_AffineChart
public import stacks_project.Chap111.Situation_111_56_5_Notation_plane_curve_Normalization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace.PlaneCurve
open scoped AlgebraicGeometry

universe u

/- Situation 111.56.5 (Notation plane curve) (1) The projective plane curve
`D = V(F) ⊂ P^2` is `scheme d F hF`. -/
@[stacks 09U0]
#check scheme

/- Situation 111.56.5 (Notation plane curve) (2) The dehomogenized affine equation
`f(x, y) = F(1, x, y)` is `affineEquation F`, with chart coordinates `x = X 1 / X 0`
and `y = X 2 / X 0`. -/
@[stacks 09U0]
#check affineEquation

/- Situation 111.56.5 (Notation plane curve) (3) The function field
`K = Frac(k[x, y] / (f))` is `fractionField F`. -/
@[stacks 09U0]
#check fractionField

/- Situation 111.56.5 (Notation plane curve) (4) The abstract curve `C` corresponding
to `K` is the normalization `abstractCurve d F hF` of `D`. -/
@[stacks 09U0]
#check abstractCurve

/- Situation 111.56.5 (Notation plane curve) (5) The canonical map `C ⟶ D` is
surjective. -/
@[stacks 09U0]
#check instSurjective_toVanishing

/- Situation 111.56.5 (Notation plane curve) (6) The map `C ⟶ D` is bijective over
the nonsingular locus of `D`. -/
@[stacks 09U0]
#check bijOn_regularLocus_toVanishing

/- Situation 111.56.5 (Notation plane curve) (7) If `D` is nonsingular, then
`C ⟶ D` is an isomorphism. -/
@[stacks 09U0]
#check instIsIso_toVanishing_of_regular

/- Situation 111.56.5 (Notation plane curve) (8) The affine partials are
`f_x = pderivX F` and `f_y = pderivY F`. -/
@[stacks 09U0]
#check pderivX
@[stacks 09U0]
#check pderivY

/- Situation 111.56.5 (Notation plane curve) (9) The canonical Kähler form
`ω = dx / f_y = - dy / f_x` in `Ω[K⁄k]` is `canonicalForm F`. -/
@[stacks 09U0]
#check canonicalForm

/- Situation 111.56.5 (Notation plane curve) (10) The canonical divisor `K_C` is
the unique Weil divisor of zeros and poles of `canonicalForm F` on `C`. -/
@[stacks 09U0]
#check canonicalDivisor
