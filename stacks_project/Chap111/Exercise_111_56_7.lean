module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import stacks_project.Chap111.Exercise_111_56_7_LinearSystem
public import stacks_project.Chap111.Situation_111_56_5_Notation_plane_curve_AffineChart
public import stacks_project.Chap111.Situation_111_56_5_Notation_plane_curve_Normalization

/-!
# Exercise 111.56.7

On a nonsingular plane quintic, the residual canonical system of five distinct
affine points is cut out by total-degree-`≤ 2` polynomials through those points,
and the possible values of `l(∑ P_i)` are exactly `1`, `2`, and `3`.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace.PlaneCurve
open MvPolynomial
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.PlaneCurve

/-- The image of a bivariate polynomial in the affine function field `K`. -/
def polynomialFrac {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k)
    [IsDomain (affineCoordinateRing F)] (h : MvPolynomial (Fin 2) k) :
    fractionField F :=
  algebraMap (affineCoordinateRing F) (fractionField F)
    (Ideal.Quotient.mk (Ideal.span {affineEquation F}) h)

/-- `polynomialFrac F h` is the class of `h` in `K = Frac(k[x, y] / (f))`. -/
theorem polynomialFrac_eq {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k)
    [IsDomain (affineCoordinateRing F)] (h : MvPolynomial (Fin 2) k) :
    polynomialFrac F h =
      algebraMap (affineCoordinateRing F) (fractionField F)
        (Ideal.Quotient.mk (Ideal.span {affineEquation F}) h) := sorry

/-- The section of a bivariate polynomial on the standard affine chart of `C`. -/
def affinePolynomialSection {k : Type u} [Field k]
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 5)
    [Curve (planeCurveOver 5 F hF)] (h : MvPolynomial (Fin 2) k) :
    Γ((abstractCurve 5 F hF).left, standardChartOpen 5 F hF) :=
  MvPolynomial.eval₂
    (Scheme.Hom.sectionsMap (abstractCurve 5 F hF).hom (standardChartOpen 5 F hF))
    (standardChartSection 5 F hF) h

/-- `affinePolynomialSection` is evaluation of `h` on the pulled-back chart coordinates. -/
theorem affinePolynomialSection_eq {k : Type u} [Field k]
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 5)
    [Curve (planeCurveOver 5 F hF)] (h : MvPolynomial (Fin 2) k) :
    affinePolynomialSection F hF h =
      MvPolynomial.eval₂
        (Scheme.Hom.sectionsMap (abstractCurve 5 F hF).hom (standardChartOpen 5 F hF))
        (standardChartSection 5 F hF) h := sorry

/-- A polynomial vanishes at an affine chart point when the residue of its section is zero. -/
def VanishesAt {k : Type u} [Field k]
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 5)
    [Curve (planeCurveOver 5 F hF)] {x : (abstractCurve 5 F hF).left}
    (hx : x ∈ standardChartOpen 5 F hF) (h : MvPolynomial (Fin 2) k) : Prop :=
  (abstractCurve 5 F hF).left.residue x
      ((abstractCurve 5 F hF).left.presheaf.germ (standardChartOpen 5 F hF) x hx
        (affinePolynomialSection F hF h)) = 0

/-- Unfold `VanishesAt` as vanishing of the residue of the affine polynomial section. -/
theorem vanishesAt_iff {k : Type u} [Field k]
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 5)
    [Curve (planeCurveOver 5 F hF)] {x : (abstractCurve 5 F hF).left}
    (hx : x ∈ standardChartOpen 5 F hF) (h : MvPolynomial (Fin 2) k) :
    VanishesAt F hF hx h ↔
      (abstractCurve 5 F hF).left.residue x
          ((abstractCurve 5 F hF).left.presheaf.germ (standardChartOpen 5 F hF) x hx
            (affinePolynomialSection F hF h)) = 0 := sorry

/-- Residual canonical forms `h • ω` of total degree at most `2` through five affine points. -/
def residualCanonicalSpace {k : Type u} [Field k]
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 5)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver 5 F hF)]
    (P : Fin 5 → (abstractCurve 5 F hF).left)
    (h_affine : ∀ i, P i ∈ standardChartOpen 5 F hF) :
    Set (Ω[fractionField F⁄k]) :=
  {ω | ∃ h : MvPolynomial (Fin 2) k,
    h.totalDegree ≤ 2 ∧ (∀ i, VanishesAt F hF (h_affine i) h) ∧
      ω = polynomialFrac F h • canonicalForm F}

/-- Membership in the residual canonical space is a degree-`≤ 2` vanishing polynomial
multiple of `canonicalForm F`. -/
theorem mem_residualCanonicalSpace {k : Type u} [Field k]
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 5)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver 5 F hF)]
    (P : Fin 5 → (abstractCurve 5 F hF).left)
    (h_affine : ∀ i, P i ∈ standardChartOpen 5 F hF)
    (ω : Ω[fractionField F⁄k]) :
    ω ∈ residualCanonicalSpace F hF P h_affine ↔
      ∃ h : MvPolynomial (Fin 2) k,
        h.totalDegree ≤ 2 ∧ (∀ i, VanishesAt F hF (h_affine i) h) ∧
          ω = polynomialFrac F h • canonicalForm F := sorry

/-- The Weil divisor `P_1 + P_2 + P_3 + P_4 + P_5` of five closed points on `C`. -/
def fivePointDivisor {k : Type u} [Field k]
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 5)
    [Curve (planeCurveOver 5 F hF)]
    (P : Fin 5 → (abstractCurve 5 F hF).left)
    (h_closed : ∀ i, P i ∈ closedPoints (abstractCurve 5 F hF).left) :
    Div((abstractCurve 5 F hF).left) :=
  Finset.univ.sum fun i ↦ Scheme.closedPointDivisor (abstractCurve 5 F hF) (P i) (h_closed i)

/-- `fivePointDivisor` is the sum of the five closed-point Weil divisors. -/
theorem fivePointDivisor_eq {k : Type u} [Field k]
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 5)
    [Curve (planeCurveOver 5 F hF)]
    (P : Fin 5 → (abstractCurve 5 F hF).left)
    (h_closed : ∀ i, P i ∈ closedPoints (abstractCurve 5 F hF).left) :
    fivePointDivisor F hF P h_closed =
      Finset.univ.sum fun i ↦
        Scheme.closedPointDivisor (abstractCurve 5 F hF) (P i) (h_closed i) := sorry

/-- Exercise 111.56.7 (1): on a nonsingular plane quintic `C = D`, the space
`L(K_C - ∑ P_i)` consists of the functions `e (polynomialFrac h)` for polynomials
`h ∈ k[x, y]` of total degree at most `2` vanishing at each of five pairwise distinct
points of the affine chart `X 0 ≠ 0`. Equivalently, the corresponding multiples of the
canonical form are the residual forms `h • ω`. -/
@[stacks 09U2]
theorem residualCanonicalSpace_eq {k : Type u} [Field k] [IsAlgClosed k]
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 5)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    [Curve (planeCurveOver 5 F hF)] [Scheme.Regular (scheme 5 F hF)]
    [IsLocallyNoetherian (abstractCurve 5 F hF).left]
    [Scheme.Modules.Invertible (Ω[(abstractCurve 5 F hF).hom.toShHom])]
    (P : Fin 5 → (abstractCurve 5 F hF).left)
    (h_closed : ∀ i, P i ∈ closedPoints (abstractCurve 5 F hF).left)
    (h_affine : ∀ i, P i ∈ standardChartOpen 5 F hF)
    (h_inj : Function.Injective P)
    (e : fractionFieldAbstractCurveIdent 5 F hF)
    (he : IsStandardChartIdent 5 F hF e) :
    Scheme.riemannRochSpace (abstractCurve 5 F hF)
        (canonicalDivisor 5 F hF - fivePointDivisor F hF P h_closed) =
      (fun h ↦ identApply 5 F hF e (polynomialFrac F h)) ''
        {h : MvPolynomial (Fin 2) k |
          h.totalDegree ≤ 2 ∧ ∀ i, VanishesAt F hF (h_affine i) h} := sorry

/-- The lecture identification of `L(K_C)` with polynomial multiples of `ω` of
total degree at most `2`. -/
theorem canonicalLinearSystem_eq {k : Type u} [Field k] [IsAlgClosed k]
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 5)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    [Curve (planeCurveOver 5 F hF)] [Scheme.Regular (scheme 5 F hF)]
    [IsLocallyNoetherian (abstractCurve 5 F hF).left]
    [Scheme.Modules.Invertible (Ω[(abstractCurve 5 F hF).hom.toShHom])]
    (e : fractionFieldAbstractCurveIdent 5 F hF)
    (he : IsStandardChartIdent 5 F hF e) :
    Scheme.riemannRochSpace (abstractCurve 5 F hF) (canonicalDivisor 5 F hF) =
      (fun h ↦ identApply 5 F hF e (polynomialFrac F h)) ''
        {h : MvPolynomial (Fin 2) k | h.totalDegree ≤ 2} := sorry

/-- Exercise 111.56.7 (2): on a nonsingular plane quintic, as `P` ranges over
five pairwise distinct closed points of the affine chart `X 0 ≠ 0`, the set of
values of `l(∑ P_i)` equals `{1, 2, 3}`. -/
@[stacks 09U2]
theorem riemannRochDim_sum_mem {k : Type u} [Field k] [IsAlgClosed k]
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 5)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    [Curve (planeCurveOver 5 F hF)] [Scheme.Regular (scheme 5 F hF)]
    [IsLocallyNoetherian (abstractCurve 5 F hF).left] :
    {n | ∃ (P : Fin 5 → (abstractCurve 5 F hF).left)
        (h_closed : ∀ i, P i ∈ closedPoints (abstractCurve 5 F hF).left),
      (∀ i, P i ∈ standardChartOpen 5 F hF) ∧ Function.Injective P ∧
        Scheme.riemannRochDim (abstractCurve 5 F hF)
            (fivePointDivisor F hF P h_closed) = n} =
      ({1, 2, 3} : Set ℕ) := sorry

/-- The dimension `l(∑ P_i)` equals the rank of degree-`≤ 2` polynomials through the
five affine points. -/
theorem riemannRochDim_sum_eq_vanishingPolynomials {k : Type u} [Field k] [IsAlgClosed k]
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 5)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    [Curve (planeCurveOver 5 F hF)] [Scheme.Regular (scheme 5 F hF)]
    [IsLocallyNoetherian (abstractCurve 5 F hF).left]
    (P : Fin 5 → (abstractCurve 5 F hF).left)
    (h_closed : ∀ i, P i ∈ closedPoints (abstractCurve 5 F hF).left)
    (h_affine : ∀ i, P i ∈ standardChartOpen 5 F hF)
    (h_inj : Function.Injective P) :
    Scheme.riemannRochDim (abstractCurve 5 F hF) (fivePointDivisor F hF P h_closed) =
      Module.finrank k
        (Submodule.span k
          {h : MvPolynomial (Fin 2) k |
            h.totalDegree ≤ 2 ∧ ∀ i, VanishesAt F hF (h_affine i) h}) := sorry

end AlgebraicGeometry.ProjectiveSpace.PlaneCurve
