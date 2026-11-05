/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ClosedPoint
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.RiemannRochSpace
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.PlaneCurve.CanonicalDivisor

/-!
# Polynomial linear systems on plane quintics

Polynomial sections on the standard affine chart describe residual canonical
forms and the associated Riemann–Roch spaces of five-point divisors.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace.PlaneCurve
open MvPolynomial
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.PlaneCurve

/-- For a nonsingular plane curve, the abstract curve has DVR stalks at prime
divisors. This supplies the valuation hypothesis of the classical `L(D)` API
without imposing regularity on the general notion of a curve. -/
instance instPrimeDivisorDiscreteValuationRings_abstractCurve_of_regular
    {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] [Scheme.Regular (Hypersurface.scheme 2 d F hF)] :
    Scheme.PrimeDivisorDiscreteValuationRings (abstractCurve d F hF).left where
  isDiscreteValuationRing Z := by
    let e := (CategoryTheory.asIso ((toVanishing d F hF).stalkMap Z.genericPoint)).commRingCatIsoToRingEquiv
    letI := Scheme.isRegularLocalRing_stalk (Hypersurface.scheme 2 d F hF)
      (toVanishing d F hF Z.genericPoint)
    have hreg : IsRegularLocalRing ((abstractCurve d F hF).left.presheaf.stalk Z.genericPoint) :=
      IsRegularLocalRing.of_ringEquiv e
    have hZ : Order.coheight Z.genericPoint = 1 := by
      change Order.coheight ((irreducibleSetEquivPoints (α := (abstractCurve d F hF).left))
        Z.support) = 1
      rw [Order.coheight_orderIso, Z.coheight_eq_one]
    apply IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp
    have hdim := ((IsRegularLocalRing.iff_finrank_cotangentSpace _).mp hreg).trans
      ((ringKrullDim_stalk_eq_coheight Z.genericPoint).trans (congrArg
        (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hZ))
    exact_mod_cast hdim

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
        (Ideal.Quotient.mk (Ideal.span {affineEquation F}) h) := rfl

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
        (standardChartSection 5 F hF) h := rfl

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
            (affinePolynomialSection F hF h)) = 0 := Iff.rfl

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
          ω = polynomialFrac F h • canonicalForm F := Iff.rfl

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
        Scheme.closedPointDivisor (abstractCurve 5 F hF) (P i) (h_closed i) := rfl

/-- The residual canonical space of a nonsingular plane quintic is represented by
quadratic polynomials vanishing at five affine points under the standard chart
identification of function fields. -/
theorem residualCanonicalSpace_eq {k : Type u} [Field k] [IsAlgClosed k]
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 5)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    [Scheme.Regular (Hypersurface.scheme 2 5 F hF)]
    (P : Fin 5 → (abstractCurve 5 F hF).left)
    (h_closed : ∀ i, P i ∈ closedPoints (abstractCurve 5 F hF).left)
    (h_affine : ∀ i, P i ∈ standardChartOpen 5 F hF)
    (h_inj : Function.Injective P) :
    Scheme.riemannRochSpace (abstractCurve 5 F hF)
        (canonicalDivisor 5 F hF - fivePointDivisor F hF P h_closed) =
      (fun h ↦ identApply 5 F hF (standardChartIdent 5 F hF) (polynomialFrac F h)) ''
        {h : MvPolynomial (Fin 2) k |
          h.totalDegree ≤ 2 ∧ ∀ i, VanishesAt F hF (h_affine i) h} := sorry

/-- The canonical Riemann–Roch space of a nonsingular plane quintic is represented
by all bivariate polynomials of total degree at most two. -/
theorem canonicalLinearSystem_eq {k : Type u} [Field k] [IsAlgClosed k]
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 5)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    [Scheme.Regular (Hypersurface.scheme 2 5 F hF)] :
    Scheme.riemannRochSpace (abstractCurve 5 F hF) (canonicalDivisor 5 F hF) =
      (fun h ↦ identApply 5 F hF (standardChartIdent 5 F hF) (polynomialFrac F h)) ''
        {h : MvPolynomial (Fin 2) k | h.totalDegree ≤ 2} := sorry

/-- For a fixed nonsingular plane quintic, the dimensions of five-point
Riemann–Roch spaces attained in the affine chart are exactly `1`, `2`, and `3`. -/
theorem riemannRochDim_sum_mem {k : Type u} [Field k] [IsAlgClosed k]
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 5)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    [Scheme.Regular (Hypersurface.scheme 2 5 F hF)] :
    {n | ∃ (P : Fin 5 → (abstractCurve 5 F hF).left)
        (h_closed : ∀ i, P i ∈ closedPoints (abstractCurve 5 F hF).left),
      (∀ i, P i ∈ standardChartOpen 5 F hF) ∧ Function.Injective P ∧
        Scheme.riemannRochDim (abstractCurve 5 F hF)
            (fivePointDivisor F hF P h_closed) = n} =
      ({1, 2, 3} : Set ℕ) := sorry

/-- The dimension of a five-point Riemann–Roch space equals the rank of the
quadratic polynomials vanishing at those affine points. -/
theorem riemannRochDim_sum_eq_vanishingPolynomials {k : Type u} [Field k] [IsAlgClosed k]
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 5)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    [Scheme.Regular (Hypersurface.scheme 2 5 F hF)]
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
