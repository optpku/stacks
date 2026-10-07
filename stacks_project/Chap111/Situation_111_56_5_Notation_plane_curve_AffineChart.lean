module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate
public import ReasLib.RingTheory.MvPolynomial.Homogenization

/-!
# Affine chart, function field, and canonical Kähler form of a plane curve

Dehomogenization of a homogeneous plane equation at `X 0`, the affine coordinate
ring `k[x, y] / (f)`, its fraction field, and the rational 1-form
`ω = dx / f_y = - dy / f_x` in `Ω[K⁄k]`.
-/

@[expose] public section

open AlgebraicGeometry
open MvPolynomial

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.PlaneCurve

/-- The dehomogenization `f(x, y) = F(1, x, y)` of a plane form at the chart `X 0 ≠ 0`. -/
def affineEquation {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k) :
    MvPolynomial (Fin 2) k :=
  MvPolynomial.Homogenization.dehomogenize (n := 2) F

/-- `affineEquation F` is finite-variable dehomogenization of `F` at the first variable. -/
theorem affineEquation_eq_dehomogenize {k : Type u} [Field k]
    (F : MvPolynomial (Fin 3) k) :
    affineEquation F = MvPolynomial.Homogenization.dehomogenize (n := 2) F := sorry

/-- `affineEquation F` agrees with chart dehomogenization of `F` at `X 0`. -/
theorem affineEquation_eq_dehomogenizeAt {k : Type u} [Field k]
    (F : MvPolynomial (Fin 3) k) :
    affineEquation F =
      ProjectiveSpace.dehomogenizeAt 2 0 (Equiv.refl (Fin 2)) F := sorry

/-- The affine coordinate ring `k[x, y] / (f)` of the dehomogenized plane equation. -/
abbrev affineCoordinateRing {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k) : Type u :=
  MvPolynomial (Fin 2) k ⧸ Ideal.span {affineEquation F}

/-- Irreducibility of the dehomogenized equation makes the affine coordinate ring a domain. -/
instance instIsDomain_affineCoordinateRing {k : Type u} [Field k]
    (F : MvPolynomial (Fin 3) k) [Fact (Irreducible (affineEquation F))] :
    IsDomain (affineCoordinateRing F) := sorry

/-- If an irreducible homogeneous plane form is not divisible by `X 0`, then its
dehomogenization at `X 0` is irreducible. -/
theorem irreducible_affineEquation_of_irreducible {k : Type u} [Field k] {d : ℕ}
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    (hirr : Irreducible F) (hX0 : ¬ X (0 : Fin 3) ∣ F) :
    Irreducible (affineEquation F) := sorry

/-- The class of the affine coordinate `x` in `k[x, y] / (f)`. -/
def coordX {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k) :
    affineCoordinateRing F :=
  Ideal.Quotient.mk (Ideal.span {affineEquation F}) (X 0)

/-- The class of the affine coordinate `y` in `k[x, y] / (f)`. -/
def coordY {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k) :
    affineCoordinateRing F :=
  Ideal.Quotient.mk (Ideal.span {affineEquation F}) (X 1)

/-- `coordX F` is the residue class of `X 0`. -/
theorem coordX_eq_mk {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k) :
    coordX F = Ideal.Quotient.mk (Ideal.span {affineEquation F}) (X 0) := sorry

/-- `coordY F` is the residue class of `X 1`. -/
theorem coordY_eq_mk {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k) :
    coordY F = Ideal.Quotient.mk (Ideal.span {affineEquation F}) (X 1) := sorry

/-- The function field `K = Frac(k[x, y] / (f))` of the affine plane chart. -/
abbrev fractionField {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k)
    [IsDomain (affineCoordinateRing F)] : Type u :=
  FractionRing (affineCoordinateRing F)

/-- The image of `x` in the fraction field `K`. -/
def xFrac {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k)
    [IsDomain (affineCoordinateRing F)] : fractionField F :=
  algebraMap (affineCoordinateRing F) (fractionField F) (coordX F)

/-- The image of `y` in the fraction field `K`. -/
def yFrac {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k)
    [IsDomain (affineCoordinateRing F)] : fractionField F :=
  algebraMap (affineCoordinateRing F) (fractionField F) (coordY F)

/-- `xFrac F` is the image of `coordX F` in `K`. -/
theorem xFrac_eq_algebraMap {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k)
    [IsDomain (affineCoordinateRing F)] :
    xFrac F = algebraMap (affineCoordinateRing F) (fractionField F) (coordX F) := sorry

/-- `yFrac F` is the image of `coordY F` in `K`. -/
theorem yFrac_eq_algebraMap {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k)
    [IsDomain (affineCoordinateRing F)] :
    yFrac F = algebraMap (affineCoordinateRing F) (fractionField F) (coordY F) := sorry

/-- The affine partial derivative `f_x = ∂f / ∂x`. -/
def pderivX {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k) :
    MvPolynomial (Fin 2) k :=
  MvPolynomial.pderiv (0 : Fin 2) (affineEquation F)

/-- The affine partial derivative `f_y = ∂f / ∂y`. -/
def pderivY {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k) :
    MvPolynomial (Fin 2) k :=
  MvPolynomial.pderiv (1 : Fin 2) (affineEquation F)

/-- `pderivX F` is the partial derivative of `affineEquation F` in the `x`-variable. -/
theorem pderivX_eq {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k) :
    pderivX F = MvPolynomial.pderiv (0 : Fin 2) (affineEquation F) := sorry

/-- `pderivY F` is the partial derivative of `affineEquation F` in the `y`-variable. -/
theorem pderivY_eq {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k) :
    pderivY F = MvPolynomial.pderiv (1 : Fin 2) (affineEquation F) := sorry

/-- The image of `f_x` in the fraction field `K`. -/
def pderivXFrac {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k)
    [IsDomain (affineCoordinateRing F)] : fractionField F :=
  algebraMap (affineCoordinateRing F) (fractionField F)
    (Ideal.Quotient.mk (Ideal.span {affineEquation F}) (pderivX F))

/-- The image of `f_y` in the fraction field `K`. -/
def pderivYFrac {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k)
    [IsDomain (affineCoordinateRing F)] : fractionField F :=
  algebraMap (affineCoordinateRing F) (fractionField F)
    (Ideal.Quotient.mk (Ideal.span {affineEquation F}) (pderivY F))

/-- The canonical rational 1-form `ω = dx / f_y`, or `- dy / f_x` if `f_y = 0`. -/
def canonicalForm {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k)
    [IsDomain (affineCoordinateRing F)] : Ω[fractionField F ⁄ k] :=
  open Classical in
    if pderivYFrac F = 0 then
      -(pderivXFrac F)⁻¹ • KaehlerDifferential.D k (fractionField F) (yFrac F)
    else
      (pderivYFrac F)⁻¹ • KaehlerDifferential.D k (fractionField F) (xFrac F)

/-- On the locus `f_y ≠ 0`, the canonical form is `dx / f_y`. -/
theorem canonicalForm_eq_smul_dX {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k)
    [IsDomain (affineCoordinateRing F)] (hfy : pderivYFrac F ≠ 0) :
    canonicalForm F =
      (pderivYFrac F)⁻¹ • KaehlerDifferential.D k (fractionField F) (xFrac F) := sorry

/-- On the locus `f_x ≠ 0`, the canonical form is `- dy / f_x`. -/
theorem canonicalForm_eq_neg_smul_dY {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k)
    [IsDomain (affineCoordinateRing F)] (hfx : pderivXFrac F ≠ 0) :
    canonicalForm F =
      -(pderivXFrac F)⁻¹ • KaehlerDifferential.D k (fractionField F) (yFrac F) := sorry

/-- The dehomogenized equation implies `f_x dx + f_y dy = 0` in `Ω[K⁄k]`. -/
theorem d_affineEquation_eq_zero {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k)
    [IsDomain (affineCoordinateRing F)] :
    pderivXFrac F • KaehlerDifferential.D k (fractionField F) (xFrac F) +
      pderivYFrac F • KaehlerDifferential.D k (fractionField F) (yFrac F) = 0 := sorry

/-- Over a perfect field, an irreducible dehomogenized plane equation has nonzero
canonical Kähler form. -/
theorem canonicalForm_ne_zero {k : Type u} [Field k] [PerfectField k]
    (F : MvPolynomial (Fin 3) k)
    [IsDomain (affineCoordinateRing F)] [Fact (Irreducible (affineEquation F))] :
    canonicalForm F ≠ 0 := sorry

end AlgebraicGeometry.ProjectiveSpace.PlaneCurve
