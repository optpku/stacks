module

public import ReasLib.AlgebraicGeometry.AffineSpace.RegularFunctions
public import Mathlib.Data.Complex.Basic

/-!
# The affine curve `t ^ 2 = s ^ 5 + 8` in `Fin 2 → ℂ`

Classical `ℂ`-points of the plane curve `X` given by `t ^ 2 = s ^ 5 + 8`, the
point `x = (1, 3)`, the punctured open `U = X \ {x}`, and the extra regular
function on `U` which is not the restriction of a polynomial in `s` and `t`.
Here `s` is `X 0` and `t` is `X 1`.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial.AffineTsqS5p8

/-- The equation `t ^ 2 - s ^ 5 - 8` of the affine plane curve, with `X 0`
corresponding to `s` and `X 1` corresponding to `t`. -/
def equation : MvPolynomial (Fin 2) ℂ :=
  X 1 ^ 2 - X 0 ^ 5 - 8

/-- The defining equation is `X 1 ^ 2 - X 0 ^ 5 - 8`. -/
theorem equation_eq : equation = X 1 ^ 2 - X 0 ^ 5 - 8 :=
  sorry

/-- The affine plane curve `X` cut out by `t ^ 2 = s ^ 5 + 8` in `Fin 2 → ℂ`. -/
def curve : Set (Fin 2 → ℂ) :=
  zeroLocus ℂ (Ideal.span {equation})

/-- A point lies on `curve` if and only if the defining equation vanishes. -/
theorem mem_curve_iff (p : Fin 2 → ℂ) : p ∈ curve ↔ eval p equation = 0 :=
  sorry

/-- The point `x = (1, 3)` on the curve, with `s`-coordinate `1` and
`t`-coordinate `3`. -/
def point : Fin 2 → ℂ := fun i ↦ if i = 0 then 1 else 3

/-- The distinguished point has `s`-coordinate `1` and `t`-coordinate `3`. -/
theorem point_eq : point 0 = 1 ∧ point 1 = 3 :=
  sorry

/-- The point `(1, 3)` lies on the curve. -/
theorem point_mem_curve : point ∈ curve :=
  sorry

/-- The Zariski open `U = X \ {x}` obtained by removing the point `(1, 3)`. -/
def punctured : Set (Fin 2 → ℂ) :=
  curve \ {point}

/-- The punctured curve is the complement of the singleton `{point}` in `curve`. -/
theorem punctured_eq : punctured = curve \ {point} :=
  sorry

/-- The numerator `t + 3` of the standard ratio presentation on `s ≠ 1`. -/
def tAddThree : MvPolynomial (Fin 2) ℂ :=
  X 1 + 3

/-- `tAddThree` is the polynomial `X 1 + 3`. -/
theorem tAddThree_eq : tAddThree = X 1 + 3 :=
  sorry

/-- The denominator `s - 1` of the standard ratio presentation on `s ≠ 1`. -/
def sSubOne : MvPolynomial (Fin 2) ℂ :=
  X 0 - 1

/-- `sSubOne` is the polynomial `X 0 - 1`. -/
theorem sSubOne_eq : sSubOne = X 0 - 1 :=
  sorry

/-- The geometric sum `s ^ 4 + s ^ 3 + s ^ 2 + s + 1` appearing in the
identity `(t - 3)(t + 3) = (s - 1)(s ^ 4 + s ^ 3 + s ^ 2 + s + 1)`. -/
def sGeomSum : MvPolynomial (Fin 2) ℂ :=
  X 0 ^ 4 + X 0 ^ 3 + X 0 ^ 2 + X 0 + 1

/-- `sGeomSum` is the polynomial `X 0 ^ 4 + X 0 ^ 3 + X 0 ^ 2 + X 0 + 1`. -/
theorem sGeomSum_eq : sGeomSum = X 0 ^ 4 + X 0 ^ 3 + X 0 ^ 2 + X 0 + 1 :=
  sorry

/-- The denominator `t - 3` of the residual ratio presentation on `s = 1`. -/
def tSubThree : MvPolynomial (Fin 2) ℂ :=
  X 1 - 3

/-- `tSubThree` is the polynomial `X 1 - 3`. -/
theorem tSubThree_eq : tSubThree = X 1 - 3 :=
  sorry

/-- The extra function on `punctured`, given by `(t + 3) / (s - 1)` away from
`s = 1` and by `(s ^ 4 + s ^ 3 + s ^ 2 + s + 1) / (t - 3)` on the residual
locus `s = 1`. -/
def extraFunction : punctured → ℂ := fun z ↦
  if z.val 0 = 1 then
    eval z.val sGeomSum / eval z.val tSubThree
  else
    eval z.val tAddThree / eval z.val sSubOne

/-- Away from `s = 1`, `extraFunction` is the ratio `(t + 3) / (s - 1)`. -/
theorem extraFunction_eq_of_s_ne_one (z : punctured) (hs : z.val 0 ≠ 1) :
    extraFunction z = eval z.val tAddThree / eval z.val sSubOne :=
  sorry

/-- On the residual locus `s = 1` in `punctured`, `extraFunction` is the ratio
`(s ^ 4 + s ^ 3 + s ^ 2 + s + 1) / (t - 3)`. -/
theorem extraFunction_eq_of_s_eq_one (z : punctured) (hs : z.val 0 = 1) :
    extraFunction z = eval z.val sGeomSum / eval z.val tSubThree :=
  sorry

/-- `extraFunction` is regular on `punctured`. -/
theorem isRegular_extraFunction : IsRegular extraFunction :=
  sorry

/-- `extraFunction` is not given by a polynomial in `s` and `t`. -/
theorem not_isPolynomial_extraFunction : ¬ IsPolynomial extraFunction :=
  sorry

/-- `extraFunction` is not the restriction of a regular function on all of
`Fin 2 → ℂ`. -/
theorem not_restricts_from_isRegular_univ :
    ¬ ∃ (ψ : ∀ (w : (Set.univ : Set (Fin 2 → ℂ))), ℂ),
      IsRegular ψ ∧ ∀ z : punctured,
        extraFunction z = ψ ⟨z.val, Set.mem_univ z.val⟩ :=
  sorry

/-- `extraFunction` is regular on the curve `t ^ 2 = s ^ 5 + 8` with `(1, 3)`
removed, but is not the restriction of a polynomial on the complex affine plane. -/
theorem isRegular_not_isPolynomial_extraFunction :
    IsRegular extraFunction ∧ ¬ IsPolynomial extraFunction :=
  sorry

end MvPolynomial.AffineTsqS5p8
