/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.WeilTrace
public import ReasLib.CategoryTheory.Monoidal.Grp.MulBy

/-!
# Multiplication endomorphisms of elliptic curves
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicCycle AlgebraicGeometry.RelativePicard
open AlgebraicGeometry.AbelianVariety AlgebraicGeometry.Curve
open scoped AlgebraicGeometry CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (E : SchemeOverField k) [Curve E] [Smooth E.hom] [Projective E.hom]
  [GrpObj E] [AbelianVariety E]

/-- Pullback by integer multiplication on an elliptic curve is multiplication by the same
integer on its Jacobian. -/
theorem pullbackComponentHom_mulByInt_eq_mulByInt (n : ℤ) :
    pullbackComponentHom E (GrpObj.mulByInt E n) =
      GrpObj.mulByInt (RelativePicard.component E 0) n := sorry

/-- The Jacobian pullback of multiplication by an integer `n` has trace `2 * n`. -/
theorem endomorphismTrace_pullbackComponentHom_mulByInt (n : ℤ) :
    endomorphismTrace (pullbackComponentHom E (GrpObj.mulByInt E n)) = 2 * n := sorry

/-- Multiplication by an integer `n` on an elliptic curve has degree `n.natAbs ^ 2`,
including degree zero when `n = 0`. -/
theorem curveEndomorphismDegree_mulByInt (n : ℤ) :
    curveEndomorphismDegree (GrpObj.mulByInt E n) = n.natAbs ^ 2 := sorry

/-- A non-identity multiplication map on an elliptic curve has fixed-point intersection
number `(n - 1) ^ 2`, counting local intersection multiplicities. -/
theorem fixedPointNumber_mulByInt (n : ℤ)
    (hφ : GrpObj.mulByInt E n ≠ 𝟙 E) :
    fixedPointNumber (GrpObj.mulByInt E n) hφ = (n - 1) ^ 2 := sorry

/-- The fixed-point intersection number of non-identity multiplication by `n` on an
elliptic curve equals `1 - 2 * n + n ^ 2`. -/
theorem weilTraceFormula_mulByInt (n : ℤ)
    (hφ : GrpObj.mulByInt E n ≠ 𝟙 E) :
    fixedPointNumber (GrpObj.mulByInt E n) hφ =
      (1 : ℤ) - 2 * n + n ^ 2 := sorry

end AlgebraicGeometry.Curve
