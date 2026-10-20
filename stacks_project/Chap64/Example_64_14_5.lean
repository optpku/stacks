/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.EllipticMulBy
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open AlgebraicGeometry.AlgebraicCycle AlgebraicGeometry.RelativePicard
open AlgebraicGeometry.AbelianVariety AlgebraicGeometry.Curve
open scoped AlgebraicGeometry CategoryTheory MonObj

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (E : SchemeOverField k) [Curve E] [Smooth E.hom] [Projective E.hom]
  [GrpObj E] [AbelianVariety E]

/- 03U2::statement_repair::2. Example 64.14.5. For integer multiplication on an elliptic curve, the Jacobian
pullback is multiplication by the same integer and has trace `2 * n`; the curve
endomorphism has degree `n.natAbs ^ 2`. Fixed points are `(n - 1)`-torsion, and
the fixed-point count uses local intersection multiplicities. Substituting the
fixed-point formula into Weil's formula gives the displayed integer identity
`(n - 1) ^ 2 = 1 - 2 * n + n ^ 2`. -/
@[stacks 03U2] #check (AlgebraicGeometry.Curve.weilTraceFormula_mulByInt :
  ∀ (E : SchemeOverField k) [Curve E] [Smooth E.hom] [Projective E.hom]
    [GrpObj E] [AbelianVariety E] (n : ℤ) (hφ : GrpObj.mulByInt E n ≠ 𝟙 E),
    fixedPointNumber (GrpObj.mulByInt E n) hφ = (1 : ℤ) - 2 * n + n ^ 2)

#check (AlgebraicGeometry.Curve.pullbackComponentHom_mulByInt_eq_mulByInt :
  ∀ (E : SchemeOverField k) [Curve E] [Smooth E.hom] [Projective E.hom]
    [GrpObj E] [AbelianVariety E] (n : ℤ),
    pullbackComponentHom E (GrpObj.mulByInt E n) =
      GrpObj.mulByInt (RelativePicard.component E 0) n)

#check (AlgebraicGeometry.Curve.endomorphismTrace_pullbackComponentHom_mulByInt :
  ∀ (E : SchemeOverField k) [Curve E] [Smooth E.hom] [Projective E.hom]
    [GrpObj E] [AbelianVariety E] (n : ℤ),
    endomorphismTrace (pullbackComponentHom E (GrpObj.mulByInt E n)) = 2 * n)

#check (AlgebraicGeometry.Curve.curveEndomorphismDegree_mulByInt :
  ∀ (E : SchemeOverField k) [Curve E] [Smooth E.hom] [Projective E.hom]
    [GrpObj E] [AbelianVariety E] (n : ℤ),
    curveEndomorphismDegree (GrpObj.mulByInt E n) = n.natAbs ^ 2)

#check (AlgebraicGeometry.Curve.fixedPointNumber_mulByInt :
  ∀ (E : SchemeOverField k) [Curve E] [Smooth E.hom] [Projective E.hom]
    [GrpObj E] [AbelianVariety E] (n : ℤ) (hφ : GrpObj.mulByInt E n ≠ 𝟙 E),
    fixedPointNumber (GrpObj.mulByInt E n) hφ = (n - 1) ^ 2)

-- This holds for generalized points and specializes to rational points when X is the unit scheme.
#check (CategoryTheory.GrpObj.comp_mulByInt_eq_self_iff E :
  ∀ (n : ℤ) {X : SchemeOverField k} (p : X ⟶ E),
    p ≫ GrpObj.mulByInt E n = p ↔ p ^ (n - 1) = 1)
