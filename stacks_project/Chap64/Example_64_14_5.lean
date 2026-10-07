module

public import stacks_project.Chap64.Theorem_64_14_4_Weil
public import ReasLib.CategoryTheory.Monoidal.Grp.MulBy
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicCycle AlgebraicGeometry.RelativePicard
open AlgebraicGeometry.AbelianVariety AlgebraicGeometry.Curve
open scoped AlgebraicGeometry CategoryTheory MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (E : SchemeOverField k) [Curve E] [Smooth E.hom] [Projective E.hom]
  [GrpObj E] [AbelianVariety E]

/-- Example 64.14.5 (1): if `E` is an elliptic curve and `φ = [n]`, then the
Jacobian pullback `φ*` is multiplication by `n` on `RelativePicard.component E 0`. -/
@[stacks 03U2]
theorem pullbackComponentHom_mulBy_eq_mulBy (n : ℕ) :
    pullbackComponentHom E (GrpObj.mulBy E n) =
      GrpObj.mulBy (RelativePicard.component E 0) n := sorry

/-- Example 64.14.5 (2): the Jacobian pullback of multiplication by `n` has
integer trace `2 * n`. -/
@[stacks 03U2]
theorem endomorphismTrace_pullbackComponentHom_mulBy (n : ℕ) :
    endomorphismTrace (pullbackComponentHom E (GrpObj.mulBy E n)) = 2 * (n : ℤ) := sorry

/-- Example 64.14.5 (3): multiplication by `n` on the elliptic curve has degree
`n ^ 2`, including degree zero for `n = 0`. -/
@[stacks 03U2]
theorem curveEndomorphismDegree_mulBy (n : ℕ) :
    curveEndomorphismDegree (GrpObj.mulBy E n) = n ^ 2 := sorry

/-- Example 64.14.5 (4): for a non-identity multiplication map, the
graph-diagonal fixed-point intersection number is `((n : ℤ) - 1) ^ 2`. -/
@[stacks 03U2]
theorem fixedPointNumber_mulBy (n : ℕ)
    (hφ : GrpObj.mulBy E n ≠ 𝟙 E) :
    fixedPointNumber (GrpObj.mulBy E n) hφ = ((n : ℤ) - 1) ^ 2 := sorry

/-- Example 64.14.5 (5): Weil's numerical identity for multiplication by `n` on
an elliptic curve is `(n - 1) ^ 2 = 1 - 2 * n + n ^ 2`. -/
@[stacks 03U2]
theorem weilTraceFormula_mulBy (n : ℕ)
    (hφ : GrpObj.mulBy E n ≠ 𝟙 E) :
    fixedPointNumber (GrpObj.mulBy E n) hφ =
      (1 : ℤ) - 2 * (n : ℤ) + (n : ℤ) ^ 2 := sorry

end AlgebraicGeometry.Curve
