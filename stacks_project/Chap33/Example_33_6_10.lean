/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced.PthPowerHypersurface
import StacksCheckRecall

@[expose] public section

open CategoryTheory

variable (p : ℕ) [Fact p.Prime]

/- Companion check: the original rational-function-plane hypersurface is a variety over its
coefficient field. -/
#check
  (AlgebraicGeometry.PthPowerHypersurface.RationalFunctionPlane.instVariety
    (p := p) :
      AlgebraicGeometry.Variety
        (AlgebraicGeometry.PthPowerHypersurface.RationalFunctionPlane.overBase p))

variable (L : Type) [Field L]
  [Algebra
    (MvPolynomial.PthPowerHypersurface.RationalFunctionPlane.BaseField p) L]

/- Example 33.6.10: let `k = 𝔽_p(s, t)` and let `X` be the variety
`Spec(k[X, Y] / (1 + s X^p + t Y^p))`. For every field extension `L / k` in which both `s` and
`t` have p-th roots, the scheme-theoretic base change `X_L` is not reduced. -/
@[stacks 020F] #check
  (AlgebraicGeometry.PthPowerHypersurface.RationalFunctionPlane.baseChange_not_isReduced
    (p := p) (L := L) :
      (∃ a : L, a ^ p =
        algebraMap
          (MvPolynomial.PthPowerHypersurface.RationalFunctionPlane.BaseField p) L
          (MvPolynomial.PthPowerHypersurface.RationalFunctionPlane.s p)) →
      (∃ b : L, b ^ p =
        algebraMap
          (MvPolynomial.PthPowerHypersurface.RationalFunctionPlane.BaseField p) L
          (MvPolynomial.PthPowerHypersurface.RationalFunctionPlane.t p)) →
      ¬ AlgebraicGeometry.IsReduced
        (AlgebraicGeometry.PthPowerHypersurface.RationalFunctionPlane.baseChange p L))
