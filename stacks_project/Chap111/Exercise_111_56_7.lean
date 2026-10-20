/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.PlaneCurve.LinearSystem
import StacksCheckRecall

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

/- Exercise 111.56.7 (1) -/
@[stacks 09U2]
#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.residualCanonicalSpace_eq :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 5)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    [Scheme.Regular (Hypersurface.scheme 2 5 F hF)]
    (P : Fin 5 → (abstractCurve 5 F hF).left)
    (h_closed : ∀ i, P i ∈ closedPoints (abstractCurve 5 F hF).left)
    (h_affine : ∀ i, P i ∈ standardChartOpen 5 F hF)
    (h_inj : Function.Injective P),
    Scheme.riemannRochSpace (abstractCurve 5 F hF)
        (canonicalDivisor 5 F hF - fivePointDivisor F hF P h_closed) =
      (fun h ↦ identApply 5 F hF (standardChartIdent 5 F hF) (polynomialFrac F h)) ''
        {h : MvPolynomial (Fin 2) k |
          h.totalDegree ≤ 2 ∧ ∀ i, VanishesAt F hF (h_affine i) h})

/- Exercise 111.56.7 (2) -/
@[stacks 09U2]
#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.riemannRochDim_sum_mem :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 5)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    [Scheme.Regular (Hypersurface.scheme 2 5 F hF)],
    {n | ∃ (P : Fin 5 → (abstractCurve 5 F hF).left)
        (h_closed : ∀ i, P i ∈ closedPoints (abstractCurve 5 F hF).left),
      (∀ i, P i ∈ standardChartOpen 5 F hF) ∧ Function.Injective P ∧
        Scheme.riemannRochDim (abstractCurve 5 F hF)
            (fivePointDivisor F hF P h_closed) = n} =
      ({1, 2, 3} : Set ℕ) )

end AlgebraicGeometry.ProjectiveSpace.PlaneCurve
