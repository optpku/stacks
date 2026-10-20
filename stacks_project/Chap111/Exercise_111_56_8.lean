/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.PlaneCurve.Rational
import StacksCheckRecall

/-!
# Exercise 111.56.8

An explicit irreducible homogeneous form of degree `100` whose associated
abstract curve has genus `0`.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace.PlaneCurve

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.rationalForm_eq k 99 :
  AlgebraicGeometry.ProjectiveSpace.PlaneCurve.rationalForm k 99 =
    MvPolynomial.X 1 ^ 100 - MvPolynomial.X 0 ^ 99 * MvPolynomial.X 2)

#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.rationalForm_mem_grading k 99 :
  AlgebraicGeometry.ProjectiveSpace.PlaneCurve.rationalForm k 99 ∈
    AlgebraicGeometry.ProjectiveSpace.grading k 2 100)

#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.rationalForm_totalDegree k 99 :
  (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.rationalForm k 99).totalDegree = 100)

#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.irreducible_rationalForm k 99 :
  Irreducible (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.rationalForm k 99))

#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.affineEquation_rationalForm k 99 :
  AlgebraicGeometry.ProjectiveSpace.PlaneCurve.affineEquation
      (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.rationalForm k 99) =
    MvPolynomial.X 0 ^ 100 - MvPolynomial.X 1)

#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.irreducible_affineEquation_rationalForm k 99 :
  Irreducible (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.affineEquation
    (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.rationalForm k 99)))

/- Exercise 111.56.8
The normalized curve associated to the degree-100 rational plane form has genus zero. -/
@[stacks 09U3] #check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.genus_rationalAbstractCurve k 99 :
  AlgebraicGeometry.Curve.genus
      (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.rationalAbstractCurve k 99) = 0)
