/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Graded
public import ReasLib.Algebra.Group.Action.NatInt
public import ReasLib.RingTheory.MvPolynomial.Finite
public import ReasLib.RingTheory.Polynomial.Numerical.Closure
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

noncomputable section

universe u v w

namespace MvPolynomial

variable {k : Type u} [hk : Field k] {σ : Type w} [hVar : Finite σ]
variable {M : Type v} [hAdd : AddCommGroup M] [hK : Module k M]
  [hPoly : Module (MvPolynomial σ k) M]
  [hTower : IsScalarTower k (MvPolynomial σ k) M]
variable (ℳ : ℤ → Submodule k M)
variable [hDecomp : DirectSum.Decomposition ℳ]
  [hGraded : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule σ k) ℳ]
variable [hFinite : Module.Finite (MvPolynomial σ k) M]

-- These hypotheses are mathematical inputs even though the conclusion mentions only the
-- component finranks.  `include` prevents section-variable pruning from silently turning the
-- standard-polynomial theorem into a false statement about an arbitrary integer grading.
include hVar hPoly hTower hDecomp hGraded hFinite

/-- Example 10.58.9: a finite graded module over the standard multivariate polynomial ring has a
numerical-polynomial Hilbert function given by the finrank of its homogeneous pieces. -/
@[stacks 00K2 "polynomial-ring Hilbert function"]
theorem finrank_isNumericalPolynomial :
    IsNumericalPolynomial (fun n ↦ (Module.finrank k (ℳ n) : ℤ)) := sorry

end MvPolynomial
