/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle.Grading

/-!
# Comparison isomorphisms for graded de Rham forms

This file records the canonical comparison isomorphisms attached to a canonical geometric grading.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle

variable {S X : Scheme.{u}} (f : X ⟶ S) (ℒ : X.Modules)
variable [Scheme.Modules.Invertible ℒ]
variable (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
variable [hP : Scheme.IsRelativeSpectrumOver P]

/-- The twisted punctured-form comparison defined by the tautological action and homogeneous generators is an isomorphism in
every form degree and integral weight. -/
theorem twistComparison_isIso (p : ℕ) (n : ℤ) :
    IsIso (twistComparison f ℒ P p n) := sorry

/-- The comparison from ordinary relative de Rham forms to the weight-zero total-space complex
defined by the tautological action and homogeneous generators is an isomorphism. -/
theorem degreeZeroComparison_isIso :
    IsIso (degreeZeroComparison f ℒ P) := sorry

/-- The positive-weight restriction comparison defined by the tautological action and homogeneous generators is an isomorphism. -/
theorem positiveWeightComparison_isIso (p n : ℕ) [NeZero n] :
    IsIso (positiveWeightComparison f ℒ P p n) := sorry

end AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle
