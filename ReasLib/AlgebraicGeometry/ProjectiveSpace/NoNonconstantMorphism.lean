/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Nonconstant
public import Mathlib.Data.Complex.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom

namespace AlgebraicGeometry.ProjectiveSpace

/-- There is no nonconstant morphism from the complex projective plane to the complex projective line. -/
theorem not_exists_isNonconstant :
    ¬ ∃ f : schemeOver ℂ 2 ⟶ schemeOver ℂ 1, f.left.IsNonconstant := sorry

/-- Every morphism from the complex projective plane to the complex projective line has singleton range. -/
theorem range_eq_singleton (f : schemeOver ℂ 2 ⟶ schemeOver ℂ 1) :
    ∃ y : scheme ℂ 1, Set.range f.left = {y} := sorry

end AlgebraicGeometry.ProjectiveSpace
