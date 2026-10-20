/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree
public import ReasLib.AlgebraicGeometry.Scheme.Normal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Norms from function-field extensions

This file owns the finite-morphism norm obtained from the norm of the induced finite extension of
function fields.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A finite surjective morphism between integral schemes with normal target admits a norm whose
degree is the degree of its induced extension of function fields. -/
@[stacks 0BD3]
theorem exists_norm_of_isFinite_of_surjective_of_isNormal
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsFinite π] [Surjective π] (hY : Y.isNormal) :
    ∃ N : FiniteMorphismNorm π,
      IsFiniteMorphismNorm π π.inducedFunctionFieldDegree N := sorry

end AlgebraicGeometry.Scheme
