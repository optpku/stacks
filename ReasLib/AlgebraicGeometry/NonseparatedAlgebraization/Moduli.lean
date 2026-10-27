/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.NonseparatedAlgebraization.FormalModule
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Algebraic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.ProperSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Representability

/-!
# Nonalgebraic moduli on a doubled power-series affine line

The coherent-sheaf stack and the proper-support Quot functor of the structure sheaf fail
algebraicity for the doubled affine line over `PowerSeries k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.NonseparatedAlgebraization

/-- The stack of coherent sheaves on the doubled power-series affine line is not algebraic. -/
theorem not_isAlgebraicStack {k : Type u} [Field k] :
    ¬ CohStack.AlgebraicStack (CohStack.toGroupoids (spaceHom k)) := sorry

/-- The proper-support Quot functor of the structure sheaf on the doubled power-series affine
line is not represented by an algebraic space over the base. -/
theorem not_isAlgebraicSpaceOver_quot {k : Type u} [Field k] :
    ¬ IsAlgebraicSpaceOver
      (AlgebraicGeometry.AlgebraicSpace.Quot.quot (spaceHom k)
        (SheafOfModules.unit (structureSheaf (spaceX k)))) := sorry

end AlgebraicGeometry.NonseparatedAlgebraization
