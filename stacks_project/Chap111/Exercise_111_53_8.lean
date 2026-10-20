/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.ConjugateLines
import StacksCheckRecall

@[expose] public section

/- Exercise 111.53.8: Give an example of a scheme `X` over a field `k` such that `X` is
irreducible and such that for some finite extension `k' / k` the base change is connected but
reducible. -/
@[stacks 069Y] #check
  (AlgebraicGeometry.ConjugateLines.conjugateLinesExample :
    IrreducibleSpace AlgebraicGeometry.ConjugateLines.scheme ∧
      FiniteDimensional ℚ AlgebraicGeometry.ratSqrtNegOne ∧
      ConnectedSpace AlgebraicGeometry.ConjugateLines.baseChange ∧
      ¬ IrreducibleSpace AlgebraicGeometry.ConjugateLines.baseChange)
