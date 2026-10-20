/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteComponents
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Structure

/-!
# Finite irreducible components of algebraic-space reductions

The property of having finitely many irreducible components on compact opens is
preserved by reduction.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The reduction of an algebraic space with finitely many irreducible components
on compact opens has the same finiteness property. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpensReduction
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    HasFiniteIrreducibleComponentsOnCompactOpens X.reduction :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
