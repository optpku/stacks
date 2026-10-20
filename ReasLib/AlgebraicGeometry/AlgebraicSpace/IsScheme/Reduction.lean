/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Structure

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsScheme

/-- An algebraic space whose reduction is a scheme is itself a scheme. -/
instance (priority := 100) of_reduction {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsScheme (reduction X)] : IsScheme X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsScheme
