/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Algebraic spaces as fpqc sheaves

The functor of points of an algebraic space over a scheme satisfies fpqc descent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The functor of points of an algebraic space over `S` is a sheaf for the fpqc topology
on the big site of schemes over `S`. -/
@[stacks 0APL]
theorem isSheaf_fpqc {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) X.functorOfPoints :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
