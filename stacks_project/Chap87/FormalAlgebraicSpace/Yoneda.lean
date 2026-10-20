/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap87.Lemma_87_34_3_Reduction

/-! Canonical inference from schemes to formal algebraic spaces. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Every scheme over S is formal through its canonical algebraic space of points. -/
instance instIsFormalAlgebraicSpace_yonedaOfOver {S : Scheme.{u}} (T : Over S) :
    IsFormalAlgebraicSpace (yoneda.obj T) :=
  inferInstanceAs (IsFormalAlgebraicSpace (AlgebraicSpace.ofOver T).functorOfPoints)

end AlgebraicGeometry.FormalAlgebraicSpace
