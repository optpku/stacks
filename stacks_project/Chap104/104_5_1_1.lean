/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent.Homology
import StacksCheckRecall

open CategoryTheory

universe u

/- 104.5.1.1 The cohomological functor
`H^i : D_QCoh(𝒪_X) ⟶ QCoh(𝒪_X)` on an algebraic stack. -/
@[stacks 07B7] #check (AlgebraicGeometry.AlgebraicStack.DerivedQCoh.cohomologyFunctor :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S)
    [AlgebraicGeometry.AlgebraicStack X] (i : ℤ),
    AlgebraicGeometry.AlgebraicStack.DerivedQCoh X ⥤ AlgebraicGeometry.GroupoidsOver.QCoh X)
