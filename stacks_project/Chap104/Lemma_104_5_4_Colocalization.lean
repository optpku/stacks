/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.Colocalization

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver

universe u

#check (AlgebraicGeometry.AlgebraicStack.DerivedLQCohFbc.colocalize_leftOrthogonal :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      (E : DerivedLQCohFbc X),
      (derivedParasitic X).leftOrthogonal ((DerivedLQCohFbc.colocalize X).obj E))
