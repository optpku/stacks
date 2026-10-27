/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction.Pullback.Criteria
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints.Dominant

/-! # Meromorphic pullback along dominant integral morphisms -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Pullbacks of meromorphic functions along a dominant morphism of integral
algebraic spaces are defined. -/
instance instPullbacksMeromorphicFunctionsDefined_of_dominant
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [Dominant f] :
    PullbacksMeromorphicFunctionsDefined f :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.Hom
