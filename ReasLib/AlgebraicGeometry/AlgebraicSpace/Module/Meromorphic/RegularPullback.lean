/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Regular
public import ReasLib.CategoryTheory.Monoidal.Invertible

/-! # Pullback of regular meromorphic sections on algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Canonical pullback along a morphism preserving meromorphic denominators sends a regular
meromorphic section of an invertible module sheaf to a regular meromorphic section. -/
theorem isRegularMeromorphicSection_pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [PullbacksMeromorphicFunctionsDefined f] (L : Y.Modules)
    [isInvertibleObject L] {s : meromorphicSections Y L}
    (hs : IsRegularMeromorphicSection Y L s) :
    IsRegularMeromorphicSection X ((Modules.pullback f).obj L)
      (MeromorphicConstruction.Pullback.pullback f L s) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
