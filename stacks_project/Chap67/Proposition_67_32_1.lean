/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.GenericFlatness
import StacksCheckRecall

open AlgebraicGeometry AlgebraicSpace

universe u

/- Proposition 67.32.1: a finite-type morphism of algebraic spaces to a reduced
algebraic space and a finite-type quasicoherent module admit a dense open subspace
on which the base change is flat, locally of finite presentation, and quasi-compact,
and the restricted module is flat over the open and of finite presentation. -/
@[stacks 06QS] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.exists_dense_open_genericFlatness_of_reduced :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsReduced Y] [FiniteType f] (ℱ : X.Modules)
      [ℱ.IsQuasicoherent] [ℱ.IsFiniteType],
      ∃ W : OpenSubspace Y, Dense (W.pointsSet : Set (Points Y)) ∧
        AlgebraicGeometry.AlgebraicSpace.Modules.GenericFlatnessOn f ℱ W)
