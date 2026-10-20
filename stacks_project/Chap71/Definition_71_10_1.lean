/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Definition 71.10.1 (1): the sheaf of meromorphic functions 𝒦_X on X_étale is the
sheafification of U ↦ S_X(U)⁻¹ 𝒪_X(U). -/
@[stacks 0EN3] #check
  (AlgebraicGeometry.AlgebraicSpace.meromorphicFunctionSheaf :
    {S : Scheme.{u}} → (X : AlgebraicSpace S) →
      Sheaf (smallEtaleTopology X) CommRingCat.{u + 1})

/- Definition 71.10.1 (2): a meromorphic function on X is a global section of 𝒦_X. -/
@[stacks 0EN3] #check
  (AlgebraicGeometry.AlgebraicSpace.meromorphicFunctions :
    {S : Scheme.{u}} → (X : AlgebraicSpace S) → CommRingCat.{u + 1})
