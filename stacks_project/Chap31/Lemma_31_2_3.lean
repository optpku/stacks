/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Support

universe u

/- Lemma 31.2.3: for a quasi-coherent `𝒪_X`-module `ℱ` on a scheme `X`, every
associated point of `ℱ` lies in the support of `ℱ`. -/
@[stacks 05AD] #check
  (AlgebraicGeometry.Scheme.Modules.associatedPoints_subset_support :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      AlgebraicGeometry.Scheme.Modules.associatedPoints ℱ ⊆
        AlgebraicGeometry.RingedSpace.moduleSupport ℱ)
