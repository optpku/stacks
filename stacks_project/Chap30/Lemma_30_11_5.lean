/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.CohenMacaulay.Regular
import StacksCheckRecall

open AlgebraicGeometry

universe u

/-
Lemma 30.11.5: Let `X` be a regular scheme and `ℱ` a coherent `𝒪_X`-module. Then
`ℱ` is Cohen-Macaulay with full support if and only if it is finite locally free with full support.
-/
@[stacks 0B3K] #check
  (AlgebraicGeometry.Scheme.Modules.CohenMacaulay.and_fullSupport_iff_isFiniteLocallyFree_and_fullSupport :
    ∀ {X : Scheme.{u}} [Scheme.Regular X] (ℱ : X.Modules) [ℱ.IsCoherent],
      (AlgebraicGeometry.Scheme.Modules.CohenMacaulay ℱ ∧
          AlgebraicGeometry.RingedSpace.moduleSupport ℱ = Set.univ) ↔
        (SheafOfModules.IsFiniteLocallyFree ℱ ∧
          AlgebraicGeometry.RingedSpace.moduleSupport ℱ = Set.univ))
