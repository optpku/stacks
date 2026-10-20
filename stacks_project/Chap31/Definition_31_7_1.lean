/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative

universe u

/- Definition 31.7.1: the relative assassin of a quasi-coherent module is the direct
specialization of the fiberwise relative assassin defined for every scheme module. -/
@[stacks 05AT] #check
  (@AlgebraicGeometry.Scheme.Modules.relativeAssassin :
    {X S : AlgebraicGeometry.Scheme.{u}} → (X ⟶ S) → X.Modules → Set X)
