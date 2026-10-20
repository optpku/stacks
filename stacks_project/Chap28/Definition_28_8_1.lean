/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 28.8.1: a scheme is Cohen-Macaulay if every point has an affine open neighborhood
whose ring of sections is Cohen-Macaulay and Noetherian. -/
@[stacks 02IO] #check
  (AlgebraicGeometry.Scheme.CohenMacaulay : AlgebraicGeometry.Scheme.{u} → Prop)
