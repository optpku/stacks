/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafSystem

universe uI u

/- Definition 59.51.1: a system of sheaves on a preorder-indexed inverse system of
schemes consists of small-etale sheaves and pullback transition morphisms satisfying
the three-index cocycle law. -/
@[stacks 0EZL] #check (AlgebraicGeometry.Scheme.Etale.SheafSystem :
  {I : Type uI} → [Preorder I] →
    CategoryTheory.PreorderInverseSystem I AlgebraicGeometry.Scheme.{u} →
      Type (max (u + 2) uI))
