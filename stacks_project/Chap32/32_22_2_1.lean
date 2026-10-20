/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Diagram

open AlgebraicGeometry CategoryTheory

universe u

/- 32.22.2.1: the commuting square through the intermediate scheme `W`. -/
@[stacks 0CNP] #check
  (AlgebraicGeometry.FiniteTypeApproximationDiagram :
    {X S Si : Scheme.{u}} → (X ⟶ S) → (S ⟶ Si) → Type (u + 1))
