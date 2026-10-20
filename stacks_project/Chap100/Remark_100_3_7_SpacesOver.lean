/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SpacesOver
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Remark 100.3.7: the hom-categories of algebraic spaces over an algebraic
stack are thin. The construction and its API are supplied by the mathematical
owner imported above. -/
@[stacks 04ZQ] #check
  (AlgebraicGeometry.SpacesOver.homIsThin :
    ∀ {S : Scheme.{u}} {Y : GroupoidsOver S} [AlgebraicStack Y]
      (P Q : AlgebraicGeometry.SpacesOver Y), Quiver.IsThin (P ⟶ Q))
