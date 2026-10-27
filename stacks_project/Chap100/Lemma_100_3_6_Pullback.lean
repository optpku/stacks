/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Presentation.Pullback

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

/- The object space of the pulled-back presentation is the actual two-fibre product. -/
#check (AlgebraicGeometry.AlgebraicStack.Presentation.pullbackObject :
  ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S} [AlgebraicStack X],
    Presentation X → (X' ⟶ X) → GroupoidsOver S)
