/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite.Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.23.8: if `f ≫ g` is locally quasi-finite and `g` is quasi-DM, then
`f` is locally quasi-finite. -/
@[stacks 06UG] #check
  (AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [LocallyQuasiFinite (f ≫ g)] [QuasiDM g],
      LocallyQuasiFinite f)
