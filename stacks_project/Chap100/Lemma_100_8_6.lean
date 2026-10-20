/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Monomorphism.DiagonalSquare
import StacksCheckRecall

open CategoryTheory
open scoped Bicategory

universe u

/- Lemma 100.8.6: the canonical diagonal square of a monomorphism of algebraic
stacks is a fibre product square. -/
@[stacks 0CBB] #check
  (AlgebraicGeometry.Groupoids.Hom.Mono.diagonalSquare.cone.isBilimit :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X X' Y : AlgebraicGeometry.GroupoidsOver S}
      [AlgebraicGeometry.AlgebraicStack X]
      [AlgebraicGeometry.AlgebraicStack X']
      [AlgebraicGeometry.AlgebraicStack Y]
      (f : X ⟶ X') (g : X' ⟶ Y) [AlgebraicGeometry.Groupoids.Hom.Mono f],
      (AlgebraicGeometry.Groupoids.Hom.Mono.diagonalSquare.cone f g).IsBilimit)
