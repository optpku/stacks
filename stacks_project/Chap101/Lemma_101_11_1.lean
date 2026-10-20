/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyOpen.Representable
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.11.1: A morphism of algebraic stacks representable by algebraic
spaces is universally open if and only if every algebraic-stack base change
induces an open map on underlying point spaces. -/
@[stacks 06U1] #check (AlgebraicGeometry.Groupoids.Hom.has_universallyOpen_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
    relativelyRepresentableByAlgebraicSpaces f →
      (AlgebraicGeometry.Groupoids.Hom.has (@AlgebraicSpace.UniversallyOpen S) f ↔
        AlgebraicGeometry.Groupoids.Hom.isOpenMapAfterBaseChange f))
