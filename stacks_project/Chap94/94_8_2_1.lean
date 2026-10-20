/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids.Hom
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory
open scoped Bicategory

universe u

/- 94.8.2.1: if categories fibred in groupoids X, Y over (Sch/S)_fppf are
representable by algebraic spaces F, G, then 1-morphisms X ⟶ Y up to
2-isomorphism are identified with morphisms F ⟶ G of algebraic spaces.
HomotopyCategory morphisms are the 2-isomorphism classes, and the suppressed
equivalences X ≌ F.toGroupoids and Y ≌ G.toGroupoids are the explicit
parameters of homEquiv. -/
@[stacks 04SW]
#check (AlgebraicGeometry.AlgebraicSpace.toGroupoids.homEquiv :
  ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S} {X Y : GroupoidsOver S},
    (X ≌ F.toGroupoids) → (Y ≌ G.toGroupoids) →
      (Bicategory.HomotopyCategory.mk X ⟶ Bicategory.HomotopyCategory.mk Y) ≃ (F ⟶ G))
