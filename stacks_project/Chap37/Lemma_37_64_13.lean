/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.Cancellation
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.64.13: a morphism `f : X ⟶ Y` over `S` is weakly étale when the
structure morphisms `f ≫ g : X ⟶ S` and `g : Y ⟶ S` are weakly étale. -/
@[stacks 0951] #check
  (AlgebraicGeometry.WeaklyEtale.left_of_comp_right :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
      (_ : AlgebraicGeometry.WeaklyEtale (f ≫ g))
      (_ : AlgebraicGeometry.WeaklyEtale g),
      AlgebraicGeometry.WeaklyEtale f)
