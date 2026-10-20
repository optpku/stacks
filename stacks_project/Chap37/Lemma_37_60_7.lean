/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.60.7: if `g : Y ⟶ S` and `f ≫ g : X ⟶ S` are pseudo-coherent,
then `f : X ⟶ Y` is pseudo-coherent. -/
@[stacks 0683] #check
  (AlgebraicGeometry.PseudoCoherent.of_comp :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
      [AlgebraicGeometry.PseudoCoherent g]
      [AlgebraicGeometry.PseudoCoherent (f ≫ g)],
      AlgebraicGeometry.PseudoCoherent f)
