/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.Stack

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 99.16.6: in Situation 99.16.3, the projection from relatively perfect
complexes with vanishing negative fibre self-Ext to schemes over `S` is a stack
in groupoids for the fppf topology. -/
@[stacks 0DLH] #check
  (AlgebraicGeometry.AlgebraicSpace.Complexes.instIsStackInGroupoids :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
      [Proper f] → [Flat f] → [FinitePresentation f] →
        IsStack.InGroupoids (Scheme.fppfTopology.over S)
          (AlgebraicGeometry.AlgebraicSpace.Complexes.p f))
