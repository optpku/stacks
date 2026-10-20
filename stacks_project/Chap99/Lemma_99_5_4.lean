/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Stack

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 99.5.4: the coherent-sheaf projection is a stack in groupoids
on the fppf site of schemes over `S`. -/
@[stacks 08KC] #check
  (AlgebraicGeometry.AlgebraicSpace.CohStack.instIsStackInGroupoids :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
      [FinitePresentation f] → IsStack.InGroupoids (Scheme.fppfTopology.over S)
        (AlgebraicGeometry.AlgebraicSpace.CohStack.p f))
