/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.QCohStack.FiniteType
import StacksCheckRecall

universe u

/- Lemma 95.5.1
The projection from finite-type quasi-coherent sheaves over a scheme to its fppf site
satisfies conditions (1), (2), and (3) of Stacks Definition 8.4.1.
-/
@[stacks 04U4] #check
  (AlgebraicGeometry.QCohStack.FG.instIsStackOnSite :
    ∀ S : AlgebraicGeometry.Scheme.{u},
      CategoryTheory.IsStack.OnSite (AlgebraicGeometry.Scheme.fppfTopology.over S)
        (AlgebraicGeometry.QCohStack.FG.p S))
