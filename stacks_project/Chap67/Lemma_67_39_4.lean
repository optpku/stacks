/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.BaseChange
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry MorphismProperty

/- Lemma 67.39.4: The base change of an étale morphism of algebraic spaces by
any morphism of algebraic spaces is étale. -/
@[stacks 0466] #check
  (AlgebraicGeometry.AlgebraicSpace.instIsStableUnderBaseChange_etale :
    ∀ {S : Scheme.{u}}, IsStableUnderBaseChange
      (@AlgebraicGeometry.AlgebraicSpace.Etale S :
        MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))
