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

/- Lemma 66.16.5: The base change of an étale morphism of algebraic spaces by
any morphism of algebraic spaces is étale. -/
@[stacks 03FU] #check
  (AlgebraicGeometry.AlgebraicSpace.instIsStableUnderBaseChange_etale :
    ∀ {S : Scheme.{u}}, IsStableUnderBaseChange
      (@AlgebraicGeometry.AlgebraicSpace.Etale S :
        MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))
