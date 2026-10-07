module

import stacks_project.Chap78.Definition_78_8_1_Action
import ReasLib.CategoryTheory.Monoidal.Cartesian.FreeAction
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
  (X : GroupAlgebraicSpace.Action G)

/- Lemma 78.8.3: In the situation of Definition 78.8.2, the action `a` of `G` on `X`
over `B` is free if and only if the shear `G ×_B X ⟶ X ×_B X`,
`(g, x) ↦ (a(g, x), x)`, is a monomorphism of algebraic spaces. -/
@[stacks 06P9] #check
  (CategoryTheory.Mod.isFree_iff_mono_leftSMul X :
    Mod.IsFree X ↔
      Mono (ModObj.leftSMul G.X X.X))
