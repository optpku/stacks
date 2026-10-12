/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap99.«99_9_1_1_Functor»

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

/- 99.9.1.1: the Hilbert functor `Hilb_{X/B} : (Sch/B)ᵒᵖ ⥤ Sets` associated to a
morphism `f : X ⟶ B` of finite presentation of algebraic spaces over a scheme
`S`. It sends a scheme `T` over `B` to the set of closed subspaces
`Z ⊂ X_T = X ×_B T` such that `Z ⟶ T` is of finite presentation, flat, and
proper. Base change of those properties yields a functor
`(Sch/B)ᵒᵖ ⥤ Sets`. -/
@[stacks 0CZZ] #check AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbert
