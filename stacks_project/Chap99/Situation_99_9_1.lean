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

/- Situation 99.9.1: let `S` be a scheme and let `f : X ⟶ B` be a morphism of
finite presentation of algebraic spaces over `S`. For a scheme `T` over `B`,
write `X_T` for the base change of `X` to `T`. The Hilbert functor
`Hilb_{X/B} : (Sch/B)ᵒᵖ ⥤ Sets` associated to `X/B` sends `T` to the set of
closed subspaces `Z ⊂ X_T` such that `Z ⟶ T` is of finite presentation, flat,
and proper. Base change of closed immersions, finite presentation, flatness,
and properness yields a functor. -/
@[stacks 0CZY] #check AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbert
