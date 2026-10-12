/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Remark_67_22_8_OpenAt
import StacksCheckRecall

@[expose] public section

/- Remark 67.22.8: apply Lemma 67.22.7 to every étale-local-on-source-and-target
scheme-morphism property listed in Descent, Remark 35.32.7 except Flat, by
defining a morphism `f` of algebraic spaces to have property `P` at a point `x`
when `etaleLocalNear P f x` holds, i.e. when `f` has `etaleLocal P` on some open
neighbourhood of `x`. -/
@[stacks 04RG] #check AlgebraicGeometry.AlgebraicSpace.etaleLocalNear
