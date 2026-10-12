/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_36_4_Syntomic
import StacksCheckRecall

@[expose] public section

/- Definition 67.36.1 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is syntomic if the equivalent conditions of Lemma 67.22.1 hold with `P` = syntomic. -/
@[stacks 03Z7] #check AlgebraicGeometry.AlgebraicSpace.Syntomic

/- Definition 67.36.1 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is syntomic at a point `x` of `|X|` if some open neighbourhood `X' ⊂ X` of `x` has
syntomic restriction `f|_{X'} : X' ⟶ Y`. -/
@[stacks 03Z7] #check AlgebraicGeometry.AlgebraicSpace.SyntomicAt
