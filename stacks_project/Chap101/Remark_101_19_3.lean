/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Remark_101_19_3_AutomorphismGroup
import StacksCheckRecall

/- Remark 101.19.3
Let P be a property of algebraic spaces over fields which is invariant under
ground field extensions. Given an algebraic stack X and x ∈ |X|, we say the
automorphism group of X at x has P if the equivalent conditions of
Lemma 101.19.2 are satisfied. For example, we say the automorphism group of X
at x is finite, if G_x ⟶ Spec(k) is finite whenever x : Spec(k) ⟶ X is a
representative of x. Similarly for smooth, proper, etc. (There is clearly an
abuse of language going on here, but we believe it will not cause confusion or
imprecision.)
-/
@[stacks 0DTU] #check AlgebraicGeometry.AlgebraicStack.automorphismGroup.HasAt
