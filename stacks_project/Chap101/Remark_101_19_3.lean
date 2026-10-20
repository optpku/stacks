module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.AutomorphismGroup
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack

universe u

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
@[stacks 0DTU] #check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.HasAt :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P : MorphismProperty (AlgebraicSpace S))
    [IsInvariantUnderGroundFieldExtension P] (x : Points X), Prop)
