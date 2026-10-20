module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Jacobson.FiniteType
import StacksCheckRecall

/-!
# Locally of finite type over Jacobson algebraic spaces

A morphism of algebraic spaces that is locally of finite type into a Jacobson
target has Jacobson source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 68.23.1: Let `S` be a scheme. Let `X` be a Jacobson algebraic space over `S`.
Any algebraic space locally of finite type over `X` is Jacobson. -/
@[stacks 0BA3] #check (AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.isJacobson :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f]
    [AlgebraicGeometry.AlgebraicSpace.IsJacobson Y],
    AlgebraicGeometry.AlgebraicSpace.IsJacobson X)
