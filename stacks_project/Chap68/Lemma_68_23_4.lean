module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Jacobson.Topology
import StacksCheckRecall

/-!
# Jacobson algebraic spaces and Jacobson spaces of points

For a decent algebraic space, the étale-local Jacobson property is equivalent to
the topological Jacobson property of the space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 68.23.4: Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Then `X` is Jacobson if and only if `Points X` is Jacobson. -/
@[stacks 0BA6] #check (AlgebraicGeometry.AlgebraicSpace.isJacobson_iff_jacobsonSpace :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X],
    IsJacobson X ↔ JacobsonSpace (Points X))
