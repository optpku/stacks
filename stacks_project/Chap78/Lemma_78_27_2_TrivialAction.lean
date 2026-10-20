module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action.Trivial

/-!
# Trivial actions of group algebraic spaces

The trivial action of a group algebraic space `G` over `B` is the module object
structure on the terminal object of `Over B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory

noncomputable section

universe u

#check (AlgebraicGeometry.GroupAlgebraicSpace.trivialAction :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    (G : AlgebraicGeometry.GroupAlgebraicSpace B),
    AlgebraicGeometry.GroupAlgebraicSpace.Action G)

#check (AlgebraicGeometry.GroupAlgebraicSpace.trivialAction_X :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    (G : AlgebraicGeometry.GroupAlgebraicSpace B),
    (AlgebraicGeometry.GroupAlgebraicSpace.trivialAction G).X = 𝟙_ (Over B))
