module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 78.8.1 (1): an action of a group algebraic space `G` on an algebraic space
over `B` is a module object for `G.X` in the cartesian monoidal slice `Over B`. -/
@[stacks 043Q] #check (AlgebraicGeometry.GroupAlgebraicSpace.Action :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B), Type (u + 1))

/- Definition 78.8.1 (2): a morphism of algebraic spaces over `B` is `G`-equivariant if and
only if it is a map of `G(T)`-sets on scheme-valued points. -/
@[stacks 043Q] #check (AlgebraicGeometry.GroupAlgebraicSpace.Action.hom_iff_schemePoints :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupAlgebraicSpace B}
    {X Y : GroupAlgebraicSpace.Action G} (ψ : X.X ⟶ Y.X),
    IsModHom G.X ψ ↔
      ∀ (T : Over S) (t : AlgebraicSpace.ofOver T ⟶ B),
        ∀ (g : Over.mk t ⟶ G.X) (x : Over.mk t ⟶ X.X),
          (g • x) ≫ ψ = g • (x ≫ ψ))
