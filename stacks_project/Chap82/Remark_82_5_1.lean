module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.IrreducibleComponent

/-!
# Irreducible components of a closed subspace in the good setup

In Situation 82.2.1, for good `X / B` and a closed subspace `Y ⊂ X`, irreducible
components of `|Y|` correspond to their generic points and to integral closed
subspaces with those supports. Such an integral closed subspace is called an
irreducible component of `Y`, and its generic point is the generic point of that
component.

The shared statements hold for every decent algebraic space. In the good setup,
quasi-separatedness transfers from the base along the structure morphism and to
closed subspaces; quasi-separated algebraic spaces are decent. Thus they apply
to `Y` in the source situation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Remark 82.5.1: each irreducible component has a unique generic point. -/
@[stacks 0EE8] #check (AlgebraicGeometry.AlgebraicSpace.irreducibleComponents_equiv_genericPoints :
  ∀ {S : Scheme.{u}}
    (Y : AlgebraicSpace S) [IsDecent Y]
    (T : irreducibleComponents (Points Y)),
    ∃! ξ : Points Y,
      ξ ∈ genericPoints Y ∧
        closure ({ξ} : Set (Points Y)) = (T : Set (Points Y)))

/- Integral closed presentations of a component are unique over the ambient space. -/
#check (AlgebraicGeometry.AlgebraicSpace.existsUnique_irreducibleComponent :
  ∀ {S : Scheme.{u}}
    (Y : AlgebraicSpace S) [IsDecent Y]
    (T : irreducibleComponents (Points Y)),
    ∃ Z : ClosedSubspace Y,
      IsIntegral Z.X ∧
        Z.pointsSet = (T : Set (Points Y)) ∧
          ∀ (Z' : ClosedSubspace Y),
            IsIntegral Z'.X →
              Z'.pointsSet = (T : Set (Points Y)) →
                ∃! g : Z'.X ⟶ Z.X, g ≫ Z.ι = Z'.ι)
