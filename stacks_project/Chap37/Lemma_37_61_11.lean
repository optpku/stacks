module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.TorDimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.61.11: for a pseudo-coherent morphism of schemes, perfectness, local finite
Tor dimension of the structure sheaf over the inverse-image structure sheaf, and finite Tor
dimension of every stalk map are equivalent. -/
@[stacks 069C] #check
  (AlgebraicGeometry.PseudoCoherent.perfect_tfae :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.PseudoCoherent f],
      List.TFAE [AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap f,
        AlgebraicGeometry.RingedSpace.ModuleDerived.LocallyHasFiniteTorDimension
          ((AlgebraicGeometry.RingedSpace.ModuleDerived.relativeRestriction f.toShHom).obj
            (AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf X).obj),
        ∀ x : X, (f.stalkMap x).hom.HasFiniteTorDimension])
