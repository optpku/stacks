module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Constructible
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Topology

universe u

/- Lemma 66.8.1: for a subset of the points of an algebraic space, local constructibility
along every étale scheme morphism, constructibility along every affine étale scheme morphism,
and local constructibility along one surjective étale scheme morphism are equivalent. -/
@[stacks 0ECT] #check (AlgebraicGeometry.AlgebraicSpace.isEtaleLocallyConstructible_tfae :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (E : Set (Points X)),
      List.TFAE [IsEtaleLocallyConstructible E, IsEtaleLocallyConstructible.forallAffine E,
        IsEtaleLocallyConstructible.existsSurjective E])
