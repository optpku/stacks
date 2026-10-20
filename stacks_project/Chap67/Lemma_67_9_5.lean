module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.LocalAtTarget
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.9.5: Universal closedness of a morphism of algebraic spaces is
 equivalent to the scheme, affine, étale-atlas, and Zariski-cover tests. -/
@[stacks 03IT] #check (AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE [AlgebraicGeometry.AlgebraicSpace.UniversallyClosed f,
      AlgebraicGeometry.AlgebraicSpace.Closed.forallScheme f,
      AlgebraicGeometry.AlgebraicSpace.Closed.forallAffine f,
      AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.existsEtaleOnTarget f,
      AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.existsZariskiCover f])
