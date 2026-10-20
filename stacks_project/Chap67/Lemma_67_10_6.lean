module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Monomorphism.Locality
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.10.6: monomorphisms of algebraic spaces are detected by scheme-valued
and affine base changes, surjective étale scheme atlases, and Zariski coverings. -/
@[stacks 042Q] #check (AlgebraicGeometry.AlgebraicSpace.Monomorphisms.tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE [Mono f,
      AlgebraicGeometry.AlgebraicSpace.Monomorphisms.forallScheme f,
      AlgebraicGeometry.AlgebraicSpace.Monomorphisms.forallAffine f,
      AlgebraicGeometry.AlgebraicSpace.Monomorphisms.existsEtaleOnTarget f,
      AlgebraicGeometry.AlgebraicSpace.Monomorphisms.existsZariskiCover f])
