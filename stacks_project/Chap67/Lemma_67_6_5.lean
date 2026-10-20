module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen.Locality
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.6.5: Universal openness of a morphism of algebraic spaces is
 equivalent to scheme and affine tests, étale target locality, and Zariski
 target locality. -/
@[stacks 03Z5] #check (AlgebraicGeometry.AlgebraicSpace.UniversallyOpen.tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE [AlgebraicGeometry.AlgebraicSpace.UniversallyOpen f,
      AlgebraicGeometry.AlgebraicSpace.UniversallyOpen.forallScheme f,
      AlgebraicGeometry.AlgebraicSpace.UniversallyOpen.forallAffine f,
      AlgebraicGeometry.AlgebraicSpace.UniversallyOpen.existsEtaleOnTarget f,
      AlgebraicGeometry.AlgebraicSpace.UniversallyOpen.existsZariskiCover f])
