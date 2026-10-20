module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Local
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.12.1. Closed immersions are characterized by scheme and affine
base changes, a surjective étale scheme atlas, and a Zariski covering. -/
@[stacks 03M4]
#check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE [AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion f,
      AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.forallScheme f,
      AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.forallAffine f,
      AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.existsEtaleOnTarget f,
      AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.existsZariskiCover f])

/- Lemma 67.12.1. Open immersions are characterized by scheme and affine
base changes, a surjective étale scheme atlas, and a Zariski covering. -/
@[stacks 03M4]
#check (AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion.tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE [AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion f,
      AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion.forallScheme f,
      AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion.forallAffine f,
      AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion.existsEtaleOnTarget f,
      AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion.existsZariskiCover f])

/- Lemma 67.12.1. Immersions are characterized by scheme and affine
base changes, a surjective étale scheme atlas, and a Zariski covering. -/
@[stacks 03M4]
#check (AlgebraicGeometry.AlgebraicSpace.IsImmersion.tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE [AlgebraicGeometry.AlgebraicSpace.IsImmersion f,
      AlgebraicGeometry.AlgebraicSpace.IsImmersion.forallScheme f,
      AlgebraicGeometry.AlgebraicSpace.IsImmersion.forallAffine f,
      AlgebraicGeometry.AlgebraicSpace.IsImmersion.existsEtaleOnTarget f,
      AlgebraicGeometry.AlgebraicSpace.IsImmersion.existsZariskiCover f])
