module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiAffine.Locality
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

/- Lemma 67.21.3: representable quasi-affineness, quasi-affineness, quasi-affineness
on a surjective étale scheme atlas, and quasi-affineness on a Zariski covering of
the target are equivalent. -/
@[stacks 03WM] #check (AlgebraicGeometry.AlgebraicSpace.QuasiAffine.tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE [(over (@QuasiAffineHom : MorphismProperty Scheme.{u})).presheaf f,
      AlgebraicGeometry.AlgebraicSpace.QuasiAffine f,
      AlgebraicGeometry.AlgebraicSpace.QuasiAffine.existsEtaleOnTarget f,
      AlgebraicGeometry.AlgebraicSpace.QuasiAffine.existsZariskiCover f])
