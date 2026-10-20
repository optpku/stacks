module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Locality
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 67.4.12: the six locality criteria for Separated. -/
@[stacks 03KM] #check (AlgebraicGeometry.AlgebraicSpace.Separated.tfae :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE [AlgebraicGeometry.AlgebraicSpace.Separated f,
      AlgebraicGeometry.AlgebraicSpace.Separated.forallScheme f,
      AlgebraicGeometry.AlgebraicSpace.Separated.forallAffine f,
      AlgebraicGeometry.AlgebraicSpace.Separated.forallAffineSpace f,
      AlgebraicGeometry.AlgebraicSpace.Separated.existsEtaleOnTarget f,
      AlgebraicGeometry.AlgebraicSpace.Separated.existsZariskiCover f])

/- Lemma 67.4.12: the six locality criteria for LocallySeparated. -/
@[stacks 03KM] #check (AlgebraicGeometry.AlgebraicSpace.LocallySeparated.tfae :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE [AlgebraicGeometry.AlgebraicSpace.LocallySeparated f,
      AlgebraicGeometry.AlgebraicSpace.LocallySeparated.forallScheme f,
      AlgebraicGeometry.AlgebraicSpace.LocallySeparated.forallAffine f,
      AlgebraicGeometry.AlgebraicSpace.LocallySeparated.forallAffineSpace f,
      AlgebraicGeometry.AlgebraicSpace.LocallySeparated.existsEtaleOnTarget f,
      AlgebraicGeometry.AlgebraicSpace.LocallySeparated.existsZariskiCover f])

/- Lemma 67.4.12: the six locality criteria for QuasiSeparated. -/
@[stacks 03KM] #check (AlgebraicGeometry.AlgebraicSpace.QuasiSeparated.tfae :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE [AlgebraicGeometry.AlgebraicSpace.QuasiSeparated f,
      AlgebraicGeometry.AlgebraicSpace.QuasiSeparated.forallScheme f,
      AlgebraicGeometry.AlgebraicSpace.QuasiSeparated.forallAffine f,
      AlgebraicGeometry.AlgebraicSpace.QuasiSeparated.forallAffineSpace f,
      AlgebraicGeometry.AlgebraicSpace.QuasiSeparated.existsEtaleOnTarget f,
      AlgebraicGeometry.AlgebraicSpace.QuasiSeparated.existsZariskiCover f])

