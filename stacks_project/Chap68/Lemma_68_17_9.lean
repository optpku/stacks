module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions.Locality
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 68.17.9: locality of PropertyBeta morphisms. -/
@[stacks 03L3] #check (AlgebraicGeometry.AlgebraicSpace.PropertyBeta.tfae :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      List.TFAE [
        AlgebraicGeometry.AlgebraicSpace.PropertyBeta f,
        AlgebraicGeometry.AlgebraicSpace.PropertyBeta.forallAffine f,
        AlgebraicGeometry.AlgebraicSpace.PropertyBeta.forallAffineObject f,
        AlgebraicGeometry.AlgebraicSpace.PropertyBeta.existsZariskiCover f,
        AlgebraicGeometry.AlgebraicSpace.PropertyBeta.existsEtaleOnTarget f])

/- Lemma 68.17.9: locality of Decent morphisms. -/
@[stacks 03L3] #check (AlgebraicGeometry.AlgebraicSpace.Decent.tfae :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      List.TFAE [
        AlgebraicGeometry.AlgebraicSpace.Decent f,
        AlgebraicGeometry.AlgebraicSpace.Decent.forallAffine f,
        AlgebraicGeometry.AlgebraicSpace.Decent.forallAffineObject f,
        AlgebraicGeometry.AlgebraicSpace.Decent.existsZariskiCover f,
        AlgebraicGeometry.AlgebraicSpace.Decent.existsEtaleOnTarget f])

/- Lemma 68.17.9: locality of Reasonable morphisms. -/
@[stacks 03L3] #check (AlgebraicGeometry.AlgebraicSpace.Reasonable.tfae :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      List.TFAE [
        AlgebraicGeometry.AlgebraicSpace.Reasonable f,
        AlgebraicGeometry.AlgebraicSpace.Reasonable.forallAffine f,
        AlgebraicGeometry.AlgebraicSpace.Reasonable.forallAffineObject f,
        AlgebraicGeometry.AlgebraicSpace.Reasonable.existsZariskiCover f,
        AlgebraicGeometry.AlgebraicSpace.Reasonable.existsEtaleOnTarget f])

/- Lemma 68.17.9: locality of VeryReasonable morphisms. -/
@[stacks 03L3] #check (AlgebraicGeometry.AlgebraicSpace.VeryReasonable.tfae :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      List.TFAE [
        AlgebraicGeometry.AlgebraicSpace.VeryReasonable f,
        AlgebraicGeometry.AlgebraicSpace.VeryReasonable.forallAffine f,
        AlgebraicGeometry.AlgebraicSpace.VeryReasonable.forallAffineObject f,
        AlgebraicGeometry.AlgebraicSpace.VeryReasonable.existsZariskiCover f])

