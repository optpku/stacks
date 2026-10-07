module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Sheaf

/-!
# Compatibility checks for chosen big h-site sheaf criteria

The sheaf criterion and its affine reduction are available from their
mathematical library owner.
-/

open CategoryTheory

universe u v w

variable (X : AlgebraicGeometry.ChosenBigHSite.{u, v}) (S : X.carrier)
  (F : (Over S)ᵒᵖ ⥤ Type w)

#check
  (AlgebraicGeometry.ChosenBigHSite.Sheaf.iffZariskiAndEqualizer X S F :
    Presheaf.IsSheaf (AlgebraicGeometry.ChosenBigHSite.bigTopology X S) F ↔
      Presheaf.IsSheaf
          (AlgebraicGeometry.ChosenBigHSite.bigZariskiTopology X S) F ∧
        AlgebraicGeometry.ChosenBigHSite.Equalizer.IsProperSurjective X S F)

#check
  (AlgebraicGeometry.ChosenBigHSite.Equalizer.iffAffine X S F :
    Presheaf.IsSheaf
        (AlgebraicGeometry.ChosenBigHSite.bigZariskiTopology X S) F →
      (AlgebraicGeometry.ChosenBigHSite.Equalizer.IsProperSurjective X S F ↔
        AlgebraicGeometry.ChosenBigHSite.Equalizer.IsAffineProperSurjective X S F))
