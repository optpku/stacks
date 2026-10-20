module

public import ReasLib.AlgebraicGeometry.Scheme.FourierMukai.RelativeEquivalence

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- A perfect kernel is a relative equivalence kernel when its isomorphism
class is invertible in the Fourier--Mukai category. -/
abbrev FourierMukaiObject.IsRelativeEquivalenceKernel {S : Scheme.{u}}
    {X Y : FourierMukaiObject S}
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace) : Prop :=
  IsIso (C := FourierMukaiObject S) (Quotient.mk'' K : X ⟶ Y)

#check (FourierMukaiObject.IsRelativeEquivalenceKernel :
  ∀ {S : Scheme.{u}} {X Y : FourierMukaiObject S},
    @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace → Prop)

#check (FourierMukaiObject.isRelativeEquivalenceKernel_iff :
  ∀ {S : Scheme.{u}} {X Y : FourierMukaiObject S}
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace),
    FourierMukaiObject.IsRelativeEquivalenceKernel K ↔
      ∃ K' : @RingedSpace.ModuleDerived.Perfect
          (Limits.pullback Y.hom X.hom).toRingedSpace,
        CategoryTheory.IsIsomorphic
            (FourierMukaiObject.convolutionKernel X Y X K K')
            (FourierMukaiObject.diagonalKernel X) ∧
          CategoryTheory.IsIsomorphic
            (FourierMukaiObject.convolutionKernel Y X Y K' K)
            (FourierMukaiObject.diagonalKernel Y))

#check (CategoryTheory.IsIso.id (C := FourierMukaiObject _) :
  ∀ {S : Scheme.{u}} (X : FourierMukaiObject S),
    FourierMukaiObject.IsRelativeEquivalenceKernel
      (FourierMukaiObject.diagonalKernel X))
