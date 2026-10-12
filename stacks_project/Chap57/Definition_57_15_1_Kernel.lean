/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap57.Lemma_57_14_1_Category

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- A perfect kernel on `X ×_S Y` is the Fourier--Mukai kernel of a relative
equivalence from `X` to `Y` over `S` when its isomorphism class is invertible
in the Fourier--Mukai category of Section 57.14. -/
class FourierMukaiObject.IsRelativeEquivalenceKernel {S : Scheme.{u}}
    {X Y : FourierMukaiObject S}
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace) : Prop where
  isIso : @IsIso (FourierMukaiObject S) (fourierMukaiObjectCategory S) X Y (Quotient.mk'' K)

/-- Invertible kernel classes are relative equivalence kernels. -/
instance FourierMukaiObject.instIsRelativeEquivalenceKernelOfIsIso
    {S : Scheme.{u}} {X Y : FourierMukaiObject S}
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace)
    [h : @IsIso (FourierMukaiObject S) (fourierMukaiObjectCategory S) X Y (Quotient.mk'' K)] :
    FourierMukaiObject.IsRelativeEquivalenceKernel K where
  isIso := h

/-- Relative equivalence kernels have invertible isomorphism classes. -/
theorem FourierMukaiObject.isRelativeEquivalenceKernel_isIso {S : Scheme.{u}}
    {X Y : FourierMukaiObject S}
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace)
    [FourierMukaiObject.IsRelativeEquivalenceKernel K] :
    @IsIso (FourierMukaiObject S) (fourierMukaiObjectCategory S) X Y (Quotient.mk'' K) := sorry

/-- A perfect kernel is a relative equivalence kernel if and only if it admits a
perfect inverse kernel on `Y ×_S X` whose derived convolutions recover the
relative diagonal kernels. -/
theorem FourierMukaiObject.isRelativeEquivalenceKernel_iff {S : Scheme.{u}}
    {X Y : FourierMukaiObject S}
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace) :
    FourierMukaiObject.IsRelativeEquivalenceKernel K ↔
      ∃ K' : @RingedSpace.ModuleDerived.Perfect
          (Limits.pullback Y.hom X.hom).toRingedSpace,
        CategoryTheory.IsIsomorphic
            (FourierMukaiObject.convolutionKernel X Y X K K')
            (FourierMukaiObject.diagonalKernel X) ∧
          CategoryTheory.IsIsomorphic
            (FourierMukaiObject.convolutionKernel Y X Y K' K)
            (FourierMukaiObject.diagonalKernel Y) := sorry

/-- The relative diagonal kernel is the identity relative equivalence. -/
instance FourierMukaiObject.instIsRelativeEquivalenceKernelDiagonal
    {S : Scheme.{u}} (X : FourierMukaiObject S) :
    FourierMukaiObject.IsRelativeEquivalenceKernel
      (FourierMukaiObject.diagonalKernel X) := sorry
