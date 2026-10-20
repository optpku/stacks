/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FourierMukai.KernelCategory

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- The isomorphism class of a perfect kernel on `X ×_S Y` is invertible if
and only if it admits a perfect inverse kernel on `Y ×_S X` whose two derived
convolutions are isomorphic to the respective relative diagonal kernels. -/
theorem FourierMukaiObject.isRelativeEquivalenceKernel_iff {S : Scheme.{u}}
    {X Y : FourierMukaiObject S}
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace) :
    IsIso (C := FourierMukaiObject S) (Quotient.mk'' K : X ⟶ Y) ↔
      ∃ K' : @RingedSpace.ModuleDerived.Perfect
          (Limits.pullback Y.hom X.hom).toRingedSpace,
        CategoryTheory.IsIsomorphic
            (FourierMukaiObject.convolutionKernel X Y X K K')
            (FourierMukaiObject.diagonalKernel X) ∧
          CategoryTheory.IsIsomorphic
            (FourierMukaiObject.convolutionKernel Y X Y K' K)
            (FourierMukaiObject.diagonalKernel Y) := sorry

/-- Arbitrary base change carries an invertible perfect kernel class to the
invertible class of its derived pullback along the comparison of relative products. -/
instance FourierMukaiObject.instIsRelativeEquivalenceKernel_modulePullback
    {S S' : Scheme.{u}} (g : S' ⟶ S) {X Y : FourierMukaiObject S}
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace)
    [IsIso (C := FourierMukaiObject S) (Quotient.mk'' K : X ⟶ Y)] :
    IsIso (C := FourierMukaiObject S')
      (Quotient.mk'' (FourierMukaiObject.modulePullbackKernel g K) :
        FourierMukaiObject.baseChange g X ⟶ FourierMukaiObject.baseChange g Y) :=
  sorry
