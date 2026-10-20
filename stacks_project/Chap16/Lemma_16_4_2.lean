/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.NeronBlowup.Localization
public import ReasLib.RingTheory.Smooth.NeronBlowup.Source

@[expose] public section

/- Lemma 16.4.2 (1): affine Neron blowups commute with localization away from the closed
center. -/
@[stacks 0BJ3]
#check @Algebra.DVR.Factorization.localizationComparison_bijective

/- Lemma 16.4.2 (2): for a surjective flat finite-type source presentation, quotienting the
base-changed source chart by uniformizer-power torsion gives the affine Neron blowup. -/
@[stacks 0BJ3] #check
  fun {R L B : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing L] [IsDomain L] [IsDiscreteValuationRing L]
    [Algebra R L] [IsExtensionOfDiscreteValuationRings R L]
    [IsExtensionOfDiscreteValuationRings.WeaklyUnramified R L]
    (S : Algebra.DVR.Factorization R L)
    [CommRing B] [Algebra R B] [Algebra B S.mid]
    [IsScalarTower R B S.mid] [Module.Flat R B]
    [Algebra.FiniteType R B]
    (π : R) (hπ : Irreducible π)
    (h : Function.Surjective (algebraMap B S.mid)) ↦
      Algebra.DVR.Factorization.NeronBlowup.Source.quotientComparison.bijective
        S π hπ h

/- The source-facing map lands directly in the affine Neron blowup; no codomain cast is exposed. -/
#check @Algebra.DVR.Factorization.NeronBlowup.Source.comparison
#check @Algebra.DVR.Factorization.NeronBlowup.Source.quotientComparison
#check @Algebra.DVR.Factorization.NeronBlowup.Source.center_eq

/- The reusable 0BIP core separates base-change surjectivity, kernel, and quotient properties. -/
#check @AffineBlowupChart.tensorMap.surjective
#check @AffineBlowupChart.tensorMap.ker_eq_powerTorsion
#check @AffineBlowupChart.tensorMap.mem_ker_iff
#check @AffineBlowupChart.tensorQuotientMap.bijective

/- The Neron specialization is a thin namespace layer over the generic chart API. -/
#check @Algebra.DVR.Factorization.NeronBlowup.Source.comparison.surjective
#check @Algebra.DVR.Factorization.NeronBlowup.Source.comparison.ker_eq_powerTorsion
#check @Algebra.DVR.Factorization.NeronBlowup.Source.comparison.mem_ker_iff
#check @Algebra.DVR.Factorization.NeronBlowup.Source.quotientComparison.bijective
