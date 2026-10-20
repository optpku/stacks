/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.Affine
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 52.16.6 -/
@[stacks 0EIN]
#check
  (AlgebraicGeometry.AffineAlgebraizationSetup.extends_iff_completion_after_adicPullback :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AlgebraicGeometry.AffineAlgebraizationSetup A)
      (F : AlgebraicGeometry.Scheme.CoherentFormalModules S.U.toScheme
        ((AlgebraicGeometry.Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
      (pullback : AlgebraicGeometry.Scheme.CoherentFormalModules S.U.toScheme
          ((AlgebraicGeometry.Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) ⥤
        AlgebraicGeometry.Scheme.CoherentFormalModules S.completionOpen.toScheme
          S.completionIdealOnOpen)
      (h_pullback : AlgebraicGeometry.Scheme.IsCoherentFormalModulesPullbackFunctor
        S.completionOpenMap
        ((AlgebraicGeometry.Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) pullback),
      (AlgebraicGeometry.Scheme.coherentFormalModulesRestrictionFunctor
        (AlgebraicGeometry.Scheme.idealSheafDataOfIdealOnSpec S.I) S.U).essImage F ↔
        (AlgebraicGeometry.Scheme.CoherentCompletion.functor S.completionIdealOnOpen).essImage
          (pullback.obj F))
