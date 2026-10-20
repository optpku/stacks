/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.LocalCohomology.MittagLeffler
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.MittagLeffler

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 52.5.2 (1): applying local cohomology supported at the maximal ideal to a
sequential inverse system of finite modules over a Noetherian local ring gives a
Mittag-Leffler system in every degree. -/
@[stacks 0DX1] #check (localCohomology.isMittagLeffler_of_finite :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : SequentialInverseSystem (FGModuleCat.{u} A)) (i : ℕ),
    SequentialInverseSystem.IsMittagLeffler
      (M ⋙ (ModuleCat.isFG A).ι ⋙
        localCohomology (IsLocalRing.maximalIdeal A) i))

/- Lemma 52.5.2 (2): applying positive-degree cohomology on the punctured spectrum
to a sequential inverse system of coherent modules gives a Mittag-Leffler system. -/
@[stacks 0DX1] #check (AlgebraicGeometry.PuncturedSpectrum.isMittagLeffler_of_coherent :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (F : SequentialInverseSystem
      (RingedSpace.Coh (PuncturedSpectrum.scheme A).toRingedSpace))
    (i : ℕ) (hi : 0 < i),
    SequentialInverseSystem.IsMittagLeffler
      (F ⋙ (SheafOfModules.isCoherent
        (PuncturedSpectrum.scheme A).ringCatSheaf).ι ⋙
        Scheme.Hom.cohomologyFunctor (PuncturedSpectrum.puncturedOpen A).ι i))
