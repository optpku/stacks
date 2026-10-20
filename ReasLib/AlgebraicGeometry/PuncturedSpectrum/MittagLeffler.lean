/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Artinian
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.Artinian
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/-- Positive-degree cohomology of a sequential inverse system of coherent modules on the
punctured spectrum of a Noetherian local ring satisfies the Mittag-Leffler condition. -/
theorem isMittagLeffler_of_coherent
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (F : SequentialInverseSystem
      (RingedSpace.Coh (PuncturedSpectrum.scheme A).toRingedSpace))
    (i : ℕ) (hi : 0 < i) :
    SequentialInverseSystem.IsMittagLeffler
      (F ⋙ (SheafOfModules.isCoherent
        (PuncturedSpectrum.scheme A).ringCatSheaf).ι ⋙
        Scheme.Hom.cohomologyFunctor (PuncturedSpectrum.puncturedOpen A).ι i) := sorry

end AlgebraicGeometry.PuncturedSpectrum
