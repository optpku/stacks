/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.LocalCohomology.Artinian
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/-- Positive-degree cohomology of a coherent module on the punctured spectrum of a
Noetherian local ring is Artinian over the ring, with scalars induced by the inclusion. -/
instance instIsArtinianCohomologySucc
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (F : (PuncturedSpectrum.scheme A).Modules) [F.IsCoherent] (i : ℕ) :
    IsArtinian A
      (Scheme.Hom.cohomology (PuncturedSpectrum.puncturedOpen A).ι F (i + 1)) := sorry

end AlgebraicGeometry.PuncturedSpectrum
