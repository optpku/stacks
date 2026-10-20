/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek.Proper

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.Bounded
open DerivedCategory.TStructure
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The canonical inclusion of bounded complexes with coherent cohomology into the
unbounded derived category of quasicoherent complexes. -/
noncomputable def coherentBoundedToDerivedQCoh (X : Scheme.{u}) [IsLocallyNoetherian X] :
    Dᵇ[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf] ⥤ DerivedQCoh X :=
  CohomologyIn.toUnbounded
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ⋙
    coherentInclusion X

/-- Forgetting boundedness and coherence through `coherentBoundedToDerivedQCoh` leaves the
underlying unbounded derived object unchanged. -/
theorem coherentBoundedToDerivedQCoh_obj_obj (X : Scheme.{u}) [IsLocallyNoetherian X]
    (K : Dᵇ[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf]) :
    ((coherentBoundedToDerivedQCoh X).obj K).obj =
      DerivedCategory.Bounded.ι.obj K.obj := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
