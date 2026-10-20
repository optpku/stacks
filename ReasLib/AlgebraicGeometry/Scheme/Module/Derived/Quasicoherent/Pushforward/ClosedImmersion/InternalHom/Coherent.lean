/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.FiniteCohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Coherent.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.ClosedImmersion.InternalHom

/-!
# Coherent internal Hom for closed immersions

This module restricts bounded-below internal Hom for a closed immersion to derived objects
with coherent cohomology over a locally Noetherian target.
-/

@[expose] public section

open CategoryTheory
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a closed immersion `i : Z ⟶ X` with `X` locally Noetherian, derived internal Hom
from `𝒪_Z` maps bounded-below complexes with coherent cohomology on `X` to bounded-below
complexes with coherent cohomology on `Z`. -/
theorem closedImmersionInternalHomPlus_coherent {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsLocallyNoetherian X] [IsClosedImmersion i]
    (K : D⁺[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf]) :
    DerivedCategory.Plus.cohomologyIn
      (SheafOfModules.isCoherent Z.toRingedSpace.ringCatSheaf)
      (((coherentPlusInclusion X ⋙ closedImmersionInternalHomPlus i) ⋙
        (DerivedCategory.Plus.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty Z.toRingedSpace)).ι).obj K) := sorry

/-- Derived internal Hom from `𝒪_Z`, restricted to bounded-below complexes with coherent
cohomology along a closed immersion into a locally Noetherian scheme. -/
noncomputable def closedImmersionInternalHomCoherentPlus
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsLocallyNoetherian X] [IsClosedImmersion i] :
    D⁺[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf] ⥤
      D⁺[SheafOfModules.isCoherent Z.toRingedSpace.ringCatSheaf] :=
  (DerivedCategory.Plus.cohomologyIn
    (SheafOfModules.isCoherent Z.toRingedSpace.ringCatSheaf)).lift
      ((coherentPlusInclusion X ⋙ closedImmersionInternalHomPlus i) ⋙
        (DerivedCategory.Plus.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty Z.toRingedSpace)).ι)
      (closedImmersionInternalHomPlus_coherent i)

/-- Forgetting coherent cohomology identifies the restricted functor with
`closedImmersionInternalHomPlus i` applied after `coherentPlusInclusion X`. -/
theorem closedImmersionInternalHomCoherentPlus_obj_obj
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsLocallyNoetherian X] [IsClosedImmersion i]
    (K : D⁺[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf]) :
    ((closedImmersionInternalHomCoherentPlus i).obj K).obj =
      ((closedImmersionInternalHomPlus i).obj ((coherentPlusInclusion X).obj K)).obj := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
