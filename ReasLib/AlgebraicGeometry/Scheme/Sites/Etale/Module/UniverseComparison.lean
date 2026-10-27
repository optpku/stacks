/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.UniverseComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.LiftedStructureSheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.Small.ModuleUniverseComparison

/-- Modules on the small étale site lift by universe lifting their sections and
transporting coefficients to the lifted structure sheaf. -/
def lift (T : Scheme.{u}) :
    RingedSite.ModuleCat.{u} (ringedSite T) ⥤
      RingedSite.ModuleCat.{u + 1} (liftedRingedSite T) :=
  let coefficientIso : SheafOfModules.UniverseLift.ring (structureSheaf T) ≅
      (liftedRingedSite T).structureSheaf :=
    (fullyFaithfulSheafToPresheaf T.smallEtaleTopology RingCat.{u + 1}).preimageIso
      (NatIso.ofComponents (fun _ => Iso.refl _) (by intros; ext x; rfl))
  SheafOfModules.UniverseLift.functor (structureSheaf T) ⋙
    (SheafOfModules.CoefficientPresentation.equivalence coefficientIso).functor

/-- Sections of a lifted small étale module are literally universe lifts of
its original sections. -/
theorem lift_carrier (T : Scheme.{u}) (M : RingedSite.ModuleCat.{u} (ringedSite T))
    (V : T.Etaleᵒᵖ) :
    (((lift T).obj M).val.obj V : Type (u + 1)) = ULift.{u + 1} (M.val.obj V) := rfl

end AlgebraicGeometry.Scheme.Etale.Small.ModuleUniverseComparison
