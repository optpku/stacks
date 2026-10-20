/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.GaussManin.SpectralSequence
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.DerivedCategory
open AlgebraicGeometry.Scheme.Modules.Kunneth
open SheafOfModules SheafOfModules.RingedSite RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/-- If a smooth proper morphism lies in a commuting triangle over a rational base scheme, then
its relative de Rham cohomology sheaves are finite locally free. -/
theorem relativeDeRhamCohomology_isFiniteLocallyFree
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (a : X ⟶ S) (b : Y ⟶ S)
    (sq : CommSq f a b (𝟙 S)) [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    [IsProper f] [S.Over (Spec (CommRingCat.of (ULift.{u} ℚ)))]
    [hPush : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u, u, u, u} (coefficientSite f))]
    [hRestr : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (scalarRestrictionHom b))
      (ModuleQis.{u, u, u, u} (coefficientSite (𝟙 Y)))]
    [hRelative : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (relativePushforwardHom sq))
      (ModuleQis.{u, u, u, u} (coefficientSite a))]
    [hTensor : @DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
        (coefficientSite (𝟙 Y))) _ _ _ _ _ _ _]
    (q : ℤ) :
    SheafOfModules.IsFiniteLocallyFree (relativeDeRhamCohomology f q) := sorry

end AlgebraicGeometry.Scheme.DeRham
