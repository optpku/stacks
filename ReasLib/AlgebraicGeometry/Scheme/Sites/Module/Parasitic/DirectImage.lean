/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Presheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.InjectiveResolution
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Parasitic.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Parasitic.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Pullback

/-!
# Direct images of parasitic module sheaves

This module records that ordinary and higher direct images along morphisms of
schemes preserve flat-objectwise vanishing on standard big sites.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace SheafOfModules.IsParasiticOne

/-- The direct image of a parasitic module sheaf along a scheme morphism is
parasitic on the corresponding standard big site. -/
theorem modulePushforward
    {S T : Scheme.{u}} (τ : StandardTopology) (f : T ⟶ S)
    {ℱ : RingedSite.ModuleCat.{u + 1}
      (StandardTopology.Big.ringedSite τ T)} (hℱ : IsParasiticOne ℱ) :
    IsParasiticOne
      ((StandardTopology.Big.pullbackRingedHom τ f).modulePushforward.obj ℱ) := sorry

/-- Every higher direct image of a parasitic module sheaf along a scheme
morphism is parasitic on the corresponding standard big site. -/
theorem higherDirectImageModule
    {S T : Scheme.{u}} (τ : StandardTopology) (f : T ⟶ S)
    {ℱ : RingedSite.ModuleCat.{u + 1}
      (StandardTopology.Big.ringedSite τ T)} (hℱ : IsParasiticOne ℱ)
    (i : ℕ) :
    IsParasiticOne
      (StandardTopology.Big.higherDirectImageModule τ f ℱ i) := sorry

end SheafOfModules.IsParasiticOne
