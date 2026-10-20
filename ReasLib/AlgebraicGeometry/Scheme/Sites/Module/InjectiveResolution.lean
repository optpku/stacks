/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Injective resolutions on standard big sites

This module provides injective resolutions and explicit higher direct images
for module sheaves on standard big sites of schemes.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.StandardTopology.Big

/-- Module sheaves on a standard big site have injective resolutions at the
site's carrier universe. -/
theorem moduleCatHasInjectiveResolutions
    (τ : StandardTopology) (S : Scheme.{u}) :
    HasInjectiveResolutions
      (RingedSite.ModuleCat.{u + 1} (ringedSite τ S)) := sorry

/-- The degree-`i` higher direct image of a module sheaf along the standard
big-site morphism induced by a scheme morphism. -/
noncomputable def higherDirectImageModule (τ : StandardTopology)
    {S T : Scheme.{u}} (f : T ⟶ S)
    (ℱ : RingedSite.ModuleCat.{u + 1} (ringedSite τ T)) (i : ℕ) :
    RingedSite.ModuleCat.{u + 1} (ringedSite τ S) :=
  @RingedSite.Hom.higherDirectImageModule
    (ringedSite τ T) (ringedSite τ S) (pullbackRingedHom τ f)
    inferInstance inferInstance (moduleCatHasInjectiveResolutions τ T) ℱ i

end AlgebraicGeometry.StandardTopology.Big
