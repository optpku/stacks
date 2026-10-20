/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ClosedSubset.SectionsWithSupport
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset

/-!
# Closed-support module functors on ringed spaces

This module specializes the coefficient-generic closed-support API to the structure sheaf of a
ringed space. The construction and its laws are owned by
`SheafOfModules.ClosedSubset.SectionsWithSupport`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ClosedSubset.SectionsWithSupport

variable (X : RingedSpace.{u}) (Z : Closeds X)

/-- The functor of `𝒪_X`-module sections supported on a closed subset. -/
@[stacks 0G6N "ringed-space closed-support functor"]
noncomputable abbrev functor :
    X.Modules ⥤ RingedSpace.ClosedSubset.Modules X Z :=
  SheafOfModules.ClosedSubset.SectionsWithSupport.functor X.ringCatSheaf Z

/-- Closed-subset module pushforward is left adjoint to the functor of supported sections. -/
@[stacks 0G6P "ringed-space closed-support adjunction"]
noncomputable abbrev adjunction :
    RingedSpace.ClosedSubset.pushforward X Z ⊣ functor X Z :=
  SheafOfModules.ClosedSubset.SectionsWithSupport.adjunction X.ringCatSheaf Z

end AlgebraicGeometry.RingedSpace.ClosedSubset.SectionsWithSupport
