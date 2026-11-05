/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.LocallyFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Rank.Invertible
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

/-!
# Finite local rank for scheme modules

This leaf specializes the generic ringed-site finite-local-freeness predicates
to modules on the opens site of a scheme.  It is intentionally an abbreviation
layer: the defining mathematics remains owned by `SheafOfModules`.
-/

@[expose] public section

open AlgebraicGeometry
open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A scheme module is finite locally free when it is finite locally free on
the opens ringed site of the scheme. -/
abbrev IsFiniteLocallyFree (F : X.Modules) : Prop :=
  SheafOfModules.IsFiniteLocallyFree F

/-- A scheme module is finite locally free of rank `r` when it has that rank
on the opens ringed site of the scheme. -/
abbrev IsFiniteLocallyFreeOfRank (r : ℕ) (F : X.Modules) : Prop :=
  SheafOfModules.IsFiniteLocallyFreeOfRank r F

/-- A fixed finite local rank supplies finite local freeness for a scheme
module. -/
theorem isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
    (r : ℕ) (F : X.Modules) [IsFiniteLocallyFreeOfRank r F] :
    IsFiniteLocallyFree F := sorry

/-- Pullback of scheme modules preserves finite local freeness of a prescribed rank. -/
instance pullback_isFiniteLocallyFreeOfRank
    {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] :
    IsFiniteLocallyFreeOfRank r ((pullback f).obj F) := sorry

/-- Pullback of scheme modules preserves finite local freeness. -/
instance pullback_isFiniteLocallyFree
    {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules) [IsFiniteLocallyFree F] :
    IsFiniteLocallyFree ((pullback f).obj F) := by
  letI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction f).isRightAdjoint
  change SheafOfModules.IsFiniteLocallyFree
    ((SheafOfModules.pullback f.toRingCatSheafHom).obj F)
  exact SheafOfModules.pullback_isFiniteLocallyFree f.toRingCatSheafHom F

/-- An invertible scheme module has finite local rank one. This is an explicit theorem rather
than a reverse instance, keeping typeclass search acyclic with the rank-one-to-invertible
instance. -/
theorem isFiniteLocallyFreeOfRankOne_of_invertible
    [CategoryTheory.MonoidalCategory X.Modules] (F : X.Modules) [Invertible F] :
    IsFiniteLocallyFreeOfRank 1 F := sorry

/-- A scheme module of finite local rank one is quasi-coherent. -/
instance instIsQuasicoherentOfRankOne {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFreeOfRank 1 L] :
    L.IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme.Modules
