/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Equidimensional
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Fppf descent of equidimensional relative cycles

Equidimensionality of a relative cycle may be checked after base change along
an fppf covering of the base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
open scoped AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.RelativeCycle

/-- A relative cycle on a locally finite-type morphism over a locally
Noetherian base is equidimensional if and only if all its base changes along
an indexed fppf covering are equidimensional. -/
theorem isEquidimensional_iff_of_fppfCovering
    {X S : Scheme.{u}} [IsLocallyNoetherian S] {f : X ⟶ S} [LocallyOfFiniteType f]
    {r : ℕ} (α : f.FiberCycleFamily r) (hα : IsRelative α)
    {ι : Type v} {Si : ι → Scheme.{u}} (g : (i : ι) → Si i ⟶ S)
    (hg : Scheme.FppfCovering (fun i ↦ Over.mk (g i))) :
    Equidimensional α ↔
      ∀ i, Equidimensional (FamilyOfCyclesOnFibres.baseChange f (g i) r α) := sorry

/-- A relative cycle on a locally finite-type morphism over a locally
Noetherian base is equidimensional if and only if its base change to every
member of an fppf cover is equidimensional. -/
@[stacks 0H5M]
theorem isEquidimensional_iff_of_fppfCover
    {X S : Scheme.{u}} [IsLocallyNoetherian S] {f : X ⟶ S} [LocallyOfFiniteType f]
    {r : ℕ} (α : f.FiberCycleFamily r) (hα : IsRelative α) (𝒰 : FppfCover.{u, v} S) :
    Equidimensional α ↔
      ∀ i : 𝒰.I₀, Equidimensional (FamilyOfCyclesOnFibres.baseChange f (𝒰.f i) r α) := by
  exact isEquidimensional_iff_of_fppfCovering α hα 𝒰.f 𝒰.mem₀

end AlgebraicGeometry.RelativeCycle
