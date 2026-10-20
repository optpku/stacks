/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.DerivedCategory.TruncationSplitting
public import ReasLib.RingTheory.GlobalDimension.Injective

@[expose] public section

/-!
# Splitting over Rings of Global Dimension One

@stack 0EWX

This leaf hides the Ext-model and universe plumbing needed to specialize shifted-cohomology
splitting to module categories. Consumers provide only the canonical ring-level global-dimension
bound.
-/

noncomputable section

universe u

namespace DerivedCategory.ShiftedCohomology.Split

open CategoryTheory
open CategoryTheory.Limits

/-- A bounded derived object over a ring of global dimension at most one is a finite biproduct of
its shifted cohomology objects over a suitable interval. -/
@[stacks 0EWX "global-dimension-one specialization"]
theorem ofGlobalDimensionLEOne
    {R : Type u} [Ring R] [HasGlobalDimensionLE R 1]
    (K : DerivedCategory.Bounded (ModuleCat.{u} R)) :
    ∃ a b : ℤ, Nonempty (K.obj ≅ ⨁ on (ModuleCat.{u} R) K.obj a b) := sorry

end DerivedCategory.ShiftedCohomology.Split
