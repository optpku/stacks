/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.DimensionOne
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback

/-!
# Proper descent for Picard groups

This file characterizes Picard classes descending along suitable proper morphisms of
Noetherian schemes with one-dimensional fibres.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- For a proper morphism of Noetherian schemes whose structure-sheaf pushforward map is an
isomorphism, whose fibres have dimension at most one, and whose fibre structure sheaves have
vanishing first cohomology, pullback on Picard groups is injective and its range consists
exactly of the classes restricting to zero on every fibre. -/
theorem picardPullback_identifies_fiberwiseTrivial
    (f : X ⟶ Y) [IsNoetherian X] [IsNoetherian Y] [IsProper f]
    [IsIso (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞))
    (hH1 : ∀ y : Y,
      IsZero (Scheme.Modules.cohomology
        (SheafOfModules.unit (f.fiber y).ringCatSheaf) 1)) :
    Function.Injective (picardPullback f) ∧
      (picardPullback f).range = ⨅ y : Y, (picardPullback (f.fiberι y)).ker := sorry

end AlgebraicGeometry.Scheme.Hom
