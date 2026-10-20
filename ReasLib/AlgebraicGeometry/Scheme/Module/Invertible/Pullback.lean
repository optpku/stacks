/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InvertiblePullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

/-!
# Pullback of invertible scheme modules

This file specializes the ringed-site preservation theorem to Mathlib's
`Scheme.Modules` presentation.  The specialization is a named bridge because
that presentation carries a distinct category instance.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

namespace Invertible

/-- Pullback along a scheme morphism preserves tensor-invertibility. -/
@[stacks 0B8P "pullback of an invertible module"]
theorem pullback {L : Y.Modules} (hL : Invertible L) :
    Invertible ((Scheme.Modules.pullback f).obj L) := sorry

end Invertible

/-- Pullback automatically transports the canonical invertibility instance. -/
@[stacks 0B8P "canonical pullback instance"]
instance pullback_isInvertible (L : Y.Modules) [Invertible L] :
    Invertible ((Scheme.Modules.pullback f).obj L) := sorry

end AlgebraicGeometry.Scheme.Modules
