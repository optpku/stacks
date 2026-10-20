/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.Additive

import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
Additivity of pushforward for modules on ringed spaces.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

/-- Pushforward along a morphism of ringed spaces is a right adjoint. -/
@[stacks 0715 "Pushforward is a right adjoint"]
theorem pushforwardIsRightAdjoint {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (pushforward f).IsRightAdjoint := sorry

end AlgebraicGeometry.RingedSpace.Hom
