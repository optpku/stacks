/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Localization.RightFraction.FiniteLimits
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u vD uD

variable {C : Type u} [Category.{v} C]
variable {D : Type uD} [Category.{vD} D]
variable (L : C ⥤ D) (W : MorphismProperty C)
variable [L.IsLocalization W] [W.HasRightCalculusOfFractions]

/- Lemma 4.27.17: a localization functor for a right multiplicative system preserves finite
limits. -/
@[stacks 05Q6]
#check (Functor.IsLocalization.preservesFiniteLimits L W : PreservesFiniteLimits L)
