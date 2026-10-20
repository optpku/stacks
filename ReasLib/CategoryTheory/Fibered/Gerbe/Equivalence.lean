/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Fiber
public import ReasLib.CategoryTheory.Fibered.Gerbe.Basic

/-!
# Gerbes and equivalences over the base

The gerbe condition depends only on the equivalence class of a category over the base.  The API
is stated for arbitrary projection functors rather than for one particular bundled category of
stacks; bundled applications use their underlying based functor directly.
-/

@[expose] public section

universe uC vC uX vX uY vY

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {X : Type uX} {Y : Type uY}
variable [Category.{vX} X] [Category.{vY} Y]
variable {J : GrothendieckTopology C} {pX : X ⥤ C} {pY : Y ⥤ C}

namespace IsGerbe

/-- A based equivalence transports the gerbe condition from its source projection to its target
projection. -/
@[stacks 06P0 "forward"]
theorem of_isEquivalence
    (F : BasedCategory.ofFunctor pX ⥤ᵇ BasedCategory.ofFunctor pY)
    (hF : F.IsEquivalence) (hX : IsGerbe J pX) :
    IsGerbe J pY := sorry

/-- Lemma 8.11.2 (tag 06P0): the gerbe condition is invariant under equivalence over the base
category. -/
@[stacks 06P0]
theorem iff_of_isEquivalence
    (F : BasedCategory.ofFunctor pX ⥤ᵇ BasedCategory.ofFunctor pY)
    (hF : F.IsEquivalence) :
    IsGerbe J pX ↔ IsGerbe J pY := sorry

end IsGerbe

end CategoryTheory
