/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Equivalence.Construction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Relative inertia comparison equivalence computations

This module exposes the quasi-inverse projections without making them part of the
construction owner.
-/

open CategoryTheory
open CategoryTheory.Limits
open BasedCategory
open BasedFunctor
open scoped Bicategory

universe uC vC

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]

namespace BasedFunctor

variable {X Y : BasedCategory C}

/-- The inverse in the explicit comparison quasi-inverse data is the recovered comparison
inverse. -/
@[simp, stacks 034H "diagonal-comparison quasi-inverse map computation"]
theorem RelativeInertia.diagonalComparison.quasiInverse.inverse (F : X ⥤ᵇ Y) :
    (RelativeInertia.diagonalComparison.quasiInverse F).inverse =
      RelativeInertia.diagonalComparison.inverse F := sorry

/-- The unit in the explicit comparison quasi-inverse data is the canonical identity-component
unit. -/
@[simp, stacks 034H "diagonal-comparison quasi-inverse unit computation"]
theorem RelativeInertia.diagonalComparison.quasiInverse.unitIso (F : X ⥤ᵇ Y) :
    (RelativeInertia.diagonalComparison.quasiInverse F).unitIso =
      RelativeInertia.diagonalComparison.unitIso F := sorry

/-- The counit in the explicit comparison quasi-inverse data is the canonical comparison counit. -/
@[simp, stacks 034H "diagonal-comparison quasi-inverse counit computation"]
theorem RelativeInertia.diagonalComparison.quasiInverse.counitIso (F : X ⥤ᵇ Y) :
    (RelativeInertia.diagonalComparison.quasiInverse F).counitIso =
      RelativeInertia.diagonalComparison.counitIso F := sorry

end BasedFunctor

end CategoryTheory
