/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Comparison.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Unit.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Counit.Construction
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Relative inertia comparison equivalence construction

This module owns the explicit quasi-inverse and the equivalence instances for the
relative-inertia diagonal comparison. Component readouts live in `Computations`.
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

/-- Explicit heterogeneous quasi-inverse data for the canonical relative-inertia comparison. -/
@[stacks 034H "relative-inertia diagonal-comparison quasi-inverse"]
noncomputable def RelativeInertia.diagonalComparison.quasiInverse (F : X ⥤ᵇ Y) :
    BasedFunctor.QuasiInverse (RelativeInertia.diagonalComparison F) where
  inverse := RelativeInertia.diagonalComparison.inverse F
  unitIso := RelativeInertia.diagonalComparison.unitIso F
  counitIso := RelativeInertia.diagonalComparison.counitIso F

/-- The canonical relative-inertia diagonal comparison is an equivalence over the base. -/
@[stacks 034H "diagonal comparison is an equivalence"]
instance RelativeInertia.diagonalComparison.isEquivalence (F : X ⥤ᵇ Y) :
    (RelativeInertia.diagonalComparison F).IsEquivalence := sorry
/- Proof strategy: apply `BasedFunctor.QuasiInverse.isEquivalence` to
`RelativeInertia.diagonalComparison.quasiInverse F`. -/

/-- The explicit inverse to the relative-inertia comparison is itself an equivalence over the
base. -/
@[stacks 034H "diagonal-comparison inverse is an equivalence"]
instance RelativeInertia.diagonalComparison.inverse.isEquivalence (F : X ⥤ᵇ Y) :
    (RelativeInertia.diagonalComparison.inverse F).IsEquivalence := sorry
/- Proof strategy: reverse `RelativeInertia.diagonalComparison.quasiInverse F` with
`BasedFunctor.QuasiInverse.symm`, then use `BasedFunctor.QuasiInverse.isEquivalence`. -/

end BasedFunctor

end CategoryTheory
