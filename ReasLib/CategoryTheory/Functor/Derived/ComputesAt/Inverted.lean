/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived values of functors which invert denominators

A functor which already inverts the chosen denominator class needs no replacement before deriving.
This leaf records the source-strength everywhere-defined and computation statements, independently
of complexes or a particular localization model.

The statements require the calculus of fractions used in the source situation (a saturated
multiplicative system); without it, even `F = W.Q` need not have an essentially constant indexing
diagram. See `ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Stability` for a counterexample.
-/

universe vC vD uC uD

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

/-- If `W` has a left calculus of fractions, a functor which inverts `W` has a source-defined
right derived value at every object. -/
theorem RightDerived.EverywhereDefined.of_isInvertedBy
    (F : C ⥤ D) (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (hF : W.IsInvertedBy F) :
    RightDerived.EverywhereDefined F W := sorry

/-- If `W` has a right calculus of fractions, a functor which inverts `W` has a source-defined
left derived value at every object. -/
theorem LeftDerived.EverywhereDefined.of_isInvertedBy
    (F : C ⥤ D) (W : MorphismProperty C) [W.HasRightCalculusOfFractions] (hF : W.IsInvertedBy F) :
    LeftDerived.EverywhereDefined F W := sorry

/-- If `W` has a left calculus of fractions and `F` inverts `W`, every object already computes
the right derived value of `F`. -/
theorem RightDerived.ComputesAt.of_isInvertedBy
    (F : C ⥤ D) (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    (hF : W.IsInvertedBy F) (X : C) :
    RightDerived.ComputesAt F W X := sorry

/-- If `W` has a right calculus of fractions and `F` inverts `W`, every object already computes
the left derived value of `F`. -/
theorem LeftDerived.ComputesAt.of_isInvertedBy
    (F : C ⥤ D) (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (hF : W.IsInvertedBy F) (X : C) :
    LeftDerived.ComputesAt F W X := sorry

end CategoryTheory.Functor
