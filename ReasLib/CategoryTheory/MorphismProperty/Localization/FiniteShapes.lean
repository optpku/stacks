module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-!
# Finite-shape preservation by localization functors

A localization admitting a left calculus of fractions preserves finite colimits; dually, one
admitting a right calculus preserves finite limits.  The model-independent theorems use the same
argument order, and canonical localization functors receive reusable instances.
-/

@[expose] public section

open CategoryTheory.Limits

universe vC uC vD uD

namespace CategoryTheory

open MorphismProperty

variable {C : Type uC} [Category.{vC} C]

namespace Functor.IsLocalization

/-- Lemma 4.27.9 (Stacks 05Q2): any localization model of a morphism property with a left calculus
of fractions preserves finite colimits. -/
@[stacks 05Q2 "left-fraction localizations preserve finite colimits"]
theorem preservesFiniteColimits
    {D : Type uD} [Category.{vD} D] (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.HasLeftCalculusOfFractions] :
    PreservesFiniteColimits L := sorry

/-- Lemma 4.27.17 (Stacks 05Q6): any localization model of a morphism property with a right
calculus of fractions preserves finite limits. -/
@[stacks 05Q6 "right-fraction localizations preserve finite limits"]
theorem preservesFiniteLimits
    {D : Type uD} [Category.{vD} D] (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.HasRightCalculusOfFractions] :
    PreservesFiniteLimits L := sorry

end Functor.IsLocalization

namespace MorphismProperty.LeftFraction.Localization

/-- The explicit left-fraction localization functor preserves finite colimits. -/
instance Q_preservesFiniteColimits
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] :
    PreservesFiniteColimits (Q W) := sorry

end MorphismProperty.LeftFraction.Localization

/-- The canonical localization functor preserves finite colimits under a left calculus of
fractions. -/
instance MorphismProperty.Q_preservesFiniteColimits
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] :
    PreservesFiniteColimits W.Q := sorry

/-- The canonical localization functor preserves finite limits under a right calculus of
fractions. -/
instance MorphismProperty.Q_preservesFiniteLimits
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions] :
    PreservesFiniteLimits W.Q := sorry

end CategoryTheory
