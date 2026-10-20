module

public import ReasLib.CategoryTheory.MorphismProperty.Localization.FiniteShapes
public import ReasLib.CategoryTheory.MorphismProperty.Localization.RightFraction.Quotient

/-!
# Finite limits in the right-fraction quotient

This leaf specializes the model-independent finite-limit theorem for right-calculus localizations
to the explicit right-fraction quotient functor.
-/

@[expose] public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory.MorphismProperty.RightFraction.Localization

variable {C : Type u} [Category.{v} C]

/-- The explicit right-fraction quotient functor preserves finite limits. -/
instance Q_preservesFiniteLimits
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions] :
    PreservesFiniteLimits (Q W) := sorry

end CategoryTheory.MorphismProperty.RightFraction.Localization
