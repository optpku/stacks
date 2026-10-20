module

public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.InGroupoids
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
public import ReasLib.CategoryTheory.Sites.Descent.Precoverage
public import ReasLib.CategoryTheory.Sites.Precoverage.Continuous
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of stacks on precoverage-presented sites

The first projection of a categorical pullback preserves stacks under coverwise continuity.
Only pullbacks along arrows in the selected covering families are required and preserved.
-/

@[expose] public section

universe uC uD uS vC vD vS

namespace CategoryTheory

open Limits

namespace Limits.CategoricalPullback.Left.Precoverage

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- Pullback along a continuous functor of precoverage-presented sites preserves stacks. -/
@[stacks 04WC "coverwise stack pullback closure"]
theorem isStackOnSite
    (P : CategoryTheory.Precoverage C) (Q : CategoryTheory.Precoverage D)
    (u : C ⥤ D) (p : S ⥤ D)
    [P.HasIsos] [P.HasPullbacks] [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition]
    [Functor.Precoverage.IsContinuous u P Q]
    [IsStack.OnSite Q.toGrothendieck p] :
    IsStack.OnSite P.toGrothendieck (π₁ u p) := sorry

/-- Pullback along a continuous functor of precoverage-presented sites preserves stacks in
groupoids. -/
@[stacks 04WD "coverwise groupoid-stack pullback closure"]
theorem isStackInGroupoids
    (P : CategoryTheory.Precoverage C) (Q : CategoryTheory.Precoverage D)
    (u : C ⥤ D) (p : S ⥤ D)
    [P.HasIsos] [P.HasPullbacks] [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition]
    [Functor.Precoverage.IsContinuous u P Q]
    [IsStack.InGroupoids Q.toGrothendieck p] :
    IsStack.InGroupoids P.toGrothendieck (π₁ u p) := sorry

end Limits.CategoricalPullback.Left.Precoverage

end CategoryTheory
