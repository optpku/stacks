/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Cartesian
public import ReasLib.CategoryTheory.Fibered.Stack.Basic
public import ReasLib.CategoryTheory.Fibered.Stack.Prestack
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stack closure of heterogeneous explicit pseudo-pullbacks

The theorem in this file belongs to the concrete `BasedCategory.PseudoPullback` owner.  It does
not impose a common universe on the three total categories and is independent of any chosen
bicategory packaging.
-/

@[expose] public section

universe u v uX vX uY vY uS vS

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}

namespace BasedCategory.PseudoPullback

/-- The explicit pseudo-pullback of two stacks over a common prestack is a stack, without a
common-universe restriction on the total categories. -/
@[stacks 026G "heterogeneous cartesian closure"]
theorem isStackOnSite
    (F : CartesianBasedFunctor X.p S.p)
    (G : CartesianBasedFunctor Y.p S.p)
    [IsStack.OnSite J X.p] [IsStack.OnSite J Y.p]
    [IsPrestack.OnSite J S.p] :
    IsStack.OnSite J
      (BasedCategory.PseudoPullback F.toBasedFunctor G.toBasedFunctor).p := sorry

end BasedCategory.PseudoPullback

end CategoryTheory
