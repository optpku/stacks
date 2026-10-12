/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Sites.Continuous
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Stack.Precoverage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of stacks along continuous functors

This module packages the site-theoretic preservation statements for the first projection of a
categorical pullback.  The canonical statements use precoverages and preservation only of the
pullbacks occurring in covering families.  The Grothendieck-topology statements with ambient
pullback hypotheses are retained as convenient specializations.

## Main declarations

* `CategoricalPullback.Left.isStackOnSite` — pullback preserves stacks.
* `CategoricalPullback.Left.isStackInGroupoids` — pullback preserves stacks in
  groupoids.
* `CategoricalPullback.Left.Precoverage.isStackOnSite` and
  `CategoricalPullback.Left.Precoverage.isStackInGroupoids` — the coverwise owners.
-/

@[expose] public section

universe uC uD uS vC vD vS

namespace CategoryTheory

open Limits

namespace Limits.CategoricalPullback

namespace Left

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Lemma 8.12.2 (tag 04WC): if `u` is continuous and preserves pullbacks, then base change
along `u` carries a stack over `(D, K)` to a stack over `(C, J)`. -/
@[stacks 04WC "projection-level stack pullback closure"]
theorem isStackOnSite
    (u : C ⥤ D) (p : S ⥤ D) [u.IsContinuous J K]
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    [IsStack.OnSite K p] :
    IsStack.OnSite J (π₁ u p) := sorry

/-- Lemma 8.12.3 (tag 04WD): under the same site hypotheses, base change along `u` carries a
stack in groupoids over `(D, K)` to a stack in groupoids over `(C, J)`. -/
@[stacks 04WD]
theorem isStackInGroupoids
    (u : C ⥤ D) (p : S ⥤ D) [u.IsContinuous J K]
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    [IsStack.InGroupoids K p] :
    IsStack.InGroupoids J (π₁ u p) := sorry

end Left

end Limits.CategoricalPullback

end CategoryTheory
