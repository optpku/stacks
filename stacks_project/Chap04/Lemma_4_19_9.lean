/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtered.Colimits
import StacksCheckRecall

@[expose] public section

universe v vI uI

namespace CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I] [Small.{v} I] [HasSpanCocones I]
variable (hMap : ∀ ⦃X Y : I⦄ (f g : X ⟶ Y),
  ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h)

/- Lemma 4.19.9 (1): under the source's span and parallel-pair cocone hypotheses, Type-valued
colimits preserve finite connected limits. -/
@[stacks 002Y "(1)"]
#check (Types.FilteredColimit.preservesFiniteConnectedLimits_of_postcomposition hMap :
  PreservesFiniteConnectedLimits (colim : (I ⥤ Type v) ⥤ Type v))

/- Lemma 4.19.9 (2): under the same hypotheses, Type-valued colimits preserve pullbacks. -/
@[stacks 002Y "(2)"]
#check (Types.FilteredColimit.preservesPullbacks_of_postcomposition hMap :
  PreservesLimitsOfShape WalkingCospan (colim : (I ⥤ Type v) ⥤ Type v))

/- Lemma 4.19.9 (3): under the same hypotheses, Type-valued colimits preserve equalizers. -/
@[stacks 002Y "(3)"]
#check (Types.FilteredColimit.preservesEqualizers_of_postcomposition hMap :
  PreservesLimitsOfShape WalkingParallelPair (colim : (I ⥤ Type v) ⥤ Type v))

end CategoryTheory.Limits
