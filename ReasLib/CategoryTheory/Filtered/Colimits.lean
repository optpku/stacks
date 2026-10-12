/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Preserves.Grothendieck
public import ReasLib.CategoryTheory.Filtered.Components
public import ReasLib.CategoryTheory.Limits.FiniteConnected

/-!
# Colimits over componentwise filtered categories

Type-valued colimits over an indexing category whose connected components are filtered preserve
finite connected limits.  Class-based consequences for span and parallel-pair cocones are paired
with explicit-hypothesis bridges for source-facing applications.
-/

@[expose] public section

open CategoryTheory.Limits

universe u v vI uI

namespace CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I] [Small.{v} I]

namespace Types.FilteredColimit

namespace Componentwise

/-- If every connected component of `I` is filtered, then `Type`-valued colimits over `I`
preserve limits of every finite connected shape. -/
theorem preservesFiniteConnectedLimits
    [∀ j : ConnectedComponents I, IsFiltered j.Component] :
    PreservesFiniteConnectedLimits (colim : (I ⥤ Type v) ⥤ Type v) := sorry

end Componentwise

/-- Span and parallel-pair cocones imply that `Type`-valued colimits preserve finite connected
limits. -/
instance preservesFiniteConnectedLimits
    [HasSpanCocones I] [HasParallelPairCocones I] :
    PreservesFiniteConnectedLimits (colim : (I ⥤ Type v) ⥤ Type v) := sorry

/-- Explicit-hypothesis bridge for preservation of finite connected limits. -/
@[stacks 002Y "finite connected limits preserved by Type colimits"]
theorem preservesFiniteConnectedLimits_of_postcomposition
    [HasSpanCocones I]
    (hMap :
      ∀ ⦃X Y : I⦄ (f g : X ⟶ Y),
        ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h) :
    PreservesFiniteConnectedLimits (colim : (I ⥤ Type v) ⥤ Type v) := sorry

/-- Explicit-shape specialization of
`Types.FilteredColimit.preservesFiniteConnectedLimits_of_postcomposition`. -/
theorem preservesLimitsOfShape_of_postcomposition
    (J : Type u) [SmallCategory J] [FinCategory J] [IsConnected J]
    [HasSpanCocones I]
    (hMap :
      ∀ ⦃X Y : I⦄ (f g : X ⟶ Y),
        ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h) :
    PreservesLimitsOfShape J (colim : (I ⥤ Type v) ⥤ Type v) := sorry

/-- Span and parallel-pair cocones imply that `Type`-valued colimits preserve pullbacks. -/
theorem preservesPullbacks
    [HasSpanCocones I] [HasParallelPairCocones I] :
    PreservesLimitsOfShape WalkingCospan
      (colim : (I ⥤ Type v) ⥤ Type v) := sorry

/-- Explicit-hypothesis bridge for preservation of pullbacks. -/
@[stacks 002Y "pullbacks preserved by Type colimits"]
theorem preservesPullbacks_of_postcomposition
    [HasSpanCocones I]
    (hMap :
      ∀ ⦃X Y : I⦄ (f g : X ⟶ Y),
        ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h) :
    PreservesLimitsOfShape WalkingCospan
      (colim : (I ⥤ Type v) ⥤ Type v) := sorry

/-- Span and parallel-pair cocones imply that `Type`-valued colimits preserve equalizers. -/
theorem preservesEqualizers
    [HasSpanCocones I] [HasParallelPairCocones I] :
    PreservesLimitsOfShape WalkingParallelPair
      (colim : (I ⥤ Type v) ⥤ Type v) := sorry

/-- Explicit-hypothesis bridge for preservation of equalizers. -/
@[stacks 002Y "equalizers preserved by Type colimits"]
theorem preservesEqualizers_of_postcomposition
    [HasSpanCocones I]
    (hMap :
      ∀ ⦃X Y : I⦄ (f g : X ⟶ Y),
        ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h) :
    PreservesLimitsOfShape WalkingParallelPair
      (colim : (I ⥤ Type v) ⥤ Type v) := sorry

end Types.FilteredColimit

end CategoryTheory.Limits
