module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Cocones on parallel pairs

`HasParallelPairCocones` records the weak, non-universal condition that every pair of parallel
arrows becomes equal after postcomposition.  It is one of the two local ingredients used to show
that connected components are filtered.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits

variable {I : Type u} [Category.{v} I]

/-- A category has parallel-pair cocones if every pair of parallel arrows is equalized after
postcomposition by some arrow. -/
@[stacks 002X "weak cocones on parallel pairs"]
class HasParallelPairCocones (I : Type u) [Category.{v} I] : Prop where
  /-- Every parallel pair admits a cofork, without any universal-property requirement. -/
  nonempty {X Y : I} (f g : X ⟶ Y) : Nonempty (Cofork f g)

namespace HasParallelPairCocones

/-- The selected cofork on a parallel pair. This is the concrete-data boundary for
`HasParallelPairCocones`; clients can use its `pt`, `π`, and `condition` API. -/
@[stacks 002X "selected weak cofork on a parallel pair"]
noncomputable def cofork [HasParallelPairCocones I]
    {X Y : I} (f g : X ⟶ Y) : Cofork f g :=
  Classical.choice (HasParallelPairCocones.nonempty f g)

/-- Construct the parallel-pair-cocone property from the explicit equalizing-arrow condition. -/
theorem of
    (h : ∀ ⦃X Y : I⦄ (f g : X ⟶ Y),
      ∃ (Z : I) (q : Y ⟶ Z), f ≫ q = g ≫ q) :
    HasParallelPairCocones I := sorry

end HasParallelPairCocones

/-- Every parallel pair has an explicit postcomposition equalizer. -/
theorem HasParallelPairCocones.exists [HasParallelPairCocones I]
    {X Y : I} (f g : X ⟶ Y) :
    ∃ (Z : I) (q : Y ⟶ Z), f ≫ q = g ≫ q := sorry

/-- The class unfolds to the explicit postcomposition-equalizer condition. -/
@[stacks 002X "parallel-pair cocone criterion"]
theorem hasParallelPairCocones_iff :
    HasParallelPairCocones I ↔
      ∀ ⦃X Y : I⦄ (f g : X ⟶ Y),
        ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h := sorry

/-- A filtered-or-empty category has cocones on all parallel pairs. -/
instance (priority := 100) hasParallelPairCocones_of_isFilteredOrEmpty
    [IsFilteredOrEmpty I] :
    HasParallelPairCocones I := sorry

/-- A category with coequalizers has cocones on all parallel pairs. -/
instance (priority := 100) hasParallelPairCocones_of_hasCoequalizers
    [HasCoequalizers I] :
    HasParallelPairCocones I := sorry

end CategoryTheory
