module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import ReasLib.Topology.Category.LCCat.Objects
public import ReasLib.Topology.Category.TopCat.Limits.Compact

/-!
# Finite limits of Hausdorff locally compact spaces

The defining object property of `LCCat` is stable under pullbacks, and `LCCat` has a terminal
object. Consequently the canonical full subcategory has finite limits. Compactness of a pullback
is also exposed as an instance for later covering arguments.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace LCCat.property

/-- Hausdorff local compactness is invariant under isomorphisms in `TopCat`. -/
@[stacks 09WZ "Hausdorff locally compact spaces are closed under isomorphisms", instance]
instance isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms LCCat.property := sorry

/-- A pullback of Hausdorff locally compact spaces in `TopCat` is Hausdorff locally compact. -/
@[stacks 09WZ "Hausdorff locally compact pullbacks"]
theorem pullback {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hX : LCCat.property X) (hY : LCCat.property Y)
    [T2Space Z] : LCCat.property (Limits.pullback f g) := sorry

/-- The Hausdorff locally compact object property is closed under pullback-shaped limits. -/
@[stacks 09WZ "Hausdorff locally compact spaces are closed under pullbacks", instance]
instance isClosedUnderPullbacks :
    ObjectProperty.IsClosedUnderLimitsOfShape
      LCCat.property WalkingCospan := sorry

end LCCat.property

namespace LCCat

/-- Lemma 21.31.1 (1): `LCCat` has pullbacks. -/
@[stacks 09WZ "(1)"]
instance instHasPullbacks : HasPullbacks LCCat.{u} := sorry

/-- Lemma 21.31.1 (2): `LCCat` has a terminal object. -/
@[stacks 09WZ "(2)"]
instance instHasTerminal : HasTerminal LCCat.{u} := sorry

/-- Lemma 21.31.1 (3): `LCCat` has all finite limits. -/
@[stacks 09WZ "(3)"]
instance instHasFiniteLimits : HasFiniteLimits LCCat.{u} := sorry

/-- Lemma 21.31.1 (4): a pullback in `LCCat` of two compact source spaces is compact. -/
@[stacks 09WZ "(4)"]
instance compactSpace_pullback {X Y Z : LCCat.{u}} [CompactSpace X.obj]
    [CompactSpace Y.obj] (f : X ⟶ Z) (g : Y ⟶ Z) :
    CompactSpace (Limits.pullback f g).obj := sorry

end LCCat
