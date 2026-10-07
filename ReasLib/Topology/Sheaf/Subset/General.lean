module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
public import ReasLib.CategoryTheory.Functor.Algebraic.Basic
public import ReasLib.Topology.Category.TopCat.Subset
public import ReasLib.Topology.Sheaves.Stalks.Filtered
public import ReasLib.Topology.Sheaves.Stalks.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sheaves on arbitrary subsets: pushforward is fully faithful

For any subset `Z ⊆ X`, the pushforward along the subset inclusion `Z ↪ X` establishes a
fully faithful embedding of sheaves on the subspace into sheaves on the ambient space.

The key result is that the counit of the pullback-pushforward adjunction is an isomorphism,
which immediately yields full faithfulness.

## Main declarations

- `TopCat.Sheaf.Subset.counit_isIso`: the counit is an isomorphism
- `TopCat.Sheaf.Subset.fullyFaithful`: pushforward is fully faithful
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite
open scoped TopCat

noncomputable section

universe v w

namespace TopCat.Sheaf.Subset

variable {X : TopCat.{v}}
variable {C : Type w} [Category.{v} C]
variable {FC : C → C → Type v} {CC : C → Type v}
variable [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory.{v} C FC]
variable [HasColimits C] [HasLimits C]
variable [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable [HasWeakSheafify (Opens.grothendieckTopology X) C]

/-- The counit of the pullback-pushforward adjunction along a subset inclusion is an isomorphism.
-/
@[stacks 00AE "pullback-pushforward counit is an isomorphism for subset inclusions",
  stacks 01AX "(4)"]
theorem counit_isIso (Z : Set X) :
    IsIso (TopCat.Sheaf.pullbackPushforwardAdjunction C
      (TopCat.subsetInclusion Z)).counit := sorry

/-- The canonical `IsIso` instance for the pullback-pushforward counit along a subset
inclusion. -/
noncomputable instance counitIsIso (Z : Set X) :
    IsIso (TopCat.Sheaf.pullbackPushforwardAdjunction C
      (TopCat.subsetInclusion Z)).counit := sorry

/-- Pushforward along a subset inclusion is fully faithful. -/
@[stacks 00AE "subset pushforward is fully faithful", stacks 01AX "(2)"]
noncomputable def fullyFaithful (Z : Set X) :
    (TopCat.Sheaf.pushforward C (TopCat.subsetInclusion Z)).FullyFaithful :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction C
    (TopCat.subsetInclusion Z)).fullyFaithfulROfIsIsoCounit

/-- Pushforward along a subset inclusion induces a bijection on every hom set.

This is the pointwise form of `fullyFaithful`, kept separate for consumers that work directly
with morphism functions. -/
theorem map_bijective (Z : Set X) (F G : TopCat.Sheaf C (TopCat.subsetSpace Z)) :
    Function.Bijective (fun (η : F ⟶ G) =>
      (TopCat.Sheaf.pushforward C (TopCat.subsetInclusion Z)).map η) := sorry

end TopCat.Sheaf.Subset

end

end
