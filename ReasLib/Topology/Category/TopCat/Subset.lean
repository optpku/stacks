module

public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Subspace inclusions

This module names the canonical morphism from a subspace of a topological space to its ambient
space. Closedness is an additional property used by later support statements, not data required
to form the subspace or its inclusion.
-/

@[expose] public section

open TopologicalSpace

universe u

open TopologicalSpace

namespace TopCat

/-- The subspace of `X` carried by an arbitrary subset `Z`. -/
abbrev subsetSpace {X : TopCat.{u}} (Z : Set X) : TopCat.{u} :=
  TopCat.of Z

/-- The inclusion morphism of a subset into its ambient topological space. -/
abbrev subsetInclusion {X : TopCat.{u}} (Z : Set X) : subsetSpace Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The canonical subset inclusion is an inducing map. -/
theorem subsetInclusion_isInducing {X : TopCat.{u}} (Z : Set X) :
    Topology.IsInducing (subsetInclusion Z) := sorry

/-- The inverse-image functor on opens along a subset inclusion is continuous for the canonical
Grothendieck topologies. -/
instance subsetInclusion_opensMap_isContinuous {X : TopCat.{u}} (Z : Set X) :
    (Opens.map (subsetInclusion Z)).IsContinuous
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (subsetSpace Z)) := sorry

end TopCat
