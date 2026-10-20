/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Instances.Real.Lemmas
public import ReasLib.Topology.Category.TopCat.Subset

/-!
# Cocontinuity of restriction to a subspace

This leaf records the density obstruction to cocontinuity of the inverse-image
functor on opens, together with the punctured-real counterexample.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open TopologicalSpace.Opens

universe u

namespace TopologicalSpace.Opens

/-- A cocontinuous inverse-image functor on opens does not send a nonempty open set to the empty
open set. -/
theorem map_ne_bot_of_isCocontinuous
    {X Z : TopCat.{u}} (i : Z ⟶ X)
    (hco : (map i).IsCocontinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z))
    {U : Opens X} (hU : U ≠ ⊥) :
    (map i).obj U ≠ ⊥ := sorry

end TopologicalSpace.Opens

namespace TopCat.Subset

/-- Cocontinuity of restriction to a subspace forces that subspace to be dense. -/
theorem dense_of_isCocontinuous
    {X : TopCat.{u}} {Z : Set X}
    (hco : (Opens.map (X.subsetInclusion Z)).IsCocontinuous
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (subsetSpace Z))) :
    Dense Z := sorry

/-- Every nonempty open subset meets a subspace whose restriction functor on opens is
cocontinuous. -/
theorem inter_nonempty_of_isCocontinuous
    {X : TopCat.{u}} {Z : Set X}
    (hco : (Opens.map (X.subsetInclusion Z)).IsCocontinuous
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (subsetSpace Z)))
    {U : Set X} (hU : IsOpen U) (hUne : U.Nonempty) :
    (U ∩ Z).Nonempty := sorry

/-- The punctured real line, regarded as a subset of `TopCat.of ℝ`. -/
def puncturedReal : Set (TopCat.of ℝ) := ({0} : Set ℝ)ᶜ

/-- Restriction from the real line to its punctured subspace is not cocontinuous on categories of
opens with their canonical Grothendieck topologies. -/
theorem puncturedReal_not_isCocontinuous :
    ¬ (Opens.map (TopCat.subsetInclusion (X := TopCat.of ℝ) puncturedReal)).IsCocontinuous
        (Opens.grothendieckTopology (TopCat.of ℝ))
        (Opens.grothendieckTopology (subsetSpace puncturedReal)) := sorry

end TopCat.Subset
