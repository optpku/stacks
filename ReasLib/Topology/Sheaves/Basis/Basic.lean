module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Topology.Category.TopCat.Opens

/-!
# Opens in a topological basis

This file defines the full subcategory of open subsets belonging to a fixed collection.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The full subcategory of `Opens X` spanned by the members of a collection `B` of opens. -/
@[stacks 009I "category of opens in a topological basis"]
abbrev BasisOpen (B : Set (Opens X)) :=
  ObjectProperty.FullSubcategory fun U : Opens X ↦ U ∈ B

/-- The inclusion of the category of opens belonging to `B` into the category of all opens. -/
abbrev basisOpenInclusion (B : Set (Opens X)) : BasisOpen B ⥤ Opens X :=
  ObjectProperty.ι fun U : Opens X ↦ U ∈ B
