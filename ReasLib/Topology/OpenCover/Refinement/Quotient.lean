module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Quotient
public import ReasLib.Topology.OpenCover.Refinement
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The open-cover refinement category

This module identifies parallel selected refinements while retaining every indexed open cover as
an object.  The quotient is therefore on morphisms only.  A coefficient-valued Čech construction
descends to this category after proving that its maps are independent of the selected refinement.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace TopologicalSpace.OpenCover

variable {X : Type u} [TopologicalSpace X]

/-- Any two selected refinements between the same indexed open covers represent the same
refinement direction. -/
@[stacks 09UZ "independence of the selected open-cover refinement"]
def selectionRel (X : Type u) [TopologicalSpace X] :
    HomRel (OpenCover.{v} X) :=
  fun _ _ _ _ ↦ True

/-- Identifying parallel selected refinements is compatible with identities and composition. -/
instance selectionRelCongruence : Congruence (selectionRel.{v} X) := sorry

/-- The category of indexed open covers with parallel selected refinements identified.  Its
objects remain indexed open covers; only hom-sets are quotiented. -/
@[stacks 09UZ "indexed open-cover refinement category"]
abbrev RefinementCategory (X : Type u) [TopologicalSpace X] :=
  CategoryTheory.Quotient (selectionRel.{v} X)

/-- The canonical functor from selected refinements to refinement classes. -/
@[stacks 09UZ "quotient functor for indexed open-cover refinements"]
def refinementQuotient (X : Type u) [TopologicalSpace X] :
    OpenCover.{v} X ⥤ RefinementCategory.{v} X :=
  CategoryTheory.Quotient.functor (selectionRel.{v} X)

/-- An indexed open cover regarded as an object of the refinement category. -/
abbrev refinementObject (𝒰 : OpenCover.{v} X) : RefinementCategory.{v} X :=
  (refinementQuotient X).obj 𝒰

/-- A selected refinement regarded as a morphism in the refinement category. -/
abbrev refinementMap {𝒰 𝒱 : OpenCover.{v} X} (r : Refinement 𝒰 𝒱) :
    refinementObject 𝒰 ⟶ refinementObject 𝒱 :=
  (refinementQuotient X).map r

/-- Passing a cover to the refinement category retains the original indexed cover. -/
@[simp]
theorem refinementObject_as (𝒰 : OpenCover.{v} X) :
    (refinementObject 𝒰).as = 𝒰 := sorry

/-- Parallel selected refinements have equal images in the refinement category. -/
@[stacks 09UZ "independence of selected refinement maps"]
theorem refinementMap_eq {𝒰 𝒱 : OpenCover.{v} X} (r s : Refinement 𝒰 𝒱) :
    refinementMap r = refinementMap s := sorry

/-- The pairwise-intersection cover regarded as a common stage of the refinement category. -/
abbrev interObject (𝒰 𝒱 : OpenCover.{v} X) : RefinementCategory.{v} X :=
  refinementObject (inter 𝒰 𝒱)

/-- The canonical morphism from the left cover to the common intersection refinement. -/
abbrev interFst (𝒰 𝒱 : OpenCover.{v} X) :
    refinementObject 𝒰 ⟶ interObject 𝒰 𝒱 :=
  refinementMap (inter.fst 𝒰 𝒱)

/-- The canonical morphism from the right cover to the common intersection refinement. -/
abbrev interSnd (𝒰 𝒱 : OpenCover.{v} X) :
    refinementObject 𝒱 ⟶ interObject 𝒰 𝒱 :=
  refinementMap (inter.snd 𝒰 𝒱)

/-- Every hom-set of the refinement category is a subsingleton. -/
instance refinementHomSubsingleton (𝒰 𝒱 : RefinementCategory.{v} X) :
    Subsingleton (𝒰 ⟶ 𝒱) := sorry

/-- Indexed open covers form a filtered category after selected refinements are identified. -/
@[stacks 09UZ "filtered category of indexed open covers"]
instance refinementCategoryIsFiltered : IsFiltered (RefinementCategory.{v} X) := sorry

end TopologicalSpace.OpenCover


