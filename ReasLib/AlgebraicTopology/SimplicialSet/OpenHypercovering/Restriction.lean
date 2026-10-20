module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import ReasLib.AlgebraicTopology.SimplicialSet.OpenHypercovering.Properties
public import ReasLib.AlgebraicTopology.SimplicialSet.OpenHypercovering.Refinement

/-!
# Removing empty opens from an open hypercovering

This module restricts an open hypercovering to the sub-simplicial set of indices carrying a
nonempty open.  It exposes both the concrete restricted data and pointwise transfer lemmas for
basis, finiteness, and descent applications.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u v

namespace SSet

variable {X : Type u} [TopologicalSpace X]

namespace OpenFamily

/-- Nonemptiness of an associated open is preserved by a simplicial operator. -/
@[stacks 01H5 "nonempty-index stability"]
theorem map_nonempty {I : SSet.{v}} (U : OpenFamily X I)
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') (i : I.obj Δ)
    (hi : (U.openAt i : Set X).Nonempty) :
    (U.openAt (I.map f i) : Set X).Nonempty := sorry

/-- The subfunctor of simplices whose associated opens are nonempty. -/
@[stacks 01H5 "nonempty-index sub-simplicial set"]
def nonemptySubfunctor {I : SSet.{v}} (U : OpenFamily X I) : Subfunctor I where
  obj _ := { i | (U.openAt i : Set X).Nonempty }
  map f i hi := U.map_nonempty f i hi

/-- Membership in the nonempty-index subfunctor means that the associated open is nonempty. -/
@[simp] theorem nonemptySubfunctor.mem_obj
    {I : SSet.{v}} (U : OpenFamily X I) {Δ : SimplexCategoryᵒᵖ} (i : I.obj Δ) :
    i ∈ U.nonemptySubfunctor.obj Δ ↔ (U.openAt i : Set X).Nonempty := sorry

/-- Membership in the nonempty-index subfunctor means that the associated open is non-bottom. -/
@[simp] theorem nonemptySubfunctor.mem_obj_iff_ne_bot
    {I : SSet.{v}} (U : OpenFamily X I) {Δ : SimplexCategoryᵒᵖ} (i : I.obj Δ) :
    i ∈ U.nonemptySubfunctor.obj Δ ↔ U.openAt i ≠ ⊥ := sorry

/-- The nonempty-index subfunctor is top exactly when every associated open is nonempty. -/
theorem nonemptySubfunctor.eq_top_iff {I : SSet.{v}} (U : OpenFamily X I) :
    U.nonemptySubfunctor = ⊤ ↔
      ∀ ⦃Δ : SimplexCategoryᵒᵖ⦄ (i : I.obj Δ), (U.openAt i : Set X).Nonempty := sorry

/-- The simplicial index set formed by the nonempty opens of a simplicial family. -/
@[stacks 01H5 "nonempty-index simplicial set"]
abbrev nonemptyIndices {I : SSet.{v}} (U : OpenFamily X I) : SSet.{v} :=
  U.nonemptySubfunctor.toFunctor

/-- The inclusion of the nonempty indices into the original simplicial index set. -/
@[stacks 01H5 "nonempty-index inclusion"]
abbrev nonemptyInclusion {I : SSet.{v}} (U : OpenFamily X I) :
    U.nonemptyIndices ⟶ I :=
  U.nonemptySubfunctor.ι

/-- The simplicial action on nonempty indices has the original action on underlying indices. -/
@[simp] theorem nonemptyIndices.map_val
    {I : SSet.{v}} (U : OpenFamily X I) {Δ Δ' : SimplexCategoryᵒᵖ}
    (f : Δ ⟶ Δ') (i : U.nonemptyIndices.obj Δ) :
    (U.nonemptyIndices.map f i).1 = I.map f i.1 := sorry

/-- Restrict a simplicial family of opens to the indices carrying nonempty opens. -/
@[stacks 01H5 "nonempty-index open family"]
abbrev restrictToNonempty {I : SSet.{v}} (U : OpenFamily X I) :
    OpenFamily X U.nonemptyIndices :=
  U.restrict U.nonemptyInclusion

/-- The nonempty-index restriction has the original open at the underlying index. -/
@[simp] theorem restrictToNonempty.openAt
    {I : SSet.{v}} (U : OpenFamily X I) {Δ : SimplexCategoryᵒᵖ}
    (i : U.nonemptyIndices.obj Δ) :
    U.restrictToNonempty.openAt i = U.openAt i.1 := sorry

/-- A pointwise predicate on a simplicial family of opens is inherited by its nonempty-index
restriction. -/
theorem restrictToNonempty.openAt_property
    {I : SSet.{v}} (U : OpenFamily X I) {P : Opens X → Prop}
    (hP : ∀ ⦃Δ : SimplexCategoryᵒᵖ⦄ (i : I.obj Δ), P (U.openAt i))
    {Δ : SimplexCategoryᵒᵖ} (i : U.nonemptyIndices.obj Δ) :
    P (U.restrictToNonempty.openAt i) := sorry

/-- Every open in the nonempty-index restriction is nonempty. -/
@[stacks 01H5 "nonempty-index open nonemptiness"]
theorem restrictToNonempty.nonempty
    {I : SSet.{v}} (U : OpenFamily X I) {Δ : SimplexCategoryᵒᵖ}
    (i : U.nonemptyIndices.obj Δ) :
    (U.restrictToNonempty.openAt i : Set X).Nonempty := sorry

/-- Every open in the nonempty-index restriction is non-bottom. -/
@[stacks 01H5 "nonempty-index open non-bottom", simp]
theorem restrictToNonempty.openAt_ne_bot
    {I : SSet.{v}} (U : OpenFamily X I) {Δ : SimplexCategoryᵒᵖ}
    (i : U.nonemptyIndices.obj Δ) :
    U.restrictToNonempty.openAt i ≠ ⊥ := sorry

end OpenFamily

namespace OpenHypercovering

/-- The degree-`0` opens indexed by nonempty simplices still cover the target space. -/
@[stacks 01H5 "nonempty-index degree-zero cover"]
theorem restrictToNonempty.zero_isOpenCover (H : OpenHypercovering.{u, v} X) :
    TopologicalSpace.IsOpenCover
      (fun i : H.family.nonemptyIndices.obj (op <| SimplexCategory.mk 0) ↦
        H.family.restrictToNonempty.openAt i) := sorry

/-- The nonempty indices satisfy the hypercovering intersection condition in every degree. -/
@[stacks 01H5 "nonempty-index successor cover"]
theorem restrictToNonempty.succ (H : OpenHypercovering.{u, v} X) (n : ℕ) :
    OpenHypercovering.BoundaryIntersection
      (fun i : H.family.nonemptyIndices.obj (op <| SimplexCategory.mk n) ↦
        H.family.restrictToNonempty.openAt i)
      (fun j : H.family.nonemptyIndices.obj (op <| SimplexCategory.mk (n + 1)) ↦
        H.family.restrictToNonempty.openAt j) := sorry

/-- Restrict an open hypercovering to the simplices whose associated opens are nonempty. -/
@[stacks 01H5 "restriction to nonempty indices"]
def restrictToNonempty (H : OpenHypercovering.{u, v} X) : OpenHypercovering X where
  I := H.family.nonemptyIndices
  family := H.family.restrictToNonempty
  zero_isOpenCover := restrictToNonempty.zero_isOpenCover H
  succ := restrictToNonempty.succ H

/-- The nonempty-index restriction uses the canonical subfunctor inclusion as its concrete
refinement map. -/
@[stacks 01H5 "nonempty-index refinement map", simp]
theorem restrictToNonempty.family_eq_restrict (H : OpenHypercovering.{u, v} X) :
    H.restrictToNonempty.family = H.family.restrict (H.family.nonemptyInclusion) := sorry

/-- The open inclusion used by the concrete nonempty-index refinement. -/
@[stacks 01H5 "nonempty-index selected-refinement inclusion"]
theorem restrictToNonempty.refinement_le (H : OpenHypercovering.{u, v} X)
    {Δ : SimplexCategoryᵒᵖ} (i : H.family.nonemptyIndices.obj Δ) :
    H.restrictToNonempty.family.openAt i ≤
      H.family.openAt (H.family.nonemptyInclusion.app Δ i) := sorry

/-- The selected refinement from the nonempty-index hypercovering to the original one. -/
@[stacks 01H5 "nonempty-index selected refinement"]
def restrictToNonempty.refinement (H : OpenHypercovering.{u, v} X) :
    Refinement H.restrictToNonempty H where
  indexMap := H.family.nonemptyInclusion
  le := restrictToNonempty.refinement_le H

/-- The selected index map of the nonempty-index refinement is the subfunctor inclusion. -/
@[simp, stacks 01H5 "nonempty-index selected-refinement map"]
theorem restrictToNonempty.refinement_indexMap (H : OpenHypercovering.{u, v} X) :
    (restrictToNonempty.refinement H).indexMap = H.family.nonemptyInclusion := sorry

/-- Restricting to the nonempty indices is an exact restriction of the original hypercovering. -/
@[stacks 01H5 "nonempty-index exact restriction"]
theorem restrictToNonempty.restricts (H : OpenHypercovering.{u, v} X) :
    H.restrictToNonempty.Restricts H := sorry

/-- Restricting to the nonempty indices is an explicit refinement of the original open
hypercovering. -/
@[stacks 01H5 "nonempty-index refinement"]
theorem restrictToNonempty.refines (H : OpenHypercovering.{u, v} X) :
    H.restrictToNonempty.Refines H := sorry

/-- The open of the nonempty-index restriction computes at the underlying original index. -/
@[stacks 01H5 "nonempty-index open computation", simp]
theorem restrictToNonempty.openAt
    (H : OpenHypercovering.{u, v} X) {Δ : SimplexCategoryᵒᵖ}
    (i : H.family.nonemptyIndices.obj Δ) :
    H.restrictToNonempty.family.openAt i = H.family.openAt i.1 := sorry

/-- A pointwise predicate on the original opens is inherited by the nonempty-index restriction. -/
theorem restrictToNonempty.openAt_property
    (H : OpenHypercovering.{u, v} X) {P : Opens X → Prop}
    (hP : ∀ ⦃Δ : SimplexCategoryᵒᵖ⦄ (i : H.I.obj Δ), P (H.family.openAt i))
    {Δ : SimplexCategoryᵒᵖ} (i : H.family.nonemptyIndices.obj Δ) :
    P (H.restrictToNonempty.family.openAt i) := sorry

/-- Every degreewise predicate on the original opens is inherited by the nonempty-index
restriction. -/
@[stacks 01H5 "nonempty-index degreewise transfer"]
theorem restrictToNonempty.degreewise
    (H : OpenHypercovering.{u, v} X) {P : Opens X → Prop} (hP : H.degreewise P) :
    H.restrictToNonempty.degreewise P := sorry

/-- An indexed open of the nonempty-index restriction is nonempty. -/
@[stacks 01H5 "nonempty-index open nonemptiness"]
theorem restrictToNonempty.nonempty
    (H : OpenHypercovering.{u, v} X) {Δ : SimplexCategoryᵒᵖ}
    (i : H.family.nonemptyIndices.obj Δ) :
    (H.restrictToNonempty.family.openAt i : Set X).Nonempty := sorry

/-- An indexed open of the nonempty-index restriction is non-bottom. -/
@[stacks 01H5 "nonempty-index open non-bottom", simp]
theorem restrictToNonempty.openAt_ne_bot
    (H : OpenHypercovering.{u, v} X) {Δ : SimplexCategoryᵒᵖ}
    (i : H.family.nonemptyIndices.obj Δ) :
    H.restrictToNonempty.family.openAt i ≠ ⊥ := sorry

/-- The nonempty-index restriction is degreewise nonempty. -/
@[stacks 01H5 "restricted hypercovering is degreewise nonempty"]
theorem restrictToNonempty.degreewiseNonempty (H : OpenHypercovering.{u, v} X) :
    H.restrictToNonempty.degreewiseNonempty := sorry

/-- Restriction to nonempty indices preserves a degreewise condition of lying in a set of opens. -/
theorem degreewiseOpensIn.restrictToNonempty
    {H : OpenHypercovering.{u, v} X} {B : Set (Opens X)}
    (hH : H.degreewiseOpensIn B) :
    H.restrictToNonempty.degreewiseOpensIn B := sorry

/-- Restriction to nonempty indices preserves degreewise finiteness. -/
theorem degreewiseFinite.restrictToNonempty
    {H : OpenHypercovering.{u, v} X} (hH : H.degreewiseFinite) :
    H.restrictToNonempty.degreewiseFinite := sorry

end OpenHypercovering
end SSet
