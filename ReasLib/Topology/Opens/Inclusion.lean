/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.Sheaves.Functors

/-!
# Open subset inclusions in TopCat

This module owns the canonical topological spaces associated to open subsets of a `TopCat` object,
their inclusion maps, and the fundamental composition/identity simp lemmas.

The API is organized under `TopCat.Opens.Subspace` namespace for dot-notation access.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open TopologicalSpace.Opens

noncomputable section

universe w

namespace TopCat.Opens.Subspace

variable {X : TopCat.{w}}

/-- The topological space underlying an open subset `U ⊆ X`. -/
abbrev space (U : Opens X) : TopCat.{w} :=
  (Opens.toTopCat X).obj U

/-- The inclusion of the open subspace `U` into its ambient space. -/
abbrev inclusion (U : Opens X) : space U ⟶ X :=
  Opens.inclusion' U

/-- The inverse image of an ambient open along the inclusion of an open subspace. -/
abbrev preimageOpen (U : Opens X) (V : Opens X) : Opens (space U) :=
  (Opens.map (inclusion U)).obj V

/-- The canonical morphism of open subspaces induced by `W ≤ U` in the lattice of opens. -/
abbrev homOfLE {W U : Opens X} (h : W ≤ U) : space W ⟶ space U :=
  (Opens.toTopCat X).map (CategoryTheory.homOfLE h)

/-- The inverse-image functor on opens induced by an inclusion of open subspaces. -/
abbrev restrictionFunctor {W U : Opens X} (h : W ≤ U) :
    Opens (space U) ⥤ Opens (space W) :=
  Opens.map (homOfLE h)

section Composition

/-- The composite inclusion `W ↪ U ↪ X` is the direct inclusion `W ↪ X`. -/
@[simp] theorem homOfLE_comp_inclusion {W U : Opens X} (h : W ≤ U) :
    homOfLE h ≫ inclusion U = inclusion W := sorry

/-- Open-subspace inclusions induced by nested open subsets compose as expected. -/
@[simp] theorem homOfLE_comp {A B C : Opens X} (hAB : A ≤ B) (hBC : B ≤ C) :
    homOfLE hAB ≫ homOfLE hBC = homOfLE (hAB.trans hBC) := sorry

/-- The map induced by the identity inclusion is the identity map. -/
@[simp] theorem homOfLE_refl (W : Opens X) :
    homOfLE (le_refl W) = 𝟙 _ := sorry

/-- Inverse-image functors on opens induced by nested inclusions compose to the inverse-image
functor of the composite inclusion. -/
theorem restrictionFunctor_comp {A B C : Opens X} (hAB : A ≤ B) (hBC : B ≤ C) :
    restrictionFunctor hBC ⋙ restrictionFunctor hAB = restrictionFunctor (hAB.trans hBC) := sorry

/-- Restricting from `X` to `U` and then to `W ⊆ U` agrees with restricting directly to `W`. -/
theorem restrictionFunctor_comp_inclusion {W U : Opens X} (h : W ≤ U) :
    Opens.map (inclusion U) ⋙ restrictionFunctor h = Opens.map (inclusion W) := sorry

end Composition

section OpenEmbedding

/-- The map of open subspaces induced by an inclusion is an open embedding. -/
theorem homOfLE_isOpenEmbedding {W U : Opens X} (h : W ≤ U) :
    IsOpenEmbedding (homOfLE h) := sorry

/-- The direct-image functor on opens induced by an inclusion of open subspaces is continuous for
the canonical Grothendieck topologies.  This is an instance because module and sheaf pushforward
constructions use that functor as a canonical input. -/
instance homOfLE_functor_isContinuous {W U : Opens X} (h : W ≤ U) :
    (homOfLE_isOpenEmbedding h).functor.IsContinuous
      (Opens.grothendieckTopology (space W))
      (Opens.grothendieckTopology (space U)) :=
  (homOfLE_isOpenEmbedding h).functor_isContinuous

/-- The direct-image functor on opens induced by the inclusion of an open subspace is continuous
for the canonical Grothendieck topologies. -/
instance inclusion_functor_isContinuous (U : Opens X) :
    U.isOpenEmbedding.functor.IsContinuous
      (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
      (Opens.grothendieckTopology X) :=
  U.isOpenEmbedding.functor_isContinuous

end OpenEmbedding

section Intersection

/-- The inclusion of `U ⊓ V` into `U`. -/
abbrev infLeftInclusion (U V : Opens X) : space (U ⊓ V) ⟶ space U :=
  homOfLE inf_le_left

/-- The inclusion of `U ⊓ V` into `V`. -/
abbrev infRightInclusion (U V : Opens X) : space (U ⊓ V) ⟶ space V :=
  homOfLE inf_le_right

/-- The left inclusion of a pairwise intersection followed by the open-subset inclusion is the
inclusion of the intersection in the ambient space. -/
@[simp] theorem infLeftInclusion_comp_inclusion (U V : Opens X) :
    infLeftInclusion U V ≫ inclusion U = inclusion (U ⊓ V) := rfl

/-- The right inclusion of a pairwise intersection followed by the open-subset inclusion is the
inclusion of the intersection in the ambient space. -/
@[simp] theorem infRightInclusion_comp_inclusion (U V : Opens X) :
    infRightInclusion U V ≫ inclusion V = inclusion (U ⊓ V) := rfl

/-- The inclusion `U ⊓ V ↪ U` is an open embedding. -/
theorem infLeftInclusion_isOpenEmbedding (U V : Opens X) :
    IsOpenEmbedding (infLeftInclusion U V) := sorry

/-- The inclusion `U ⊓ V ↪ V` is an open embedding. -/
theorem infRightInclusion_isOpenEmbedding (U V : Opens X) :
    IsOpenEmbedding (infRightInclusion U V) := sorry

end Intersection

section Triple

/-- The inclusion of `U ⊓ V ⊓ W` into `U`. -/
abbrev tripleFirst (U V W : Opens X) : space (U ⊓ V ⊓ W) ⟶ space U :=
  homOfLE (inf_le_left.trans inf_le_left)

/-- The inclusion of `U ⊓ V ⊓ W` into `V`. -/
abbrev tripleSecond (U V W : Opens X) : space (U ⊓ V ⊓ W) ⟶ space V :=
  homOfLE (inf_le_left.trans inf_le_right)

/-- The inclusion of `U ⊓ V ⊓ W` into `W`. -/
abbrev tripleThird (U V W : Opens X) : space (U ⊓ V ⊓ W) ⟶ space W :=
  homOfLE inf_le_right

/-- `U ⊓ V ⊓ W ↪ U` is an open embedding. -/
theorem tripleFirst_isOpenEmbedding (U V W : Opens X) :
    IsOpenEmbedding (tripleFirst U V W) := sorry

/-- `U ⊓ V ⊓ W ↪ V` is an open embedding. -/
theorem tripleSecond_isOpenEmbedding (U V W : Opens X) :
    IsOpenEmbedding (tripleSecond U V W) := sorry

/-- `U ⊓ V ⊓ W ↪ W` is an open embedding. -/
theorem tripleThird_isOpenEmbedding (U V W : Opens X) :
    IsOpenEmbedding (tripleThird U V W) := sorry

/-- The inclusion of `U ⊓ V ⊓ W` into `U ⊓ V`. -/
abbrev tripleToPairLeft (U V W : Opens X) : space (U ⊓ V ⊓ W) ⟶ space (U ⊓ V) :=
  homOfLE inf_le_left

/-- The inclusion of `U ⊓ V ⊓ W` into `V ⊓ W`. -/
abbrev tripleToPairCenter (U V W : Opens X) : space (U ⊓ V ⊓ W) ⟶ space (V ⊓ W) :=
  homOfLE (inf_le_inf inf_le_right le_rfl)

/-- The inclusion of `U ⊓ V ⊓ W` into `U ⊓ W`. -/
abbrev tripleToPairOuter (U V W : Opens X) : space (U ⊓ V ⊓ W) ⟶ space (U ⊓ W) :=
  homOfLE (inf_le_inf inf_le_left le_rfl)

/-- The inclusion into `U ⊓ V` followed by its inclusion into `U` is the first projection
from the triple intersection. -/
@[simp] theorem tripleToPairLeft_comp_infLeft (U V W : Opens X) :
    tripleToPairLeft U V W ≫ infLeftInclusion U V = tripleFirst U V W := rfl

/-- The inclusion into `U ⊓ V` followed by its inclusion into `V` is the second projection
from the triple intersection. -/
@[simp] theorem tripleToPairLeft_comp_infRight (U V W : Opens X) :
    tripleToPairLeft U V W ≫ infRightInclusion U V = tripleSecond U V W := rfl

/-- The inclusion into `V ⊓ W` followed by its inclusion into `V` is the second projection
from the triple intersection. -/
@[simp] theorem tripleToPairCenter_comp_infLeft (U V W : Opens X) :
    tripleToPairCenter U V W ≫ infLeftInclusion V W = tripleSecond U V W := rfl

/-- The inclusion into `V ⊓ W` followed by its inclusion into `W` is the third projection
from the triple intersection. -/
@[simp] theorem tripleToPairCenter_comp_infRight (U V W : Opens X) :
    tripleToPairCenter U V W ≫ infRightInclusion V W = tripleThird U V W := rfl

/-- The inclusion into `U ⊓ W` followed by its inclusion into `U` is the first projection
from the triple intersection. -/
@[simp] theorem tripleToPairOuter_comp_infLeft (U V W : Opens X) :
    tripleToPairOuter U V W ≫ infLeftInclusion U W = tripleFirst U V W := rfl

/-- The inclusion into `U ⊓ W` followed by its inclusion into `W` is the third projection
from the triple intersection. -/
@[simp] theorem tripleToPairOuter_comp_infRight (U V W : Opens X) :
    tripleToPairOuter U V W ≫ infRightInclusion U W = tripleThird U V W := rfl

/-- `U ⊓ V ⊓ W ↪ U ⊓ V` is an open embedding. -/
theorem tripleToPairLeft_isOpenEmbedding (U V W : Opens X) :
    IsOpenEmbedding (tripleToPairLeft U V W) := sorry

/-- `U ⊓ V ⊓ W ↪ V ⊓ W` is an open embedding. -/
theorem tripleToPairCenter_isOpenEmbedding (U V W : Opens X) :
    IsOpenEmbedding (tripleToPairCenter U V W) := sorry

/-- `U ⊓ V ⊓ W ↪ U ⊓ W` is an open embedding. -/
theorem tripleToPairOuter_isOpenEmbedding (U V W : Opens X) :
    IsOpenEmbedding (tripleToPairOuter U V W) := sorry

end Triple

end TopCat.Opens.Subspace

end

end
