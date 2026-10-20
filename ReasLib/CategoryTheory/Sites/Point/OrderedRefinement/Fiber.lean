/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.OrderedRefinement.Basic
public import ReasLib.CategoryTheory.Sites.Point.Reindexing.OrderEmbedding.Fiber

/-!
# Fiber maps of ordered refinements

This module attaches object-fiber maps to bundled `OrderedRefinement` data and
provides identity, composition, and factorization computation rules.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v q w₀ w₁ w₂

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.OrderedRefinement

variable {C : Type u} [Category.{v} C]
variable {ι : Type w₀} [Preorder ι]
variable {ι' : Type w₁} [Preorder ι']
variable {ι'' : Type w₂} [Preorder ι'']
variable {S : ιᵒᵖ ⥤ C} {T : ι'ᵒᵖ ⥤ C} {U : ι''ᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [InitiallySmall.{q} ιᵒᵖ] [InitiallySmall.{q} ι'ᵒᵖ]

/-- The object-fiber map induced by a pure order-embedding refinement. -/
noncomputable def fiberMap (R : OrderedRefinement S T) :
    ofIsCofiltered.fiber.{q} S ⟶ ofIsCofiltered.fiber.{q} T :=
  Reindexing.OrderEmbedding.fiber R.embedding T R.restrictionIso

/-- The fiber map of the identity pure refinement is the identity. -/
@[simp]
theorem fiberMap_id (S : ιᵒᵖ ⥤ C) :
    fiberMap (id S) = 𝟙 (ofIsCofiltered.fiber.{q} S) := sorry

section Composition

variable [InitiallySmall.{q} ι''ᵒᵖ]

/-- The fiber map of a composite pure refinement is the composite of its
fiber maps. -/
@[simp]
theorem fiberMap_comp (R : OrderedRefinement S T) (Q : OrderedRefinement T U) :
    fiberMap (R.comp Q) = R.fiberMap ≫ Q.fiberMap := sorry

end Composition

namespace IsFactorization

variable [InitiallySmall.{q} ι''ᵒᵖ]

/-- A refinement whose embedding and restriction isomorphism factor through two others induces
the composite map on inverse-system fibers.  This is the fiber-level elimination rule for
`IsFactorization`; it is independent of any application-specific refinement-stage payload. -/
theorem fiberMap
    {R : OrderedRefinement S T} {Q : OrderedRefinement T U}
    {P : OrderedRefinement S U} (h : IsFactorization R Q P) :
    P.fiberMap = R.fiberMap ≫ Q.fiberMap := sorry

end IsFactorization

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.OrderedRefinement
