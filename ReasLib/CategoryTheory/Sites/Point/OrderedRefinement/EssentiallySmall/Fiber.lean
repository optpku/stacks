module

public import ReasLib.CategoryTheory.Sites.Point.OrderedRefinement.Basic
public import ReasLib.CategoryTheory.Sites.Point.Reindexing.OrderEmbedding.EssentiallySmall

/-!
# Fiber maps of essentially-small ordered refinements

This module attaches the essentially-small object-fiber reindexing map to a
bundled `OrderedRefinement` and exposes its computation and coherence API.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v q w₀ w₁ w₂

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

variable {C : Type u} [Category.{v} C]

namespace OrderedRefinement.EssentiallySmall

variable {ι : Type w₀} [Preorder ι]
variable {ι' : Type w₁} [Preorder ι']
variable {ι'' : Type w₂} [Preorder ι'']
variable {S : ιᵒᵖ ⥤ C} {T : ι'ᵒᵖ ⥤ C} {U : ι''ᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [CategoryTheory.EssentiallySmall.{q} ιᵒᵖ]
  [CategoryTheory.EssentiallySmall.{q} ι'ᵒᵖ]

/-- The object-fiber map induced by a pure refinement of essentially-small
inverse systems. -/
noncomputable def fiberMap (R : OrderedRefinement S T) :
    EssentiallySmallFiber.fiber S ⟶ EssentiallySmallFiber.fiber T :=
  Reindexing.OrderEmbedding.EssentiallySmall.fiberMap
    R.embedding T R.restrictionIso

/-- The essentially-small fiber map of a pure refinement transports canonical
fiber generators along its stored restriction isomorphism. -/
@[simp]
theorem fiberMap_app_mk
    (R : OrderedRefinement S T) {U : ιᵒᵖ} {W : C} (f : S.obj U ⟶ W) :
    (fiberMap R).app W (EssentiallySmallFiber.mk (S := S) f) =
      EssentiallySmallFiber.mk (S := T) (R.restrictionIso.inv.app U ≫ f) := sorry

/-- The essentially-small fiber map of the identity pure refinement is the
identity. -/
@[simp]
theorem fiberMap_id (S : ιᵒᵖ ⥤ C) :
    fiberMap (id S) = 𝟙 (EssentiallySmallFiber.fiber S) := sorry

section Composition

variable [CategoryTheory.EssentiallySmall.{q} ι''ᵒᵖ]

/-- The essentially-small fiber map of a composite pure refinement is the
composite of its fiber maps. -/
@[simp]
theorem fiberMap_comp
    (R : OrderedRefinement S T) (Q : OrderedRefinement T U) :
    fiberMap (R.comp Q) = fiberMap R ≫ fiberMap Q := sorry

end Composition

end OrderedRefinement.EssentiallySmall

namespace OrderedRefinement.IsFactorization.EssentiallySmall

variable {ι : Type w₀} [Preorder ι]
variable {ι' : Type w₁} [Preorder ι']
variable {ι'' : Type w₂} [Preorder ι'']
variable {S : ιᵒᵖ ⥤ C} {T : ι'ᵒᵖ ⥤ C} {U : ι''ᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [CategoryTheory.EssentiallySmall.{q} ιᵒᵖ]
  [CategoryTheory.EssentiallySmall.{q} ι'ᵒᵖ]
  [CategoryTheory.EssentiallySmall.{q} ι''ᵒᵖ]

/-- A factorization of pure refinements induces the corresponding composite map on
essentially-small inverse-system fibers. -/
theorem fiberMap
    {R : OrderedRefinement S T} {Q : OrderedRefinement T U}
    {P : OrderedRefinement S U} (h : IsFactorization R Q P) :
    OrderedRefinement.EssentiallySmall.fiberMap P =
      OrderedRefinement.EssentiallySmall.fiberMap R ≫
        OrderedRefinement.EssentiallySmall.fiberMap Q := sorry

end OrderedRefinement.IsFactorization.EssentiallySmall

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
