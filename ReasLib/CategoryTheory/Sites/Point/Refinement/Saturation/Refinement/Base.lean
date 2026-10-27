/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.System
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Separation
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Refinement.Hom

/-!
# Initial finite-cover refinement stages

This leaf owns the canonical neutral stage whose target is the original
directed preorder diagram and whose refinement is the identity.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v q r r'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace RefinementStage

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι] [IsDirected ι (· ≤ ·)]
variable {J : GrothendieckTopology C}
variable (S : ιᵒᵖ ⥤ C)
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]

/-- The canonical initial refinement stage on a directed preorder diagram. -/
noncomputable def base : RefinementStage.{u, v, q, r, r} S where
  target := Target.of (DirectedPreorderSystem.ofDiagram S)
  refinement := OrderedRefinement.id S

namespace base

/-- The target of the initial refinement stage is the original diagram
packaged as a saturation target. -/
@[simp]
theorem target :
    (base S).target = Target.of (DirectedPreorderSystem.ofDiagram S) := rfl

/-- The directed preorder system of the initial refinement stage is the one
canonically associated to the original diagram. -/
@[simp]
theorem system :
    (base S).system = DirectedPreorderSystem.ofDiagram S := rfl

/-- The diagram of the initial refinement stage is the original diagram. -/
@[simp]
theorem diagram : (base S).diagram = S := rfl

/-- The refinement carried by the initial stage is the identity refinement. -/
@[simp]
theorem toRefinement :
    (base S).toRefinement = OrderedRefinement.id S := rfl

omit [IsDirected ι (· ≤ ·)]
  [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)] in
private theorem fiberMap_id :
    OrderedRefinement.EssentiallySmall.fiberMap (OrderedRefinement.id S) =
      𝟙 (EssentiallySmallFiber.fiber S) := by
  letI : InitiallySmall.{q} ιᵒᵖ := initiallySmall_of_essentiallySmall ιᵒᵖ
  letI : HasColimitsOfShape ιᵒᵖᵒᵖ (Type q) :=
    hasColimitsOfShape_of_finallySmall _ _
  apply NatTrans.ext
  funext X
  change colim.map (Reindexing.diagramMap (𝟭 ι) S (Reindexing.idIso S) X) ≫
      colimit.pre (Reindexing.fiberDiagram S X) (Reindexing.indexFunctor (𝟭 ι)) =
    𝟙 (colimit (Reindexing.fiberDiagram S X))
  apply colimit.hom_ext (F := Reindexing.fiberDiagram S X)
  intro i
  erw [← Category.assoc, colimit.ι_map, Category.assoc, colimit.ι_pre]
  change (shrinkYoneda.{q}.obj X).map
      ((𝟙 (S.obj i.unop)).op ≫ 𝟙 (op (S.obj i.unop))) ≫
        colimit.ι (Reindexing.fiberDiagram S X) i =
    colimit.ι (Reindexing.fiberDiagram S X) i ≫
      𝟙 (colimit (Reindexing.fiberDiagram S X))
  simp only [op_id, Category.comp_id, Functor.map_id, Category.id_comp]

/-- The initial refinement stage separates two fiber elements exactly when the
elements are distinct. -/
@[simp]
theorem separates_iff (P : Cᵒᵖ ⥤ Type q)
    (x y : (EssentiallySmallFiber.presheafFiber S).obj P) :
    OrderedRefinement.EssentiallySmall.Separates (base S).toRefinement P x y ↔
      x ≠ y := by
  have h : OrderedRefinement.EssentiallySmall.presheafFiberMap (OrderedRefinement.id S) =
      𝟙 (EssentiallySmallFiber.presheafFiber S) := by
    change (OrderedRefinement.EssentiallySmall.fiberMap (OrderedRefinement.id S)).presheafFiber = _
    rw [fiberMap_id]
    apply NatTrans.ext
    funext F
    apply colimit.hom_ext
    intro i
    change colimit.ι _ i ≫ colimit.desc _ _ = colimit.ι _ i ≫ 𝟙 _
    rw [colimit.ι_desc, Category.comp_id]
    rfl
  change (OrderedRefinement.EssentiallySmall.presheafFiberMap
    (OrderedRefinement.id S)).app P x ≠
      (OrderedRefinement.EssentiallySmall.presheafFiberMap
        (OrderedRefinement.id S)).app P y ↔ x ≠ y
  rw [h]
  rfl

/-- Distinct fiber elements are separated by the initial refinement stage. -/
theorem separates (P : Cᵒᵖ ⥤ Type q)
    {x y : (EssentiallySmallFiber.presheafFiber S).obj P} (hxy : x ≠ y) :
    OrderedRefinement.EssentiallySmall.Separates (base S).toRefinement P x y :=
  (separates_iff S P x y).2 hxy

/-- Transport from the original diagram to its initial stage leaves a request
unchanged. -/
@[simp]
theorem mapRequest
    (request : EssentiallySmallFiber.CoverLift.Request J S) :
    (base S).mapRequest request = request := by
  change request.map (OrderedRefinement.EssentiallySmall.fiberMap
    (OrderedRefinement.id S)) = request
  rw [fiberMap_id]
  rfl

end base

namespace baseTo

/-- The identity source refinement factors the refinement carried by any
finite-cover refinement stage. -/
theorem factorization (A : RefinementStage.{u, v, q, r, r'} S) :
    IsFactorization (base S).toRefinement A.toRefinement A.toRefinement := by
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  apply Iso.ext
  apply NatTrans.ext
  funext i
  change A.restrictionIso.hom.app i = 𝟙 _ ≫ (A.restrictionIso.hom.app i ≫ 𝟙 _)
  simp only [Category.id_comp, Category.comp_id]

end baseTo

/-- The canonical compatible morphism from the initial refinement stage to an
arbitrary finite-cover refinement stage. -/
noncomputable def baseTo (A : RefinementStage.{u, v, q, r, r'} S) :
    RefinementStage.Hom (base S) A where
  refinement := A.toRefinement
  factorization := baseTo.factorization S A

namespace baseTo

/-- The ordered refinement underlying the canonical base morphism is the
refinement carried by its target stage. -/
@[simp]
theorem toRefinement (A : RefinementStage.{u, v, q, r, r'} S) :
    (baseTo S A).toRefinement = A.toRefinement := rfl

/-- Transport along the canonical base morphism agrees with direct transport
from the original inverse system. -/
@[simp]
theorem mapRequest (A : RefinementStage.{u, v, q, r, r'} S)
    (request : EssentiallySmallFiber.CoverLift.Request J S) :
    (baseTo S A).mapRequest ((base S).mapRequest request) =
      A.mapRequest request := by
  rw [base.mapRequest]
  rfl

end baseTo

/- The non-proposition data of `base` are explicit; any `sorryAx` inherited by
the target is confined to packaged proof fields. -/

end RefinementStage
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
