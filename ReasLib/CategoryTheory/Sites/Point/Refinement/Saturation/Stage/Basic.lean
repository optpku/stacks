module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.SeparatingStage.Basic

/-!
# Scheduled separating refinement stages

This leaf adds finite-cover request scheduling to the neutral separating-stage
core. A stage records which requests at its target are already realized.
Morphisms and the category structure are layered separately.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v q r r' w'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation

variable {C : Type u} [Category.{v} C]

section Stage

variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}

/-- A scheduled separating refinement stage over `S`.  It keeps two arbitrary elements
of the presheaf fiber of `P` distinct, while recording a set of target finite-cover requests
whose realization is already known. -/
structure Stage
    (S : ιᵒᵖ ⥤ C) [LocallySmall.{q} C]
    [EssentiallySmall.{q} ιᵒᵖ]
    [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
    (P : Cᵒᵖ ⥤ Type q)
    (x y : (EssentiallySmallFiber.presheafFiber S).obj P)
    extends toSeparatingStage : SeparatingStage.{u, v, q, r, r'} S P x y where
  /-- The target finite-cover requests already scheduled and solved at this stage. -/
  solved : Set (toSeparatingStage.target.Request J)
  /-- Every recorded solved request is realized in the target fiber. -/
  solvedRealized : ∀ ⦃request : toSeparatingStage.target.Request J⦄,
    request ∈ solved → request.is_realized

namespace Stage

variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}

/-- The directed preorder system carried by a saturation stage. -/
abbrev system (A : Stage.{u, v, q, r, r'} (J := J) S P x y) :
    DirectedPreorderSystem.{u, v, r'} C :=
  A.toSeparatingStage.system

/-- The index preorder of a saturation stage. -/
abbrev index (A : Stage.{u, v, q, r, r'} (J := J) S P x y) : Type r' :=
  A.system.index

/-- The inverse-system diagram of a saturation stage. -/
abbrev diagram (A : Stage.{u, v, q, r, r'} (J := J) S P x y) : A.indexᵒᵖ ⥤ C :=
  A.toSeparatingStage.diagram

/-- The ordered refinement from the original inverse system to a saturation stage. -/
abbrev toRefinement (A : Stage.{u, v, q, r, r'} (J := J) S P x y) :
  OrderedRefinement S A.diagram :=
  A.toSeparatingStage.toRefinement

/-- The order embedding of a stage refinement. -/
abbrev embedding (A : Stage.{u, v, q, r, r'} (J := J) S P x y) : ι ↪o A.index :=
  A.toRefinement.embedding

/-- The inverse-system comparison isomorphism carried by a stage refinement. -/
abbrev restrictionIso (A : Stage.{u, v, q, r, r'} (J := J) S P x y) :
    S ≅ (A.embedding.toOrderHom.toFunctor).op ⋙ A.diagram :=
  A.toRefinement.restrictionIso

/-- Scheduled stages are determined by their separating stage and solved-request set;
the realization certificate is proposition-valued. -/
@[ext]
theorem ext {A B : Stage.{u, v, q, r, r'} (J := J) S P x y}
    (h_separating : A.toSeparatingStage = B.toSeparatingStage)
    (h_solved : HEq A.solved B.solved) :
    A = B := sorry

/-- Transport a finite-cover request from the original system to a saturation stage. -/
noncomputable def mapRequest (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : EssentiallySmallFiber.CoverLift.Request J S) : A.target.Request J :=
  A.toSeparatingStage.mapRequest request

namespace mapRequest

/-- A realized source request remains realized after transport to a scheduled-stage target. -/
theorem isRealized (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : EssentiallySmallFiber.CoverLift.Request J S) :
    request.is_realized → (A.mapRequest request).is_realized := sorry

end mapRequest

/-- A stage solves a source request when its refinement realizes the transported request. -/
def solves (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : EssentiallySmallFiber.CoverLift.Request J S) : Prop :=
  A.toSeparatingStage.solves request

/-- The source-facing solved predicate is equivalent to realization after transport to the
scheduled-stage target. -/
@[simp]
theorem solves_iff (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : EssentiallySmallFiber.CoverLift.Request J S) :
    A.solves request ↔ (A.mapRequest request).is_realized := sorry

namespace toSeparatingStage

/-- Forgetting scheduling does not change transport of a request from the original system. -/
@[simp]
theorem mapRequest
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : EssentiallySmallFiber.CoverLift.Request J S) :
    A.toSeparatingStage.mapRequest request = A.mapRequest request := sorry

/-- Forgetting scheduling does not change whether a source request is solved. -/
@[simp]
theorem solves_iff
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : EssentiallySmallFiber.CoverLift.Request J S) :
    A.toSeparatingStage.solves request ↔ A.solves request := sorry

end toSeparatingStage

/-- A scheduled saturation stage is target-complete when every finite-cover request on its
target fiber is realized. -/
def targetComplete (A : Stage.{u, v, q, r, r'} (J := J) S P x y) : Prop :=
  A.target.complete J

/-- Target completion of a scheduled saturation stage is equivalent to finite-cover lifting on
its target fiber. -/
theorem targetComplete_iff_finiteCoverLifts
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y) :
    A.targetComplete ↔
      Functor.FiniteCoverLifts.{u, v, q, w'} A.target.fiber J := sorry

/-- A scheduled saturation stage is source-complete when it solves every finite-cover request
on the original inverse-system fiber. -/
def sourceComplete (A : Stage.{u, v, q, r, r'} (J := J) S P x y) : Prop :=
  A.toSeparatingStage.sourceComplete J

/-- Source completion of a scheduled saturation stage is equivalent to finite-cover lifting by
its refinement map. -/
theorem sourceComplete_iff_finiteCoverLifts
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y) :
    A.sourceComplete ↔
      NatTrans.FiniteCoverLifts.{u, v, q, w'}
        (OrderedRefinement.EssentiallySmall.fiberMap A.toRefinement) J := sorry

/-- Target completion implies source completion along the refinement carried by a scheduled
saturation stage. -/
theorem sourceComplete_of_targetComplete
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y) :
    A.targetComplete → A.sourceComplete := sorry

namespace toSeparatingStage

/-- Forgetting scheduling preserves source completion. -/
@[simp]
theorem sourceComplete_iff
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y) :
    A.toSeparatingStage.sourceComplete J ↔ A.sourceComplete := sorry

end toSeparatingStage

end Stage

end Stage

end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
