/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Target.Basic

/-!
# Unseparated finite-cover refinement stages

This leaf owns the object-level data and semantic API for compatible
refinements with finite-cover lifting. Morphisms and category structure are
layered separately.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v q r r' w'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}

/-- A finite-cover refinement stage over an inverse system.  Unlike
`SeparatingStage`, this canonical core does not select a presheaf or a pair of
elements to keep distinct. -/
structure RefinementStage
    (S : ιᵒᵖ ⥤ C) [LocallySmall.{q} C]
    [EssentiallySmall.{q} ιᵒᵖ]
    [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)] where
  /-- The directed target system together with its fiber support. -/
  target : Target.{u, v, q, r'} C
  /-- The canonical ordered refinement from the original inverse system. -/
  refinement : OrderedRefinement S target.diagram

namespace RefinementStage

variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]

/-- The directed preorder system carried by a finite-cover refinement stage. -/
abbrev system (A : RefinementStage.{u, v, q, r, r'} S) :
    DirectedPreorderSystem.{u, v, r'} C :=
  A.target.system

/-- The index preorder of a finite-cover refinement stage. -/
abbrev index (A : RefinementStage.{u, v, q, r, r'} S) : Type r' :=
  A.system.index

/-- The inverse-system diagram of a finite-cover refinement stage. -/
abbrev diagram (A : RefinementStage.{u, v, q, r, r'} S) : A.indexᵒᵖ ⥤ C :=
  A.system.diagram

/-- The ordered refinement from the original system to a finite-cover refinement stage. -/
abbrev toRefinement (A : RefinementStage.{u, v, q, r, r'} S) :
    OrderedRefinement S A.diagram :=
  A.refinement

/-- The order embedding carried by a finite-cover refinement stage. -/
abbrev embedding (A : RefinementStage.{u, v, q, r, r'} S) : ι ↪o A.index :=
  A.toRefinement.embedding

/-- The restriction isomorphism carried by a finite-cover refinement stage. -/
abbrev restrictionIso (A : RefinementStage.{u, v, q, r, r'} S) :
    S ≅ (A.embedding.toOrderHom.toFunctor).op ⋙ A.diagram :=
  A.toRefinement.restrictionIso

/-- Refinement stages are determined by their target and underlying ordered refinement;
the latter is heterogeneous because its codomain depends on the target. -/
@[ext]
theorem ext {A B : RefinementStage.{u, v, q, r, r'} S}
    (h_target : A.target = B.target)
    (h_refinement : HEq A.toRefinement B.toRefinement) :
    A = B := sorry

/-- Transport a finite-cover request from the original system to a refinement-stage target. -/
noncomputable def mapRequest (A : RefinementStage.{u, v, q, r, r'} S)
    (request : EssentiallySmallFiber.CoverLift.Request J S) : A.target.Request J :=
  A.toRefinement.mapRequest request

namespace mapRequest

/-- A realized source request remains realized after transport to a refinement-stage target. -/
theorem isRealized (A : RefinementStage.{u, v, q, r, r'} S)
    (request : EssentiallySmallFiber.CoverLift.Request J S) :
    request.is_realized → (A.mapRequest request).is_realized := sorry

end mapRequest

/-- A finite-cover refinement stage solves a source request when its transported request is
realized at the target. -/
def solves (A : RefinementStage.{u, v, q, r, r'} S)
    (request : EssentiallySmallFiber.CoverLift.Request J S) : Prop :=
  A.toRefinement.solves request

/-- The source-facing solved predicate is realization after transport to the target. -/
@[simp]
theorem solves_iff (A : RefinementStage.{u, v, q, r, r'} S)
    (request : EssentiallySmallFiber.CoverLift.Request J S) :
    A.solves request ↔ (A.mapRequest request).is_realized := sorry

/-- Source completion means that the refinement solves every finite-cover request from the
original inverse-system fiber. -/
def sourceComplete (A : RefinementStage.{u, v, q, r, r'} S)
    (J : GrothendieckTopology C) : Prop :=
  ∀ request : EssentiallySmallFiber.CoverLift.Request J S, A.solves request

/-- Source completion is finite-cover lifting by the stage refinement. -/
theorem sourceComplete_iff_finiteCoverLifts
    (A : RefinementStage.{u, v, q, r, r'} S)
    (J : GrothendieckTopology C) :
    A.sourceComplete J ↔
      NatTrans.FiniteCoverLifts.{u, v, q, w'}
        (OrderedRefinement.EssentiallySmall.fiberMap A.toRefinement) J := sorry

/-- Target completion propagates to source completion along a refinement stage. -/
theorem sourceComplete_of_targetComplete
    (A : RefinementStage.{u, v, q, r, r'} S)
    (J : GrothendieckTopology C) :
    A.target.complete J → A.sourceComplete J := sorry

end RefinementStage

end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
