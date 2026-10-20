/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Separation
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Target.Basic

/-!
# Separating refinement stages

This file owns the topology-independent separating-stage data and its object-level finite-cover
API.  Morphisms and the category structure are layered separately in `SeparatingStage.Category`.
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

/-- A refinement stage that separates two elements of an arbitrary presheaf fiber.
This core is independent of a topology and of any request-scheduling policy. -/
structure SeparatingStage
    (S : ιᵒᵖ ⥤ C) [LocallySmall.{q} C]
    [EssentiallySmall.{q} ιᵒᵖ]
    [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
    (P : Cᵒᵖ ⥤ Type q)
    (x y : (EssentiallySmallFiber.presheafFiber S).obj P) where
  /-- The possibly empty directed preorder system at the refined stage. -/
  target : Target.{u, v, q, r'} C
  /-- The canonical refinement from the original inverse system to the target. -/
  refinement : OrderedRefinement S target.diagram
  /-- The refinement separates the chosen source fiber elements. -/
  separates : OrderedRefinement.EssentiallySmall.Separates refinement P x y

namespace SeparatingStage

variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}

/-- The directed preorder system carried by a separating stage. -/
abbrev system (A : SeparatingStage.{u, v, q, r, r'} S P x y) :
    DirectedPreorderSystem.{u, v, r'} C :=
  A.target.system

/-- The index preorder of a separating stage. -/
abbrev index (A : SeparatingStage.{u, v, q, r, r'} S P x y) : Type r' :=
  A.system.index

/-- The inverse-system diagram of a separating stage. -/
abbrev diagram (A : SeparatingStage.{u, v, q, r, r'} S P x y) : A.indexᵒᵖ ⥤ C :=
  A.system.diagram

/-- The ordered refinement from the original inverse system to a separating stage. -/
abbrev toRefinement (A : SeparatingStage.{u, v, q, r, r'} S P x y) :
    OrderedRefinement S A.diagram :=
  A.refinement

/-- The order embedding of a separating-stage refinement. -/
abbrev embedding (A : SeparatingStage.{u, v, q, r, r'} S P x y) : ι ↪o A.index :=
  A.toRefinement.embedding

/-- The inverse-system comparison isomorphism carried by a separating-stage refinement. -/
abbrev restrictionIso (A : SeparatingStage.{u, v, q, r, r'} S P x y) :
    S ≅ (A.embedding.toOrderHom.toFunctor).op ⋙ A.diagram :=
  A.toRefinement.restrictionIso

/-- Separating stages are determined by their target and underlying ordered refinement;
the separation witness is proposition-valued. -/
@[ext]
theorem ext {A B : SeparatingStage.{u, v, q, r, r'} S P x y}
    (h_target : A.target = B.target)
    (h_refinement : HEq A.toRefinement B.toRefinement) :
    A = B := sorry

/-- Transport a finite-cover request from the original system to a separating-stage target. -/
noncomputable def mapRequest (A : SeparatingStage.{u, v, q, r, r'} S P x y)
    (request : EssentiallySmallFiber.CoverLift.Request J S) : A.target.Request J :=
  A.toRefinement.mapRequest request

namespace mapRequest

/-- A realized source request remains realized after transport to a separating-stage target. -/
theorem isRealized (A : SeparatingStage.{u, v, q, r, r'} S P x y)
    (request : EssentiallySmallFiber.CoverLift.Request J S) :
    request.is_realized → (A.mapRequest request).is_realized := sorry

end mapRequest

/-- A separating stage solves a source request when its refinement realizes the transported
request. -/
def solves (A : SeparatingStage.{u, v, q, r, r'} S P x y)
    (request : EssentiallySmallFiber.CoverLift.Request J S) : Prop :=
  A.toRefinement.solves request

/-- The source-facing solved predicate is equivalent to realization after transport to the
separating-stage target. -/
@[simp]
theorem solves_iff (A : SeparatingStage.{u, v, q, r, r'} S P x y)
    (request : EssentiallySmallFiber.CoverLift.Request J S) :
    A.solves request ↔ (A.mapRequest request).is_realized := sorry

/-- Source completion means that the separating refinement solves every finite-cover request on
the original inverse-system fiber. -/
def sourceComplete (A : SeparatingStage.{u, v, q, r, r'} S P x y)
    (J : GrothendieckTopology C) : Prop :=
  ∀ request : EssentiallySmallFiber.CoverLift.Request J S, A.solves request

/-- Source completion is equivalent to finite-cover lifting of the separating refinement, in every
cover-family universe `w'`. -/
theorem sourceComplete_iff_finiteCoverLifts
    (A : SeparatingStage.{u, v, q, r, r'} S P x y)
    (J : GrothendieckTopology C) :
    A.sourceComplete J ↔
      NatTrans.FiniteCoverLifts.{u, v, q, w'}
        (OrderedRefinement.EssentiallySmall.fiberMap A.toRefinement) J := sorry

/-- Completion of a target fiber implies source completion along a separating refinement. -/
theorem sourceComplete_of_targetComplete
    (A : SeparatingStage.{u, v, q, r, r'} S P x y)
    (J : GrothendieckTopology C) :
    A.target.complete J → A.sourceComplete J := sorry

end SeparatingStage

end Stage

end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
