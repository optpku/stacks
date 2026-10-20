module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.SeparatingStage.Category
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Stage.Basic

/-!
# Morphisms of scheduled separating refinement stages

This leaf owns solved-request-preserving morphisms between scheduled stages and
their request-transport API. Identity, composition, and the category instance
are layered separately in `Stage.Category`.
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
variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}

namespace Stage

/-- A morphism of scheduled saturation stages is a factorized separating-stage morphism that
carries solved requests forward. -/
structure Hom
    (A B : Stage.{u, v, q, r, r'} (J := J) S P x y)
    extends toSeparatingStage :
      SeparatingStage.Hom A.toSeparatingStage B.toSeparatingStage where
  /-- Solved requests of the source stage remain solved after transport. -/
  solvedMono : ∀ ⦃request : A.toSeparatingStage.target.Request J⦄, request ∈ A.solved →
    toSeparatingStage.mapRequest request ∈ B.solved

namespace Hom

variable {A B : Stage.{u, v, q, r, r'} (J := J) S P x y}

/-- The ordered refinement carried by a stage morphism. -/
abbrev toRefinement (f : Hom A B) : OrderedRefinement A.diagram B.diagram :=
  f.toSeparatingStage.toRefinement

/-- Transport a finite-cover request along a morphism of saturation stages. -/
noncomputable def mapRequest (f : Hom A B)
    (request : A.toSeparatingStage.target.Request J) : B.toSeparatingStage.target.Request J :=
  f.toSeparatingStage.mapRequest request

namespace mapRequest

/-- A realized target request remains realized after transport along a scheduled-stage
morphism. -/
theorem isRealized (f : Hom A B)
    (request : A.toSeparatingStage.target.Request J) :
    request.is_realized → (f.mapRequest request).is_realized := sorry

/-- Transporting an original-system request through a stage morphism agrees with direct
transport to the target stage. -/
theorem fromSource (f : Hom A B)
    (request : EssentiallySmallFiber.CoverLift.Request J S) :
    f.mapRequest (A.mapRequest request) = B.mapRequest request := sorry

end mapRequest

namespace toSeparatingStage

/-- Forgetting scheduling does not change target-request transport along a stage morphism. -/
@[simp]
theorem mapRequest (f : Hom A B)
    (request : A.toSeparatingStage.target.Request J) :
    f.toSeparatingStage.mapRequest request = f.mapRequest request := sorry

end toSeparatingStage

/-- A saturation-stage morphism realizes every finite-cover request at its source target. -/
abbrev realizesAll (f : Hom A B) : Prop :=
  f.toSeparatingStage.realizesAll (J := J)

/-- The stage-level all-request realization predicate is finite-cover lifting by the underlying
refinement map. -/
theorem realizesAll_iff_finiteCoverLifts (f : Hom A B) :
    f.realizesAll ↔
      NatTrans.FiniteCoverLifts.{u, v, q, w'}
        (OrderedRefinement.EssentiallySmall.fiberMap f.toRefinement) J := sorry

namespace toSeparatingStage

/-- Forgetting scheduling preserves the all-request realization predicate. -/
@[simp]
theorem realizesAll_iff (f : Hom A B) :
    f.toSeparatingStage.realizesAll (J := J) ↔ f.realizesAll := sorry

end toSeparatingStage

/-- A scheduled-stage morphism carries every recorded solved request to a recorded solved
request at its target. -/
theorem mapRequest.memSolved (f : Hom A B)
    {request : A.toSeparatingStage.target.Request J}
    (h_request : request ∈ A.solved) : f.mapRequest request ∈ B.solved := sorry

/-- A request recorded as solved remains realized after transport along a scheduled-stage
morphism. -/
theorem mapRequest.isRealized.ofMem (f : Hom A B)
    {request : A.toSeparatingStage.target.Request J} (h_request : request ∈ A.solved) :
    (f.mapRequest request).is_realized := sorry

end Hom
end Stage

end Stage

end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
