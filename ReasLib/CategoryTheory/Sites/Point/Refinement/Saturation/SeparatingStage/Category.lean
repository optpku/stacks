/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.SeparatingStage.Basic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Refinement.Category

/-!
# The category of separating refinement stages

This file owns factorized morphisms of separating stages, their finite-cover request API, identity
and composition, and the resulting category instance.
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

namespace SeparatingStage

/-- A morphism of separating stages is a further refinement compatible with their original
refinements. Its data and factorization condition are exactly those of
`RefinementStage.Hom` on the inherited stages. -/
structure Hom (A B : SeparatingStage.{u, v, q, r, r'} S P x y)
    extends toBase : RefinementStage.Hom A.toRefinementStage B.toRefinementStage

namespace Hom

variable {A B D E : SeparatingStage.{u, v, q, r, r'} S P x y}

/-- The ordered refinement carried by a separating-stage morphism. -/
abbrev toRefinement (f : Hom A B) : OrderedRefinement A.diagram B.diagram :=
  RefinementStage.Hom.toRefinement f.toBase

/-- Transport a finite-cover request along a separating-stage morphism. -/
noncomputable def mapRequest (f : Hom A B) (request : A.target.Request J) :
    B.target.Request J :=
  RefinementStage.Hom.mapRequest f.toBase request

namespace mapRequest

/-- A realized target request remains realized after transport along a separating-stage
morphism. -/
theorem isRealized (f : Hom A B) (request : A.target.Request J) :
    request.is_realized → (f.mapRequest request).is_realized :=
  RefinementStage.Hom.mapRequest.isRealized f.toBase request

/-- Transporting a request from the original system and then along a separating-stage morphism
agrees with transporting it directly to the target stage. -/
theorem fromSource (f : Hom A B)
    (request : EssentiallySmallFiber.CoverLift.Request J S) :
    f.mapRequest (A.mapRequest request) = B.mapRequest request :=
  RefinementStage.Hom.mapRequest.fromSource f.toBase request

end mapRequest

/-- A separating-stage morphism realizes all finite-cover requests already present at its source
target. -/
def realizesAll (f : Hom A B) : Prop :=
  RefinementStage.Hom.realizesAll (J := J) f.toBase

/-- Realizing every source-target request is equivalent to finite-cover lifting by the underlying
refinement map. -/
theorem realizesAll_iff_finiteCoverLifts (f : Hom A B) :
    f.realizesAll (J := J) ↔
      NatTrans.FiniteCoverLifts.{u, v, q, w'}
        (OrderedRefinement.EssentiallySmall.fiberMap f.toRefinement) J :=
  RefinementStage.Hom.realizesAll_iff_finiteCoverLifts f.toBase

/-- The identity morphism of a separating stage. -/
noncomputable def id (A : SeparatingStage.{u, v, q, r, r'} S P x y) : Hom A A where
  toBase := RefinementStage.Hom.id A.toRefinementStage

/-- Compose two morphisms of separating stages. -/
noncomputable def comp (f : Hom A B) (g : Hom B D) : Hom A D where
  toBase := RefinementStage.Hom.comp f.toBase g.toBase

/-- The ordered refinement underlying an identity separating-stage morphism is the identity
refinement. -/
@[simp]
theorem id.toRefinement (A : SeparatingStage.{u, v, q, r, r'} S P x y) :
    (id A).toRefinement = OrderedRefinement.id A.diagram := rfl

/-- The ordered refinement underlying a composite separating-stage morphism is the composite of
the underlying refinements. -/
@[simp]
theorem comp.toRefinement (f : Hom A B) (g : Hom B D) :
    (comp f g).toRefinement = f.toRefinement.comp g.toRefinement := rfl

/-- Separating-stage morphisms are determined by their ordered refinement. -/
@[ext]
theorem ext {f g : Hom A B} (h_refinement : f.toRefinement = g.toRefinement) : f = g := by
  cases f with
  | mk f =>
    cases g with
    | mk g =>
      have h : f = g := RefinementStage.Hom.ext h_refinement
      cases h
      rfl

/-- Mapping a request through an identity separating-stage morphism leaves it unchanged. -/
@[simp]
theorem id.mapRequest (A : SeparatingStage.{u, v, q, r, r'} S P x y)
    (request : A.target.Request J) : mapRequest (id A) request = request :=
  RefinementStage.Hom.id.mapRequest A.toRefinementStage request

/-- Mapping a request through a composite separating-stage morphism agrees with successive
transport. -/
@[simp]
theorem comp.mapRequest (f : Hom A B) (g : Hom B D) (request : A.target.Request J) :
    mapRequest (comp f g) request = mapRequest g (mapRequest f request) :=
  RefinementStage.Hom.comp.mapRequest f.toBase g.toBase request

/-- Composing an identity separating-stage morphism on the left leaves a morphism unchanged. -/
theorem id_comp (f : Hom A B) : comp (id A) f = f := by
  apply ext
  exact congrArg RefinementStage.Hom.toRefinement (RefinementStage.Hom.id_comp f.toBase)

/-- Composing an identity separating-stage morphism on the right leaves a morphism unchanged. -/
theorem comp_id (f : Hom A B) : comp f (id B) = f := by
  apply ext
  exact congrArg RefinementStage.Hom.toRefinement (RefinementStage.Hom.comp_id f.toBase)

/-- Composition of separating-stage morphisms is associative. -/
theorem comp_assoc (f : Hom A B) (g : Hom B D) (h : Hom D E) :
    comp (comp f g) h = comp f (comp g h) := by
  apply ext
  exact congrArg RefinementStage.Hom.toRefinement
    (RefinementStage.Hom.comp_assoc f.toBase g.toBase h.toBase)

end Hom

/-- Separating stages and factorized refinement morphisms form a category. -/
noncomputable instance instCategory :
    Category (SeparatingStage.{u, v, q, r, r'} S P x y) where
  Hom A B := Hom A B
  id A := Hom.id A
  comp f g := Hom.comp f g
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

end SeparatingStage

end Stage

end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
