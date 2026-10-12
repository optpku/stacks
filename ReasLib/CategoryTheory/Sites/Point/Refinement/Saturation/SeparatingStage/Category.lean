/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.SeparatingStage.Basic

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
refinements. -/
structure Hom (A B : SeparatingStage.{u, v, q, r, r'} S P x y) where
  /-- The ordered refinement from the source separating-stage target to the target one. -/
  refinement : OrderedRefinement A.diagram B.diagram
  /-- The target-stage refinement factors through the source-stage refinement. -/
  factorization : IsFactorization A.toRefinement refinement B.toRefinement

namespace Hom

variable {A B D E : SeparatingStage.{u, v, q, r, r'} S P x y}

/-- The ordered refinement carried by a separating-stage morphism. -/
abbrev toRefinement (f : Hom A B) : OrderedRefinement A.diagram B.diagram :=
  f.refinement

/-- Transport a finite-cover request along a separating-stage morphism. -/
noncomputable def mapRequest (f : Hom A B) (request : A.target.Request J) :
    B.target.Request J :=
  f.toRefinement.mapRequest request

namespace mapRequest

/-- A realized target request remains realized after transport along a separating-stage
morphism. -/
theorem isRealized (f : Hom A B) (request : A.target.Request J) :
    request.is_realized → (f.mapRequest request).is_realized := sorry

/-- Transporting a request from the original system and then along a separating-stage morphism
agrees with transporting it directly to the target stage. -/
theorem fromSource (f : Hom A B)
    (request : EssentiallySmallFiber.CoverLift.Request J S) :
    f.mapRequest (A.mapRequest request) = B.mapRequest request := sorry

end mapRequest

/-- A separating-stage morphism realizes all finite-cover requests already present at its source
target. -/
def realizesAll (f : Hom A B) : Prop :=
  ∀ request : A.target.Request J, (f.mapRequest request).is_realized

/-- Realizing every source-target request is equivalent to finite-cover lifting by the underlying
refinement map. -/
theorem realizesAll_iff_finiteCoverLifts (f : Hom A B) :
    f.realizesAll (J := J) ↔
      NatTrans.FiniteCoverLifts.{u, v, q, w'}
        (OrderedRefinement.EssentiallySmall.fiberMap f.toRefinement) J := sorry

/-- The identity morphism of a separating stage. -/
noncomputable def id (A : SeparatingStage.{u, v, q, r, r'} S P x y) : Hom A A where
  refinement := OrderedRefinement.id A.diagram
  factorization := IsFactorization.id_right A.toRefinement

/-- Compose two morphisms of separating stages. -/
noncomputable def comp (f : Hom A B) (g : Hom B D) : Hom A D where
  refinement := f.toRefinement.comp g.toRefinement
  factorization := IsFactorization.trans f.factorization g.factorization

/-- The ordered refinement underlying an identity separating-stage morphism is the identity
refinement. -/
@[simp]
theorem id.toRefinement (A : SeparatingStage.{u, v, q, r, r'} S P x y) :
    (id A).toRefinement = OrderedRefinement.id A.diagram := sorry

/-- The ordered refinement underlying a composite separating-stage morphism is the composite of
the underlying refinements. -/
@[simp]
theorem comp.toRefinement (f : Hom A B) (g : Hom B D) :
    (comp f g).toRefinement = f.toRefinement.comp g.toRefinement := sorry

/-- Separating-stage morphisms are determined by their ordered refinement. -/
@[ext]
theorem ext {f g : Hom A B} (h_refinement : f.toRefinement = g.toRefinement) : f = g := sorry

/-- Mapping a request through an identity separating-stage morphism leaves it unchanged. -/
@[simp]
theorem id.mapRequest (A : SeparatingStage.{u, v, q, r, r'} S P x y)
    (request : A.target.Request J) : mapRequest (id A) request = request := sorry

/-- Mapping a request through a composite separating-stage morphism agrees with successive
transport. -/
@[simp]
theorem comp.mapRequest (f : Hom A B) (g : Hom B D) (request : A.target.Request J) :
    mapRequest (comp f g) request = mapRequest g (mapRequest f request) := sorry

/-- Composing an identity separating-stage morphism on the left leaves a morphism unchanged. -/
theorem id_comp (f : Hom A B) : comp (id A) f = f := sorry

/-- Composing an identity separating-stage morphism on the right leaves a morphism unchanged. -/
theorem comp_id (f : Hom A B) : comp f (id B) = f := sorry

/-- Composition of separating-stage morphisms is associative. -/
theorem comp_assoc (f : Hom A B) (g : Hom B D) (h : Hom D E) :
    comp (comp f g) h = comp f (comp g h) := sorry

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
