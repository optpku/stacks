/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.FstFiber.Basic

/-!
# Inverse structured-arrow comparison for a pseudo-pullback fibre

This leaf constructs the inverse functor from the fixed first fibre back to structured arrows and
records its direct component formulas. It depends only on the comparison in `FstFiber.Basic`.
-/

@[expose] public section

universe uC vC uX vX uY vY

namespace CategoryTheory

open BasedCategory
open BasedFunctor
open Functor
open Functor.Fiber
open CategoryTheory.Limits
open Functor.IsHomLift

variable {C : Type uC} [Category.{vC} C]
variable {X : Type uX} [Category.{vX} X]
variable {Y : Type uY} [Category.{vY} Y]
variable {pX : X ⥤ C} {pY : Y ⥤ C}

namespace BasedCategory.PseudoPullback
namespace FstFiber

variable {U : C}
variable (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor pY)
variable (F : BasedCategory.ofFunctor pX ⥤ᵇ BasedCategory.ofFunctor pY)

section FromFiberImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The common base of a pseudo-pullback object in the fibre of the first projection is the
domain of the fixed slice object.

Proof strategy: compose the equality stored by the first fibre component with the image under
`Over.left` of the outer-fibre equality. -/
private theorem fromFiberBaseEq
    (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    PseudoPullback.baseObj Q.1 = f.left := sorry

/-- The right component of an object in the fibre of the first projection, transported to the
standard fibre of `pX` over `f.left`. Its underlying total object is definitionally the second
pseudo-pullback component; only its Prop-valued base equality is transported. -/
private def fromFiberRight
    (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    pX.Fiber f.left :=
  ⟨PseudoPullback.sndObj Q.1,
    (PseudoPullback.fiberObj Q.1).snd.2.trans
      (fromFiberBaseEq G F f Q)⟩

/-- The ambient arrow underlying the structured arrow recovered from an object in the fibre of
the first projection. The only endpoint transport is induced by the supplied outer-fibre
equality; the mathematical map is the stored pseudo-pullback comparison. -/
private def fromFiberHomVal
    (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    ((G.fiberFunctor f.left).obj (Fiber.mk rfl)).1 ⟶
      ((F.fiberFunctor f.left).obj (fromFiberRight G F f Q)).1 :=
  eqToHom (congrArg G.toFunctor.obj Q.2.symm) ≫
    PseudoPullback.comparison Q.1

/-- The recovered comparison arrow is vertical over `f.left`.

Proof strategy: combine the endpoint transport with
`PseudoPullback.comparison.isHomLift`, then rewrite the common base using
`fromFiberBaseEq`. -/
private theorem fromFiberHomValIsHomLift
    (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    pY.IsHomLift (𝟙 f.left) (fromFiberHomVal G F f Q) := sorry

/-- The comparison arrow recovered in the standard fibre of `pY`. Its underlying non-Prop map
is `fromFiberHomVal`; the lift condition is proof-only. -/
private def fromFiberHom
    (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    (G.fiberFunctor f.left).obj (Fiber.mk rfl) ⟶
      (F.fiberFunctor f.left).obj (fromFiberRight G F f Q) :=
  ⟨fromFiberHomVal G F f Q, fromFiberHomValIsHomLift G F f Q⟩

/-- The structured arrow recovered from a pseudo-pullback object in the fixed first fibre. -/
private def fromFiberObj
    (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    structuredArrow G F f :=
  StructuredArrow.mk (fromFiberHom G F f Q)

/-- The ambient arrow underlying the right component of the recovered structured-arrow map.
It is exactly the second component of the supplied pseudo-pullback morphism. -/
private def fromFiberRightMapVal
    (f : Over U)
    {Q R : ((PseudoPullback.fst G F).toFunctor).Fiber f}
    (α : Q ⟶ R) :
    (fromFiberRight G F f Q).1 ⟶ (fromFiberRight G F f R).1 :=
  PseudoPullback.sndMap α.1

/-- The recovered right-component map is vertical over `f.left`.

Proof strategy: combine the outer-fibre equation for `α` with
`PseudoPullback.sndMap.isHomLift` and the endpoint base transports. -/
private theorem fromFiberRightMapValIsHomLift
    (f : Over U)
    {Q R : ((PseudoPullback.fst G F).toFunctor).Fiber f}
    (α : Q ⟶ R) :
    pX.IsHomLift (𝟙 f.left) (fromFiberRightMapVal G F f α) := sorry

/-- The second pseudo-pullback component, packaged as a morphism in the standard fibre of
`pX`. -/
private def fromFiberRightMap
    (f : Over U)
    {Q R : ((PseudoPullback.fst G F).toFunctor).Fiber f}
    (α : Q ⟶ R) :
    fromFiberRight G F f Q ⟶ fromFiberRight G F f R :=
  ⟨fromFiberRightMapVal G F f α,
    fromFiberRightMapValIsHomLift G F f α⟩

/-- The recovered right map satisfies the structured-arrow triangle.

Proof strategy: take the underlying equality in `pY` and use
`PseudoPullback.comm G F α.1`; the first component becomes an identity because `α` lies in the
fibre over `f`. -/
private theorem fromFiberMapComm
    (f : Over U)
    {Q R : ((PseudoPullback.fst G F).toFunctor).Fiber f}
    (α : Q ⟶ R) :
    fromFiberHom G F f Q ≫
        (F.fiberFunctor f.left).map (fromFiberRightMap G F f α) =
      fromFiberHom G F f R := sorry

/-- The structured-arrow morphism recovered from a morphism in the fixed first fibre. -/
private def fromFiberMap
    (f : Over U)
    {Q R : ((PseudoPullback.fst G F).toFunctor).Fiber f}
    (α : Q ⟶ R) :
    fromFiberObj G F f Q ⟶ fromFiberObj G F f R :=
  StructuredArrow.homMk (fromFiberRightMap G F f α) (fromFiberMapComm G F f α)

/-- The recovered structured-arrow map preserves identities.

Proof strategy: apply `StructuredArrow.hom_ext`, then `Functor.Fiber.hom_ext`, and reduce to
`PseudoPullback.sndMap.id`. -/
private theorem fromFiberMapId
    (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    fromFiberMap G F f (𝟙 Q) = 𝟙 (fromFiberObj G F f Q) := sorry

/-- The recovered structured-arrow map preserves composition.

Proof strategy: apply `StructuredArrow.hom_ext`, then `Functor.Fiber.hom_ext`, and reduce to
`PseudoPullback.sndMap.comp`. -/
private theorem fromFiberMapComp
    (f : Over U)
    {Q R S : ((PseudoPullback.fst G F).toFunctor).Fiber f}
    (α : Q ⟶ R) (β : R ⟶ S) :
    fromFiberMap G F f (α ≫ β) =
      fromFiberMap G F f α ≫ fromFiberMap G F f β := sorry

end Implementation

/-- Forget the redundant fixed first component of a pseudo-pullback object and retain its second
component and comparison arrow as a structured arrow.

Unlike `comparison`, this inverse-direction functor does not require `pY` to be fibered in
groupoids: a pseudo-pullback object already supplies an isomorphism, while a structured arrow
uses only its forward map. -/
@[stacks 02Y5 "(1) inverse structured-arrow comparison"]
def comparisonInverse
    (f : Over U) :
    ((PseudoPullback.fst G F).toFunctor).Fiber f ⥤
      structuredArrow G F f where
  obj := Implementation.fromFiberObj G F f
  map := Implementation.fromFiberMap G F f
  map_id := Implementation.fromFiberMapId G F f
  map_comp := Implementation.fromFiberMapComp G F f

end FromFiberImplementation

/-- The recovered structured arrow retains the second total-category object of the
pseudo-pullback object. -/
@[simp] theorem comparisonInverse.obj.right
    (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    ((comparisonInverse G F f).obj Q).right.1 =
      PseudoPullback.sndObj Q.1 := sorry

/-- The recovered structured-arrow map is the stored comparison, preceded only by the endpoint
transport supplied by the outer-fibre equality. -/
@[simp] theorem comparisonInverse.obj.comparisonHom
    (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    ((comparisonInverse G F f).obj Q).hom.1 =
      eqToHom (congrArg G.toFunctor.obj Q.2.symm) ≫
        PseudoPullback.comparison Q.1 := sorry

/-- The recovered comparison has the inverse already stored by the pseudo-pullback,
with the opposite endpoint transport supplied by the outer-fibre equality. -/
def comparisonInverse.obj.homInv
    (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    ((F.fiberFunctor f.left).obj ((comparisonInverse G F f).obj Q).right) ⟶
      (G.fiberFunctor f.left).obj (Fiber.mk rfl) :=
  ⟨(PseudoPullback.comparisonIsoApp Q.1).inv ≫
      eqToHom (congrArg G.toFunctor.obj Q.2), by sorry⟩

/-- The inverse comparison uses exactly the stored inverse and endpoint transport. -/
@[simp] theorem comparisonInverse.obj.homInv_val
    (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    (comparisonInverse.obj.homInv G F f Q).1 =
      (PseudoPullback.comparisonIsoApp Q.1).inv ≫
      eqToHom (congrArg G.toFunctor.obj Q.2) := rfl

/-- The comparison arrow recovered from the fixed first fibre is an isomorphism. Registering
this canonical fact lets consumers use `asIso` without rebuilding a local instance. -/
instance comparisonInverse.obj.hom.isIso
    (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    IsIso ((comparisonInverse G F f).obj Q).hom :=
  ⟨⟨comparisonInverse.obj.homInv G F f Q, by sorry, by sorry⟩⟩

/-- After forgetting the standard fibre, the complete isomorphism carried by a recovered
structured arrow is the endpoint transport followed by the pseudo-pullback comparison
isomorphism. -/
@[simp, stacks 02Y5 "inverse comparison object isomorphism"]
theorem comparisonInverse.obj.homIso
    (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    (Fiber.fiberInclusion : pY.Fiber f.left ⥤ Y).mapIso
        (@asIso _ _ _ _ ((comparisonInverse G F f).obj Q).hom
          (comparisonInverse.obj.hom.isIso G F f Q)) =
      G.toFunctor.mapIso (eqToIso Q.2.symm) ≪≫
        PseudoPullback.comparisonIsoApp Q.1 := sorry

/-- The right component of a recovered structured-arrow morphism is the second
pseudo-pullback component map. -/
@[simp] theorem comparisonInverse.map.right
    (f : Over U)
    {Q R : ((PseudoPullback.fst G F).toFunctor).Fiber f}
    (α : Q ⟶ R) :
    ((comparisonInverse G F f).map α).right.1 =
      PseudoPullback.sndMap α.1 := sorry

end FstFiber
end BasedCategory.PseudoPullback

end CategoryTheory
