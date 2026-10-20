/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.SndFiber.Basic

/-!
# Inverse costructured-arrow comparison for a second pseudo-pullback fibre

This leaf constructs the inverse functor from a fixed second fibre to costructured arrows. The
recovered structure map is the stored pseudo-pullback comparison followed by the target transport
induced by the second-projection endpoint equality.
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
namespace SndFiber

variable {U : C}
variable (F : BasedCategory.ofFunctor pX ⥤ᵇ BasedCategory.ofFunctor pY)
variable (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor pY)

section FromFiberImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The common base of an object in the fixed second fibre is `f.left`. -/
private theorem fromFiberBaseEq
    (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    PseudoPullback.baseObj Q.1 = f.left := sorry

/-- The first component of a second-fibre object, transported to the standard fibre of `pX`. -/
private def fromFiberLeft
    (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    pX.Fiber f.left :=
  ⟨PseudoPullback.fstObj Q.1,
    (PseudoPullback.fiberObj Q.1).fst.2.trans
      (fromFiberBaseEq F G f Q)⟩

/-- The ambient structure arrow recovered from a second-fibre object.

Its non-Prop payload is the stored comparison followed by target transport along `Q.2`; target
transport is deliberately on the right, matching the costructured-arrow orientation. -/
private def fromFiberHomVal
    (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    ((F.fiberFunctor f.left).obj (fromFiberLeft F G f Q)).1 ⟶
      ((G.fiberFunctor f.left).obj (Fiber.mk rfl)).1 :=
  PseudoPullback.comparison Q.1 ≫
    eqToHom (congrArg G.toFunctor.obj Q.2)

/-- The recovered structure arrow is vertical over `f.left`. -/
private theorem fromFiberHomValIsHomLift
    (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    pY.IsHomLift (𝟙 f.left) (fromFiberHomVal F G f Q) := sorry

/-- The structure arrow recovered in the standard fibre of `pY`. -/
private def fromFiberHom
    (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    (F.fiberFunctor f.left).obj (fromFiberLeft F G f Q) ⟶
      (G.fiberFunctor f.left).obj (Fiber.mk rfl) :=
  ⟨fromFiberHomVal F G f Q, fromFiberHomValIsHomLift F G f Q⟩

/-- The costructured arrow recovered from an object in the fixed second fibre. -/
private def fromFiberObj
    (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    costructuredArrow F G f :=
  CostructuredArrow.mk (fromFiberHom F G f Q)

/-- The ambient arrow underlying the left component of a recovered map. -/
private def fromFiberLeftMapVal
    (f : Over U)
    {Q R : ((PseudoPullback.snd F G).toFunctor).Fiber f}
    (α : Q ⟶ R) :
    (fromFiberLeft F G f Q).1 ⟶ (fromFiberLeft F G f R).1 :=
  PseudoPullback.fstMap α.1

/-- The recovered left-component map is vertical over `f.left`. -/
private theorem fromFiberLeftMapValIsHomLift
    (f : Over U)
    {Q R : ((PseudoPullback.snd F G).toFunctor).Fiber f}
    (α : Q ⟶ R) :
    pX.IsHomLift (𝟙 f.left) (fromFiberLeftMapVal F G f α) := sorry

/-- The first pseudo-pullback component packaged as a map in the standard fibre of `pX`. -/
private def fromFiberLeftMap
    (f : Over U)
    {Q R : ((PseudoPullback.snd F G).toFunctor).Fiber f}
    (α : Q ⟶ R) :
    fromFiberLeft F G f Q ⟶ fromFiberLeft F G f R :=
  ⟨fromFiberLeftMapVal F G f α,
    fromFiberLeftMapValIsHomLift F G f α⟩

/-- The recovered left map satisfies the costructured-arrow triangle. -/
private theorem fromFiberMapComm
    (f : Over U)
    {Q R : ((PseudoPullback.snd F G).toFunctor).Fiber f}
    (α : Q ⟶ R) :
    (F.fiberFunctor f.left).map (fromFiberLeftMap F G f α) ≫
        fromFiberHom F G f R =
      fromFiberHom F G f Q := sorry

/-- The costructured-arrow morphism recovered from a fixed-second-fibre morphism. -/
private def fromFiberMap
    (f : Over U)
    {Q R : ((PseudoPullback.snd F G).toFunctor).Fiber f}
    (α : Q ⟶ R) :
    fromFiberObj F G f Q ⟶ fromFiberObj F G f R :=
  CostructuredArrow.homMk (fromFiberLeftMap F G f α)
    (fromFiberMapComm F G f α)

/-- The recovered costructured-arrow map preserves identities. -/
private theorem fromFiberMapId
    (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    fromFiberMap F G f (𝟙 Q) = 𝟙 (fromFiberObj F G f Q) := sorry

/-- The recovered costructured-arrow map preserves composition. -/
private theorem fromFiberMapComp
    (f : Over U)
    {Q R S : ((PseudoPullback.snd F G).toFunctor).Fiber f}
    (α : Q ⟶ R) (β : R ⟶ S) :
    fromFiberMap F G f (α ≫ β) =
      fromFiberMap F G f α ≫ fromFiberMap F G f β := sorry

end Implementation

/-- Forget the redundant fixed second component and retain the first component with the
comparison-to-`G(f)` map as a costructured arrow. -/
@[stacks 02Y5 "(1) formal dual inverse costructured-arrow comparison"]
def comparisonInverse
    (f : Over U) :
    ((PseudoPullback.snd F G).toFunctor).Fiber f ⥤
      costructuredArrow F G f where
  obj := Implementation.fromFiberObj F G f
  map := Implementation.fromFiberMap F G f
  map_id := Implementation.fromFiberMapId F G f
  map_comp := Implementation.fromFiberMapComp F G f

end FromFiberImplementation

/-- The recovered costructured arrow retains the first total-category object. -/
@[simp] theorem comparisonInverse.obj.left
    (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    ((comparisonInverse F G f).obj Q).left.1 =
      PseudoPullback.fstObj Q.1 := sorry

/-- The recovered structure map is comparison followed by target endpoint transport. -/
@[simp] theorem comparisonInverse.obj.comparisonHom
    (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    ((comparisonInverse F G f).obj Q).hom.1 =
      PseudoPullback.comparison Q.1 ≫
        eqToHom (congrArg G.toFunctor.obj Q.2) := sorry

/-- The recovered comparison has the inverse already stored by the pseudo-pullback,
with the opposite endpoint transport supplied by the outer-fibre equality. -/
def comparisonInverse.obj.homInv
    (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    (G.fiberFunctor f.left).obj (Fiber.mk rfl) ⟶
      ((F.fiberFunctor f.left).obj ((comparisonInverse F G f).obj Q).left) :=
  ⟨eqToHom (congrArg G.toFunctor.obj Q.2.symm) ≫
      (PseudoPullback.comparisonIsoApp Q.1).inv, by sorry⟩

/-- The inverse comparison uses exactly the stored inverse and endpoint transport. -/
@[simp] theorem comparisonInverse.obj.homInv_val
    (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    (comparisonInverse.obj.homInv F G f Q).1 =
      eqToHom (congrArg G.toFunctor.obj Q.2.symm) ≫
      (PseudoPullback.comparisonIsoApp Q.1).inv := rfl

/-- The structure map recovered from a fixed second fibre is canonically invertible. -/
@[stacks 02Y5 "formal dual recovered comparison isomorphism instance"]
instance comparisonInverse.obj.hom.isIso
    (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    IsIso ((comparisonInverse F G f).obj Q).hom :=
  ⟨⟨comparisonInverse.obj.homInv F G f Q, by sorry, by sorry⟩⟩

/-- After forgetting the standard fibre, the recovered isomorphism is the pseudo-pullback
comparison followed by target transport induced by the second-projection equality. -/
@[simp, stacks 02Y5 "formal dual inverse comparison object isomorphism"]
theorem comparisonInverse.obj.homIso
    (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    (Fiber.fiberInclusion : pY.Fiber f.left ⥤ Y).mapIso
        (@asIso _ _ _ _ ((comparisonInverse F G f).obj Q).hom
          (comparisonInverse.obj.hom.isIso F G f Q)) =
      PseudoPullback.comparisonIsoApp Q.1 ≪≫
        G.toFunctor.mapIso (eqToIso Q.2) := sorry

/-- The left component of a recovered costructured-arrow morphism is the first
pseudo-pullback component map. -/
@[simp] theorem comparisonInverse.map.left
    (f : Over U)
    {Q R : ((PseudoPullback.snd F G).toFunctor).Fiber f}
    (α : Q ⟶ R) :
    ((comparisonInverse F G f).map α).left.1 =
      PseudoPullback.fstMap α.1 := sorry

end SndFiber
end BasedCategory.PseudoPullback

end CategoryTheory
