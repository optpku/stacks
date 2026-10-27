/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Projections
public import ReasLib.CategoryTheory.Fibered.InGroupoids
public import ReasLib.CategoryTheory.Functor.CostructuredArrow.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Costructured-arrow construction of a second pseudo-pullback fibre

When the right input is a slice category, a fibre of the second pseudo-pullback projection is
canonically described by a costructured-arrow category. This leaf owns that category, the explicit
comparison functor, and its foundational projection formulas.
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

/- The canonical owner for pairs `(x, φ)` is `CostructuredArrow`: its objects are an object
`x` of the fibre of `pX` together with `φ : F(x) ⟶ G(f)`. The raw total construction below
is private; public consumers see only the pseudo-pullback projections. -/

/-- The costructured-arrow category describing the second projection fibre over `f`. -/
@[stacks 02Y5 "(1) formal dual costructured-arrow model"]
abbrev costructuredArrow (f : Over U) :=
  CostructuredArrow (F.fiberFunctor f.left)
    ((G.fiberFunctor f.left).obj (Fiber.mk rfl))

section ToFiberImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The explicit pseudo-pullback object associated to a costructured arrow. Its inverse map is
the Cartesian factor supplied by the original groupoid-fibration input; only the inverse laws
use the deferred proofs. -/
private noncomputable def obj
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : costructuredArrow F G f) :
    (PseudoPullback F G).obj :=
  PseudoPullback.mk F G f.left
    { fst := A.left
      snd := Fiber.mk rfl
      iso :=
        { hom := A.hom
          inv := Functor.IsFibered.InGroupoids.fiberInverse (p := pY) f.left A.hom
          hom_inv_id := Functor.IsFibered.InGroupoids.comp_fiberInverse (p := pY) f.left A.hom
          inv_hom_id := Functor.IsFibered.InGroupoids.fiberInverse_comp (p := pY) f.left A.hom } }

/-- The comparison square induced by a costructured-arrow morphism. -/
private theorem mapComm
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    {A B : costructuredArrow F G f} (α : A ⟶ B) :
    CommSq (F.toFunctor.map α.left.1) A.hom.1 B.hom.1
      (G.toFunctor.map (𝟙 f)) := sorry

/-- The explicit pseudo-pullback morphism induced by a costructured-arrow morphism. -/
private noncomputable def map
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    {A B : costructuredArrow F G f} (α : A ⟶ B) :
    obj F G f A ⟶ obj F G f B :=
  PseudoPullback.Hom.mk (𝟙 f.left)
    α.left.1 α.left.2
    (𝟙 f) (IsHomLift.id rfl)
    (mapComm F G f α)

/-- The explicit map construction preserves identities. -/
private theorem mapId
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : costructuredArrow F G f) :
    map F G f (𝟙 A) = 𝟙 (obj F G f A) := sorry

/-- The explicit map construction preserves composition. -/
private theorem mapComp
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    {A B D : costructuredArrow F G f}
    (α : A ⟶ B) (β : B ⟶ D) :
    map F G f (α ≫ β) = map F G f α ≫ map F G f β := sorry

/-- The costructured-arrow construction as a functor to the total pseudo-pullback. -/
private noncomputable def toTotal
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    costructuredArrow F G f ⥤ (PseudoPullback F G).obj where
  obj := obj F G f
  map := map F G f
  map_id := mapId F G f
  map_comp := mapComp F G f

/-- The total construction has constant second projection at `f`. -/
private theorem toTotalCompSnd
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    toTotal F G f ⋙ (PseudoPullback.snd F G).toFunctor =
      (Functor.const (costructuredArrow F G f)).obj f := sorry

end Implementation

/-- Every object of the fixed second fibre has common base `f.left`. -/
@[simp] theorem fiberObj.base
    (f : Over U) (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    PseudoPullback.baseObj
        ((Fiber.fiberInclusion :
          ((PseudoPullback.snd F G).toFunctor).Fiber f ⥤
            (PseudoPullback F G).obj).obj Q) =
      f.left := sorry

/-- Forgetting a second-fibre object recovers the fixed slice object under the second
projection. -/
@[simp] theorem fiberObj.snd
    (f : Over U) (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    (PseudoPullback.snd F G).obj
        ((Fiber.fiberInclusion :
          ((PseudoPullback.snd F G).toFunctor).Fiber f ⥤
            (PseudoPullback F G).obj).obj Q) =
      f := sorry

/-- Every morphism in the fixed second fibre has identity common base map, up to endpoint
transport. -/
@[simp] theorem fiberMap.base
    (f : Over U) {Q R : ((PseudoPullback.snd F G).toFunctor).Fiber f}
    (α : Q ⟶ R) :
    HEq
      (PseudoPullback.baseMap
        ((Fiber.fiberInclusion :
          ((PseudoPullback.snd F G).toFunctor).Fiber f ⥤
            (PseudoPullback F G).obj).map α))
      (𝟙 f.left) := sorry

/-- Forgetting a second-fibre morphism gives the identity of the fixed slice object, up to
endpoint transport. -/
@[simp] theorem fiberMap.snd
    (f : Over U) {Q R : ((PseudoPullback.snd F G).toFunctor).Fiber f}
    (α : Q ⟶ R) :
    HEq
      ((PseudoPullback.snd F G).map
        ((Fiber.fiberInclusion :
          ((PseudoPullback.snd F G).toFunctor).Fiber f ⥤
            (PseudoPullback F G).obj).map α))
      (𝟙 f) := sorry

/-- The canonical functor from costructured arrows to the second fibre over `f`. -/
@[stacks 02Y5 "(1) formal dual costructured-arrow comparison"]
noncomputable def comparison
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    costructuredArrow F G f ⥤
      ((PseudoPullback.snd F G).toFunctor).Fiber f :=
  Fiber.inducedFunctor (Implementation.toTotalCompSnd F G f)

end ToFiberImplementation

/-- The common base of an evaluated costructured arrow is `f.left`. -/
@[simp] theorem comparison.obj.base
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : costructuredArrow F G f) :
    PseudoPullback.baseObj
        ((Fiber.fiberInclusion :
          ((PseudoPullback.snd F G).toFunctor).Fiber f ⥤
            (PseudoPullback F G).obj).obj ((comparison F G f).obj A)) =
      f.left := sorry

/-- The first component of an evaluated costructured arrow is its stored fibre object. -/
@[simp] theorem comparison.obj.fst
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : costructuredArrow F G f) :
    PseudoPullback.fstObj
        ((Fiber.fiberInclusion :
          ((PseudoPullback.snd F G).toFunctor).Fiber f ⥤
            (PseudoPullback F G).obj).obj ((comparison F G f).obj A)) =
      A.left.1 := sorry

/-- The second component of an evaluated costructured arrow is the fixed slice object. -/
@[simp] theorem comparison.obj.snd
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : costructuredArrow F G f) :
    PseudoPullback.sndObj
        ((Fiber.fiberInclusion :
          ((PseudoPullback.snd F G).toFunctor).Fiber f ⥤
            (PseudoPullback F G).obj).obj ((comparison F G f).obj A)) =
      f := sorry

/-- The pseudo-pullback comparison of an evaluated costructured arrow is its defining arrow. -/
@[simp] theorem comparison.obj.comparisonHom
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : costructuredArrow F G f) :
    PseudoPullback.comparison
        ((Fiber.fiberInclusion :
          ((PseudoPullback.snd F G).toFunctor).Fiber f ⥤
            (PseudoPullback F G).obj).obj ((comparison F G f).obj A)) =
      A.hom.1 := sorry

/-- The full pseudo-pullback comparison isomorphism is the image of `asIso A.hom` under the
standard fibre inclusion. -/
@[simp] theorem comparison.obj.comparisonIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : costructuredArrow F G f) :
    PseudoPullback.comparisonIsoApp
        ((Fiber.fiberInclusion :
          ((PseudoPullback.snd F G).toFunctor).Fiber f ⥤
            (PseudoPullback F G).obj).obj ((comparison F G f).obj A)) =
      (Fiber.fiberInclusion : pY.Fiber f.left ⥤ Y).mapIso (@asIso _ _ _ _ A.hom
        (Functor.IsFibered.InGroupoids.hom_isIso (p := pY) f.left A.hom)) := sorry

/-- The first component of an evaluated costructured-arrow morphism is its stored left map. -/
@[simp] theorem comparison.map.fst
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    {A B : costructuredArrow F G f} (α : A ⟶ B) :
    PseudoPullback.fstMap
        ((Fiber.fiberInclusion :
          ((PseudoPullback.snd F G).toFunctor).Fiber f ⥤
            (PseudoPullback F G).obj).map ((comparison F G f).map α)) =
      α.left.1 := sorry

/-- The common base map of an evaluated costructured-arrow morphism is the identity. -/
@[simp] theorem comparison.map.base
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    {A B : costructuredArrow F G f} (α : A ⟶ B) :
    PseudoPullback.baseMap
        ((Fiber.fiberInclusion :
          ((PseudoPullback.snd F G).toFunctor).Fiber f ⥤
            (PseudoPullback F G).obj).map ((comparison F G f).map α)) =
      𝟙 f.left := sorry

/-- The second component of an evaluated costructured-arrow morphism is the identity of `f`. -/
@[simp] theorem comparison.map.snd
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    {A B : costructuredArrow F G f} (α : A ⟶ B) :
    PseudoPullback.sndMap
        ((Fiber.fiberInclusion :
          ((PseudoPullback.snd F G).toFunctor).Fiber f ⥤
            (PseudoPullback F G).obj).map ((comparison F G f).map α)) =
      𝟙 f := sorry

/-- In a groupoid fibre, the costructured-arrow morphism equation is equivalent to the
inverse-form equation for its left component. -/
@[stacks 02Y5 "(2) formal dual groupoid-fibre specialization"]
theorem exists_hom_left_iff_map_eq [Functor.IsFibered.InGroupoids pY]
    (f : Over U) (A B : costructuredArrow F G f)
    (ψ : A.left ⟶ B.left) :
    (∃ α : A ⟶ B, α.left = ψ) ↔
      (F.fiberFunctor f.left).map ψ =
        A.hom ≫ (@asIso _ _ _ _ B.hom
          (Functor.IsFibered.InGroupoids.hom_isIso (p := pY) f.left B.hom)).inv := sorry

end SndFiber
end BasedCategory.PseudoPullback

end CategoryTheory
