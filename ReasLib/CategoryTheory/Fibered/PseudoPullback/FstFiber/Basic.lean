module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Projections
public import ReasLib.CategoryTheory.Fibered.InGroupoids
public import ReasLib.CategoryTheory.Functor.StructuredArrow.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Structured-arrow construction of a pseudo-pullback fibre

When the left input is a slice category, a fibre of the first pseudo-pullback projection is
canonically described by a structured-arrow category. This leaf provides the structured-arrow
owner, the explicit comparison functor, and its foundational projection formulas. The inverse
comparison, equivalence data, and packaged computation formulas live in later leaves.
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

/- The canonical owner for pairs `(x, φ)` is `StructuredArrow`: its objects are
exactly an object `x` of the fiber of `pX` together with `φ : G(f) ⟶ F(x)`.  Keeping that owner
visible also makes the morphism equation available through `StructuredArrow.w`, instead of
introducing a second bespoke pair category.

The raw total object, total map, functor-law, and constant-projection declarations are private
assembly for `comparison`. Public computation is expressed only through the canonical
`PseudoPullback` projections below, so consumers need not unfold either the outer
`Functor.Fiber` packaging or the implementation carrier.

The public imports expose `Over U`, `StructuredArrow`, the pseudo-pullback owner, and
`Functor.IsFibered.InGroupoids`, all of which occur in public declaration types. Any dependencies
needed only to discharge the deferred equivalence proof should remain plain imports. -/

/-- The structured-arrow category describing the fiber of the slice two-fibre-product over `f`. -/
@[stacks 02Y5 "(1) structured-arrow model"]
abbrev structuredArrow (f : Over U) :=
  StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl)) (F.fiberFunctor f.left)

section ToFiberImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The explicit two-fibre-product object associated to a structured arrow `(x, φ)` over `f`.
Its non-Prop payload is the source data `f`, `x`, and the canonical isomorphism attached to `φ`. -/
private noncomputable def obj
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : structuredArrow G F f) :
    (PseudoPullback G F).obj :=
  PseudoPullback.mk G F f.left
    { fst := Fiber.mk rfl
      snd := A.right
      iso := @asIso _ _ _ _ A.hom
        (Functor.IsFibered.InGroupoids.hom_isIso (p := pY) f.left A.hom) }

/-- The comparison square used by the explicit two-fibre-product morphism attached to a
structured-arrow morphism.

Proof strategy: apply `congrArg Subtype.val` to `StructuredArrow.w α`, use
`G.toFunctor.map_id`, and normalize identity composition. -/
private theorem mapComm
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    {A B : structuredArrow G F f} (α : A ⟶ B) :
    CommSq (G.toFunctor.map (𝟙 f)) A.hom.1 B.hom.1 (F.toFunctor.map α.right.1) := sorry

/-- The explicit two-fibre-product morphism induced by a structured-arrow morphism. The two
component maps are explicit; only their Prop-valued comparison square is deferred. -/
private noncomputable def map
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    {A B : structuredArrow G F f} (α : A ⟶ B) :
    obj G F f A ⟶ obj G F f B :=
  PseudoPullback.Hom.mk (𝟙 f.left)
    (𝟙 f) (IsHomLift.id rfl)
    α.right.1 α.right.2
    (mapComm G F f α)

/-- The explicit map construction preserves identities.

Proof strategy: use `PseudoPullback.hom_ext`; after unfolding the explicit map, its left
component is an identity and its right component is the identity structured-arrow map. -/
private theorem mapId
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : structuredArrow G F f) :
    map G F f (𝟙 A) = 𝟙 (obj G F f A) := sorry

/-- The explicit map construction preserves composition.

Proof strategy: apply `PseudoPullback.hom_ext`; the fixed left identity components and the
right structured-arrow components agree by the category laws. -/
private theorem mapComp
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    {A B D : structuredArrow G F f}
    (α : A ⟶ B) (β : B ⟶ D) :
    map G F f (α ≫ β) = map G F f α ≫ map G F f β := sorry

/-- The structured-arrow construction viewed in the total explicit pseudo-pullback. -/
private noncomputable def toTotal
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    structuredArrow G F f ⥤ (PseudoPullback G F).obj where
  obj := obj G F f
  map := map G F f
  map_id := mapId G F f
  map_comp := mapComp G F f

/-- The total functor has constant first projection at `f`.

Proof strategy: use `Functor.ext`; object components are reflexive and every map component
reduces to `𝟙 f` after unfolding the private map assembly. -/
private theorem toTotalCompFst
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    toTotal G F f ⋙ (PseudoPullback.fst G F).toFunctor =
      (Functor.const (structuredArrow G F f)).obj f := sorry

end Implementation

/-- Every object of the fibre of the first pseudo-pullback projection has common base
`f.left`. -/
@[simp] theorem fiberObj.base
    (f : Over U) (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    PseudoPullback.baseObj
        ((Fiber.fiberInclusion :
          ((PseudoPullback.fst G F).toFunctor).Fiber f ⥤
            (PseudoPullback G F).obj).obj Q) =
      f.left := sorry

/-- Forgetting a first-projection fibre object recovers the fixed slice object under the
first pseudo-pullback projection. -/
@[simp] theorem fiberObj.fst
    (f : Over U) (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    (PseudoPullback.fst G F).obj
        ((Fiber.fiberInclusion :
          ((PseudoPullback.fst G F).toFunctor).Fiber f ⥤
            (PseudoPullback G F).obj).obj Q) =
      f := sorry

/-- Every morphism in the fibre of the first pseudo-pullback projection has identity common
base map, up to the endpoint transports recorded by the outer fibre. -/
@[simp] theorem fiberMap.base
    (f : Over U) {Q R : ((PseudoPullback.fst G F).toFunctor).Fiber f}
    (α : Q ⟶ R) :
    HEq
      (PseudoPullback.baseMap
        ((Fiber.fiberInclusion :
          ((PseudoPullback.fst G F).toFunctor).Fiber f ⥤
            (PseudoPullback G F).obj).map α))
      (𝟙 f.left) := sorry

/-- Forgetting a first-projection fibre morphism gives the identity of the fixed slice object,
up to the endpoint transports recorded by the outer fibre. -/
@[simp] theorem fiberMap.fst
    (f : Over U) {Q R : ((PseudoPullback.fst G F).toFunctor).Fiber f}
    (α : Q ⟶ R) :
    HEq
      ((PseudoPullback.fst G F).map
        ((Fiber.fiberInclusion :
          ((PseudoPullback.fst G F).toFunctor).Fiber f ⥤
            (PseudoPullback G F).obj).map α))
      (𝟙 f) := sorry

/-- The canonical functor from the structured-arrow description to the fiber over `f` of the
left projection. `Fiber.inducedFunctor` is the mathlib owner for restricting a functor whose
composite with the projection is constant. -/
@[stacks 02Y5 "(1) structured-arrow comparison"]
noncomputable def comparison
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    structuredArrow G F f ⥤
      ((PseudoPullback.fst G F).toFunctor).Fiber f :=
  Fiber.inducedFunctor (Implementation.toTotalCompFst G F f)

end ToFiberImplementation

/-- The common base of an evaluated structured arrow is the domain of the fixed slice
object. -/
@[simp] theorem comparison.obj.base
    [Functor.IsFibered.InGroupoids pY] (f : Over U) (A : structuredArrow G F f) :
    PseudoPullback.baseObj
        ((Fiber.fiberInclusion :
          ((PseudoPullback.fst G F).toFunctor).Fiber f ⥤
            (PseudoPullback G F).obj).obj ((comparison G F f).obj A)) =
      f.left := sorry

/-- The first component of an evaluated structured arrow is the fixed slice object `f`.

Proof strategy: forget the outer fiber with `Fiber.fiberInclusion`, unfold `comparison`, and read
the first component of the explicit `PseudoPullback.mk` object. -/
@[simp] theorem comparison.obj.fst
    [Functor.IsFibered.InGroupoids pY] (f : Over U) (A : structuredArrow G F f) :
    PseudoPullback.fstObj
        ((Fiber.fiberInclusion :
          ((PseudoPullback.fst G F).toFunctor).Fiber f ⥤
            (PseudoPullback G F).obj).obj ((comparison G F f).obj A)) =
      f := sorry

/-- The second component of an evaluated structured arrow is its stored fiber object.

Proof strategy: forget the outer fiber, unfold `comparison`, and read the second component of the
explicit `PseudoPullback.mk` object. -/
@[simp] theorem comparison.obj.snd
    [Functor.IsFibered.InGroupoids pY] (f : Over U) (A : structuredArrow G F f) :
    PseudoPullback.sndObj
        ((Fiber.fiberInclusion :
          ((PseudoPullback.fst G F).toFunctor).Fiber f ⥤
            (PseudoPullback G F).obj).obj ((comparison G F f).obj A)) =
      A.right.1 := sorry

/-- The pseudo-pullback comparison of an evaluated structured arrow is its defining arrow.

Proof strategy: forget the outer fiber, unfold `comparison`, and reduce the comparison of the
explicit object to the hom of `asIso A.hom`. -/
@[simp] theorem comparison.obj.comparisonHom
    [Functor.IsFibered.InGroupoids pY] (f : Over U) (A : structuredArrow G F f) :
    PseudoPullback.comparison
        ((Fiber.fiberInclusion :
          ((PseudoPullback.fst G F).toFunctor).Fiber f ⥤
            (PseudoPullback G F).obj).obj ((comparison G F f).obj A)) =
      A.hom.1 := sorry

/-- The entire pseudo-pullback comparison isomorphism of an evaluated structured arrow is the
image of `asIso A.hom` under the standard fibre inclusion.

This is the stable inverse-map API: consumers needing the inverse comparison can project
`.inv` from this equality without unfolding the `IsIso` choice used by `asIso`. -/
@[simp] theorem comparison.obj.comparisonIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U) (A : structuredArrow G F f) :
    PseudoPullback.comparisonIsoApp
        ((Fiber.fiberInclusion :
          ((PseudoPullback.fst G F).toFunctor).Fiber f ⥤
            (PseudoPullback G F).obj).obj ((comparison G F f).obj A)) =
      (Fiber.fiberInclusion : pY.Fiber f.left ⥤ Y).mapIso (@asIso _ _ _ _ A.hom
        (Functor.IsFibered.InGroupoids.hom_isIso (p := pY) f.left A.hom)) := sorry

/-- The first component of an evaluated structured-arrow morphism is the identity of `f`.

Proof strategy: forget the outer fiber map, unfold `comparison`, and read the first component of
the explicit `PseudoPullback.Hom.mk` morphism. -/
@[simp] theorem comparison.map.fst
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    {A B : structuredArrow G F f} (α : A ⟶ B) :
    PseudoPullback.fstMap
        ((Fiber.fiberInclusion :
          ((PseudoPullback.fst G F).toFunctor).Fiber f ⥤
            (PseudoPullback G F).obj).map ((comparison G F f).map α)) =
      𝟙 f := sorry

/-- The common base map of an evaluated structured-arrow morphism is the identity of the
domain of the fixed slice object. -/
@[simp] theorem comparison.map.base
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    {A B : structuredArrow G F f} (α : A ⟶ B) :
    PseudoPullback.baseMap
        ((Fiber.fiberInclusion :
          ((PseudoPullback.fst G F).toFunctor).Fiber f ⥤
            (PseudoPullback G F).obj).map ((comparison G F f).map α)) =
      𝟙 f.left := sorry

/-- The second component of an evaluated structured-arrow morphism is its stored right map.

Proof strategy: forget the outer fiber map, unfold `comparison`, and read the second component of
the explicit `PseudoPullback.Hom.mk` morphism. -/
@[simp] theorem comparison.map.snd
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    {A B : structuredArrow G F f} (α : A ⟶ B) :
    PseudoPullback.sndMap
        ((Fiber.fiberInclusion :
          ((PseudoPullback.fst G F).toFunctor).Fiber f ⥤
            (PseudoPullback G F).obj).map ((comparison G F f).map α)) =
      α.right.1 := sorry

/-- Lemma 4.42.1 (Stacks 02Y5) (2): in a groupoid fiber, the structured-arrow morphism equation
is equivalent to the usual inverse formula for its right component.

The intrinsic Hom equivalence and its inverse-form constructor are owned by
`StructuredArrow.homEquivInv` and `StructuredArrow.homMkInv`; this theorem is only the
source-facing specialization to a groupoid fiber. -/
@[stacks 02Y5 "(2) groupoid-fibre specialization"]
theorem exists_hom_right_iff_map_eq [Functor.IsFibered.InGroupoids pY]
    (f : Over U) (A B : structuredArrow G F f)
    (ψ : A.right ⟶ B.right) :
    (∃ α : A ⟶ B, α.right = ψ) ↔
      (F.fiberFunctor f.left).map ψ =
        (@asIso _ _ _ _ A.hom
          (Functor.IsFibered.InGroupoids.hom_isIso (p := pY) f.left A.hom)).inv ≫ B.hom := sorry

end FstFiber
end BasedCategory.PseudoPullback

end CategoryTheory
