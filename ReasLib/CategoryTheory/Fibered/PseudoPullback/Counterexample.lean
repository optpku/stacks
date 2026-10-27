/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Data.ZMod.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.CrossRefAttribute

/-!
# A two-arrow pseudo-pullback counterexample

This leaf owns a compact concrete cospan for comparing an ordinary categorical pullback with
the explicit pseudo-pullback in `Cat/C`.  The two constructions have respectively two and one
objects, so they are not equivalent categories.  The example is deliberately fixed at the
two-element group: it is a reusable regression fixture for the difference between an
iso-comma construction and a based pseudo-pullback, rather than a second general pullback API.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoryTheory.BasedCategory
open scoped CategoricalPullback

namespace CategoryTheory
namespace BasedCategory.PseudoPullback
namespace TwoArrowCounterexample

/- Data audit: `pointToBase`, `pointLift`, `identityLift`, and `ordinaryPullbackPoint` are
`sorryAx`-free. The `sorryAx` footprint of `basedPullbackPoint` comes from existing upstream
Prop fields in `toBase`, the induced fibre functor, and the pseudo-pullback category laws.
Its object, functor, and identity-comparison payloads remain explicit. -/

/-- The two-element group whose one-object category realizes the comparison groupoid. -/
abbrev TwoArrowGroup := Multiplicative (ZMod 2)

/-- The canonical one-object groupoid with two arrows. -/
abbrev TwoArrowGroupoid := SingleObj TwoArrowGroup

/-- The canonical one-object discrete category used for both legs of the cospan. -/
abbrev OnePointCategory := Discrete PUnit

/-- The unique object of `TwoArrowGroupoid`. -/
def baseObject : TwoArrowGroupoid :=
  SingleObj.star TwoArrowGroup

/-- The unique functor from `OnePointCategory` to `TwoArrowGroupoid`. -/
@[stacks 0H2D "one-point leg of the two-arrow counterexample"]
def pointToBase : OnePointCategory ⥤ TwoArrowGroupoid :=
  Functor.fromPUnit baseObject

/-- The one-point category regarded as an object of `Cat/TwoArrowGroupoid`. -/
def pointOverBase : BasedCategory TwoArrowGroupoid :=
  BasedCategory.ofFunctor pointToBase

/-- The unique object of `OnePointCategory`. -/
def pointObject : OnePointCategory :=
  Discrete.mk PUnit.unit

/-- The unique point is sent to the unique base object. -/
theorem pointToBase_obj :
    pointOverBase.p.obj pointObject = baseObject := by
  rfl

/-- The identity functor fixes the unique base object. -/
theorem baseIdentity_obj :
    (𝟭 TwoArrowGroupoid).obj baseObject = baseObject := by
  rfl

/-- The canonical lift of the point object to the fibre over `baseObject`. -/
def pointLift : Functor.Fiber pointOverBase.p baseObject :=
  Functor.Fiber.mk pointToBase_obj

/-- The canonical lift of `baseObject` through its identity functor. -/
def identityLift : Functor.Fiber (𝟭 TwoArrowGroupoid) baseObject :=
  Functor.Fiber.mk baseIdentity_obj

/-- The object of the ordinary categorical pullback whose comparison is the chosen group
element. -/
@[stacks 0H2D "ordinary pullback point with arbitrary comparison arrow"]
noncomputable def ordinaryPullbackPoint
    (g : TwoArrowGroup) : pointToBase ⊡ pointToBase where
  fst := pointObject
  snd := pointObject
  iso := asIso g

/-- The identity-comparison point of the pseudo-pullback in `Cat/TwoArrowGroupoid`. -/
@[stacks 0H2D "over-base pullback point with identity comparison"]
def basedPullbackPoint :
    (PseudoPullback pointOverBase.toBase pointOverBase.toBase).obj :=
  PseudoPullback.mk pointOverBase.toBase pointOverBase.toBase baseObject
    { fst := pointLift
      snd := pointLift
      iso := Iso.refl identityLift }

/-- Every arrow of the two-arrow group occurs as the comparison isomorphism of an object of the
ordinary categorical pullback. -/
@[stacks 0H2D "arbitrary comparison arrows in the categorical pullback"]
theorem ordinaryPullbackPoint_iso_hom
    (g : TwoArrowGroup) :
    (ordinaryPullbackPoint g).iso.hom = g := by
  rfl

/-- Objects of the ordinary pullback are determined by their comparison arrows. -/
private theorem ordinaryPullback_ext {P Q : pointToBase ⊡ pointToBase}
    (h : P.iso.hom = Q.iso.hom) : P = Q := by
  rcases P with ⟨x, y, i⟩
  rcases Q with ⟨x', y', i'⟩
  obtain rfl : x' = x := Subsingleton.elim _ _
  obtain rfl : y' = y := Subsingleton.elim _ _
  have hi : i = i' := Iso.ext h
  cases hi
  rfl

/-- The ordinary categorical pullback of the one-point category with itself over the two-arrow
groupoid is discrete. -/
@[stacks 0H2D "ordinary categorical pullback is discrete"]
instance ordinaryPullbackIsDiscrete : IsDiscrete (pointToBase ⊡ pointToBase) where
  subsingleton _ _ := ⟨fun f g ↦
    CategoricalPullback.hom_ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
  eq_of_hom f := by
    apply ordinaryPullback_ext
    simpa [pointToBase, SingleObj.comp_as_mul, SingleObj.id_as_one] using f.w.symm

/-- The ordinary categorical pullback has exactly two objects. -/
@[stacks 0H2D "ordinary categorical pullback has two objects"]
theorem ordinaryPullbackNatCard :
    Nat.card (pointToBase ⊡ pointToBase) = 2 := by
  let e : (pointToBase ⊡ pointToBase) ≃ TwoArrowGroup :=
    { toFun := fun P ↦ P.iso.hom
      invFun := ordinaryPullbackPoint
      left_inv := fun P ↦ ordinaryPullback_ext rfl
      right_inv := fun _ ↦ rfl }
  calc
    Nat.card (pointToBase ⊡ pointToBase) = Nat.card TwoArrowGroup := Nat.card_congr e
    _ = 2 := Nat.card_zmod 2

/-- Every object of the pseudo-pullback in `Cat/TwoArrowGroupoid` is the
identity-comparison point. -/
@[stacks 0H2D "over-base pullback has only the identity comparison point"]
theorem basedPullback_eq_point
    (P : (PseudoPullback pointOverBase.toBase pointOverBase.toBase).obj) :
    P = basedPullbackPoint := by
  rcases P with ⟨U, x, y, i⟩
  obtain rfl : U = baseObject := Subsingleton.elim _ _
  obtain rfl : x = pointLift := Subtype.ext (Subsingleton.elim (α := OnePointCategory) _ _)
  obtain rfl : y = pointLift := Subtype.ext (Subsingleton.elim (α := OnePointCategory) _ _)
  have hi : i = Iso.refl identityLift := by
    apply Iso.ext
    apply Functor.Fiber.hom_ext
    -- Supply endpoints and the lift certificate explicitly in the one-object base category.
    exact (@IsHomLift.eq_of_isHomLift _ _ _ _ (𝟭 TwoArrowGroupoid)
      baseObject baseObject (𝟙 baseObject) i.hom.val i.hom.property).symm
  cases hi
  rfl

/-- The pseudo-pullback formed in `Cat/TwoArrowGroupoid` is discrete. -/
@[stacks 0H2D "pullback in the over-category is discrete"]
instance basedPullbackIsDiscrete :
    IsDiscrete (PseudoPullback pointOverBase.toBase pointOverBase.toBase).obj where
  subsingleton P Q := ⟨by
    intro f g
    obtain rfl := basedPullback_eq_point P
    obtain rfl := basedPullback_eq_point Q
    rcases f with ⟨b, f, hf, f', hf', w⟩
    rcases g with ⟨c, g, hg, g', hg', w'⟩
    have hfst : f = g := Subsingleton.elim (α := pointObject ⟶ pointObject) _ _
    have hsnd : f' = g' := Subsingleton.elim (α := pointObject ⟶ pointObject) _ _
    have hb : b = c := by
      calc
        b = pointOverBase.p.map f := @IsHomLift.eq_of_isHomLift _ _ _ _ pointOverBase.p
          pointObject pointObject b f hf
        _ = pointOverBase.p.map g := congrArg (fun φ ↦ pointOverBase.p.map φ) hfst
        _ = c := (@IsHomLift.eq_of_isHomLift _ _ _ _ pointOverBase.p
          pointObject pointObject c g hg).symm
    cases hb
    cases hfst
    cases hsnd
    rfl⟩
  eq_of_hom {P Q} _ := (basedPullback_eq_point P).trans (basedPullback_eq_point Q).symm

/-- The pseudo-pullback formed in `Cat/TwoArrowGroupoid` has exactly one object. -/
@[stacks 0H2D "pullback in the over-category has one object"]
theorem basedPullbackNatCard :
    Nat.card (PseudoPullback pointOverBase.toBase pointOverBase.toBase).obj = 1 := by
  exact Nat.card_eq_one_iff_exists.mpr ⟨basedPullbackPoint, basedPullback_eq_point⟩

/-- The ordinary categorical pullback and the pseudo-pullback formed in `Cat/TwoArrowGroupoid`
are not equivalent categories. -/
@[stacks 0H2D "the two pullback constructions are inequivalent"]
theorem notEquivalent :
    ¬ Nonempty
      (pointToBase ⊡ pointToBase ≌
        (PseudoPullback pointOverBase.toBase pointOverBase.toBase).obj) := by
  rintro ⟨e⟩
  let eObj : (pointToBase ⊡ pointToBase) ≃
      (PseudoPullback pointOverBase.toBase pointOverBase.toBase).obj :=
    { toFun := e.functor.obj
      invFun := e.inverse.obj
      left_inv := fun P ↦ (IsDiscrete.eq_of_hom (e.unitIso.app P).hom).symm
      right_inv := fun P ↦ IsDiscrete.eq_of_hom (e.counitIso.app P).hom }
  have h := Nat.card_congr eObj
  rw [ordinaryPullbackNatCard, basedPullbackNatCard] at h
  exact (by decide : (2 : ℕ) ≠ 1) h

end TwoArrowCounterexample
end BasedCategory.PseudoPullback
end CategoryTheory
