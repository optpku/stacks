/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Data.ZMod.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic
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

/- Data audit: `#print axioms` is clean up to `[propext, Classical.choice, Quot.sound]` for
`pointToBase` and `ordinaryPullbackPoint`. The `sorryAx` reported for `pointLift` and
`basedPullbackPoint` is confined to the equality-proof fields supplied by `pointToBase_obj` and
`baseIdentity_obj`; their object, functor, and comparison-isomorphism payloads remain explicit. -/

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
    pointOverBase.p.obj pointObject = baseObject := sorry
/- Proof strategy: unfold `pointOverBase`, `pointToBase`, and `pointObject`; the object map of
`Functor.fromPUnit` is definitionally constant at `baseObject`. -/

/-- The identity functor fixes the unique base object. -/
theorem baseIdentity_obj :
    (𝟭 TwoArrowGroupoid).obj baseObject = baseObject := sorry
/- Proof strategy: reduce the object map with `Functor.id_obj`; both sides are then
`baseObject`. -/

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
    (ordinaryPullbackPoint g).iso.hom = g := sorry
/- Proof strategy: unfold `ordinaryPullbackPoint` and use `asIso_hom`; the
`SingleObj` groupoid instance supplies the inverse of the chosen arrow. -/

/-- The ordinary categorical pullback of the one-point category with itself over the two-arrow
groupoid is discrete. -/
@[stacks 0H2D "ordinary categorical pullback is discrete"]
instance ordinaryPullbackIsDiscrete : IsDiscrete (pointToBase ⊡ pointToBase) := sorry
/- Proof strategy: use `CategoricalPullback.hom_ext` and the subsingleton hom-types of
`Discrete PUnit` for morphism uniqueness. For `IsDiscrete.eq_of_hom`, the compatibility field
`CategoricalPullback.Hom.w` identifies the two comparison arrows; reconstruct both endpoints
with `ordinaryPullbackPoint` and `ordinaryPullbackPoint_iso_hom`. -/

/-- The ordinary categorical pullback has exactly two objects. -/
@[stacks 0H2D "ordinary categorical pullback has two objects"]
theorem ordinaryPullbackNatCard :
    Nat.card (pointToBase ⊡ pointToBase) = 2 := sorry
/- Proof strategy: send a pullback object to its comparison arrow and use
`ordinaryPullbackPoint` as inverse. Prove the inverse laws with
`ordinaryPullbackPoint_iso_hom` and extensionality for the unique point components, apply
`Nat.card_congr`, and finish with `Nat.card_zmod`; `Multiplicative` leaves the carrier unchanged. -/

/-- Every object of the pseudo-pullback in `Cat/TwoArrowGroupoid` is the
identity-comparison point. -/
@[stacks 0H2D "over-base pullback has only the identity comparison point"]
theorem basedPullback_eq_point
    (P : (PseudoPullback pointOverBase.toBase pointOverBase.toBase).obj) :
    P = basedPullbackPoint := sorry
/- Proof strategy: eliminate the unique base and point objects, then apply
`PseudoPullback.comparison.isHomLift` to the structural comparison. Since the target projection
is the identity functor, `IsHomLift.eq_of_isHomLift` forces the underlying arrow to be
`𝟙 baseObject`; use `Functor.Fiber.hom_ext` and isomorphism extensionality to identify the
remaining comparison with `Iso.refl identityLift`. -/

/-- The pseudo-pullback formed in `Cat/TwoArrowGroupoid` is discrete. -/
@[stacks 0H2D "pullback in the over-category is discrete"]
instance basedPullbackIsDiscrete :
    IsDiscrete (PseudoPullback pointOverBase.toBase pointOverBase.toBase).obj := sorry
/- Proof strategy: identify both endpoints with `basedPullbackPoint` using
`basedPullback_eq_point`. Morphisms are equal by `PseudoPullback.hom_ext`, since both components
lie in the subsingleton hom-types of `Discrete PUnit`; the same point identification supplies
`IsDiscrete.eq_of_hom`. -/

/-- The pseudo-pullback formed in `Cat/TwoArrowGroupoid` has exactly one object. -/
@[stacks 0H2D "pullback in the over-category has one object"]
theorem basedPullbackNatCard :
    Nat.card (PseudoPullback pointOverBase.toBase pointOverBase.toBase).obj = 1 := sorry
/- Proof strategy: apply `Nat.card_eq_one_iff_unique`; nonemptiness is witnessed by
`basedPullbackPoint`, and subsingleton equality is exactly `basedPullback_eq_point`. -/

/-- The ordinary categorical pullback and the pseudo-pullback formed in `Cat/TwoArrowGroupoid`
are not equivalent categories. -/
@[stacks 0H2D "the two pullback constructions are inequivalent"]
theorem notEquivalent :
    ¬ Nonempty
      (pointToBase ⊡ pointToBase ≌
        (PseudoPullback pointOverBase.toBase pointOverBase.toBase).obj) := sorry
/- Proof strategy: from a supposed equivalence, use its functor and inverse object maps to build
an equivalence of object types; the unit and counit components become equalities by
`IsDiscrete.eq_of_hom`. Apply `Nat.card_congr`, then rewrite with `ordinaryPullbackNatCard` and
`basedPullbackNatCard` to obtain `2 = 1`. -/

end TwoArrowCounterexample
end BasedCategory.PseudoPullback
end CategoryTheory
