/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

-- The lifted layer supplies both canonical slice models. This leaf owns only the genuine
-- heterogeneous boundary where source and target may have different total-category universes.
public import ReasLib.CategoryTheory.Fibered.Representable.Lifted
import Mathlib.Tactic.CrossRefAttribute

/-!
# Representable fibred groupoids over a common base

Heterogeneous representability and bridges between fixed-owner and over-base presentations.
-/

@[expose] public section

universe u v w vS wX vX wY vY

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids

/-- The canonical down functor from a lifted slice total category to the ordinary slice total
category commutes with their projections to `C`. -/
theorem sliceLiftToSlice.comm (U : C) :
    Cat.TwoULift.down.{max u v, v, w, vS} (Over U) ⋙ (slice U).p =
      (sliceLift.{u, v, w, vS} U).p := sorry
/- Proof strategy: rewrite `slice.p` and `sliceLift.p`, then reassociate the explicit composite
defining `sliceLift.projection`. -/

/-- Forget the universe lift from `sliceLift U` to the smallest slice fibration `slice U`.
This based functor is the explicit heterogeneous boundary bridge; within a fixed saturated owner,
representability uses `sliceLift U` directly. -/
@[stacks 0046 "universe-forgetting slice bridge"]
def sliceLiftToSlice (U : C) :
    (sliceLift.{u, v, w, vS} U).toBasedCategory ⥤ᵇ
      (slice U).toBasedCategory :=
  BasedFunctor.ofFunctor
    (Cat.TwoULift.down (Over U))
    (sliceLiftToSlice.comm.{u, v, w, vS} U)

/-- The total-category functor of the universe-forgetting slice bridge is the canonical inverse
of mathlib's two-universe lift equivalence. -/
@[simp]
theorem sliceLiftToSlice.toFunctor (U : C) :
    (sliceLiftToSlice.{u, v, w, vS} U).toFunctor =
      Cat.TwoULift.down.{max u v, v, w, vS} (Over U) := sorry
/- Proof strategy: unfold `sliceLiftToSlice` and `BasedFunctor.ofFunctor`. -/

/-- On objects, the universe-forgetting slice bridge is the canonical two-universe down
functor. -/
@[simp]
theorem sliceLiftToSlice.obj (U : C)
    (a : Cat.twoULift.{max u v, v, w, vS} (Over U)) :
    ((sliceLiftToSlice.{u, v, w, vS} U).toFunctor).obj a =
      (Cat.TwoULift.down.{max u v, v, w, vS} (Over U)).obj a := sorry

/-- On morphisms, the universe-forgetting slice bridge is the canonical two-universe down
functor. -/
@[simp]
theorem sliceLiftToSlice.map (U : C)
    {a b : Cat.twoULift.{max u v, v, w, vS} (Over U)} (f : a ⟶ b) :
    ((sliceLiftToSlice.{u, v, w, vS} U).toFunctor).map f =
      (Cat.TwoULift.down.{max u v, v, w, vS} (Over U)).map f := sorry

/-- The canonical two-universe up functor commutes with the ordinary and lifted slice
projections. -/
theorem sliceLiftToSlice.inverse.comm (U : C) :
    Cat.TwoULift.up.{max u v, v, w, vS} (Over U) ⋙
        (sliceLift.{u, v, w, vS} U).p =
      (slice U).p := sorry

/-- The explicit inverse universe bridge from the ordinary slice fibration to its lifted
model. Its total functor is the canonical `Cat.TwoULift.up`. -/
def sliceLiftToSlice.inverse (U : C) :
    (slice U).toBasedCategory ⥤ᵇ
      (sliceLift.{u, v, w, vS} U).toBasedCategory :=
  BasedFunctor.ofFunctor
    (Cat.TwoULift.up (Over U))
    (sliceLiftToSlice.inverse.comm.{u, v, w, vS} U)

/-- The total functor of the explicit inverse slice bridge is the canonical two-universe up
functor. -/
@[simp]
theorem sliceLiftToSlice.inverse.toFunctor (U : C) :
    (sliceLiftToSlice.inverse.{u, v, w, vS} U).toFunctor =
      Cat.TwoULift.up.{max u v, v, w, vS} (Over U) := sorry

/-- On objects, the explicit inverse slice bridge is the canonical two-universe up functor. -/
@[simp]
theorem sliceLiftToSlice.inverse.obj (U : C) (a : Over U) :
    ((sliceLiftToSlice.inverse.{u, v, w, vS} U).toFunctor).obj a =
      (Cat.TwoULift.up.{max u v, v, w, vS} (Over U)).obj a := sorry

/-- On morphisms, the explicit inverse slice bridge is the canonical two-universe up functor. -/
@[simp]
theorem sliceLiftToSlice.inverse.map (U : C) {a b : Over U} (f : a ⟶ b) :
    ((sliceLiftToSlice.inverse.{u, v, w, vS} U).toFunctor).map f =
      (Cat.TwoULift.up.{max u v, v, w, vS} (Over U)).map f := sorry

/-- The canonical universe-forgetting map from `sliceLift U` to `slice U` is an equivalence over
the base. -/
instance sliceLiftToSlice.isEquivalence (U : C) :
    (sliceLiftToSlice.{u, v, w, vS} U).IsEquivalence := sorry
/- Proof strategy: use `Cat.TwoULift.up (Over U)` as inverse and lift the unit and counit of
`Cat.TwoULift.equiv (Over U)` to vertical based natural isomorphisms. -/

/-- The explicit inverse universe bridge is itself an equivalence over the base. -/
instance sliceLiftToSlice.inverse.isEquivalence (U : C) :
    (sliceLiftToSlice.inverse.{u, v, w, vS} U).IsEquivalence := sorry

/-- The generic inverse selected from the equivalence property agrees with the explicit
two-universe up bridge. This lets downstream code use concrete inverse computations without
unfolding a choice. -/
@[simp]
theorem sliceLiftToSlice.inv (U : C) :
    (sliceLiftToSlice.{u, v, w, vS} U).inv =
      sliceLiftToSlice.inverse.{u, v, w, vS} U := sorry

/-- Heterogeneous-universe presentation of representability. This companion is reserved for
resizing boundaries where the source object and the canonical slice model do not inhabit one
fixed bicategory. The canonical mathematical owner is `IsRepresentable`. -/
@[stacks 0046 "heterogeneous-universe representability"]
def IsRepresentable.OverBase :
    ObjectProperty (FiberedCategoryOver.Groupoids.{u, v, w, vS} C) :=
  fun X ↦
    ∃ (U : C) (j : X.toBasedCategory ⥤ᵇ (slice U).toBasedCategory),
      BasedFunctor.IsEquivalence j

/-- A based equivalence over the base to a canonical slice fibration directly exhibits the
heterogeneous-boundary form of representability. This constructor is for a genuine universe
boundary; same-owner applications should use `IsRepresentable.ofEquivalence`. -/
theorem IsRepresentable.OverBase.ofBasedEquivalence
    {X : FiberedCategoryOver.Groupoids.{u, v, wX, vX} C} {U : C}
    (j : X.toBasedCategory ⥤ᵇ (slice U).toBasedCategory)
    [BasedFunctor.IsEquivalence j] :
    IsRepresentable.OverBase X := sorry

/-- Heterogeneous representability is exactly the existence of a representing object and a
based equivalence to its ordinary slice fibration. -/
theorem IsRepresentable.OverBase.iff_exists_basedEquivalence
    (X : FiberedCategoryOver.Groupoids.{u, v, wX, vX} C) :
    IsRepresentable.OverBase X ↔
      ∃ (U : C) (j : X.toBasedCategory ⥤ᵇ (slice U).toBasedCategory),
        BasedFunctor.IsEquivalence j := sorry

/-- Eliminate heterogeneous representability into a representing object and an equivalence over
the base to its ordinary slice fibration. -/
theorem IsRepresentable.OverBase.exists_basedEquivalence
    {X : FiberedCategoryOver.Groupoids.{u, v, wX, vX} C}
    (hX : IsRepresentable.OverBase X) :
    ∃ (U : C) (j : X.toBasedCategory ⥤ᵇ (slice U).toBasedCategory),
      BasedFunctor.IsEquivalence j := sorry
/- Proof strategy: unfold `IsRepresentable.OverBase`. -/

namespace IsRepresentable

/-- In the ordinary fixed bicategory, the canonical representability property agrees with its
heterogeneous based-functor presentation. -/
theorem iff_overBase
    (X : FiberedCategoryOver.Groupoids C) :
    X.IsRepresentable ↔ IsRepresentable.OverBase X := sorry
/- Proof strategy: convert between bicategorical equivalences and quasi-invertible based
functors using `BasedFunctor.isEquivalence_iff_exists_equivalence`. -/

/-- In the ordinary owner, canonical and lifted representability agree. This bridge lets
universe-generic infrastructure specialize without exposing resizing details to applications. -/
theorem iff_lifted
    (X : FiberedCategoryOver.Groupoids C) :
    IsRepresentable X ↔ IsRepresentable.Lifted.{u, v, 0, 0} X := sorry
/- Proof strategy: compare both properties through `IsRepresentable.OverBase`. -/

end IsRepresentable

namespace IsRepresentable.Lifted

/-- In a universe-saturated fixed bicategory, lifted representability agrees with the
heterogeneous based-functor presentation. -/
theorem iff_overBase
    (X : FiberedCategoryOver.Groupoids.{u, v,
      max w (max u v), max vS v} C) :
    IsRepresentable.Lifted X ↔ IsRepresentable.OverBase X := sorry
/- Proof strategy: convert a bicategorical equivalence to its based forward morphism and compose
with `sliceLiftToSlice`. Conversely, compose a heterogeneous slice presentation with a
quasi-inverse of `sliceLiftToSlice` and package the resulting same-owner data as a bicategorical
equivalence. -/

end IsRepresentable.Lifted

namespace IsRepresentable.OverBase

/-- The heterogeneous representability companion is invariant under a universe-changing
equivalence over the base. -/
theorem iff_of_basedEquivalence
    {X : FiberedCategoryOver.Groupoids.{u, v, wX, vX} C}
    {Y : FiberedCategoryOver.Groupoids.{u, v, wY, vY} C}
    (e : X.toBasedCategory ⥤ᵇ Y.toBasedCategory)
    [BasedFunctor.IsEquivalence e] :
    IsRepresentable.OverBase X ↔ IsRepresentable.OverBase Y := sorry
/- Proof strategy: compose a chosen slice presentation with a based quasi-inverse of `e` in one
direction and with `e` in the other, using closure of `BasedFunctor.IsEquivalence` under
composition. -/

end IsRepresentable.OverBase

end FiberedCategoryOver.Groupoids

end CategoryTheory
