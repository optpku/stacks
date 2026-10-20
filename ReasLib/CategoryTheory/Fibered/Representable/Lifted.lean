/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

-- The basic layer owns the ordinary slice model and fixed-owner representability property.
-- The discrete-fibration ULift layer makes the lifted projection compositional by typeclass search.
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.ULift
public import ReasLib.CategoryTheory.Fibered.Representable.Slice
import Mathlib.Tactic.CrossRefAttribute

/-!
# Universe-resized representable fibred groupoids

Same-owner slice models and representability in universe-saturated bicategories.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids

/-- The slice projection lifted independently in its object and morphism universes. Its
non-Prop data are the canonical universe-forgetting equivalence followed by `Over.forget U`. -/
@[stacks 0046 "universe-resized slice projection"]
abbrev sliceLift.projection (U : C) :
    Cat.twoULift.{max u v, v, w, vS} (Over U) ⥤ C :=
  Cat.TwoULift.down (Over U) ⋙ Over.forget U

/-- The canonical slice fibration represented by `U`, resized into the owner whose total object
and morphism universes are respectively `max w (max u v)` and `max vS v`.

This is the same-owner target used by the canonical lifted representability property. It contains
no chosen carrier or map: its projection is the explicit `sliceLift.projection U`. -/
@[stacks 0046 "universe-resized canonical slice fibration"]
def sliceLift (U : C) :
    FiberedCategoryOver.Groupoids.{u, v,
      max w (max u v), max vS v} C :=
  ofFunctor (sliceLift.projection.{u, v, w, vS} U)

/- Axiom audit: `sliceLift` stores the explicit lifted slice category and projection. Its
`sorryAx` dependency is confined to the Prop-valued groupoid-fibration membership witness. -/

/-- The total category of `sliceLift U` is the canonical two-universe lift of `Over U`. -/
@[simp]
theorem sliceLift.total (U : C) :
    (sliceLift.{u, v, w, vS} U).total =
      Cat.twoULift.{max u v, v, w, vS} (Over U) := sorry
/- Proof strategy: unfold `sliceLift`, the owner total projection, and `ofFunctor`. -/

/-- The projection of `sliceLift U` is the explicit lifted slice projection. -/
@[simp]
theorem sliceLift.p (U : C) :
    (sliceLift.{u, v, w, vS} U).p =
      sliceLift.projection.{u, v, w, vS} U := sorry
/- Proof strategy: unfold `sliceLift` and apply `ofFunctor.p`. -/

/-- Representability inside a universe-saturated fixed bicategory. This is the same mathematical
property as `IsRepresentable`, with `sliceLift U` as its same-owner canonical model; ordinary
small-owner applications should use `IsRepresentable`. -/
@[stacks 0046 "universe-resized representability"]
def IsRepresentable.Lifted :
    ObjectProperty
      (FiberedCategoryOver.Groupoids.{u, v,
        max w (max u v), max vS v} C) :=
  fun X ↦
    ∃ U : C, Nonempty (X ≌ sliceLift.{u, v, w, vS} U)

/-- A bicategorical equivalence to a same-owner lifted slice fibration directly exhibits
lifted representability. -/
theorem IsRepresentable.Lifted.ofEquivalence
    {X : FiberedCategoryOver.Groupoids.{u, v,
      max w (max u v), max vS v} C}
    {U : C} (e : X ≌ sliceLift.{u, v, w, vS} U) :
    IsRepresentable.Lifted X := sorry

/-- The universe-saturated representability property is exactly existence of a bicategorical
equivalence to a same-owner lifted slice. -/
theorem IsRepresentable.Lifted.iff_exists_equivalence
    (X : FiberedCategoryOver.Groupoids.{u, v,
      max w (max u v), max vS v} C) :
    IsRepresentable.Lifted X ↔
      ∃ U : C, Nonempty (X ≌ sliceLift.{u, v, w, vS} U) := sorry
/- Proof strategy: unfold `IsRepresentable.Lifted`. -/

/-- Eliminate lifted representability into a representing object and an equivalence to its
same-owner lifted slice fibration. -/
theorem IsRepresentable.Lifted.exists_equivalence
    {X : FiberedCategoryOver.Groupoids.{u, v,
      max w (max u v), max vS v} C}
    (hX : IsRepresentable.Lifted X) :
    ∃ U : C, Nonempty (X ≌ sliceLift.{u, v, w, vS} U) := sorry
/- Proof strategy: apply the forward direction of
`IsRepresentable.Lifted.iff_exists_equivalence X`. -/

/-- In a universe-saturated fixed bicategory, representable objects are exactly the equivalence
closure of its same-owner lifted slice family. -/
theorem IsRepresentable.Lifted.eq_equivalenceClosure :
    (IsRepresentable.Lifted (C := C) :
      ObjectProperty
        (FiberedCategoryOver.Groupoids.{u, v,
          max w (max u v), max vS v} C)) =
      (ObjectProperty.ofObj
        (fun U : C ↦ sliceLift.{u, v, w, vS} U)).equivalenceClosure := sorry
/- Proof strategy: use `IsRepresentable.Lifted.iff_exists_equivalence` and the generic
equivalence-closure membership criterion. -/

/-- Lifted representability is closed under bicategorical equivalence in every saturated fixed
owner universe. -/
instance IsRepresentable.Lifted.isClosedUnderEquivalences :
    (IsRepresentable.Lifted (C := C) :
      ObjectProperty
        (FiberedCategoryOver.Groupoids.{u, v,
          max w (max u v), max vS v} C)).IsClosedUnderEquivalences := sorry
/- Proof strategy: rewrite with `IsRepresentable.Lifted.eq_equivalenceClosure` and use the generic
closure instance. -/

/-- Every same-owner lifted slice fibration is representable. -/
theorem sliceLift.isRepresentable (U : C) :
    IsRepresentable.Lifted (sliceLift.{u, v, w, vS} U) := sorry
/- Proof strategy: apply `IsRepresentable.Lifted.iff_exists_equivalence` with representing object
`U` and the identity bicategorical equivalence. -/

end FiberedCategoryOver.Groupoids

end CategoryTheory
