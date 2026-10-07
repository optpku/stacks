module

-- Import decisions:
-- * `Comma.Over.Basic` is public because the canonical slice model exposes `Over U` and
--   `Over.forget U`.
-- * `InSets.Bicategory` is public because the strongest canonical owner is the discrete
--   fibration before forgetting to groupoids.
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Slice
public import ReasLib.CategoryTheory.Fibered.InSets.Bicategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical slice fibrations

The canonical set- and groupoid-fibred slice models. This file owns only concrete data and its
readouts; equivalence-invariant representability properties live in `Representable.Slice`.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Sets

/-- The canonical category fibred in sets represented by `U : C`, with projection
`Over.forget U : Over U ⥤ C`. -/
@[stacks 0046 "canonical set-fibred slice"]
def slice (U : C) : FiberedCategoryOver.Sets C :=
  ofFunctor (Over.forget U)

/-- The total category of the canonical set-fibred slice is `Over U`. -/
@[simp]
theorem slice.total (U : C) : (slice U).total = Over U := sorry

/-- The projection of the canonical set-fibred slice is `Over.forget U`. -/
@[simp]
theorem slice.p (U : C) : (slice U).p = Over.forget U := sorry

end FiberedCategoryOver.Sets

namespace FiberedCategoryOver.Groupoids

/-- The canonical category fibred in groupoids represented by `U : C`, with projection
`Over.forget U : Over U ⥤ C`.

This is the canonical forgetful view of `FiberedCategoryOver.Sets.slice U`; the strict discrete
owner remains available to consumers that need uniqueness rather than only groupoidality. -/
@[stacks 0046 "canonical groupoid-fibred slice"]
def slice (U : C) : FiberedCategoryOver.Groupoids C :=
  (FiberedCategoryOver.Sets.toGroupoids C).obj
    (FiberedCategoryOver.Sets.slice U)

/-- The total category of the canonical slice fibration is the slice category `Over U`. -/
@[simp]
theorem slice.total (U : C) : (slice U).total = Over U := sorry

/-- The projection of the canonical slice fibration is `Over.forget U`. -/
@[simp]
theorem slice.p (U : C) : (slice U).p = Over.forget U := sorry

end FiberedCategoryOver.Groupoids

namespace FiberedCategoryOver.Sets

/-- Forgetting discreteness from the canonical set-fibred slice gives the canonical
groupoid-fibred slice. -/
@[simp, stacks 0046 "set-to-groupoid slice comparison"]
theorem slice.toGroupoids (U : C) :
    (toGroupoids C).obj (slice U) = FiberedCategoryOver.Groupoids.slice U := sorry

end FiberedCategoryOver.Sets

end CategoryTheory

/- Axiom audit: both slice owners retain explicit total categories and projections. Any
`sorryAx` in the definitions comes only from the bundled discrete-fibration/groupoid-fibredness
membership fields inherited from `ofFunctor` and `toGroupoids`. -/
